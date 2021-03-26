#!/usr/bin/env python3
#
# Router to synchronize RSP, GLUE2, and RDR informaton into the Warehouse Resource tables
#
# Author: JP Navarro, March 2020
#         Jonathan Kim, October 2020
#
# Resource Group:Type
#   Function
# -------------------------------------------------------------------------------------------------
# Organizations:*
#   Write_RSP_Gateway_Providers
#   Write_RSP_Support_Providers
#   Write_RSP_HPC_Providers          -> (including XSEDE)
#   Write_RDR_Providers
#
# Computing Tools and Services:*
#   Write_RSP_HPC_Resources
#   Write_RDR_BaseResources
#   Write_RDR_SubResources
#
# Software:Vendor Software
#   Write_RSP_Vendor_Software
#
# Software:Online Service
#   Write_RSP_Network_Service        -> from RSP Operational Software
#   Write_Glue2_Network_Service      -> from glue2.{AbstractService, Endpoint}
#
# Software:Executable Software
#   Write_RSP_Executable_Software
#   Write_Glue2_Executable_Software  ->from glue2.{ApplicationEnvironment, ApplicationHandle}
#
# Software:Packaged Software
#   Write_RSP_Packaged_Software
#
import argparse
from collections import Counter
from datetime import datetime, timezone, timedelta
from hashlib import md5
import http.client as httplib
import io
import json
import logging
import logging.handlers
import os
from pid import PidFile
import pwd
import re
import shutil
import signal
import ssl
import sys, traceback
from time import sleep
from urllib.parse import urlparse
import pytz
Central = pytz.timezone("US/Central")

import django
django.setup()
from django.conf import settings as django_settings
from django.db import DataError, IntegrityError
from django.forms.models import model_to_dict
from django_markup.markup import formatter
from resource_v3.models import *
from processing_status.process import ProcessingActivity

import elasticsearch_dsl.connections
from elasticsearch import Elasticsearch, RequestsHttpConnection

import pdb

# Used during initialization before loggin is enabled
def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class Format_Description():
#   Initialize a Description that may be html or markup text
#   Functions that append markup
#   Finally convert everything to html using django-markup (don't convert initial if it's already html)
    def __init__(self, value):
        self.markup_stream = io.StringIO()
        self.markup_settings = {'warning_stream': self.markup_stream } # Docutils settings
        self.initial = None
        self.added = None
        if value is None:
            return
        clean_value = value.rstrip()
        if len(clean_value) == 0:
            return
        self.initial = clean_value
    def append(self, value):
        clean_value = value.rstrip()
        if len(clean_value) > 0:
            if self.added is None:
                self.added = clean_value
            else:
                self.added += '\n{0}'.format(clean_value)
    def blank_line(self): # Forced blank line used to start a markup list
        if self.initial or self.added:  # If we have something, prevents blank initial line
            if self.added:
                self.added += '\n'
            else:
                self.added = '\n'
    def html(self, ID=None): # If an ID is provided, log it to record what resource had the warnings
        if self.initial is None and self.added is None:
            return(None)
        initial_html = self.initial and self.initial[:1] == '<'
        if initial_html:
            formatin = '%%INITIAL%%{0}'.format(self.added)
        else:
            formatin = '{0}{1}'.format(self.initial or '', self.added)
        formatout = formatter(formatin, filter_name='restructuredtext', settings_overrides=self.markup_settings)
        warnings = self.markup_stream.getvalue()
        if warnings:
            logger = logging.getLogger('DaemonLog')
            if ID:
                logger.warning('markup warnings for ID: {}'.format(ID))
            for line in warnings.splitlines():
                logger.warning('markup: {}'.format(line))
        if initial_html:
            output = formatout.replace('%%INITIAL%%', self.initial, 1)
        else:
            output = formatout
        return(output)
    
class Router():
    # Initialization BEFORE we know if another self is running
    def __init__(self):
        # Parse arguments
        parser = argparse.ArgumentParser()
        parser.add_argument('--once', action='store_true', \
                            help='Run once and exit, or run continuous with sleep between interations (default)')
        parser.add_argument('--daemon', action='store_true', \
                            help='Run as daemon redirecting stdout, stderr to a file, or interactive (default)')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', dest='config', required=True, \
                            help='Configuration file')
        parser.add_argument('--dev', action='store_true', \
                            help='Running in development environment')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        # Trace for debugging as early as possible
        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        config_path = os.path.abspath(self.args.config)
        try:
            with open(config_path, 'r') as file:
                conf=file.read()
        except IOError as e:
            eprint('Error "{}" reading config={}'.format(e, config_path))
            sys.exit(1)
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            eprint('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        # Configuration verification and processing
        if len(self.config['STEPS']) < 1:
            eprint('Missing config STEPS')
            sys.exit(1)
        
        if self.config.get('PID_FILE'):
            self.pidfile_path =  self.config['PID_FILE']
        else:
            name = os.path.basename(__file__).replace('.py', '')
            self.pidfile_path = '/var/run/{}/{}.pid'.format(name, name)
            
    # Setup AFTER we know that no other self is running
    def Setup(self, peak_sleep=10, offpeak_sleep=60, max_stale=24 * 60):
        # Initialize log level from arguments, or config file, or default to WARNING
        loglevel_str = (self.args.log or self.config.get('LOG_LEVEL', 'WARNING')).upper()
        loglevel_num = getattr(logging, loglevel_str, None)
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(loglevel_num)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], \
            when='W6', backupCount=999, utc=True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Initialize stdout, stderr
        if self.args.daemon and 'LOG_FILE' in self.config:
            self.stdout_path = self.config['LOG_FILE'].replace('.log', '.daemon.log')
            self.stderr_path = self.stdout_path
            self.SaveDaemonStdOut(self.stdout_path)
            sys.stdout = open(self.stdout_path, 'wt+')
            sys.stderr = open(self.stderr_path, 'wt+')

        # Signal handling
        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)

        mode =  ('daemon,' if self.args.daemon else 'interactive,') + \
            ('once' if self.args.once else 'continuous')
        self.logger.critical('Starting mode=({}), program={}, pid={}, uid={}({})'.format(mode, os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

        # Connect Database
        configured_database = django_settings.DATABASES['default'].get('HOST', None)
        if configured_database:
            self.logger.critical('Warehouse database={}'.format(configured_database))
        # Django connects automatially as needed

        # Connect Elasticsearch
        if 'ELASTIC_HOSTS' in self.config:
            self.logger.critical('Warehouse elastichost={}'.format(self.config['ELASTIC_HOSTS']))
            self.ESEARCH = elasticsearch_dsl.connections.create_connection( \
                hosts = self.config['ELASTIC_HOSTS'], \
                connection_class = RequestsHttpConnection, \
                timeout = 10)
            ResourceV3Index.init()              # Initialize it if it doesn't exist
        else:
            self.logger.info('Warehouse elastichost=NONE')
            self.ESEARCH = None

        # Initialize application variables
        self.peak_sleep = peak_sleep * 60       # 10 minutes in seconds during peak business hours
        self.offpeak_sleep = offpeak_sleep * 60 # 60 minutes in seconds during off hours
        self.max_stale = max_stale * 60         # 24 hours in seconds force refresh
        self.application = os.path.basename(__file__)
        self.memory = {}                        # Used to put information in "memory"
        self.Affiliation = 'xsede.org'
        self.DefaultValidity = timedelta(days = 14)

        self.GWPROVIDER_URNMAP = {}             # Mapping of Gateway Name to its GLOBALURN
        self.SUPPORTPROVIDER_URNMAP = {}        # Mapping of Support GlobalID to its GLOBALURN
        self.SUPPORTPROVIDER_URL2URN = {}       # Mapping of Support GlobalID to its Information Services URL

        # HPC PROVIDER ORGANIZATION maps
        self.RSP_HPCPROVIDER_URNMAP = {}        # SiteID to GLOBALURN from RSP
        self.RDR_HPCPROVIDER_URNMAP = {}        # Organization ID to GLOBALURN from RDR

        # HPC RESOURCE maps from ResourceID to a GLOBALRUN
        self.RSP_HPCRESOURCE_URNMAP = {}        # Original from RSP
        self.RDR_HPCRESOURCE_URNMAP = {}        # Replacement from RDR

        self.RSP_HPCRESOURCE_INFO = {}              # Resource detail by ResourceID
        self.RDRRESOURCE_BASE_URNMAP = {}       # Mapping of RDR base-resource id to its GLOBALURN
        self.RDRRESOURCE_INFOID_URNMAP = {}     # Mapping of RDR base-resource infoid to its GLOBALURN
        self.RDRRESOURCE_SUB_URNMAP = {}        # Mapping of RDR sub-resource id to its GLOBALURN
        if self.args.dev:
            self.WAREHOUSE_API_PREFIX = 'http://localhost:8000'
        else:
            self.WAREHOUSE_API_PREFIX = 'https://info.xsede.org/wh1'
        self.WAREHOUSE_API_VERSION = 'v3'
        self.WAREHOUSE_CATALOG = 'ResourceV3'

        # Used in Get_HTTP as memory cache for contents
        self.HTTP_CACHE = {}
        self.URL_USE_COUNT = {}

        # Loading all the Catalog entries for our affiliation
        self.CATALOGS = {}
        for cat in ResourceV3Catalog.objects.filter(Affiliation__exact=self.Affiliation):
            self.CATALOGS[cat.ID] = model_to_dict(cat)

        self.STEPS = []
        for stepconf in self.config['STEPS']:
            if 'CATALOGURN' not in stepconf:
                self.logger.error('Step CATALOGURN is missing or invalid')
                self.exit(1)
            if stepconf['CATALOGURN'] not in self.CATALOGS:
                self.logger.error('Step CATALOGURN is not define in Resource Catalogs')
                self.exit(1)
            myCAT = self.CATALOGS[stepconf['CATALOGURN']]
            stepconf['SOURCEURL'] = myCAT['CatalogAPIURL']
            
            # if use the same CatalogAPIURL, count and keep 
            if stepconf['SOURCEURL'] in self.URL_USE_COUNT:
                self.URL_USE_COUNT[stepconf['SOURCEURL']] += 1
            else:
                self.URL_USE_COUNT[stepconf['SOURCEURL']] = 1

            try:
                SRCURL = urlparse(stepconf['SOURCEURL'])
            except:
                self.logger.error('Step SOURCE is missing or invalid')
                self.exit(1)
            if SRCURL.scheme not in ['file', 'http', 'https']:
                self.logger.error('Source not {file, http, https}')
                self.exit(1)
            stepconf['SRCURL'] = SRCURL
            
            try:
                DSTURL = urlparse(stepconf['DESTINATION'])
            except:
                self.logger.error('Step DESTINATION is missing or invalid')
                self.exit(1)
            if DSTURL.scheme not in ['file', 'analyze', 'function', 'memory']:
                self.logger.error('Destination is not one of {file, analyze, function, memory}')
                self.exit(1)
            stepconf['DSTURL'] = DSTURL
            
            if SRCURL.scheme in ['file'] and DSTURL.scheme in ['file']:
                self.logger.error('Source and Destination can not both be a {file}')
                self.exit(1)
                
            # Merge CATALOG config and STEP config, with the latter taking precendence
            self.STEPS.append({**self.CATALOGS[stepconf['CATALOGURN']], **stepconf})

    def SaveDaemonStdOut(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            file = open(path, 'r')
            lines = file.read()
            file.close()
            if not re.match("^started with pid \d+$", lines) and not re.match("^$", lines):
                ts = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                newpath = '{}.{}'.format(path, ts)
                self.logger.debug('Saving previous daemon stdout to {}'.format(newpath))
                shutil.copy(path, newpath)
        except Exception as e:
            self.logger.error('Exception in SaveDaemonStdOut({})'.format(path))
        return

    def exit_signal(self, signum, frame):
        self.logger.critical('Caught signal={}({}), exiting with rc={}'.format(signum, signal.Signals(signum).name, signum))
        sys.exit(signum)
        
    def exit(self, rc):
        if rc:
            self.logger.error('Exiting with rc={}'.format(rc))
        sys.exit(rc)

    def CATALOGURN_to_URL(self, id):
        return('{}/resource-api/{}/catalog/id/{}/'.format(self.WAREHOUSE_API_PREFIX, self.WAREHOUSE_API_VERSION, id))
        
    def format_GLOBALURN(self, *args):
        newargs = list(args)
        newargs[0] = newargs[0].rstrip(':')
        return(':'.join(newargs))

    def Get_HTTP(self, url, contype):
        # return previously saved data if the source is the same 
        data_cache_key = contype + ':' + url.geturl()
        if data_cache_key in self.HTTP_CACHE:
            return({contype: self.HTTP_CACHE[data_cache_key]})

        headers = {}
        # different headers for RDR site 
        if 'rdr.xsede.org' == url.hostname:
            headers = {'Content-type': 'application/json',
                        'XA-CLIENT': 'XSEDE',
                        'XA-KEY-FORMAT': 'underscore'}
        ctx = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        conn = httplib.HTTPSConnection(host=url.hostname, port=getattr(url, 'port', None), context=ctx)

        conn.request('GET', url.path, None, headers)
        self.logger.debug('HTTP GET {}'.format(url.geturl()))
        response = conn.getresponse()
        result = response.read().decode("utf-8-sig")
        self.logger.debug('HTTP RESP {} {} (returned {}/bytes)'.format(response.status, response.reason, len(result)))
        try:
            content = json.loads(result)
        except ValueError as e:
            self.logger.error('Response not in expected JSON format ({})'.format(e))
            return(None)
        else:
            # cache content only for the url used more than once
            if url.geturl() in self.URL_USE_COUNT:
                if (self.URL_USE_COUNT[url.geturl()] > 1):
                    # save retrieved content to the HTTP_CACHE to reuse from memory
                    self.HTTP_CACHE[data_cache_key] = content
            return({contype: content})

    def Analyze_CONTENT(self, content):
        # Write when needed
        return(0, '')

    def Write_MEMORY(self, content, contype, conkey):
        # Stores in a dictionary for reference by other processing steps
        if contype not in self.memory:
            self.memory[contype] = {}
        for item in content[contype]:
            try:
                self.memory[contype][item[conkey]] = item
            except:
                pass
        return(0, '')

    def Write_CACHE(self, file, content):
        data = json.dumps(content)
        with open(file, 'w') as my_file:
            my_file.write(data)
        self.logger.info('Serialized and wrote {} bytes to file={}'.format(len(data), file))
        return(0, '')

    def Read_CACHE(self, file, contype):
        with open(file, 'r') as my_file:
            data = my_file.read()
            my_file.close()
        try:
            content = json.loads(data)
            self.logger.info('Read and parsed {} bytes from file={}'.format(len(data), file))
            return({contype: content})
        except ValueError as e:
            self.logger.error('Error "{}" parsing file={}'.format(e, file))
            self.exit(1)

########## CUSTOMIZATIONS START ##########
    #
    # Delete old items (those in 'cur') that weren't updated (those in 'new')
    #
    def Delete_OLD(self, me, cur, new):
        for URN in [id for id in cur if id not in new]:
            if self.ESEARCH:
                try:
                    ResourceV3Index.get(id = URN).delete()
                except Exception as e:
                    self.logger.error('{} deleting Elastic id={}: {}'.format(type(e).__name__, URN, e))
            try:
                ResourceV3Relation.objects.filter(FirstResourceID__exact = URN).delete()
                ResourceV3.objects.get(pk = URN).delete()
                ResourceV3Local.objects.get(pk = URN).delete()
            except Exception as e:
                self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, URN, e))
            else:
                self.logger.info('{} deleted ID={}'.format(me, URN))
                self.STATS.update({me + '.Delete'})

    #
    # Update relations and delete relations for myURN that weren't just updated (newIDS)
    #
    def Update_REL(self, myURN, newRELATIONS):
        newIDS = []
        for relatedID in newRELATIONS:
            try:
                relationType = newRELATIONS[relatedID]
                relationHASH = md5(':'.join([relatedID, relationType]).encode('UTF-8')).hexdigest()
                relationID = ':'.join([myURN, relationHASH])
                relation = ResourceV3Relation(
                            ID = relationID,
                            FirstResourceID = myURN,
                            SecondResourceID = relatedID,
                            RelationType = relationType,
                     )
                relation.save()
            except Exception as e:
                msg = '{} saving Relation ID={}: {}'.format(type(e).__name__, relationID, e)
                self.logger.error(msg)
                return(False, msg)
            newIDS.append(relationID)
        try:
            ResourceV3Relation.objects.filter(FirstResourceID__exact = myURN).exclude(ID__in = newIDS).delete()
        except Exception as e:
            self.logger.error('{} deleting Relations for Resource ID={}: {}'.format(type(e).__name__, myURN, e))
    #
    # Log how long a processing step took
    #
    def Log_STEP(self, me):
        summary_msg = 'Processed {} in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format(me,
            self.PROCESSING_SECONDS[me],
            self.STATS[me + '.Update'], self.STATS[me + '.Delete'], self.STATS[me + '.Skip'])
        self.logger.info(summary_msg)
    #
    # Determine which RDR resources are active
    #
    def Is_Active_RDR(self, allresources, organization=None, resource=None):
        if not hasattr(self, 'RDRACTIVEORGANIZATIONS') or not hasattr(self, 'RDRACTIVERESOURCES'):
            self.Identity_RDRACTIVE(allresources)
        if organization and organization in self.RDRACTIVEORGANIZATIONS:
            return(True)
        if resource and resource in self.RDRACTIVERESOURCES:
            return(True)
        return(False)
    #
    # Parallels the filter in django_xsede_warehouse/rdr_db.filters.py except:
    # - All provider_levels
    # - Doesn't have to be allocated
    #
    def Identity_RDRACTIVE(self, allresources):
        active_status_set = set(['friendly', 'coming soon', 'pre-production', 'production', 'post-production'])
        excluded_resourceid_set = set(['stand-alone.tg.teragrid.org', 'futuregrid0.futuregrid.xsede.org', 'Abe-QB-Grid.teragrid.org'])
        self.RDRACTIVEORGANIZATIONS = {}        # Keyed by organization_id
        self.RDRACTIVERESOURCES = {}            # Keyed by info_resourceid
        for baseresource in allresources:
            if baseresource['project_affiliation'] != 'XSEDE' or \
                    baseresource['xsede_services_only'] or \
                    baseresource['info_resourceid'] in excluded_resourceid_set or \
                    not list(set(baseresource['current_statuses']) & active_status_set):        # This finds the intersection
                continue
            for subtype in ['compute_resources', 'storage_resources']:
                if subtype not in baseresource:
                    continue
                for subresource in baseresource[subtype]:       # This is a list
                    if not list(set(subresource['current_statuses']) & active_status_set):      # This finds the intersection
                        continue
                    # We now have an active sub-resource, add it, its baseresource, and its organizations
                    self.RDRACTIVERESOURCES[subresource['info_resourceid']] = True
                    self.RDRACTIVERESOURCES[baseresource['info_resourceid']] = True
                    for org in baseresource['organizations']:
                        self.RDRACTIVEORGANIZATIONS[org['organization_id']] = True
    #
    # This function populates self.GWPROVIDER_URNMAP
    #
    def Write_RSP_Gateway_Providers(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Organizations'
        myRESTYPE = 'Online Service'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)
        
        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact = self.Affiliation).filter(ID__startswith = config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            self.GWPROVIDER_URNMAP[item['Name']] = myGLOBALURN
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = 'The {} Science Gateway Project'.format(item['Name'])
                Description = Format_Description(item.get('Description'))
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = 'Production',
                            Name = item['Name'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = None,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = item['FieldScience'],
                            Keywords = None,
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing()
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
                
            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    #
    # This function populates self.SUPPORTPROVIDER_URNMAP
    #
    def Write_RSP_Support_Providers(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Organizations'
        myRESTYPE = 'Consulting and Support'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
#           As of 2020-05-12 we need all the support providers, JP
#            if (item.get('GlobalID') or '') == 'helpdesk.xsede.org': # We're only using HPC_Provider for now
#                continue
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            self.SUPPORTPROVIDER_URNMAP[item['GlobalID']] = myGLOBALURN
            myINFOURL = 'https://info.xsede.org/wh1/xcsr-db/v1/supportcontacts/globalid/{}/'.format(item['GlobalID'])
            self.SUPPORTPROVIDER_URL2URN[myINFOURL] = myGLOBALURN
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = None
                Description = Format_Description(item.get('Description'))
                Description.blank_line()
                for c in ['ContactURL', 'ContactEmail', 'ContactPhone']:
                    if c in item and item[c] is not None and item[c] is not '':
                        Description.append('- {} is {}'.format(c, item[c]))
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = 'Production',
                            Name = item['Name'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = None,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = 'Support',
                            Keywords = None,
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing()
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
                
            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')
        
    ####################################
    #
    # This function populates self.RSP_HPCPROVIDER_URNMAP
    # Obselete on 03-25-2021 as we replace RSP Providers with RDR Providers
    #
    def Write_RSP_HPC_Providers(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Organizations'
        myRESTYPE = 'Provider'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            self.RSP_HPCPROVIDER_URNMAP[item['SiteID']] = myGLOBALURN
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = None
                Description = Format_Description(item.get('Description'))
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = 'Production',
                            Name = item['Name'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = None,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = 'HPC',
                            Keywords = item['SiteID'],
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing()
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
                
            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    #
    # This function populates self.RSP_HPCPROVIDER_URNMAP
    # Replaces on 03-25-2021 Write_RSP_HPC_Providers
    #
    def Memory_RSP_HPC_Providers(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        me = '{} to RSP_HPCPROVIDER_URNMAP'.format(sys._getframe().f_code.co_name)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        for item in content[contype]:
            self.RSP_HPCPROVIDER_URNMAP[item['SiteID']] = item.get('GlobalResourceID')
            self.STATS.update({me + '.Update'})
        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    #
    # This function populates self.RSP_HPCRESOURCE_URNMAP and self.RSP_HPCRESOURCE_INFO
    # Obselete on 03-25-2021 as we replace RSP Resources with RDR Resources
    #
    def Write_RSP_HPC_Resources(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Computing Tools and Services'
        myRESTYPE = 'Research Computing'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            self.RSP_HPCRESOURCE_URNMAP[item['ResourceID']] = myGLOBALURN
            self.RSP_HPCRESOURCE_INFO[item['ResourceID']] = item
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            providerURN = self.RSP_HPCPROVIDER_URNMAP.get(item.get('SiteID', ''))
#            providerURN = self.RDR_HPCPROVIDER_URNMAP.get(item.get('SiteID', ''))
            if providerURN:
                myNEWRELATIONS[providerURN] = 'Provided By'
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = None
                Description = Format_Description('{} operated by {}'.format(item['Name'], item['SiteName']))
                Keywords = ','.join([item['SiteID'], item['ResourceID']])
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = 'Production',
                            Name = item['Name'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = 'HPC',
                            Keywords = Keywords,
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
                
            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    #
    # This function populates self.RSP_HPCRESOURCE_INFO
    # Replaces on 03-25-2021 Write_RSP_HPC_Providers
    #
    def Memory_RSP_HPC_Resources(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        me = '{} to RSP_HPCRESOURCE_INFO'.format(sys._getframe().f_code.co_name)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        for item in content[contype]:
            self.RSP_HPCRESOURCE_INFO[item['ResourceID']] = item
            self.STATS.update({me + '.Update'})

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    def Write_RSP_Vendor_Software(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Vendor Software'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}     # Current items
        new = {}     # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            # Items can have a related ProviderID (Vendor), SupportOrganizationGlobalID, ParentComponentID (Element)
            # Set relations: Provided By (Vendor), Supported By, Element Of (Parent)
            if item.get('ParentNodeid'):
                parentURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['ParentNodeid'])
                myNEWRELATIONS[parentURN] = 'Component Of'
            supportURN = None
            providerURN = None
            if item.get('Vendor') == 'Globus':
                supportURN = 'urn:ogf:glue2:info.xsede.org:resource:rsp:support.organizations:drupalnodeid:1565'
            elif item.get('Vendor') == 'XSEDE':
                supportURN = 'urn:ogf:glue2:info.xsede.org:resource:rsp:support.organizations:drupalnodeid:1553'
                providerURN = 'urn:ogf:glue2:info.xsede.org:resource:rdr:resource.organizations:2438'
            elif item.get('Vendor') == 'NCSA':
                supportURN = 'urn:ogf:glue2:info.xsede.org:resource:rsp:support.organizations:drupalnodeid:1553'
                providerURN = 'urn:ogf:glue2:info.xsede.org:resource:rdr:resource.organizations:844'
            if supportURN:
                myNEWRELATIONS[supportURN] = 'Supported By'
            if providerURN:
                myNEWRELATIONS[providerURN] = 'Provided By'
                
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = None
                Description = Format_Description(item.get('Description'))
                Description.blank_line()
                if item.get('VendorSoftwareURL'):
                    Description.append('- Vendor Software URL: ' + item.get('VendorSoftwareURL'))
                if item.get('RelatedDiscussionForums'):
                    Description.append('- Related Discussion Forum: ' + item.get('RelatedDiscussionForums'))
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = 'Production',
                            Name = item['CommonName'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = None,
                            Keywords = item['Tags'],
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)

            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})
 
        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    def Write_RSP_Network_Service(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Online Service'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        ##########
        # Load with selected items for GLUE2 Abstract Service and Endpoint
        RSP2GLUE2 = {}
        ##########
        
        cur = {}     # Current items
        new = {}     # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            if item['AccessType'] != 'Network Service':
                continue
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            # Items can have HostingResourceID and related SiteID, ScienceGatewayName, SupportOrganizationGlobalID
            # Set relations: Gateway Integrated, Hosted On, Supported By
            gatewayURN = self.GWPROVIDER_URNMAP.get(item.get('ScienceGatewayName', ''), None)
            siteURN = self.RSP_HPCPROVIDER_URNMAP.get(item.get('SiteID', ''), None)
#            siteURN = self.RDR_HPCPROVIDER_URNMAP.get(item.get('SiteID', ''), None)
#            resourceURN = self.RSP_HPCRESOURCE_URNMAP.get(item.get('HostingResourceID', ''), None)
            resourceURN = self.RDR_HPCRESOURCE_URNMAP.get(item.get('HostingResourceID', ''), None)
            supportURN = self.SUPPORTPROVIDER_URNMAP.get(item.get('SupportOrganizationGlobalID', ''), None)

            providerURNxsede = self.RSP_HPCPROVIDER_URNMAP.get('xsede.org', None) \
                if item.get('SupportOrganizationGlobalID', '') == 'helpdesk.xsede.org' else None
#            providerURNxsede = self.RDR_HPCPROVIDER_URNMAP.get('xsede.org', None) \
#                if item.get('SupportOrganizationGlobalID', '') == 'helpdesk.xsede.org' else None
            # ProviderID priority order of Gateway, (SP) Site, or XSEDE (if supported by XSEDE)
            providerURN = gatewayURN or siteURN or providerURNxsede
            if providerURN:
                myNEWRELATIONS[providerURN] = 'Provided By'
            if gatewayURN:
                myNEWRELATIONS[gatewayURN] = 'Gateway Integrated'
            if resourceURN:
                myNEWRELATIONS[resourceURN] = 'Hosted On'
            if supportURN:
                myNEWRELATIONS[supportURN] = 'Supported By'
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = None
                Description = Format_Description(item.get('Description') or item.get('Title') or None)
                Description.blank_line()
                if item.get('NetworkServiceEndpoints'):
                    Description.append('- Service Access URL: {}'.format(item.get('NetworkServiceEndpoints')))
                if item.get('UserDocumentationURL'):
                    Description.append('- Service Documentation: {}'.format(item.get('UserDocumentationURL')))
                if item.get('VendorSoftwareURL') and item.get('NetworkServiceEndpoints') and item.get('VendorSoftwareURL') != item.get('NetworkServiceEndpoints'):
                    Description.append('- Vendor Software URL: {}'.format(item.get('VendorSoftwareURL')))
                if item.get('VendorURL') and item.get('VendorSoftwareURL') and item.get('VendorURL') != item.get('VendorSoftwareURL'):
                    Description.append('- Vendor URL: {}'.format(item.get('VendorURL')))
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = item.get('ServingState', 'Production').capitalize(),
                            Name = item['Title'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = None,
                            Keywords = item['Keywords'],
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)

            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})
            
            
#            if item.get('VendorSoftwareURL','') == 'http://grid.ncsa.illinois.edu/ssh/' and
#                    item.get('HostingResourceID'):
#                RSP2GLUE2[myGLOBALURN] = item
#       }
 
        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    def Write_Glue2_Network_Service(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Online Service'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = item['ID']        # Glue2 entities already have a unique ID
            if not self.RSP_HPCRESOURCE_INFO.get(item['ResourceID']):
                msg = 'Undefined ResourceID={} in Local ID={}'.format(item['ResourceID'], myGLOBALURN)
                self.logger.error(msg)
                break
                
            mySiteID = self.RSP_HPCRESOURCE_INFO.get(item['ResourceID'])['SiteID']
            providerURN = self.RSP_HPCPROVIDER_URNMAP[mySiteID]
#            providerURN = self.RDR_HPCPROVIDER_URNMAP.get(mySiteID)
#            myResourceURN = self.RSP_HPCRESOURCE_URNMAP.get(item['ResourceID'])
            myResourceURN = self.RDR_HPCRESOURCE_URNMAP.get(item['ResourceID'])
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            if providerURN:
                myNEWRELATIONS[providerURN] = 'Provided By'
            if myResourceURN:
                myNEWRELATIONS[myResourceURN] = 'Hosted On'
            try: # Convert SupportContact URL into a Support Provider Resource URN
                mySUPPORTURN = self.SUPPORTPROVIDER_URL2URN.get(item['SupportContact'])
                if mySUPPORTURN:
                    myNEWRELATIONS[mySUPPORTURN] = 'Supported By'
            except:
                continue

            if item['InterfaceName'] == 'org.globus.gridftp':
                Name = 'GridFTP data transfer endpoint'
                Description = Format_Description('Globus GridFTP data transfer endpoint')
                Keywords = 'gridftp,data,transfer'
            elif item['InterfaceName'] == 'org.globus.openssh':
                Name = 'GSI OpenSSH login service'
                Description = Format_Description('Globus GSI OpenSSH remote login service')
                Keywords = 'openssh,scp,ssh,login'
            elif item['InterfaceName'] == 'org.globus.gram':
                Name = 'GRAM5 execution service'
                Description = Format_Description('Globus GRAM5 remote execution service')
                Keywords = 'gram5,job,execution'
            else:
                Name = item['InterfaceName']
                Description = Format_Description(item['ServiceType'] + ' ' + item['InterfaceName'] + ' ' + item['InterfaceVersion'])
                Keywords = ''
            LocalURL = '{}/glue2-views-api/v1/services/ID/{}/'.format(self.WAREHOUSE_API_PREFIX, item['ID'])

            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = item.get('CreationTime', datetime.now(timezone.utc)),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['ID'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = LocalURL,
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = None
                Description.blank_line()
                if item.get('URL'):
                    Description.append('- Service URL: {}'.format(item.get('URL')))
                try:
                    Description.append('- Running on {} ({})'.format(self.RSP_HPCRESOURCE_INFO[item['ResourceID']]['Name'], item['ResourceID']))
                except:
                    pass
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['ID'],
                            QualityLevel = item.get('ServingState', 'Production').capitalize(),
                            Name = Name,
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = item['ServiceType'],
                            Keywords = Keywords,
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
                
            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    def Write_RSP_Executable_Software(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Executable Software'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            if item['AccessType'] != 'Execution Environment':
                continue
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
                
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
#            myHostedID = self.RSP_HPCRESOURCE_URNMAP.get(item['HostingResourceID'],'')
            myHostedID = self.RDR_HPCRESOURCE_URNMAP.get(item['HostingResourceID'],'')
            if myHostedID:
                myNEWRELATIONS[myHostedID] = 'Hosted On'
            
            # Set new relations and ProviderID to the GW or the SP if not from GW
            if len(item.get('ScienceGatewayName') or '') > 0:
                myGatewayID = self.GWPROVIDER_URNMAP.get(item['ScienceGatewayName'])
                if myGatewayID:
                    myNEWRELATIONS[myGatewayID] = 'Accessible From'

            providerURN = myGatewayID or self.RSP_HPCPROVIDER_URNMAP.get(item['HostingResourceID'].split('.', 1)[1],'')
#            providerURN = myGatewayID or self.RDR_HPCPROVIDER_URNMAP.get(item['HostingResourceID'].split('.', 1)[1],'')
            if providerURN:
                myNEWRELATIONS[providerURN] = 'Provided By'
            
            if len(item.get('SupportOrganizationGlobalID') or '') > 0:
                myRelatedID = self.SUPPORTPROVIDER_URNMAP.get(item['SupportOrganizationGlobalID'])
                if myRelatedID:
                    myNEWRELATIONS[myRelatedID] = 'Supported By'

            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                ShortDescription = (item.get('VendorCommonName') or item.get('Title') or '').strip()
                Description = Format_Description(item.get('Description'))
                Description.blank_line()
                if item.get('NetworkServiceEndpoints'):
                    Description.append('- Service URL: {}'.format(item.get('NetworkServiceEndpoints')))
                if item.get('UserDocumentationURL'):
                    Description.append('- Service Documentation: {}'.format(item.get('UserDocumentationURL')))
                if item.get('VendorSoftwareURL','') != item.get('NetworkServiceEndpoints', ''):
                    Description.append('- Vendor Product URL: {}'.format(item.get('VendorSoftwareURL')))
                if item.get('VendorURL','') != item.get('VendorSoftwareURL', ''):
                    Description.append('- Vendor URL: {}'.format(item.get('VendorURL')))
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = item.get('ServingState', 'Production').capitalize(),
                            Name = item['Title'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = None,
                            Keywords = item['Keywords'],
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)

            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    ####################################
    def Write_Glue2_Executable_Software(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Executable Software'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = item['ID']        # Glue2 entities already have a unique ID
            providerURN = self.RSP_HPCPROVIDER_URNMAP.get(item.get('SiteID', ''))
#            providerURN = self.RDR_HPCPROVIDER_URNMAP.get(item.get('SiteID', ''))
#            myResourceURN = self.RSP_HPCRESOURCE_URNMAP.get(item['ResourceID'])
            myResourceURN = self.RDR_HPCRESOURCE_URNMAP.get(item['ResourceID'])
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            if providerURN:
                myNEWRELATIONS[providerURN] = 'Provided By'
            if myResourceURN:
                myNEWRELATIONS[myResourceURN] = 'Hosted On'
            try: # Convert SupportContact URL into a Support Provider Resource URN
                mySUPPORTURN = self.SUPPORTPROVIDER_URL2URN.get(item['SupportContact'])
                if mySUPPORTURN:
                    myNEWRELATIONS[mySUPPORTURN] = 'Supported By'
            except:
                continue
            
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = item.get('CreationTime', datetime.now(timezone.utc)),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['ID'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = '{}/glue2-views-api/v1/software/ID/{}/'.format(self.WAREHOUSE_API_PREFIX, item['ID']),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try:
                if item.get('SupportStatus'):
                    if isinstance(item['SupportStatus'], list):
                        newlist = list()
                        for i in item['SupportStatus']:
                            newlist.append('Pre-producton' if i.lower() == 'preliminary' else i.capitalize())
                        QualityLevel = ','.join(newlist)
                    else:
                        QualityLevel = item.get('SupportStatus').capitalize()
                        if QualityLevel.lower() == 'preliminary':
                            QualityLevel = 'Pre-production'
                else:
                    QualityLevel = 'Production'

                ShortDescription = item.get('AppName')
                if item.get('AppVersion'):
                    ShortDescription += ' Version {}'.format(item['AppVersion'])
                Description = Format_Description(item.get('Description'))
                Description.blank_line()
                try:
                    Description.append('Running on {} ({})'.format(self.RSP_HPCRESOURCE_INFO[item['ResourceID']]['Name'], item['ResourceID']))
                except:
                    pass
                Handle = item.get('Handle')
                if Handle:
                    if Handle.get('HandleType','').lower() == 'module' and Handle.get('HandleKey'):
                        Description.append('To access from a shell use the command:\n\n  module load {}'.format(Handle.get('HandleKey')))

                if item.get('Domain'):
                    Domain = ','.join(item['Domain'])
                else:
                    Domain = None
                if item.get('Keywords'):
                    if isinstance(item['Keywords'], list):
                        Keywords = ','.join(item['Keywords'])
                    else:
                        Keywords = item.get('Keywords')
                else:
                    Keywords = None
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['ID'],
                            QualityLevel = QualityLevel,
                            Name = item['AppName'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = Domain,
                            Keywords = Keywords,
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)

            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    def Write_RSP_Packaged_Software(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Software'
        myRESTYPE = 'Packaged Software'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items
        new = {}   # New items
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]:
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], 'drupalnodeid', item['DrupalNodeid'])
            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            mySupportOrgID = item.get('SupportOrganizationGlobalID','')
            if mySupportOrgID == 'helpdesk.xsede.org':
                providerURN = 'urn:ogf:glue2:info.xsede.org:resource:rdr:resource.organizations:2438'
                myNEWRELATIONS[providerURN] = 'Provided By'
            else: # TODO: Handle other Support Orgs
                providerURN = None
            supportURN = self.SUPPORTPROVIDER_URNMAP.get(mySupportOrgID, None)
            if supportURN:
                myNEWRELATIONS[supportURN] = 'Supported By'

            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            LocalType = config['LOCALTYPE'],
                            LocalURL = item.get('DrupalUrl', config.get('SOURCEDEFAULTURL', None)),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
                
            try: #TODO
                ShortDescription = item.get('Title','').strip()
                Description = Format_Description(item.get('Description'))
                Description.blank_line()
                TargetAudience = item.get('TargetAudience')
                if TargetAudience:
                    Description.append('For target audience: {}'.format(TargetAudience))
                PackageURL = item.get('PackageURL')
                Description.blank_line()
                if PackageURL:
                    PackageFormat = '({})'.format(item.get('PackageFormat')) if item.get('PackageFormat') else ''
                    Description.append('- Package {} URL: {}'.format(PackageFormat, PackageURL))
                ProvisioningInstructionsURL = item.get('ProvisioningInstructionsURL')
                if ProvisioningInstructionsURL:
                    Description.append('- Installation Instructions: {}'.format(ProvisioningInstructionsURL))
#                if not bool(BeautifulSoup(Description, "html.parser").find()):      # Test for pre-existing HTML
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = item['DrupalNodeid'],
                            QualityLevel = item.get('DeclaredStatus', 'Production').capitalize(),
                            Name = item['VendorSoftwareCommonName'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            ProviderID = providerURN,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = None,
                            Keywords = item['Keywords'],
                            Audience = self.Affiliation,
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
                
            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')


    #####################################################################
    # Function for loading RDR (Resource Description Repository) data
    # Load RDR's organization data to ResourceV3 tables (local, standard)
    # This function clears and re-populates self.RDR_HPCRESOURCE_URNMAP in each iteration
    #
    def Write_RDR_Providers(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Organizations'
        myRESTYPE = 'Provider'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)
        localUrlPrefix = config['SOURCEDEFAULTURL'] + '/xsede-api/provider/rdr/v1/organizations/'

        self.RDR_HPCPROVIDER_URNMAP = {}    # Clear
        cur = {}   # Current items
        new = {}   # New items
        # get existing organization data from local table
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        for item in content[contype]['resources'] :
            # Support multiple organiztion cases 
            for orgs in item['organizations']:
                if not self.Is_Active_RDR(content[contype]['resources'], organization=orgs['organization_id']):
                    continue
                myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], str(orgs['organization_id']))

                # Skip if this org already processed
                if myGLOBALURN == self.RDR_HPCPROVIDER_URNMAP.get(orgs['organization_id']):
                    continue

                # This will be used when resource data is loading for relationship connections
                self.RDR_HPCPROVIDER_URNMAP[orgs['organization_id']] = myGLOBALURN

                # --------------------------------------------
                # update ResourceV3 (local) table
                try:
                    local = ResourceV3Local(
                                ID = myGLOBALURN,
                                CreationTime = datetime.now(timezone.utc),
                                Validity = self.DefaultValidity,
                                Affiliation = self.Affiliation,
                                LocalID = str(orgs['organization_id']),
                                LocalType = 'organization',
                                LocalURL = localUrlPrefix + str(orgs['organization_id']),
                                CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                                EntityJSON = orgs,
                            )
                    local.save()
                except Exception as e:
                    msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                    self.logger.error(msg)
                    return(False, msg)
                new[myGLOBALURN] = local

                # --------------------------------------------
                # update ResourceV3 (standard) table
                try:
                    ShortDescription = None
                    Description = Format_Description(orgs.get('organization_name'))
                    resource = ResourceV3(
                                ID = myGLOBALURN,
                                Affiliation = self.Affiliation,
                                LocalID = str(orgs['organization_id']),
                                QualityLevel = 'Production',
                                Name = orgs['organization_name'],
                                ResourceGroup = myRESGROUP,
                                Type = myRESTYPE,
                                ShortDescription = ShortDescription,
                                ProviderID = None,
                                Description = Description.html(ID=myGLOBALURN),
                                Topics = 'HPC, XSEDE',
                                Keywords = orgs['organization_abbreviation'],
                                Audience = self.Affiliation,
                        )
                    resource.save()
                    if self.ESEARCH:
                        resource.indexing()
                except Exception as e:
                    msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                    self.logger.error(msg)
                    return(False, msg)
            
            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')

    #################################################################################
    # Function for loading RDR (Resource Description Repository) data
    # Load RDR's base-resource data to ResourceV3 tables (local, standard, relation)
    # This function populates self.RDRRESOURCE_BASE_URNMAP
    # This function populates self.RDRRESOURCE_INFOID_URNMAP
    #
    def Write_RDR_BaseResources(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Computing Tools and Services'
        myRESTYPE = 'Research Computing'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)
        localUrlPrefix = config['SOURCEDEFAULTURL'] + '/xsede-api/provider/rdr/v1/resources/id/' 
        
        cur = {}   # Current items
        new = {}   # New items
        # get existing base resource data from local table
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item
        
        for item in content[contype]['resources'] :
            if not self.Is_Active_RDR(content[contype]['resources'], resource=item['info_resourceid']):
                continue
            myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], str(item['resource_id']))

            self.RDRRESOURCE_BASE_URNMAP[item['resource_id']] = myGLOBALURN
            if item.get('info_resourceid'):
                self.RDRRESOURCE_INFOID_URNMAP[item['info_resourceid']] = myGLOBALURN
            self.RDR_HPCRESOURCE_URNMAP[item['info_resourceid']] = myGLOBALURN
            
            # --------------------------------------------
            # prepare for ResourceV3 (relation) table
            # update occurs later

            # The new relations for this item, key=related ID, value=type of relation
            myNEWRELATIONS = {}
            # Support multiple organiztion cases for relation table update,but set
            # only the first organization for ProviderID of standard table 
            myProviderID = None
            for orgs in item['organizations']:
                orgURN = self.RDR_HPCPROVIDER_URNMAP.get(orgs.get('organization_id', ''), None)
                if orgURN:
                    # save only the first provider
                    if not myProviderID:
                        myProviderID = self.RDR_HPCPROVIDER_URNMAP.get(orgs['organization_id'])
                    # set relation with organizations
                    myNEWRELATIONS[orgURN] = 'Provided By'

            # set relation with "XSEDE support org"
            supportURN = self.SUPPORTPROVIDER_URNMAP.get('helpdesk.xsede.org', None)
            if supportURN:
                myNEWRELATIONS[supportURN] = 'Supported By'

            LocalURL = item.get('public_url', (localUrlPrefix + str(item['resource_id'])) )

            # --------------------------------------------
            # update ResourceV3 (local) table
            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = str(item['resource_id']),
                            LocalType = 'base-resource',
                            LocalURL = LocalURL,
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            EntityJSON = item,
                        )
                local.save()
            except Exception as e:
                msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local
            
            # --------------------------------------------
            # update ResourceV3 (standard) table  

            # For QalityLevel from rdr.currentStatuses
            if not item['current_statuses']:  # empty cases
                    qualityLevel='Retired'
            if 'decommissioned' in item['current_statuses']:
                qualityLevel = 'Retired'
            elif set(['friendly', 'production', 'post-production']) & set(item['current_statuses']):
                qualityLevel = 'Production'
            elif 'pre-production' in item['current_statuses']:
                qualityLevel = 'Testing'
            else: # should not be here if currentStatuses is correct
                qualityLevel = 'Retired'

            # For Keywords, get comma seperated org-abbrev for multiple orgs.
            # For ShortDescription, get comma seperated org-name for multiple orgs.
            orgKeywords=''
            orgNames=''
            for orgs in item['organizations']:
                if orgKeywords:
                    orgKeywords += ', '
                orgKeywords += orgs['organization_abbreviation']
                if orgNames:
                    # replace is needed, otherwise incorrect
                    orgNames = orgNames.replace('\n', '') + ', '
                orgNames += orgs['organization_name']
            
            # For ShortDescription 
            ShortDescription = '{} ({}) provided by the {}'.format(item['resource_descriptive_name'], item['info_resourceid'], orgNames)
            Description = Format_Description(item.get('resource_description'))
            try:
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = str(item['resource_id']),
                            QualityLevel = qualityLevel,
                            Name = item['resource_descriptive_name'],
                            ResourceGroup = myRESGROUP,
                            Type = myRESTYPE,
                            ShortDescription = ShortDescription,
                            # pick the fitst, if contain multiple orgs
                            ProviderID = myProviderID,
                            Description = Description.html(ID=myGLOBALURN),
                            Topics = 'HPC',
                            Keywords = orgKeywords + ', XSEDE',
                            Audience = self.Affiliation,
                    )
                resource.save()
                if self.ESEARCH:
                    resource.indexing(relations=myNEWRELATIONS)
            except Exception as e:
                msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            
            # --------------------------------------------
            # update ResourceV3 (relation) table
            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')


    ################################################################################
    # Function for loading RDR (Resource Description Repository) data
    # Load RDR's sub-resource data to ResourceV3 tables (local, standard, relation)
    # This function populates self.RDRRESOURCE_SUB_URNMAP
    #
    def Write_RDR_SubResources(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Computing Tools and Services'
        myRESTYPE = 'Research Computing'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)
        
        cur = {}   # Current items
        new = {}   # New items
        # get existing sub resource data from local table
        for item in ResourceV3Local.objects.filter(Affiliation__exact=self.Affiliation).filter(ID__startswith=config['URNPREFIX']):
            cur[item.ID] = item

        subNameList=['compute_resources', 'storage_resources', 'other_resources', 'grid_resources']
        for item in content[contype]['resources'] :
            if not self.Is_Active_RDR(content[contype]['resources'], resource=item['info_resourceid']):
                continue
            # iterate different types of sub-resource
            for subName in subNameList:
                localUrlPrefix = config['SOURCEDEFAULTURL'] + '/xsede-api/provider/rdr/v1/' + subName + '/id/' 

                res = item.get(subName, None)
                # if one or more sub-resource type exist
                if res:
                    # iterate sub-resource types in base-resource
                    for sub in item[subName]:
                        if subName == 'compute_resources':
                            subID = str(sub['compute_resource_id'])
                            localType = 'computeResource'
                            if sub['machine_type']:
                                topics = 'HPC, Compute, ' + sub['machine_type']
                            else:
                                topics = 'HPC, Compute'
                        elif subName == 'storage_resources':
                            subID = str(sub['storage_resource_id'])
                            localType = 'storageResource'
                            topics = 'HPC, Storage'
                        elif subName == 'other_resources':
                            subID =  str(sub['other_resource_id'])
                            localType = 'otherResource'
                            topics = 'HPC'  # no adding ', Other' for this
                        elif subName == 'grid_resources':
                            subID = str(sub['grid_resource_id'])
                            localType = 'gridResource'
                            topics = 'HPC, Grid'

                        myGLOBALURN = self.format_GLOBALURN(config['URNPREFIX'], subID)

                        # --------------------------------------------
                        # prepare for ResourceV3 (relation) table
                        # update occurs later

                        # update to RDRRESOURCE_SUB_URNMAP
                        self.RDRRESOURCE_SUB_URNMAP[subID] = myGLOBALURN
                        # The new relations for this item, key=related ID, value=type of relation
                        myNEWRELATIONS = {}
                        # Support multiple organiztion cases for relation table update,but set
                        # only the first organization for ProviderID of standard table 
                        myProviderID = None
                        org_urls = []       # Save to include in Description
                        for orgs in item['organizations']:
                            if orgs.get('organization_url'):
                                org_urls.append(orgs['organization_url'])
                            orgURN = self.RDR_HPCPROVIDER_URNMAP.get(orgs.get('organization_id', ''), None)
                            if orgURN:
                                # save only the first provider
                                if not myProviderID:
                                    myProviderID = self.RDR_HPCPROVIDER_URNMAP.get(orgs['organization_id'])
                                # set relation with organizations
                                myNEWRELATIONS[orgURN] = 'Provided By'

                        # set relation with base-resource
                        baseURN = self.RDRRESOURCE_BASE_URNMAP.get(item.get('resource_id', ''), None)
                        if baseURN:
                            myNEWRELATIONS[baseURN] = 'Component Of'
                        # set relation with "XSEDE support org"
                        supportURN = self.SUPPORTPROVIDER_URNMAP.get('helpdesk.xsede.org', None)
                        if supportURN:
                            myNEWRELATIONS[supportURN] = 'Supported By'

                        LocalURL = item.get('public_url') or (localUrlPrefix + subID)

                        # --------------------------------------------
                        # update ResourceV3 (local) table
                        try:
                            local = ResourceV3Local(
                                        ID = myGLOBALURN,
                                        CreationTime = datetime.now(timezone.utc),
                                        Validity = self.DefaultValidity,
                                        Affiliation = self.Affiliation,
                                        LocalID = subID, 
                                        LocalType = localType,
                                        LocalURL = LocalURL,
                                        CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                                        EntityJSON = sub,
                                    )
                            local.save()
                        except Exception as e:
                            msg = '{} saving local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                            self.logger.error(msg)
                            return(False, msg)
                        new[myGLOBALURN] = local


                        # --------------------------------------------
                        # update ResourceV3 (standard) table  
                        
                        # For QalityLevel from sub.currentStatuses
                        if not sub['current_statuses']:  # empty cases
                                qualityLevel='Retired'
                        if 'decommissioned' in sub['current_statuses']:
                            qualityLevel = 'Retired'
                        elif set(['friendly', 'production', 'post-production']) & set(sub['current_statuses']):
                            qualityLevel = 'Production'
                        elif 'pre-production' in sub['current_statuses']:
                            qualityLevel = 'Testing'
                        else: # should not be here if currentStatueses is correct
                            qualityLevel = 'Retired'

                        # For Keywords, get comma seperated org-abbrev for multiple orgs.
                        # For ShortDescription, get comma seperated org-name for multiple orgs.
                        orgKeywords=''
                        orgNames=''
                        for orgs in item['organizations']:
                            if orgKeywords:
                                orgKeywords += ', '
                            orgKeywords += orgs['organization_abbreviation']
                            if orgNames:
                                orgNames = orgNames.replace('\n', '') + ', '
                            orgNames += orgs['organization_name']
                        
                        # For ShortDescription
                        ShortDescription = '{} ({}) provided by the {}'.format(sub['resource_descriptive_name'], sub['info_resourceid'], orgNames)
                        Description = Format_Description(sub.get('resource_description'))
                        Description.blank_line()
                        if sub.get('user_guide_url'):
                            Description.append('- User Guide URL: {}'.format(sub.get('user_guide_url')))
                        for url in org_urls:
                            Description.append('- Organization web site: {}'.format(url))
                        try:
                            resource = ResourceV3(
                                        ID = myGLOBALURN,
                                        Affiliation = self.Affiliation,
                                        LocalID = subID,
                                        QualityLevel = qualityLevel,
                                        Name = sub['resource_descriptive_name'],
                                        ResourceGroup = myRESGROUP,
                                        Type = myRESTYPE,
                                        ShortDescription = ShortDescription,
                                        # pick the fitst, if contain multiple orgs
                                        ProviderID = myProviderID,
                                        Description = Description.html(ID=myGLOBALURN),
                                        Topics = topics,
                                        Keywords = orgKeywords + ', XSEDE',
                                        Audience = self.Affiliation,
                                )
                            resource.save()
                            if self.ESEARCH:
                                resource.indexing(relations=myNEWRELATIONS)
                        except Exception as e:
                            msg = '{} saving resource ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                            self.logger.error(msg)
                            return(False, msg)

                        # ----------------------------------------
                        # update ResourceV3 (relation) table
                        self.Update_REL(myGLOBALURN, myNEWRELATIONS)

                        self.logger.debug('{} updated resource ID={}'.format(contype, myGLOBALURN))
                        self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.Log_STEP(me)
        return(0, '')


    def Run(self):
        while True:
            loop_start_utc = datetime.now(timezone.utc)
            self.STATS = Counter()
            self.PROCESSING_SECONDS = {}

            for stepconf in self.STEPS:
                step_start_utc = datetime.now(timezone.utc)
                pa_application = os.path.basename(__file__)
                pa_function = stepconf['DSTURL'].path
                pa_topic = stepconf['LOCALTYPE']
                pa_about = self.Affiliation
                pa_id = '{}:{}:{}:{}->{}'.format(pa_application, pa_function, pa_topic,
                    stepconf['SRCURL'].scheme, stepconf['DSTURL'].scheme)
                pa = ProcessingActivity(pa_application, pa_function, pa_id, pa_topic, pa_about)

                if stepconf['SRCURL'].scheme == 'file':
                    content = self.Read_CACHE(stepconf['SRCURL'].path, stepconf['LOCALTYPE'])
                else:
                    content = self.Get_HTTP(stepconf['SRCURL'], stepconf['LOCALTYPE'])

                if stepconf['LOCALTYPE'] not in content:
                    (rc, message) = (False, 'JSON is missing the \'{}\' element'.format(contype))
                    self.logger.error(msg)
                elif stepconf['DSTURL'].scheme == 'file':
                    (rc, message) = self.Write_CACHE(stepconf['DSTURL'].path, content)
                elif stepconf['DSTURL'].scheme == 'analyze':
                    (rc, message) = self.Analyze_CONTENT(content)
                elif stepconf['DSTURL'].scheme == 'memory':
                    (rc, message) = self.Write_MEMORY(content, stepconf['LOCALTYPE'], stepconf['DSTURL'].path)
                elif stepconf['DSTURL'].scheme == 'function':
                    (rc, message) = getattr(self, pa_function)(content, stepconf['LOCALTYPE'], stepconf)
                if not rc and message == '':  # No errors
                    message = 'Executed {} in {:.3f}/seconds'.format(pa_function,
                            (datetime.now(timezone.utc) - step_start_utc).total_seconds())
                pa.FinishActivity(rc, message)
     
            self.logger.info('Iteration duration={:.3f}/seconds'.format((datetime.now(timezone.utc) - loop_start_utc).total_seconds()))
            if self.args.once:
                break
            # Continuous
            self.smart_sleep()
        return(0)

    def smart_sleep(self):
        # Between 6 AM and 9 PM Central
        current_sleep = self.peak_sleep if 6 <= datetime.now(Central).hour <= 21 else self.offpeak_sleep
        self.logger.debug('sleep({})'.format(current_sleep))
        sleep(current_sleep)

########## CUSTOMIZATIONS END ##########

if __name__ == '__main__':
    router = Router()
    with PidFile(router.pidfile_path):
        try:
            router.Setup()
            rc = router.Run()
        except Exception as e:
            msg = '{} Exception: {}'.format(type(e).__name__, e)
            router.logger.error(msg)
            traceback.print_exc(file=sys.stdout)
            rc = 1
    router.exit(rc)
