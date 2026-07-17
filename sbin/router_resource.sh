#!/bin/bash

####### Customizations START #######
APP_NAME=%APP_NAME%
APP_HOME=%APP_HOME%
WAREHOUSE_DJANGO=%WAREHOUSE_DJANGO%
DAEMON_USER=software
####### Customizations END #######

####### Everything else should be standard #######
APP_SOURCE=${APP_HOME}/PROD

APP_LOG=${APP_HOME}/var/${APP_NAME}.daemon.log
if [[ "$1" != --pdb && "$2" != --pdb && "$3" != --pdb && "$4" != --pdb ]]; then
    exec >${APP_LOG} 2>&1
fi

APP_BIN=${APP_SOURCE}/bin/${APP_NAME}.py
APP_OPTS="-l info -c ${APP_HOME}/conf/${APP_NAME}.conf"

export PYTHONPATH=${APP_SOURCE}/lib:${WAREHOUSE_DJANGO}
export APP_CONFIG=${APP_HOME}/conf/django_prod_router.conf
export DJANGO_SETTINGS_MODULE=Operations_Warehouse_Django.settings

echo "Starting: /usr/local/bin/uv run --project ${APP_HOME} ${APP_BIN} ${APP_OPTS}"
/usr/local/bin/uv run --project ${APP_HOME} ${APP_BIN} ${APP_OPTS}
RETVAL=$?
echo rc=$RETVAL
exit $RETVAL