#!/bin/bash

echo -n "Starting router_resource:"
exec /usr/local/bin/uv run --project ${APP_HOME} ${APP_BIN} --daemon ${APP_OPTS}
RETVAL=$?
echo rc=$RETVAL
exit $RETVAL