#!/bin/sh
do_start () {
    echo -n "Starting ${DAEMON_NAME}:"
    export LD_LIBRARY_PATH=${PYTHON_BASE}/lib
    source ${PIPENV_BASE}/bin/activate
    exec ${PYTHON_BIN} ${DAEMON_BIN} --daemon -l info $@ ${DAEMON_OPTS}
    RETVAL=$?
}
do_debug () {
    echo -n "Debugging: ${PIPENV_BASE}/bin/python ${DAEMON_BIN} -l debug $@ ${DAEMON_OPTS}"
    export LD_LIBRARY_PATH=${PYTHON_BASE}/lib
    source ${PIPENV_BASE}/bin/activate
    exec ${PYTHON_BIN} ${DAEMON_BIN} -l debug $@ ${DAEMON_OPTS}
    RETVAL=$?
}

case "$1" in
    start)
        do_start ${@:2}
        ;;

    debug)
        do_debug ${@:2}
        ;;

    *)
        echo "Usage: ${DAEMON_NAME} {start|debug}"
        exit 1
        ;;

esac
echo rc=$RETVAL
exit $RETVAL
