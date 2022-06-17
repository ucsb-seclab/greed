#!/usr/bin/env python3
import argparse
import logging
from SEtaac import Project
from SEtaac.utils import gen_exec_id

LOGGING_FORMAT = '%(levelname)s | %(name)s | %(message)s'
# LOGGING_FORMAT = '%(message)s'
logging.basicConfig(level=logging.INFO, format=LOGGING_FORMAT)
log = logging.getLogger(__name__)


def main(args):
    p = Project(f"{args.target}/IR_DICT.dill",
                f"{args.target}/TAC_CFG.dill")

    xid = gen_exec_id()
    entry_state = p.factory.entry_state(xid=xid)
    simgr = p.factory.simgr(entry_state=entry_state)

    try:
        simgr.run()
    except KeyboardInterrupt:
        pass

    import IPython; IPython.embed()


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser._action_groups.pop()
    required = parser.add_argument_group('Required arguments')
    optional = parser.add_argument_group('Optional arguments')

    required.add_argument('--target', type=str, action='store', help='Path to Gigahorse output folder', required=True)

    optional.add_argument('-d', '--debug', action='store_true',
                            help='Enable debug output')
    # optional.add_argument('--breakpoints', type=str, nargs='+', default=[], action='store',
    #                         help='Set a breakpoint at a specific instruction count')
    # optional.add_argument('-i', '--interactive', action='store_true',
    #                         help='Drop an IPython shell after the execution')
    optional.add_argument('--log', type=str, action='store',
                            help='Path to save the logfile')

    args = parser.parse_args()

    # setup logging
    if args.debug:
        log.setLevel('DEBUG')
    else:
        log.setLevel('INFO')

    if args.log:
        fh = logging.FileHandler(args.log)
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(logging.Formatter(LOGGING_FORMAT))
        log.addHandler(fh)
        log.setLevel(logging.DEBUG)
        log.propagate = False

    main(args)
