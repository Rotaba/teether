#!/usr/bin/env python2.7
# from binascii import hexlify
# from copy import copy
# from combined_call_exploit import attempt_exploit_new_call, attempt_exploit_other_three, addr_to_project
# from ethanalyze.evm import CombinedSymbolicResult, SymbolicEVMState
# from ethanalyze.project import Project
# from z3 import z3

INTERESTING_INS = ('CALL', 'CALLCODE', 'DELEGATECALL', 'SUICIDE', 'RETURN', 'STOP')

if __name__ == '__main__':
    import sys
    import json

    critical_op = None
    critical_addr = None
    critical_amount = None

    # if len(sys.argv) < 5:
    #     print >> sys.stderr, "Usage: %s <project.json> <exploit.json> <target-addr> <target-amount>" % sys.argv[0]
    #     sys.exit(-1)
    # unpack target contract project
    with open(sys.argv[1]) as f:
        err_log_last = f.readlines()[-1]

    # project = Project.from_json(project_dict)
    # unpack target contract exploit
    with open(sys.argv[1][:-3] + 'exploit.json') as f:
        exploit_dict = json.load(f)

    try:
        #simple search for address != 0 (targeted contract)
        for i in exploit_dict[u'paths']:
            if i[u'addres'] != 0:
                print sys.argv[1][-36:-4] + " " + i[u'addres']
        #
        # if (exploit_dict[u'paths'][0][u'xid'] == exploit_dict[u'paths'][1][u'xid']): #they share xid; could be part of triple, could be duplicate of xid_mistake
        #     str_split = err_log_last.split('(')[1]
        #     if(str_split[0] == str_split[3]):
        #     # print "possible duplicate xid fail"
        #         # print sys.argv[1][-36:-4]  # + "last line:"
        #         # print err_log_last
        #         pass
        #     else:
        #         print sys.argv[1][-36:-4]  # + "last line:"
        #         pass
        # else:
        #     # print "could be a real exploit"
        #     # print sys.argv[1][-36:-4]# + "last line:"
        #     pass
        #     # print err_log_last
    except:
        # print sys.argv[1][-36:-4]
        pass



