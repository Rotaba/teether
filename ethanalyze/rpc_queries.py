from ethjsonrpc.client import EthJsonRpc

def getStorageAt(contract_addr, index):

    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getStorageAt(str(contract_addr), index)

def getByteCode(contract_addr):

    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getCode(contract_addr)

def getBalance(contract_addr):

    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getBalance(contract_addr)

#sendExploit(int(target_addr, 16), hexlify(c.get('payload', '')), contract_addr, ", value:%d" % c['value'] if c.get('value', 0) else '')
def sendExploit(attacker_addr, payload, contract_addr):
    c = EthJsonRpc('127.0.0.1', 8545)

    # def eth_sendTransaction(self, to_address=None, from_address=None, gas=None, gas_price=None,  data=None,
    #                         nonce=None):
    # if (attacker_addr != '0x3cc7c038f7eea1b70014b788b821d675b13b8760'):
    #     #we're doing a shellcode-contract middleman here; rewrite the FROM
    #     print ("    RPC.sendExploit: attacker address doesn't match the MASTER addr, are we using shellcontract as middle-man? \n    Rewritting FROM field; "
    #            "%s "
    #            "to "
    #            "'0x3cc7c038f7eea1b70014b788b821d675b13b8760'" % attacker_addr)
    #     attacker_addr = '0x3cc7c038f7eea1b70014b788b821d675b13b8760'
    # return c.eth_sendTransaction(from_address=attacker_addr, data='0x'+payload, to_address=contract_addr)
    #return c.eth_sendTransaction(to_address="0x400000000000000000000000000000000000008b", from_address="0x3cc7c038f7eea1b70014b788b821d675b13b8760", gas=None, gas_price=None, data="0xe8208d01")

    # if(critical_op == 'DELEGATECALL' or critical_op == 'CALLCODE' or critical_op == 'CALL'):
    #     print ("    RPC.sendExploit: need to use middle-man shellcode contract \n    Rewritting FROM field; "
    #            "%s "
    #            "-> "
    #            "'0x4000000000000000000000000000000000000000'" % attacker_addr)
    #     attacker_addr = '0x1000000000000000000000000000000000000000'
        # attacker_addr = '0x3cc7c038f7eea1b70014b788b821d675b13b8760'

    return c.eth_sendTransaction(from_address=attacker_addr, data='0x' + payload, to_address=contract_addr)
# def main():
#     sendExploit(1)

def checkBalance(target):
    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getBalance(target)