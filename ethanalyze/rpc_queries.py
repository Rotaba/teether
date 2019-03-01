from ethjsonrpc.client import EthJsonRpc

def getStorageAt(contract_addr, index):

    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getStorageAt(str(contract_addr), index)

def getByteCode(contract_addr):

    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getCode(contract_addr)

#sendExploit(int(target_addr, 16), hexlify(c.get('payload', '')), contract_addr, ", value:%d" % c['value'] if c.get('value', 0) else '')
def sendExploit(attacker_addr, payload, contract_addr, value):
    c = EthJsonRpc('127.0.0.1', 8545)

    # def eth_sendTransaction(self, to_address=None, from_address=None, gas=None, gas_price=None,  data=None,
    #                         nonce=None):
    return c.eth_sendTransaction(from_address=attacker_addr, data='0x'+payload, to_address=contract_addr)
    #return c.eth_sendTransaction(to_address="0x400000000000000000000000000000000000008b", from_address="0x3cc7c038f7eea1b70014b788b821d675b13b8760", gas=None, gas_price=None, data="0xe8208d01")

# def main():
#     sendExploit(1)

def checkBalance(target):
    c = EthJsonRpc('127.0.0.1', 8545)
    return c.eth_getBalance(target)