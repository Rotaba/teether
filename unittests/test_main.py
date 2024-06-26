import unittest

from combined_call_exploit import main


class TestMain(unittest.TestCase):
    def check(self, i):
        assert (main('../../test/test%d.contract.code' % i, '0x3cc7c038f7eea1b70014b788b821d675b13b8760', '=1337'))

for i in xrange(1,22):
    if i == 12:
        # test12.sol is not exploitable
        continue
    def lambda_wrap(i):
        return lambda self:self.check(i)
    setattr(TestMain, 'test_%02d'%i, lambda_wrap(i))




#if __name__ == '__main__':
#    unittest.main()