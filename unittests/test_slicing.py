import unittest
from binascii import unhexlify

from ethanalyze import project
from ethanalyze.slicing import backward_slice


class MyTestCase(unittest.TestCase):
    def test_slicing(self):

        p = project.Project(unhexlify("3460085733600b565b60005b600052"))
        last_store = p.filter_ins('MSTORE')[-1]
        slices = list(backward_slice(last_store))
        self.assertEqual(len(slices), 2)


if __name__ == '__main__':
    unittest.main()
