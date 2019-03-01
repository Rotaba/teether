#!/bin/bash
set -e
set -u

srcfile=$1

python2 combined_call_exploit.py ../teether-test/$srcfile.contract.code 0x3cc7c038f7eea1b70014b788b821d675b13b8760 +1
