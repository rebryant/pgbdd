#!/bin/bash
# 6
make orab CAT='-f4' PROFILE=1+1+2+2
# 7
make osab CAT='-t4' PROFILE=1+2+2+2
# 10
make orab CAT='-f4' PROFILE=2+2+3+3
make osab CAT='-t4' PROFILE=1+3+3+3
# 14
make orab CAT='-f4' PROFILE=3+3+4+4
make osab CAT='-t4' PROFILE=2+4+4+4
# 18
make orab CAT='-f4' PROFILE=4+4+5+5
make osab CAT='-t4' PROFILE=3+5+5+5
# 19
make osab CAT='-t4' PROFILE=4+5+5+5
# 20
make orab CAT='-f4' PROFILE=5+5+5+5
make osab CAT='-t4' PROFILE=4+5+5+6
# 21
make osab CAT='-t4' PROFILE=5+5+5+6
# 22
make orab CAT='-f4' PROFILE=5+5+6+6
make osab CAT='-t4' PROFILE=4+6+6+6
# 23
make osab CAT='-t4' PROFILE=5+6+6+6
# 24
make orab CAT='-f4' PROFILE=6+6+6+6
# 26
make orab CAT='-f4' PROFILE=6+6+7+7
#make osab CAT='-t4' PROFILE=5+7+7+7
# 28
make orab CAT='-f4' PROFILE=7+7+7+7
# 30
make orab CAT='-f4' PROFILE=7+7+8+8
#make osab CAT='-t4' PROFILE=6+8+8+8
