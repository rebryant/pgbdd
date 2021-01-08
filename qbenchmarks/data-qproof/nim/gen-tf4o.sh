#!/bin/bash
make orao CAT='-f4' PROFILE=1+1+1+1
make osao CAT='-t4' PROFILE=1+1+1+2
make orao CAT='-f4' PROFILE=1+1+2+2
make osao CAT='-t4' PROFILE=1+2+2+2
make orao CAT='-f4' PROFILE=2+2+2+2
make osao CAT='-t4' PROFILE=2+3+3+3
make orao CAT='-f4' PROFILE=2+2+3+3
make osao CAT='-t4' PROFILE=1+3+3+3
make orao CAT='-f4' PROFILE=3+3+4+4
make osao CAT='-t4' PROFILE=2+4+4+4
make orao CAT='-f4' PROFILE=4+4+5+5
make osao CAT='-t4' PROFILE=3+5+5+5
# 19
make osao CAT='-t4' PROFILE=4+5+5+5
# 20
make orao CAT='-f4' PROFILE=5+5+5+5
make osao CAT='-t4' PROFILE=4+5+5+6
# 21
make osao CAT='-t4' PROFILE=5+5+5+6
make orao CAT='-f4' PROFILE=5+5+6+6
make osao CAT='-t4' PROFILE=4+6+6+6
# 23
make osao CAT='-t4' PROFILE=5+6+6+6
# 24
make orao CAT='-f4' PROFILE=6+6+6+6
make orao CAT='-f4' PROFILE=6+6+7+7
make osao CAT='-t4' PROFILE=5+7+7+7
# 28
make orao CAT='-f4' PROFILE=7+7+7+7
make orao CAT='-f4' PROFILE=7+7+8+8
make osao CAT='-t4' PROFILE=6+8+8+8
# 32
make orao CAT='-f4' PROFILE=8+8+8+8
# 34
make orao CAT='-f4' PROFILE=8+8+9+9
make orao CAT='-f4' PROFILE=9+9+9+9
make orao CAT='-f4' PROFILE=10+10+10+10
make orao CAT='-f4' PROFILE=11+11+11+11
#make orao CAT='-f4' PROFILE=12+12+12+12

