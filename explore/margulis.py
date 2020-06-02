#!/usr/bin/python
import sys

# Test of Margulis' construction of an expander graph

def usage(name):
    print("Usage: %s M" % name)
    print("M = Defining paramter.  Generates graph with 2 * M*M nodes")
    sys.exit(0)

# Map from M X M --> M*M
def mmap(x, y, m):
    return m*x+y
    
# Family of functions defining permuations.
# Each defines a mapping from M X M --> M*M
def perm0(x, y, m):
    return mmap(x, y, m)

def perm1(x, y, m):
    return mmap(x, (x+y)%m, m)

def perm2(x, y, m):
    return mmap(x, (x+y+1)%m, m)

def perm3(x, y, m):
    return mmap((x+y)%m, y, m)

def perm4(x, y, m):
    return perm2((x+y+1)%m, y, m)

permuters = [perm0, perm1, perm2, perm3, perm4]


def gen_perms(m):
    plist = []
    for p in permuters:
        ls  = [p(x,y,m) for x in range(m) for y in range(m)]
        plist.append(ls)
    return plist

# Set repeated elements in list to blanks
def prune(ls):
    result = []
    for ele in ls:
        if ele in result:
            result.append("")
        else:
            result.append(ele)
    return result

def run(name, args):
    if len(args) != 1:
        usage(name)
    try:
        m = int(args[0])
    except:
        usage(name)
    plist = gen_perms(m)
    for i in range(m*m):
        slist = [str(plist[j][i]) for j in range(len(permuters))]
        pslist = prune(slist)
        print("\t%d:\t" % i + "\t".join(pslist))


if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
        






