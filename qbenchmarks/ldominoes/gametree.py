#!/usr/bin/python

import sys
import getopt

# Exhaustive play of linear dominoes game
# Game played on 1 x N grid
# Each domino covers two squares
# Last player to place domino wins

def usage(name):
    print("Usage: %s [-h] [-v] [-n N] [-N NMAX] [-C]" % name)
    print("  -h      Print this message")
    print("  -v      Verbose printing of search")
    print("  -n N    Run for single value of N")
    print("  -N NMAX Run for all values up to NMAX")
    print("  -C      Disable result caching")


class GameException(Exception):
    reason = "Game Exception"

    def __init__(self, reason = None):
        if reason is not None:
            self.reason += ": " + reason

    def __str__(self, reason):
        return self.reason


class Board:
    no_one, A, B = range(3)

    size = 0
    # State represented by array of length size-1
    # each representing boundary between two squares
    # Indices range between 0 and size-2
    state = []
    searchCount = 0
    
    def __init__(self, size):
        self.size = size
        self.state = [self.no_one for i in range(size-1)]
        self.searchCount = 0

    def __str__(self):
        varray = [" "] * self.size
        for m in range(self.size-1):
            if self.state[m] == self.A:
                varray[m] = "A"
                varray[m+1] = "A"
            elif self.state[m] == self.B:
                varray[m] = "B"
                varray[m+1] = "B"
        return "[" + "|".join(varray) + "]"

    def addSearch(self):
        self.searchCount += 1

    def otrim(self, s):
        while len(s) > 0 and s[0] == '1':
            s = s[1:]
        while len(s) > 0 and s[-1] == '1':
            s = s[:-1]
        return s

    # Compress state to eliminate consecutive ones
    def ftrim(self, s):
        result = ""
        while len(s) > 0 and s[0] == '1':
            s = s[1:]
        while len(s) > 0:
            while len(s) > 0 and s[0] == '0':
                result += '0'
                s = s[1:]
            while len(s) > 0 and s[0] == '1':
                s = s[1:]
            result += '1'
        if len(result) > 0 and result[-1] == '1':
            result = result[:-1]
        return result
                    
    # Compress by keeping track of runs of consecutive zeros
    # Sort to put into canonical form
    def trim(self, s):
        substrings = []
        while len(s) > 0:
            ns = ""
            while len(s) > 0 and s[0] == '1':
                s = s[1:]
            while len(s) > 0 and s[0] == '0':
                ns += '0'
                s = s[1:]
            if len(ns) > 0:
                substrings.append(ns)
        substrings.sort()
        return '1'.join(substrings)

    def compress(self):
        sarray = ['0'] * self.size
        for m in range(self.size-1):
            if self.state[m] != self.no_one:
                sarray[m] =   '1'
                sarray[m+1] = '1'
        s = self.trim("".join(sarray))
        sarray.reverse()
        rs = self.trim("".join(sarray))
        # Exploit mirror symmetry
        return min(s, rs)

    def isLegal(self, m):
        if m < 0 or m >= self.size-1:
            return False
        if self.state[m] != self.no_one:
            return False
        if m < self.size-2 and self.state[m+1] != self.no_one:
            return False
        if m > 0 and self.state[m-1] != self.no_one:
            return False
        return True

    def name(self, whom):
        return "A" if whom == self.A else "B"

    def allLegal(self):
        return [m for m in range(self.size-1) if self.isLegal(m)]

    # Place domino to cross specified border
    def place(self, m, whom):
        if not self.isLegal(m):
            raise GameException("Cannot move to position %d" % m)
        if whom < self.A or whom > self.B:
            raise GameException("Invalid player value %d" % whom)
        self.state[m] = whom

    def unplace(self, m):
        self.state[m] = self.no_one

    def opponent(self, whom):
        if whom == self.A:
            return self.B
        if whom == self.B:
            return self.A
        raise GameException("Invalid player value %d" % whom)


# Cache search results
class Cache:

    # Compress board state into zeros (empty) and ones (occupied)
    # Key = Mover + State
    # Result = winner

    history = {}
    storeCount = 0
    lookupCount = 0
    hitCount = 0

    def __init__(self):
        self.history = {}
        self.storeCount = 0
        self.lookupCount = 0
        self.hitCount = 0

    def key(self, board, mover):
        return board.name(mover) + ':' + board.compress()

    def add(self, board, mover, winner):
        key = self.key(board, mover)
        self.history[key] = winner
        self.storeCount += 1

    def lookup(self, board, mover):
        self.lookupCount += 1
        key = self.key(board, mover)
        if key in self.history:
            self.hitCount += 1
            return self.history[key]
        return None

    def summarize(self):
        rate = float(self.hitCount) / self.lookupCount
        print("    Cache performance: %d items, %d lookups, %d hits, %.1f hit rate" % (self.storeCount, self.lookupCount, self.hitCount, rate))

# Node in game tree
class Node:
    
    board = None
    # Which side has next move
    mover = None  # Board.A or Board.B
    verbosity = 1 # 0-2
    sofar = ""
    cache = None

    def __init__(self, board, mover, verbosity, cache, sofar = ""):
        self.board = board
        self.mover = mover
        self.verbosity = verbosity
        self.cache = cache
        self.sofar = sofar
        self.board.addSearch()

    def playSubgame(self, m):
        self.board.place(m, self.mover)
        nsofar = self.sofar + "   " + str(self.board)
        subNode = Node(self.board, self.board.opponent(self.mover), self.verbosity, self.cache, nsofar)
        result = subNode.play()
        self.board.unplace(m)
        return result

    def document(self, winner):
        if self.verbosity >= 2:
            wstring = self.board.name(winner)
            print(self.sofar + " : " + wstring)

    # Try to play game
    # Return who is the winner
    def play(self):
        if self.cache is not None:
            winner = self.cache.lookup(self.board, self.mover)
            if winner is not None:
                return winner
        moves = self.board.allLegal()
        winner = None
        if len(moves) == 0:
            winner = self.board.opponent(self.mover)
            self.document(winner)
        elif self.mover == self.board.A:
            # Only need to find one winning move
            for m in moves:
                subresult = self.playSubgame(m)
                if subresult == self.board.A:
                    winner = subresult
                    break
            if winner is None:
                winner = self.board.B
        else:
            # Need to win for every move
            for m in moves:
                subresult = self.playSubgame(m)
                if subresult == self.board.B:
                    winner = subresult
                    break
            if winner is None:
                winner = self.board.A
        if self.cache is not None:
            self.cache.add(self.board, self.mover, winner)
        return winner
            
    
def run(name, args):
    verbosity = 1
    nMin = 10
    nMax = nMin
    useCache = True
    
    optlist, args = getopt.getopt(args, "hvCn:N:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbosity = 2
        elif opt == '-n':
            nMin = int(val)
            nMax = nMin
        elif opt == '-N':
            nMin = 0
            nMax = int(val)
        elif opt == '-C':
            useCache = False

    cache = Cache() if useCache else None

    for n in range(nMin, nMax+1):
        board = Board(n)
        sys.stdout.write("%d:" % n)
        if verbosity > 1:
            sys.stdout.write("\n")
        node = Node(board, board.A, verbosity, cache)
        result = node.play()
        print("%s wins.  %d positions searched" % (board.name(result), board.searchCount))
        if cache is not None and verbosity > 1:
            cache.summarize()

maxSize = 30
size = 5

run(sys.argv[0], sys.argv[1:])
