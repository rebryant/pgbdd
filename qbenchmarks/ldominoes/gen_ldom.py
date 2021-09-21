#!/usr/bin/python

import sys
import getopt

import writer


def usage(name):
    print("Usage: %s: [-h][-v][-i][-s][-n N][-t b|a|i] -r ROOT")
    print("  -h             Print this message")
    print("  -v             Include comments in output")
    print("  -i             Invert formula")
    print("  -s             Use Sinz encoding of at-most-one constraints")
    print("  -n N           Specify number of squares")
    print("  -t b|a|e|M     Specify position of Tseitin (& Sinz) variables:")
    print("                   b: before their defining variables (when possible, otherwise after)")
    print("                   a: after their defining variables")
    print("                   e: at end of quantifier string")
    print("  -r ROOT        Specify root name for files.  Will generate ROOT.qcnf, ROOT.order")

# Generate QBF and other files for 1 X N domino tiling game

# VARIABLES:
# Input
#   Let T = Floor(N/2)
#
#   edgeRemoved[i,t]: 1<=i<N, 1<=t<=T
#    Attempt to remove edge i on step t
#
#
# Tseitin
#
#   edgePresent[i,t]: 1<=i<N, 1<=t<T
#    Edge i still present after step t
#
#   edgeClear[i,t]: 1<=i<N, 1<t<=T
#    Edge i, as well as the ones adjacent to it,
#    were present after step t-1
#
#   edgeAvailable[i,t]: 1<=i<N, 1<t<=T
#    Any edge removed on step t, as well as the ones adjacent to it,
#    were present after step t-1
#
#   uniqueChanged[t]: 1<=t<=T
#    Exactly one edge removed on step t
#
#   onlyAvailable[t]: 1<t<=T
#    The edge removed on step t, as well as the ones adjacent to it,
#    were present after step t-1
#
#   moved[t]: 1<=t<=T
#    Legal move took place
#


# Tseitin variable computation

#  edgePresent[i,t] <--> edgePresent[i,t-1] & !edgeRemoved[i,t]
#
#   t = 1:
#     edgePresent[i,1] --> !edgeRemoved[i,1]
#     !edgeRemoved[i,1] --> edgePresent[i,1]
#
#   t > 1:
#     edgePresent[i,t-1] & !edgeRemoved[i,t] --> edgePresent[i,t]
#     edgePresent[i,t] --> edgePresent[i,t-1]
#     edgePresent[i,t] --> !edgeRemoved[i,t]
#
#   edgeClear[i,t] <--> edgePresent[i-1,t-1] & edgePresent[i,t-1] & edgePresent[i+1,t-1]
#     edgeClear[i,t] --> edgePresent[i-1,t-1]
#     edgeClear[i,t] --> edgePresent[i,t-1]
#     edgeClear[i,t] --> edgePresent[i+1,t-1]
#     edgePresent[i-1,t-1] & edgePresent[i,t-1] & edgePresent[i+1,t-1] --> edgeClear[i,t]
#
#  edgeAvailable[i,t] <--> !edgeRemoved[i,t] OR edgeClear[i,t]
#     edgeAvailable[i,t] --> !edgeRemoved[i,t] OR edgeClear[i,t]
#     !edgeRemoved[i,t] --> edgeAvailable[i,t]
#     edgeClear[i,t] --> edgeAvailable[i,t]
#
#  uniqueChanged[t] <--> Exactly1_i edgeRemoved[i,t]
#     uniqueChanged[t] --> (!edgeRemoved[i,t] OR !edgeRemoved[i',t]) 1 <= i < i' < N
#     uniqueChanged[t] --> OR_i edgeRemoved[i,t]  
#     !edgeRemoved[1,t] & .. & !edgeRemoved[i-1,t] & edgeRemoved[i,t] & !edgeRemoved[i+1,t] & .. & !edgeRemoved[N-1,t] --> uniqueChanged[t] 1 <=i<N
#
#  onlyAvailable[t] <--> AND_i edgeAvailable[i,t]
#     onlyAvailable[t] --> edgeAvailable[i,t]  1<=i<N
#     AND_i edgeAvailable[i,t] --> onlyAvailable[t]
# 
#  moved[t] <--> uniqueChanged[t] & onlyAvailable[t]
#     moved[t] --> uniqueChanged[t]
#     moved[t] --> onlyAvailable[t]
#     uniqueChanged[t] & onlyAvailable[t] --> moved[t]
#

# Global Constraints.  

# Winning scenarios (Normal)
# w[t] --> AND_(t'<=t) moved[t'] & !moved[t+1]  All odd t
#
# Winning
# OR_odd_t w[t]

# Winning scenarios (Inverted)
# w[t] --> AND_(t'<=t) moved[t'] & !moved[t+1]  All even t>=0
#
# Winning
# OR_even_t w[t]


def unitRange(n):
    return list(range(1,n+1))

class Variable:
    name = None
    id = None
    isExistential = True
    # Variable level -1 used to hold innermost Tseitin variables
    level = -1

    def __init__(self, id, isExistential, level, name = None):
        if name is None:
            name = "V%d" % id
        self.name = name
        self.id = id
        self.isExistential = isExistential
        self.level = level

    def __str__(self):
        return self.name + '?' if self.isExistential else '!'


class Manager:

    tseitinBefore, tseitinAfter, tseitinEnd = range(3)

    writer = None
    variableCount = 0
    verbose = False
    tseitinMode = None

    

    def __init__(self, writer, verbose = False, tseitinMode = None):
        self.writer = writer
        self.variableCount = 0
        self.verbose = verbose
        if tseitinMode is None:
            tseitinMode = self.tseitinEnd
        self.tseitinMode = tseitinMode

    # Determine level of variable, including cases where levels of Tseitin variables are included
    def levelMap(self, level, isTseitin, isExistential):
        if self.tseitinMode == self.tseitinEnd:
            return -1 if isTseitin else level
        elif self.tseitinMode == self.tseitinAfter:
            return 2*level if isTseitin else 2*level-1
        elif self.tseitinMode == self.tseitinBefore:
            if isExistential:
                return 2*level-1 if isTseitin else 2*level
            else:
                return 2*level if isTseitin else 2*level-1
        # Shouldn't happen
        return 0

    def createVariable(self, isExistential, level, name):
        vlevel = self.levelMap(level, False, isExistential)
        id = self.variableCount + 1
        v = Variable(id, isExistential, vlevel, name)
        self.variableCount += 1
        return v

    # Create Tseitin variable.  Level indicates position at which it is defined
    # isExistential relates to level, not to the fact these are Tseitin variables
    def createTseitinVariable(self, level, name, isExistential):
        vlevel = self.levelMap(level, True, isExistential)
        id = self.variableCount + 1
        v = Variable(id, True, vlevel, name)
        self.variableCount += 1
        return v

    def translateVariables(self, vlist):
        return [v.id for v in vlist]

    def addVariables(self, vdict):
        keys = sorted(vdict.keys())
        for k in keys:
            v = vdict[k]
            self.writer.addVariable(v.level, v.id, v.isExistential)
        
    # plist is list of phases: 1 --> positive, 0 --> negative
    def doClause(self, vlist, plist):
        if len(vlist) != len(plist):
            estring = "Mismatched list lengths %d != %d" % (len(vlist), len(plist))
            raise Exception(estring)
        idList = self.translateVariables(vlist)
        litList = [id if phase == 1 else -id for (id, phase) in zip(idList, plist)]
        self.writer.doClause(litList)

    def doComment(self, line):
        if self.verbose:
            self.writer.doComment(line)

    def doVariableComment(self, level, isExistential, line):
        vlevel = self.levelMap(level, False, isExistential)
        if self.verbose:
            self.writer.doVariableComment(vlevel, line)

    def doTseitinVariableComment(self, level, isExistential, line):
        vlevel = self.levelMap(level, True, isExistential)
        if self.verbose:
            self.writer.doVariableComment(vlevel, line)
            
    def finish(self):
        self.writer.finish()

# Manage single move of game
class Move:

    level = 1
    manager = None
    N = 1
    isExistential = False
    #   edgeRemoved[i,t]: 1<=i<N
    #    Attempt to remove edge i on step t
    edgeRemovedVars = {}
    #   edgePresent[i,t]: 1<=i<N
    #    Edge i still present after step t
    edgePresentVars = {}
    #   edgePresent[i,t-1]: 1<=i<N
    #    Edge i still present after step t-1
    prevVars = None
    #   edgeClear[i,t]: 1<=i<N, 1<t<=T
    #    Edge i, as well as the ones adjacent to it,
    #    were present at the start of step t
    edgeClearVars = {}
    #   edgeAvailable[i,t]: 1<=i<N
    #    Any edge removed was available for step t
    edgeAvailableVars = None
    #   uniqueChanged[t]
    #    Exactly one edge removed on step t
    uniqueChangedVar = None
    #   onlyAvailable[t]:
    #    The edge removed was present after step t-1
    onlyAvailableVar = None
    #   moved[t]:
    #    Legal move took place
    movedVar = None

    def __init__(self, manager, level, N, invert, prevVars):
        self.level = level
        self.isExistential = level % 2 == (0 if invert else 1)
        self.manager = manager
        self.N = N
        self.prevVars = prevVars
        self.makeInputVars()
        self.makeTseitinVars()
        
    def makeInputVars(self):
        slist = []
        self.edgeRemovedVars = {}
        for i in unitRange(self.N-1):
            name = "edgeRemoved[%d,%d]" % (i, self.level)
            v = self.manager.createVariable(self.isExistential, self.level, name)
            self.edgeRemovedVars[i] = v
            slist.append(str(v.id))
        cstring = "Level %d input variables: %s" % (self.level, ", ".join(slist))
        self.manager.doVariableComment(self.level, self.isExistential, cstring)
                                      
    def makeTseitinVars(self):
        #   edgePresent[i,t]: 1<=i<N
        self.edgePresentVars = {}
        slist = []
        for i in unitRange(self.N-1):
            name = "edgePresent[%d,%d]" % (i, self.level)
            v = self.manager.createTseitinVariable(self.level, name, self.isExistential)
            self.edgePresentVars[i] = v
            slist.append(str(v.id))
        cstring = "Level %d Tseitin variables" % self.level
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)
        cstring = "  edgePresent: %s" % ", ".join(slist)
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)
        #   uniqueChanged[t]
        self.uniqueChangedVar = self.manager.createTseitinVariable(self.level, "uniqueChanged[%d]" % self.level, self.isExistential)
        cstring = "  uniqueChanged: %s" % self.uniqueChangedVar.id
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)
        if self.level == 1:
            self.edgeAvailableVars = None
            self.onlyAvailableVar = None
        else:
            # edgeClear[i,t]: 1<=i<N, 1<t<=N
            self.edgeClearVars = {}
            slist = []
            for i in unitRange(self.N-1):
                name = "edgeClear[%d,%d]" % (i, self.level)
                v = self.manager.createTseitinVariable(self.level, name, self.isExistential)
                self.edgeClearVars[i] = v
                slist.append(str(v.id))
            cstring = "  edgeClear: %s" % ", ".join(slist)
            self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)
            #   edgeAvailable[i,t]: 1<=i<N, 1<t<=N
            self.edgeAvailableVars = {}
            slist = []
            for i in unitRange(self.N-1):
                name = "edgeAvailable[%d,%d]" % (i, self.level)
                v = self.manager.createTseitinVariable(self.level, name, self.isExistential)
                self.edgeAvailableVars[i] = v
                slist.append(str(v.id))
            cstring = "  edgeAvailable: %s" % ", ".join(slist)
            self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

            #   onlyAvailable[t]
            self.onlyAvailableVar = self.manager.createTseitinVariable(self.level, "onlyAvailable[%d]" % self.level, self.isExistential)
            cstring = "  onlyAvailable: %s" % self.onlyAvailableVar.id
            self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        #   moved[t]
        self.movedVar = self.manager.createTseitinVariable(self.level, "moved[%d]" % self.level, self.isExistential)
        cstring = "  moved: %s" % self.movedVar.id
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

    def emitVariables(self):
        self.manager.addVariables(self.edgeRemovedVars)
        self.manager.addVariables(self.edgePresentVars)
        vdict = {1: self.uniqueChangedVar, 3: self.movedVar}
        if self.level > 1:
            self.manager.addVariables(self.edgeClearVars)
            self.manager.addVariables(self.edgeAvailableVars)
            vdict[2] = self.onlyAvailableVar
        self.manager.addVariables(vdict)

    def doEdgePresentClauses(self):
        self.manager.doComment("Edge Present, level %d" % self.level)
        if self.level == 1:
            #  edgePresent[i,1] <--> !edgeRemoved[i,1]
            for i in unitRange(self.N-1):
                vlist = [self.edgePresentVars[i], self.edgeRemovedVars[i]]
                self.manager.doClause(vlist, [0,0])
                self.manager.doClause(vlist, [1,1])
        else:
            #  edgePresent[i,t] <--> edgePresent[i,t-1] & !edgeRemoved[i,t]
            for i in unitRange(self.N-1):
                #     edgePresent[i,t] --> !edgeRemoved[i,t]
                vlist = [self.edgePresentVars[i], self.edgeRemovedVars[i]]
                self.manager.doClause(vlist, [0,0])
                #     edgePresent[i,t] --> edgePresent[i,t-1]
                vlist = [self.edgePresentVars[i], self.prevVars[i]]
                self.manager.doClause(vlist, [0,1])
                #     edgePresent[i,t-1] & !edgeRemoved[i,t] --> edgePresent[i,t]
                vlist = [self.prevVars[i], self.edgeRemovedVars[i], self.edgePresentVars[i]]
                self.manager.doClause(vlist, [0, 1, 1])

    def doEdgeClearClauses(self):
        if self.level == 1:
            return
        else:
            self.manager.doComment("Edge Clear, level %d" % self.level)
            #  edgeClear[i,t] <--> edgePresent[i-1,t-1] & edgePresent[i,t-1] & edgePresent[i+1,t-1]
            for i in unitRange(self.N-1):
                rvlist = [self.edgeClearVars[i]]
                rplist = [1]
                if i > 1:
                    #     edgeClear[i,t] --> edgePresent[i-1,t]
                    vlist = [self.edgeClearVars[i], self.prevVars[i-1]]
                    self.manager.doClause(vlist, [0,1])                    
                    rvlist.append(self.prevVars[i-1])
                    rplist.append(0)
                #     edgeClear[i,t] --> edgePresent[i,t]
                vlist = [self.edgeClearVars[i], self.prevVars[i]]
                self.manager.doClause(vlist, [0,1])                    
                rvlist.append(self.prevVars[i])
                rplist.append(0)
                if i < self.N-1:
                    #     edgeClear[i,t] --> edgePresent[i+1,t]
                    vlist = [self.edgeClearVars[i], self.prevVars[i+1]]
                    self.manager.doClause(vlist, [0,1])                    
                    rvlist.append(self.prevVars[i+1])
                    rplist.append(0)
                #  edgePresent[i-1,t-1] & edgePresent[i,t-1] & edgePresent[i+1,t-1] --> edgeClear[i,t]
                self.manager.doClause(rvlist, rplist)

    def doEdgeAvailableClauses(self):
        if self.level == 1:
            return
        else:
            #  edgeAvailable[i,t] <--> !edgeRemoved[i,t] OR edgeClear[i,t]
            self.manager.doComment("Edge Available, level %d" % self.level)
            for i in unitRange(self.N-1):
                #     edgeAvailable[i,t] --> !edgeRemoved[i,t] OR edgeClear[i,t]
                vlist = [self.edgeAvailableVars[i], self.edgeRemovedVars[i], self.edgeClearVars[i]]
                self.manager.doClause(vlist, [0,0,1])                
                #     edgeClear[i,t]  --> edgeAvailable[i,t]
                vlist = [self.edgeClearVars[i], self.edgeAvailableVars[i]]
                self.manager.doClause(vlist, [0,1])
                #     !edgeRemoved[i,t] --> edgeAvailable[i,t]
                vlist = [self.edgeRemovedVars[i], self.edgeAvailableVars[i]]
                self.manager.doClause(vlist, [1,1])

    def doUniqueChangedClauses(self):
        #  uniqueChanged[t] <--> Exactly1(edgeRemoved[i,t])
        self.manager.doComment("Unique Changed, level %d" % self.level)
        for i1 in unitRange(self.N-1):
            for i2 in range(i1+1, self.N):
                #     uniqueChanged[t] --> (!edgeRemoved[i,t] OR !edgeRemoved[i',t])  1 <= i < i'< N
                vlist = [self.uniqueChangedVar, self.edgeRemovedVars[i1], self.edgeRemovedVars[i2]]
                self.manager.doClause(vlist, [0, 0, 0])
        #     uniqueChanged[t] --> OR_i edgeRemoved[i,t]
        vlist = [self.uniqueChangedVar] + [self.edgeRemovedVars[i] for i in unitRange(self.N-1)]
        plist = [0] + [1] * (self.N-1)
        self.manager.doClause(vlist, plist)
        for i1 in unitRange(self.N-1):
            #     !edgeRemoved[1,t] & ... & !edgeRemoved[i-1, t] & edgeRemoved[i,t] & !edgeRemoved[i+1,t] & ... & !edgeRemoved[N-1,t] --> uniqueChanged[t]  1<=i< N
            plist = [1] + [0 if i1 == i else 1 for i in unitRange(self.N-1)]
            self.manager.doClause(vlist, plist)            


    def onlyAvailableClauses(self):
        if self.level == 1:
            return
        #  onlyAvailable[t] <--> AND_i edgeAvailable[i,t]
        self.manager.doComment("Only Available, level %d" % self.level)
        for i in unitRange(self.N-1):
            #     onlyAvailable[t] --> edgeAvailable[i,t]  1<=i< N, 1<=j<=N_i
            vlist = [self.onlyAvailableVar, self.edgeAvailableVars[i]]
            self.manager.doClause(vlist, [0,1])
        #     AND_i edgeAvailable[i,t] --> onlyAvailable[t]
        vlist = [self.onlyAvailableVar] + [self.edgeAvailableVars[i] for i in unitRange(self.N-1)]
        plist = [1] + [0] * (self.N-1)
        self.manager.doClause(vlist, plist)

    def doMovedClauses(self):
        self.manager.doComment("Moved, level %d" % self.level)
        clist = [self.uniqueChangedVar]
        if self.level > 1:
            clist.append(self.onlyAvailableVar)
        vlist = [self.movedVar] + clist
        plist = [1] + [0] * len(clist)
        self.manager.doClause(vlist, plist)
        for v in clist:
            vlist = [self.movedVar, v]
            self.manager.doClause(vlist, [0,1])            

    def doClauses(self):
        self.doEdgePresentClauses()
        self.doEdgeClearClauses()
        self.doEdgeAvailableClauses()
        self.doUniqueChangedClauses()
        self.onlyAvailableClauses()
        self.doMovedClauses()

    # Provide ordered list of variables that depend only on t
    def listTopVariables(self):
        #   uniqueChanged[t]: 1<=t<=N
        #   onlyAvailable[t]: 1 <t<=N
        #   moved[t]: 1<=t<=N
        vlist = [self.uniqueChangedVar.id]
        if self.level > 1:
            vlist.append(self.onlyAvailableVar.id)
        vlist.append(self.movedVar.id)
        return vlist
        
    # Provide ordered list of variables that depend on i and t
    def listBottomVariables(self, i):
        #   edgeRemoved[i,t]: 1<=i<=N-1, 1<=t<=N
        #   edgePresent[i,t]: 1<=i<=N-1, 1<=t<=N
        #   edgeClear[i,t]: 1<=i<=N-1, 1<t<=N
        #   edgeAvailable[i,t]: 1<=i<=N-1, 1<t<=N
        vlist = [self.edgeRemovedVars[i].id, self.edgePresentVars[i].id]
        if self.level > 1:
            vlist = [self.edgeClearVars[i].id] + vlist + [self.edgeAvailableVars[i].id]
        return vlist

class Domino:

    manager = None
    profile = None
    N = 0
    moveCount = 0
    moveList = []
    winnerVars = None
    invert = False

    def __init__(self, manager, N, invert):
        self.manager = manager
        self.N = N
        self.moveCount = N // 2
        self.invert = invert
        pmove = Move(manager, 1, N, invert, None)
        self.moveList = [pmove]
        for l in range(2, self.moveCount+1):
            nmove = Move(manager, l, N, invert, pmove.edgePresentVars)
            self.moveList.append(nmove)
            pmove = nmove
        self.doWinnerVars()

    def doWinnerVars(self):
        self.winnerVars = {}
        for l in range(self.moveCount+1):
            if l % 2 == (1 if self.invert else 0):
                continue
            v = self.manager.createTseitinVariable(l+1, "win[%d]" % l, False)
            self.winnerVars[l] = v
            cstring = "  win[%d]: %s" % (l, str(v.id))
            self.manager.doTseitinVariableComment(l+1, False, cstring)


    def doWinnerClauses(self):
        condition = "even" if self.invert else "odd"
        self.manager.doComment("Must have win in an %s number of steps" % condition)
        wkeys = sorted(self.winnerVars.keys())
        vlist = [self.winnerVars[l] for l in wkeys]
        plist = [1] * len(wkeys)
        self.manager.doClause(vlist, plist)
        for lastl in wkeys:
            self.manager.doComment("Win in %d steps" % lastl)
            for l in unitRange(lastl):
                vlist = [self.winnerVars[lastl], self.moveList[l-1].movedVar]
                self.manager.doClause(vlist, [0, 1])
            if lastl < self.moveCount:
                vlist = [self.winnerVars[lastl], self.moveList[lastl].movedVar]
                self.manager.doClause(vlist, [0, 0])            

    def doVariables(self):
        for move in self.moveList:
            move.emitVariables()


    def doClauses(self):
        for move in self.moveList:
            move.doClauses()
        self.doWinnerClauses()

    def buildQcnf(self):
        self.doVariables()
        self.manager.addVariables(self.winnerVars)
        self.doClauses()
        self.manager.finish()

    def listVariables(self, writer):
        for l in unitRange(self.moveCount):
#        for l in range(self.moveCount,0,-1):
            vlist = []
            vlist += self.moveList[l-1].listTopVariables()
            if l-1 in self.winnerVars:
                # Winner variable belongs to next higher level
                vlist.append(self.winnerVars[l-1].id)
            if l == self.moveCount and l in self.winnerVars:
                # Final winner variable belongs in last level
                vlist.append(self.winnerVars[l].id)
            writer.doOrder(vlist)
        for i in unitRange(self.N-1):
            for l in unitRange(self.moveCount):
#            for l in range(self.moveCount,0,-1):
                writer.doOrder(self.moveList[l-1].listBottomVariables(i))


def run(name, args):
    N = 2
    root = None
    verbose = False
    invert = False
    tseitinMode = Manager.tseitinEnd
    optlist, args = getopt.getopt(args, "hvit:n:r:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
        elif opt == '-i':
            invert = True
        elif opt == '-t':
            if val == 'b':
                tseitinMode = Manager.tseitinBefore
            elif val == 'a':
                tseitinMode = Manager.tseitinAfter
            elif val == 'e':
                tseitinMode = Manager.tseitinEnd
            else:
                print("Unknown Tseitin variable placement mode '%s'" % val)
                usage(name)
                return
        elif opt == '-n':
            N = int(val)
        elif opt == '-r':
            root = val
    if root is None:
        print("Must have output file root name")
        usage(name)
        return
    qwrite = writer.QcnfWriter(root)
    manager = Manager(qwrite, verbose, tseitinMode)
    domino = Domino(manager, N, invert)
    domino.buildQcnf()
    vwrite = writer.OrderWriter(manager.variableCount, root, verbose=verbose)
    domino.listVariables(vwrite)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
        
        
