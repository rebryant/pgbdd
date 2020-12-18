#!/usr/bin/python

import sys
import getopt

import writer


def usage(name):
    print("Usage: %s: [-h][-v] [-t b|a|i] -p N1+N2+..+Nk -r ROOT")
    print("  -h             Print this message")
    print("  -v             Include comments in output")
    print("  -t b|a|e       Specify position of Tseitin variables:")
    print("                   b: before their defining variables (when possible, otherwise after)")
    print("                   a: after their defining variables")
    print("                   e: at end of quantifier string")
    print("  -V p|b         Specify variable ordering strategy:")
    print("                   p: Ply-major")
    print("                   b: Bucket-major")
    print("  -p N1:N2:..Nk  Specify bucket profile")
    print("  -r ROOT        Specify root name for files.  Will generate ROOT.qcnf, ROOT.order, and ROOT.buckets")

# Generate QBF and other files for game of NIM

# Game defined by list of numbers [N1, N2, ..., Nk], with N = SUM Ni
# describing number of objects in each bucket initially

# VARIABLES:
# Input
#   itemRemoved[i,j,t]: 1<=i<=k, 1<=j<=Ni, 1<=t<=N
#    Attempt to remove item j from bucket i on step t
#
#
# Tseitin
#
#   itemPresent[i,j,t]: 1<=i<=k, 1<=j<=Ni, 1<=t<=N
#    Bucket i contains item j after step t
#
#   bucketChanged[i,t]:  1<=i<=k, 1<=t<=N
#    At least one element was removed from bucket i on step t
#
#   uniqueChanged[t]: 1<=t<=N
#    Items removed from exactly one bucket on step t
#
#   bucketMonotonic[i,t]: 1<=i<=k, 1<=t<=N
#    State elements for bucket i are monotonically ordered
#
#   gameMonotonic[t]: All state is monotonically ordered
#
#   itemAvailable[i,j,t]: 1<=i<=k, 1<=j<=Ni, 2<=t<=N
#    Any item taken was available for step t
#
#   allAvailable[t]:
#    All items taken were available for step t
#
#   moved[t]: 1<=t<=N
#    Legal move took place
#


# Tseitin variable computation

#  itemPresent[i,j,t] <--> itemPresent[i,j,t-1] & !itemRemoved[i,j,t]
#
#     itemPresent[i,j,t] --> !itemRemoved[i,j,t]
#     itemPresent[i,j,t] --> itemPresent[i,j,t-1]
#     itemPresent[i,j,t-1] & !itemRemoved[i,j,t] --> itemPresent[i,j,t]
#
#  bucketChanged[i,t] <--> OR_j itemRemoved[i,j,t]   1<=j<=Ni, 1<=i<=k, 1<=t<=N
#
#     bucketChanged[i,t] --> OR_j itemRemoved[i,j,t]
#     itemRemoved[i,j,t] --> bucketChanged[i,t]  1<=j<= Ni
#
#  uniqueChanged[t] <--> Exactly1(bucketChanged[i,t])
#
#     uniqueChanged[t] --> OR_i bucketChanged[i,t]
#     uniqueChanged[t] --> (!bucketChanged[i,t] OR !bucketChanged[i',t])  1 <= i < i'<= k
#     !bucketChanged[1,t] & ... & !bucketChanged[i-1, t] & bucketChanged[i,t] & !bucketChanged[i+1,t] & ... & !bucketChanged[k,t] --> uniqueChanged[t]  1<=i<=k
#
#  itemAvailable[i,j,t] <--> itemRemoved[i,j,t] --> itemPresent[i,j,t-1]
#
#     itemAvailable[i,j,t] --> itemRemoved[i,j,t] --> itemPresent[i,j,t-1]
#     itemPresent[i,j,t-1] --> itemAvailable[i,j,t]
#     !itemRemoved[i,j,t] --> itemAvailable[i,j,t]
#
#  allAvailable[t] <--> AND_i AND_j itemAvailable[i,j,t]
#     allAvailable[t] --> itemAvailable[i,j,t]  1<=i<=k, 1<=j<=N_i
#     AND_i AND_j itemAvailable[i,j,t] --> allAvailable[t]
#
#  bucketMonotonic[i,t] <--> AND_j itemPresent[i,j+1,t] --> itemPresent[i,j,t]
#     bucketMonotonic[i,t] --> itemPresent[i,j+1,t] --> itemPresent[i,j,t]  1<=j< N_i
#     (AND_[1<=j<J] itemPresent[i,j,t] & AND[J<=j<=N_i] !itemPresent[i,j,t]) --> bucketMonotonic[i,t]  0<=J<=N_i
#
#  gameMonotonic[t] <--> AND_i bucketMonotonic[i,t]
#     gameMonotonic[t] --> bucketMonotonic[i,t] 1<=i<=k
#     (AND_i bucketMonotonic[i,t]) --> gameMonotonic[t]
#
#  moved[t] <--> uniqueChanged[t] & gameMonotonic[t] & allAvailable[t]
#     moved[t] --> uniqueChanged[t]
#     moved[t] --> gameMonotonic[t]
#     moved[t] --> allAvailable[t]
#     uniqueChanged[t] & gameMonotonic[t] & allAvailable[t] --> moved[t]
#

# Global Constraints.  

# Winning scenarios
# w[t] --> AND_t' moved[t'] & !moved[t+1]  All odd t
#
# Winning
# OR_odd_t w[t]

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

# Manage single ply of game
class Ply:

    level = 1
    manager = None
    # profile is a list of bucket sizes
    profile = []
    bucketCount = 0 
    isExistential = False
    #   itemRemoved[i,j,t]: 1<=i<=k, 1<=j<=Ni
    #    Attempt to remove item j from bucket i on step t
    itemRemovedVars = {}
    #   itemPresent[i,j,t]: 1<=i<=k, 1<=j<=Ni
    #    Bucket i contains item j after step t
    itemPresentVars = {}
    #   itemPresent[i,j,t-1]: 1<=i<=k, 1<=j<=Ni
    #    Bucket i contains item j after step t-1
    prevVars = None
    #   bucketChanged[i,t]:  1<=i<=k, 1<=t<=N
    #    At least one element was removed from bucket i on step t
    bucketChangedVars = {}
    #   uniqueChanged[t]
    #    Items removed from exactly one bucket on step t
    uniqueChangedVar = None
    #   bucketMonotonic[i,t]: 1<=i<=k
    #    State elements for bucket i are monotonically ordered
    bucketMonotonicVars = None
    #   gameMonotonic[t]: All state is monotonically ordered
    gameMonotonicVar = None
    #   itemAvailable[i,j,t]: 1<=i<=k, 1<=j<=Ni, 1<t<=N
    #    Any item removed was available for step t
    itemAvailableVars = None
    #   allAvailable[t]:
    #    All items taken were available for step t
    allAvailableVar = None
    #   moved[t]: 1<=t<=N
    #    Legal move took place
    movedVar = None

    def __init__(self, manager, level, profile, prevVars):
        self.level = level
        self.isExistential = level % 2 == 1
        self.manager = manager
        self.profile = profile
        self.bucketCount = len(profile)
        self.prevVars = prevVars
        self.makeInputVars()
        self.makeTseitinVars()
        
    def makeInputVars(self):
        slist = []
        self.itemRemovedVars = {}
        for i in unitRange(self.bucketCount):
            for j in unitRange(self.profile[i-1]):
                name = "itemRemoved[%d,%d,%d]" % (i, j, self.level)
                v = self.manager.createVariable(self.isExistential, self.level, name)
                self.itemRemovedVars[(i,j)] = v
                slist.append(str(v.id))
        cstring = "Level %d input variables: %s" % (self.level, ", ".join(slist))
        self.manager.doVariableComment(self.level, self.isExistential, cstring)
                                      
    def makeTseitinVars(self):
        #   itemPresent[i,j,t]: 1<=i<=k, 1<=j<=Ni
        self.itemPresentVars = {}
        slist = []
        for i in unitRange(self.bucketCount):
            for j in unitRange(self.profile[i-1]):
                name = "itemPresent[%d,%d,%d]" % (i, j, self.level)
                v = self.manager.createTseitinVariable(self.level, name, self.isExistential)
                self.itemPresentVars[(i,j)] = v
                slist.append(str(v.id))
        cstring = "Level %d Tseitin variables" % self.level
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)
        cstring = "  itemPresent: %s" % ", ".join(slist)
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        #   bucketChanged[i,t]:  1<=i<=k
        self.bucketChangedVars = {}
        slist = []
        for i in unitRange(self.bucketCount):
            name = "bucketChanged[%d,%d]" % (i, self.level)
            v = self.manager.createTseitinVariable(self.level, name, self.isExistential)
            self.bucketChangedVars[i] = v
            slist.append(str(v.id))
        cstring = "  bucketChanged: %s" % ", ".join(slist)
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        #   uniqueChanged[t]
        self.uniqueChangedVar = self.manager.createTseitinVariable(self.level, "uniqueChanged[%d]" % self.level, self.isExistential)
        cstring = "  uniqueChanged: %s" % self.uniqueChangedVar.id
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        #   bucketMonotonic[i,t]: 1<=i<=k, 1<=t<=N
        self.bucketMonotonicVars = {}
        slist = []
        for i in unitRange(self.bucketCount):
            name = "bucketMonotonic[%d,%d]" % (i, self.level)
            v = self.manager.createTseitinVariable(self.level, name, self.isExistential) 
            self.bucketMonotonicVars[i] = v
            slist.append(str(v.id))
        cstring = "  bucketMonotonic: %s" % ", ".join(slist)
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        #   gameMonotonic[t]
        self.gameMonotonicVar = self.manager.createTseitinVariable(self.level, "gameMonotonic[%d]" % self.level, self.isExistential)
        cstring = "  gameMonotonic: %s" % self.gameMonotonicVar.id
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        if self.level == 1:
            self.itemAvailableVars = None
            self.allAvailableVar = None
        else:
            #   itemAvailable[i,j,t]: 1<=i<=k, 1<=j<=Ni, 1<t<=N
            self.itemAvailableVars = {}
            slist = []
            for i in unitRange(self.bucketCount):
                for j in unitRange(self.profile[i-1]):
                    name = "itemAvailable[%d,%d,%d]" % (i, j, self.level)
                    v = self.manager.createTseitinVariable(self.level, name, self.isExistential)
                    self.itemAvailableVars[(i,j)] = v
                    slist.append(str(v.id))
            cstring = "  itemAvailable: %s" % ", ".join(slist)
            self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

            #   allAvailable[t]
            self.allAvailableVar = self.manager.createTseitinVariable(self.level, "allAvailable[%d]" % self.level, self.isExistential)
            cstring = "  allAvailable: %s" % self.allAvailableVar.id
            self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

        #   moved[t]: 1<=t<=N
        self.movedVar = self.manager.createTseitinVariable(self.level, "moved[%d]" % self.level, self.isExistential)
        cstring = "  moved: %s" % self.movedVar.id
        self.manager.doTseitinVariableComment(self.level, self.isExistential, cstring)

    def emitVariables(self):
        self.manager.addVariables(self.itemRemovedVars)
        self.manager.addVariables(self.itemPresentVars)
        self.manager.addVariables(self.bucketChangedVars)
        self.manager.addVariables(self.bucketMonotonicVars)
        if self.level == 1:
            self.manager.addVariables({1: self.uniqueChangedVar,
                                       2: self.gameMonotonicVar,
                                       3: self.movedVar})
        else:
            self.manager.addVariables(self.itemAvailableVars)
            self.manager.addVariables({1: self.uniqueChangedVar,
                                       2: self.gameMonotonicVar,
                                       3: self.allAvailableVar, 
                                       4: self.movedVar})

    def doItemPresentClauses(self):
        self.manager.doComment("Item Present, level %d" % self.level)
        if self.level == 1:
            #  itemPresent[i,j,1] <--> !itemRemoved[i,j,1]
            for i in unitRange(self.bucketCount):
                for j in unitRange(self.profile[i-1]):
                    vlist = [self.itemPresentVars[(i,j)], self.itemRemovedVars[(i,j)]]
                    self.manager.doClause(vlist, [0,0])
                    self.manager.doClause(vlist, [1,1])
        else:
            #  itemPresent[i,j,t] <--> itemPresent[i,j,t-1] & !itemRemoved[i,j,t]
            for i in unitRange(self.bucketCount):
                for j in unitRange(self.profile[i-1]):
                    #     itemPresent[i,j,t] --> !itemRemoved[i,j,t]
                    vlist = [self.itemPresentVars[(i,j)], self.itemRemovedVars[(i,j)]]
                    self.manager.doClause(vlist, [0,0])
                    #     itemPresent[i,j,t] --> itemPresent[i,j,t-1]
                    vlist = [self.itemPresentVars[(i,j)], self.prevVars[(i,j)]]
                    self.manager.doClause(vlist, [0,1])
                    #     itemPresent[i,j,t-1] & !itemRemoved[i,j,t] --> itemPresent[i,j,t]
                    vlist = [self.prevVars[(i,j)], self.itemRemovedVars[(i,j)], self.itemPresentVars[(i,j)]]
                    self.manager.doClause(vlist, [0, 1, 1])

    def doBucketChangedClauses(self):
        #  bucketChanged[i,t] <--> OR_j itemRemoved[i,j,t]   1<=j<=Ni, 1<=i<=k, 1<=t<=N
        self.manager.doComment("Bucket Changed, level %d" % self.level)
        for i in unitRange(self.bucketCount):
            #     bucketChanged[i,t] --> OR_j itemRemoved[i,j,t]
            vlist = [self.bucketChangedVars[i]] + [self.itemRemovedVars[(i,j)] for j in unitRange(self.profile[i-1])]
            plist = [0] + [1] * self.profile[i-1]
            self.manager.doClause(vlist, plist)
            for j in unitRange(self.profile[i-1]):
                #     itemRemoved[i,j,t] --> bucketChanged[i,t]  1<=j<= Ni
                vlist = [self.itemRemovedVars[(i,j)], self.bucketChangedVars[i]]
                self.manager.doClause(vlist, [0, 1])

    def doUniqueChangedClauses(self):
        #  uniqueChanged[t] <--> Exactly1(bucketChanged[i,t])
        self.manager.doComment("Unique Changed, level %d" % self.level)
        for i1 in unitRange(self.bucketCount):
            for i2 in range(i1+1, self.bucketCount+1):
                #     uniqueChanged[t] --> (!bucketChanged[i,t] OR !bucketChanged[i',t])  1 <= i < i'<= k
                vlist = [self.uniqueChangedVar, self.bucketChangedVars[i1], self.bucketChangedVars[i2]]
                self.manager.doClause(vlist, [0, 0, 0])
        #     uniqueChanged[t] --> OR_i bucketChanged[i,t]
        vlist = [self.uniqueChangedVar] + [self.bucketChangedVars[i] for i in unitRange(self.bucketCount)]
        plist = [0] + [1] * self.bucketCount
        self.manager.doClause(vlist, plist)
        for i1 in unitRange(self.bucketCount):
            #     !bucketChanged[1,t] & ... & !bucketChanged[i-1, t] & bucketChanged[i,t] & !bucketChanged[i+1,t] & ... & !bucketChanged[k,t] --> uniqueChanged[t]  1<=i<=k
            plist = [1] + [0 if i1 == i else 1 for i in unitRange(self.bucketCount)]
            self.manager.doClause(vlist, plist)            


    def doBucketMonotonicClauses(self):
        #  bucketMonotonic[i,t] <--> AND_j itemPresent[i,j+1,t] --> itemPresent[i,j,t]
        self.manager.doComment("Bucket Monotonic, level %d" % self.level)
        for i in unitRange(self.bucketCount):
            for j in unitRange(self.profile[i-1]-1):
                #     bucketMonotonic[i,t] --> itemPresent[i,j+1,t] --> itemPresent[i,j,t]  1<=j< N_i
                vlist = [self.bucketMonotonicVars[i], self.itemPresentVars[(i,j+1)], self.itemPresentVars[(i,j)]]
                self.manager.doClause(vlist, [0, 0, 1])
        for i in unitRange(self.bucketCount):
            vlist = [self.bucketMonotonicVars[i]] + [self.itemPresentVars[(i,j)] for j in unitRange(self.profile[i-1])]
            for J in range(1,self.profile[i-1]+2):
                #     (AND_[1<=j<J] itemPresent[i,j,t] & AND[J<=j<=N_i] !itemPresent[i,j,t]) --> bucketMonotonic[i,t]  0<=J<=N_i
                plist = [1] + [0 if j < J else 1 for j in unitRange(self.profile[i-1])]
                self.manager.doClause(vlist, plist)                

    def doGameMontonicClauses(self):
        #  gameMonotonic[t] <--> AND_i bucketMonotonic[i,t]
        self.manager.doComment("Game Monotonic, level %d" % self.level)
        for i in unitRange(self.bucketCount):
            #     gameMonotonic[t] --> bucketMonotonic[i,t] 1<=i<=k
            vlist = [self.gameMonotonicVar, self.bucketMonotonicVars[i]]
            self.manager.doClause(vlist, [0,1])
        #     (AND_i bucketMonotonic[i,t]) --> gameMonotonic[t]
        vlist = [self.gameMonotonicVar] + [self.bucketMonotonicVars[i] for i in unitRange(self.bucketCount)]
        plist = [1] + [0] * self.bucketCount
        self.manager.doClause(vlist, plist)

    def doItemAvailableClauses(self):
        if self.level == 1:
            return
        else:
            #  itemAvailable[i,j,t] <--> itemRemoved[i,j,t] --> itemPresent[i,j,t-1]
            self.manager.doComment("Item Available, level %d" % self.level)
            for i in unitRange(self.bucketCount):
                for j in unitRange(self.profile[i-1]):
                    #     itemAvailable[i,j,t] --> itemRemoved[i,j,t] --> itemPresent[i,j,t-1]
                    vlist = [self.itemAvailableVars[(i,j)], self.itemRemovedVars[(i,j)], self.prevVars[(i,j)]]
                    self.manager.doClause(vlist, [0,0,1])                
                    #     itemPresent[i,j,t-1]  --> itemAvailable[i,j,t]
                    vlist = [self.prevVars[(i,j)], self.itemAvailableVars[(i,j)]]
                    self.manager.doClause(vlist, [0,1])
                    #     !itemRemoved[i,j,t] --> itemAvailable[i,j,t]
                    vlist = [self.itemRemovedVars[(i,j)], self.itemAvailableVars[(i,j)]]
                    self.manager.doClause(vlist, [1,1])

    def allAvailableClauses(self):
        if self.level == 1:
            return
        #  allAvailable[t] <--> AND_i AND_j itemAvailable[i,j,t]
        self.manager.doComment("All Available, level %d" % self.level)
        for i in unitRange(self.bucketCount):
            for j in unitRange(self.profile[i-1]):
                #     allAvailable[t] --> itemAvailable[i,j,t]  1<=i<=k, 1<=j<=N_i
                vlist = [self.allAvailableVar, self.itemAvailableVars[(i,j)]]
                self.manager.doClause(vlist, [0,1])
        #     AND_i AND_j itemAvailable[i,j,t] --> allAvailable[t]
        vlist = [self.allAvailableVar]
        plist = [1]
        for i in unitRange(self.bucketCount):
            vlist += [self.itemAvailableVars[(i,j)] for j in unitRange(self.profile[i-1])]
            plist += [0] * self.profile[i-1]
        self.manager.doClause(vlist, plist)

    def doMovedClauses(self):
        if self.level == 1:
            #  moved[t] <--> uniqueChanged[t] & gameMonotonic[t]
            self.manager.doComment("Moved, level %d" % self.level)
            #     moved[t] --> uniqueChanged[t]
            vlist = [self.movedVar, self.uniqueChangedVar]
            self.manager.doClause(vlist, [0,1])
            #     moved[t] --> gameMonotonic[t]
            vlist = [self.movedVar, self.gameMonotonicVar]
            self.manager.doClause(vlist, [0,1])
            #     uniqueChanged[t] & gameMonotonic[t] --> moved[t]
            vlist = [self.uniqueChangedVar, self.gameMonotonicVar, self.movedVar]
            self.manager.doClause(vlist, [0,0,1])
        else:
            #  moved[t] <--> uniqueChanged[t] & gameMonotonic[t] & allAvailable[t]
            self.manager.doComment("Moved, level %d" % self.level)
            #     moved[t] --> uniqueChanged[t]
            vlist = [self.movedVar, self.uniqueChangedVar]
            self.manager.doClause(vlist, [0,1])
            #     moved[t] --> gameMonotonic[t]
            vlist = [self.movedVar, self.gameMonotonicVar]
            self.manager.doClause(vlist, [0,1])
            #     moved[t] --> allAvailable[t]
            vlist = [self.movedVar, self.allAvailableVar]
            self.manager.doClause(vlist, [0,1])
            #     uniqueChanged[t] & gameMonotonic[t] & allAvailable[t] --> moved[t]
            vlist = [self.uniqueChangedVar, self.gameMonotonicVar, self.allAvailableVar, self.movedVar]
            self.manager.doClause(vlist, [0,0,0,1])

    def doClauses(self):
        self.doItemPresentClauses()
        self.doBucketChangedClauses()
        self.doUniqueChangedClauses()
        self.doBucketMonotonicClauses()
        self.doGameMontonicClauses()
        self.doItemAvailableClauses()
        self.allAvailableClauses()
        self.doMovedClauses()


    # Provide ordered list of variables that depend only on t
    def listTopVariables(self):
        #   uniqueChanged[t]: 1<=t<=N
        #   gameMonotonic[t]: All state is monotonically ordered
        #   allAvailable[t]: 1 <t<=N
        #   moved[t]: 1<=t<=N
        if self.level == 1:
            vlist = [self.uniqueChangedVar.id, self.gameMonotonicVar.id, self.movedVar.id]
        else:
            vlist = [self.uniqueChangedVar.id, self.gameMonotonicVar.id, self.allAvailableVar.id, self.movedVar.id]
        return vlist

    # Provide ordered list of variables that depend only on i and t
    # If bucket specified, then only those for indicated bucket
    def listMiddleVariables(self, bucket = None):

        #   bucketChanged[i,t]:  1<=i<=k, 1<=t<=N
        #   bucketMonotonic[i,t]: 1<=i<=k, 1<=t<=N
        if bucket is None:
            vlist = []
            for i in unitRange(self.bucketCount):
                vlist += [self.bucketChangedVars[i].id, self.bucketMonotonicVars[i].id]
        else:
            vlist = [self.bucketChangedVars[bucket].id, self.bucketMonotonicVars[bucket].id]
        return vlist
        
    # Provide ordered list of variables that depend on i, j, and t
    # If bucket specified, then only those for indicated bucket
    def listBottomVariables(self, bucket = None):
        #   itemRemoved[i,j,t]: 1<=i<=k, 1<=j<=Ni, 1<=t<=N
        #   itemPresent[i,j,t]: 1<=i<=k, 1<=j<=Ni, 1<=t<=N
        #   itemAvailable[i,j,t]: 1<=i<=k, 1<=j<=Ni, 2<=t<=N
        vlist = []
        if bucket is None:
            for i in unitRange(self.bucketCount):
                for j in unitRange(self.profile[i-1]):
                    vlist += [self.itemRemovedVars[(i,j)].id, self.itemPresentVars[(i,j)].id]
                    if self.level > 1:
                        vlist += [self.itemAvailableVars[(i,j)].id]
        else:
            for j in unitRange(self.profile[bucket-1]):
                vlist += [self.itemRemovedVars[(bucket,j)].id, self.itemPresentVars[(bucket,j)].id]
                if self.level > 1:
                    vlist += [self.itemAvailableVars[(bucket,j)].id]
        return vlist



class Nim:

    # Variable ordering strategies
    plyMajor, bucketMajor = range(2)


    manager = None
    profile = None
    bucketCount = 0
    plyList = []
    plyCount = 0
    winnerVars = None

    def __init__(self, manager, profile):
        self.manager = manager
        self.profile = profile
        self.bucketCount = len(profile)
        self.plyCount = sum(profile)
        pply = Ply(manager, 1, profile, None)
        self.plyList = [pply]
        for l in range(2, self.plyCount+1):
            nply = Ply(manager, l, profile, pply.itemPresentVars)
            self.plyList.append(nply)
            pply = nply
        self.doWinnerVars()

    def doWinnerVars(self):
        self.winnerVars = {}
        for l in unitRange(self.plyCount):
            if l % 2 == 0:
                continue
            v = self.manager.createTseitinVariable(l+1, "win[%d]" % l, False)
            self.winnerVars[l] = v
            cstring = "  win[%d]: %s" % (l, str(v.id))
            self.manager.doTseitinVariableComment(l+1, False, cstring)


    def doWinnerClauses(self):
        self.manager.doComment("Must have win in an odd number of steps")
        wkeys = sorted(self.winnerVars.keys())
        vlist = [self.winnerVars[l] for l in wkeys]
        plist = [1] * len(wkeys)
        self.manager.doClause(vlist, plist)
        for lastl in wkeys:
            self.manager.doComment("Win in %d steps" % lastl)
            for l in unitRange(lastl):
                vlist = [self.winnerVars[lastl], self.plyList[l-1].movedVar]
                self.manager.doClause(vlist, [0, 1])
            if lastl < self.plyCount:
                vlist = [self.winnerVars[lastl], self.plyList[lastl].movedVar]
                self.manager.doClause(vlist, [0, 0])            

    def doVariables(self):
        for ply in self.plyList:
            ply.emitVariables()


    def doClauses(self):
        for ply in self.plyList:
            ply.doClauses()
        self.doWinnerClauses()

    def buildQcnf(self):
        self.doVariables()
        self.manager.addVariables(self.winnerVars)
        self.doClauses()
        self.manager.finish()

    def listVariablesPlyMajor(self, writer):
        for l in unitRange(self.plyCount):
            vlist = []
            vlist += self.plyList[l-1].listTopVariables()
            if l-1 in self.winnerVars:
                # Winner variable belongs to next higher level
                vlist.append(self.winnerVars[l-1].id)
            if l == self.plyCount and l in self.winnerVars:
                # Final winner variable belongs in last level
                vlist.append(self.winnerVars[l].id)
            writer.doOrder(vlist)
            writer.doOrder(self.plyList[l-1].listMiddleVariables(bucket = None))
            writer.doOrder(self.plyList[l-1].listBottomVariables(bucket = None))
        return vlist

    def listVariablesBucketMajor(self, writer):
        for l in unitRange(self.plyCount):
            vlist = []
            vlist += self.plyList[l-1].listTopVariables()
            if l-1 in self.winnerVars:
                # Winner variable belongs to next higher level
                vlist.append(self.winnerVars[l-1].id)
            if l == self.plyCount and l in self.winnerVars:
                # Final winner variable belongs in last level
                vlist.append(self.winnerVars[l].id)
            writer.doOrder(vlist)
        for i in unitRange(self.bucketCount):
            for l in unitRange(self.plyCount):
                writer.doOrder(self.plyList[l-1].listMiddleVariables(bucket = i))
                writer.doOrder(self.plyList[l-1].listBottomVariables(bucket = i))
        return vlist
    
    def listVariables(self, mode, writer):
        if mode == self.plyMajor:
            self.listVariablesPlyMajor(writer)
        elif mode == self.bucketMajor:
            self.listVariablesBucketMajor(writer)
        else:
            msg = "Unknown variable ordering mode %s" % str(mode)
            raise Exception(msg)


def run(name, args):
    profile = []
    root = None
    verbose = False
    tseitinMode = Manager.tseitinEnd
    variableMode = None
    optlist, args = getopt.getopt(args, "hvt:V:p:r:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        elif opt == '-v':
            verbose = True
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
        elif opt == '-V':
            if val == 'p':
                variableMode = Nim.plyMajor
            elif val == 'b':
                variableMode = Nim.bucketMajor
            else:
                print("Unknown Tseitin variable ordering strategy '%s'" % val)
                usage(name)
                return
        elif opt == '-p':
            pfields = val.split('+')
            try:
                profile = [int(s) for s in pfields]
            except:
                print("Couldn't parse profile '%s'" % val)
                usage(name)
                return
            if sum(profile) == 0:
                print("invalid profile '%s'" % val)
                return
        elif opt == '-r':
            root = val
    if profile is None:
        print("Must have profile")
        usage(name)
        return
    if root is None:
        print("Must have output file root name")
        usage(name)
        return
    qwrite = writer.QcnfWriter(root)
    manager = Manager(qwrite, verbose, tseitinMode)
    nim = Nim(manager, profile)
    nim.buildQcnf()

    if variableMode is not None:
        vwrite = writer.OrderWriter(manager.variableCount, root, verbose=verbose)
        nim.listVariables(variableMode, vwrite)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
    
        
        
