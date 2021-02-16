#!/usr/bin/python

#####################################################################################
# Copyright (c) 2021 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
# Last edit: Feb. 16, 2021
# 
# Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
# associated documentation files (the "Software"), to deal in the Software without restriction,
# including without limitation the rights to use, copy, modify, merge, publish, distribute,
# sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all copies or
# substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
# NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
# DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
# OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
########################################################################################


# Simple, proof-generating QBF solver based on BDDs

import sys
import getopt
import datetime

import bdd
import resolver
import proof
import util


# Increase maximum recursion depth
sys.setrecursionlimit(50 * sys.getrecursionlimit())

def usage(name):
    sys.stderr.write("Usage: %s [-h][-v LEVEL] [-m (n|d|s|r)] [-l e|u|eu] [-i CNF] [-o file.{qrat,qproof}] [-B BPERM] [-p VPERM] [-c CLUSTER] [-L logfile]\n" % name)
    sys.stderr.write("  -h          Print this message\n")
    sys.stderr.write("  -m MODE     Set proof mode (n = no proof, d = dual, s = satisfaction only, r = refutation only)\n")
    sys.stderr.write("  -l e|u|eu   Linearize quantifier blocks for existential (e) and/or universal (u) variables\n")
    sys.stderr.write("  -v LEVEL    Set verbosity level\n")
    sys.stderr.write("  -i CNF      Name of CNF input file\n")
    sys.stderr.write("  -o pfile    Name of proof output file (QRAT or QPROOF format)\n")
    sys.stderr.write("  -B BPERM    Process terms via bucket elimination ordered by permutation file BPERM\n")
    sys.stderr.write("  -p VPERM    Name of file specifying mapping from CNF variable to BDD level\n")
    sys.stderr.write("  -c CLUSTER  Name of file specifying how to group clauses into clusters\n")
    sys.stderr.write("  -L logfile  Append standard error output to logfile\n")

# Verbosity levels
# 0: Totally silent
# 1: Key statistics only
# 2: Summary information
# 3: Proof information
# 4: ?
# 5: Tree generation information

def trim(s):
    while len(s) > 0 and s[-1] == '\n':
        s = s[:-1]
    return s

# Abstract representation of Boolean function
class Term:

    manager = None
    root = None
    support = None    # Variables in support represented by list
    size = 0
    validation = None # Clause id providing validation
    mode = None # What is type of proof is being generated

    def __init__(self, manager, root, validation, mode = None):
        self.manager = manager
        self.root = root
        self.size = self.manager.getSize(root)
        self.support = None
        self.validation = validation
        if mode is None:
            self.mode = proof.ProverMode.noProof
        else:
            self.mode = mode

    def getSupport(self):
        if self.support is None:
            self.support = self.manager.getSupportIds(self.root)
        return self.support

    # Generate conjunction of two terms
    # All four modes
    def combine(self, other):
        validation = None
        if self.mode in [proof.ProverMode.refProof, proof.ProverMode.dualProof]:
            antecedents = [self.validation, other.validation]
            newRoot, implication = self.manager.applyAndJustify(self.root, other.root)
            if newRoot == self.manager.leaf0:
                comment = "Conjunction: Validation of Empty clause"
            else:
                comment = "Conjunction: Validation of %s" % newRoot.label()
            if implication == resolver.tautologyId:
                if newRoot == self.root:
                    validation = self.validation
                elif newRoot == other.root:
                    validation = other.validation
            else:
                antecedents += [implication]
            if validation is None:
                validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, comment)
        else:
            newRoot = self.manager.applyAnd(self.root, other.root)
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # No proof or refutation
    def equantifySimple(self, literals, prover):
        newRoot = self.manager.equant(self.root, literals)
        if newRoot == self.manager.leaf1:
            return None
        validation = None
        if self.mode == proof.ProverMode.refProof:
            antecedents = [self.validation]
            check, implication = self.manager.justifyImply(self.root, newRoot)
            if not check:
                raise bdd.BddException("Implication failed %s -/-> %s" % (self.root.label(), newRoot.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, "EQuant: Validation of %s" % newRoot.label())
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # No proof or satisfaction.  
    def uquantify(self, literals, prover):
        newRoot = self.manager.uquant(self.root, literals)
        validation = None
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # Refutation proof: Split universal quantification into two operations per variable
    def restrictRefutation(self, literal, prover):
        antecedents = [self.validation]
        newRoot, implication = self.manager.applyRestrictDown(self.root, literal)
        if implication != resolver.tautologyId:
            antecedents += [implication]
        if newRoot == self.manager.leaf1:
            return None
        ulit = literal.variable.id
        if literal.high == self.manager.leaf1:
            ulit = -ulit
        rclause = [ulit, newRoot.id]
        # Now apply universal reduction.
        comment = "Apply universal reduction to eliminate variable %d" % literal.variable.id
        if self.manager.prover.doQrat:
            rule1 = self.manager.prover.createClause(rclause)
            validation = self.manager.prover.qratUniversal(rule1, ulit)
        else:
            rule1 = self.manager.prover.proveAddResolution(rclause, antecedents, comment)
            validation = self.manager.prover.proveUniversal(ulit, rule1, None)
        return Term(self.manager, newRoot, validation, mode = self.mode)

    # Dual proof.  Universal quantification
    def uquantifyDual(self, lit, nlit, prover):
        lname = str(lit.variable)
        litid = lit.variable.id

        root1, downImplication1 = self.manager.applyRestrictDown(self.root, lit)
        root1, upImplication1 = self.manager.applyRestrictUp(self.root, lit)
        up1Antecedents = None
        validation1 = None
        if root1 == self.manager.leaf1:
            # Down Implication will be tautology
            # Up Implication will be [-lit, self.root.id]
            # validation1 will be tautology
            # up1 will be [-lit, self.root.id]
            up1 = upImplication1
        elif root1 == self.manager.leaf0:
            # Down Implication will be [-lit, -self.root.id]
            # Up Implication will be tautology
            # validation1 will be []
            # up1 will be tautology
            dclause = [-litid]
            antecedents = [downImplication1, self.validation]
            comment = "Restrict: Validation of empty clause"
            down1 = self.manager.prover.proveAddResolution(dclause, antecedents, comment)            
            comment = "Restriction by -%d, followed by universal reduction yields empty clause" % litid
            if self.manager.prover.doQrat:
                validation1 = self.manager.prover.qratUniversal(down1, -litid)
            else:
                validation1 = self.manager.prover.proveUniversal(-litid, down1, comment)
            return None
        else:
            # Down Implication will be [-lit, -self.root.id, root1.id]
            # Up Implication will be   [-lit, -root1.id, self.root.id]
            # validation1 will be [root1.id]
            # up1 will be [-lit, self.root.id]
            dclause = [-litid, root1.id]
            antecedents = [downImplication1, self.validation]
            comment = "Restrict: Validation of positive restriction %s" % root1.label()
            down1 = self.manager.prover.proveAddResolution(dclause, antecedents, comment)
            # Apply universal reduction
            comment = "Apply universal reduction to eliminate variable %d" % litid
            if self.manager.prover.doQrat:
                validation1 = self.manager.prover.qratUniversal(down1, -litid)
            else:
                validation1 = self.manager.prover.proveUniversal(-litid, down1, comment)
                # Now remove down1
                comment = "Remove downward implication of positive restriction"
                self.manager.prover.proveDeleteResolution(down1, antecedents, comment)
            uclause = [-litid, self.root.id]
            up1Antecedents = [upImplication1, validation1]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up1 = prover.proveAddResolution(uclause, up1Antecedents, comment)

        root0, downImplication0 = self.manager.applyRestrictDown(self.root, nlit)
        root0, upImplication0 = self.manager.applyRestrictUp(self.root, nlit)
        up0Antecedents = None
        validation0 = None
        if root0 == self.manager.leaf1:
            # Down Implication will be tautology
            # Up Implication will be [lit, self.root.id]
            # validation0 will be tautology
            # up0 will be [lit, self.root.id]
            up0 = upImplication0
        elif root0 == self.manager.leaf0:
            # Down Implication will be [lit, -self.root.id]
            # Up Implication will be tautology
            # validation0 will be []
            # up0 will be tautology
            dclause = [litid]
            antecedents = [downImplication0, self.validation]
            comment = "Restrict: Validation of empty clause"
            down0 = self.manager.prover.proveAddResolution(dclause, antecedents, comment)
            comment = "Restriction by %d, followed by universal reduction yields empty clause" % litid
            if self.manager.prover.doQrat:
                validation0 = self.manager.prover.qratUniversal(down0, litid)
            else:
                validation0 = self.manager.prover.proveUniversal(litid, down0, comment)
            return None
        else:
            # Down Implication will be [lit, -self.root.id, root1.id]
            # Up Implication will be   [lit, -root1.id, self.root.id]
            # validation0 will be [root1.id]
            # up0 will be [lit, self.root.id]
            dclause = [litid, root0.id]
            antecedents = [downImplication0, self.validation]
            comment = "Restrict: Validation of negative restriction %s" % root0.label()
            down0 = self.manager.prover.proveAddResolution(dclause, antecedents, comment)
            comment = "Apply universal reduction to eliminate variable %d" % litid
            if self.manager.prover.doQrat:
                validation0 = self.manager.prover.qratUniversal(down0, litid)
            else:
                validation0 = self.manager.prover.proveUniversal(litid, down0, comment)
                # Now remove down0
                comment = "Remove downward implication of negative restriction"
                self.manager.prover.proveDeleteResolution(down0, antecedents, comment)
            uclause = [litid, self.root.id]
            up0Antecedents = [upImplication0, validation0]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up0 = prover.proveAddResolution(uclause, up0Antecedents, comment)


        antecedents = [up1, up0]
        comment = "Deletion of clause #%d during universal quantfication" % self.validation
        prover.proveDeleteResolution(self.validation, antecedents, comment)
        if up1Antecedents is not None:
            comment = "Delete upward implication of positive restriction"
            prover.proveDeleteResolution(up1, up1Antecedents, comment)            
        if up0Antecedents is not None:
            comment = "Delete upward implication of negative restriction"
            prover.proveDeleteResolution(up0, up0Antecedents, comment)            

        # Form conjunction of two restrictions
        if root1 == self.manager.leaf1:
            newRoot = root0
            validation = validation0
        elif root0 == self.manager.leaf1:
            newRoot = root1
            validation = validation1
        else:
            validation = None
            antecedents = [validation1, validation0]
            newRoot, implication = self.manager.applyAndJustify(root1, root0)
            if newRoot == self.manager.leaf0:
                comment = "Conjunction of restrictions %s and %s: Validation of Empty clause" % (root1.label(), root0.label())
            else:
                comment = "Conjunction of restrictions %s and %s: Validation of %s" % (root1.label(), root0.label(), newRoot.label())
            if implication == resolver.tautologyId:
                if newRoot == root1:
                    validation = validation1
                elif newRoot == root0:
                    validation = validation0
            else:
                antecedents += [implication]
            if validation is None:
                validation = self.manager.prover.proveAddResolution([newRoot.id], antecedents, comment)

            justification1 = [validation]
            impl1 = self.manager.justifyImply(newRoot, root1)[1]
            if impl1 is not resolver.tautologyId:
                justification1.append(impl1)
            impl0 = self.manager.justifyImply(newRoot, root0)[1]
            justification0 = [validation]
            if impl0 is not resolver.tautologyId:
                justification0.append(impl0)
            if newRoot != root1:
                comment = "Delete unit clause for positive restriction of N%d" % self.root.id
                prover.proveDeleteResolution(validation1, justification1, comment)
            if newRoot != root0:
                comment = "Delete unit clauses for negative restriction of N%d" % self.root.id
                prover.proveDeleteResolution(validation0, justification0, comment)

        # Manager needs to be informed that quantification has completed
        self.manager.markQuantified(lit.variable)

        return Term(self.manager, newRoot, validation, mode = self.mode)


    # Satisfaction proof.  Existential quantification
    def equantifySatisfaction(self, lit, nlit, prover):
        lname = str(lit.variable)
        litid = lit.variable.id

        root1, implication1 = self.manager.applyRestrictUp(self.root, lit)
        if root1 == self.manager.leaf1:
            # Implication will be [-lit, self.root.id]
            up1 = implication1
            shannon1 = None
        elif root1 == self.manager.leaf0:
            rclause = [-litid]
            comment = "Shannon Expansion: Assert !%s" % (lname)
            shannon1 = self.manager.prover.proveAdd(rclause, comment)
            up1 = shannon1
        else:
            rclause = [-litid, root1.id]
            comment = "Shannon Expansion: Assert %s --> %s" % (lname, root1.label())
            shannon1 = self.manager.prover.proveAdd(rclause, comment)
            antecedents = [shannon1, implication1]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up1 = prover.proveAddResolution([-litid, self.root.id], antecedents, comment)

        root0, implication0 = self.manager.applyRestrictUp(self.root, nlit)
        if root0 == self.manager.leaf1:
            up0 = implication0
            shannon0 = None
        elif root0 == self.manager.leaf0:
            rclause = [litid]
            comment = "Shannon Expansion: Assert %s" % (lname)
            shannon0 = self.manager.prover.proveAdd(rclause, comment)
            up0 = shannon0
        else:
            rclause = [litid, root0.id]
            comment = "Shannon Expansion: Assert -%s --> %s" % (lname, root0.label())
            shannon0 = self.manager.prover.proveAdd(rclause, comment)
            antecedents = [shannon0, implication0]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up0 = prover.proveAddResolution([litid, self.root.id], antecedents, comment)

        antecedents = [up1, up0]
        comment = "Deletion of clause [%d] during existential quantfication" % self.root.id
        prover.proveDeleteResolution(self.validation, antecedents, comment)
        prover.qcollect(lit.variable.qlevel+1)

        comment = "Davis Putnam reduction of variable %s" % lname
        if root1 == self.manager.leaf1:
            newRoot = root1
            prover.proveDeleteDavisPutnam(litid, [shannon0], [], comment)
            validation = resolver.tautologyId
        elif root0 == self.manager.leaf1:
            newRoot = root0
            prover.proveDeleteDavisPutnam(litid, [shannon1], [], comment)
            validation = resolver.tautologyId
        else:
            comment = "Introduce intermediate disjunction of %s and %s" % (root1.label(), root0.label())
            distid = prover.proveAdd([root1.id, root0.id], comment = comment)
            comment = "Delete Shannon expansion clauses"
            prover.proveDeleteDavisPutnam(litid, [shannon1, shannon0], [distid], comment)
            newRoot, justifyOr = self.manager.applyOrJustify(root1, root0)
            antecedents = []
            if justifyOr == resolver.tautologyId:
                pass
            else:
                antecedents.append(justifyOr)
            if newRoot != self.manager.leaf1:
                comment = "Assert unit clause for disjunction %s (= %s | %s)" % (newRoot.label(), root1.label(), root0.label())
                validation = self.manager.prover.proveAdd([newRoot.id], comment)
                antecedents.append(validation)
            comment = "Remove intermediate disjunction"
            prover.proveDeleteResolution(distid, antecedents, comment)

        # Manager needs to be informed that quantification has completed
        self.manager.markQuantified(lit.variable)

        if newRoot == self.manager.leaf1:
            return None

        return Term(self.manager, newRoot, validation, mode = self.mode)

    # Dual proof.  Existential quantification
    def equantifyDual(self, lit, nlit, prover):
        lname = str(lit.variable)
        litid = lit.variable.id

        root1, downImplication1 = self.manager.applyRestrictDown(self.root, lit)
        root1, upImplication1 = self.manager.applyRestrictUp(self.root, lit)
        if root1 == self.manager.leaf1:
            # Down Implication will be tautology
            # Up Implication will be [-lit, self.root.id]
            # Shannon will be tautology
            up1 = upImplication1
            shannon1 = None
        elif root1 == self.manager.leaf0:
            # Down Implication will be [-lit, -self.root.id]
            # Up Implication will be tautology
            # Shannon will be [-lit]
            rclause = [-litid]
            comment = "Shannon Expansion: Add !%s" % (lname)
            antecedents = [downImplication1, self.validation]
            shannon1 = self.manager.prover.proveAddResolution(rclause, antecedents, comment)
            up1 = shannon1
        else:
            # Down Implication will be [-lit, -self.root.id, root1.id]
            # Up Implication will be   [-lit, -root1.id, self.root.id]
            # Shannon will be [-lit, root1.id]
            rclause = [-litid, root1.id]
            antecedents = [downImplication1, self.validation]
            comment = "Shannon Expansion: Add %s --> %s" % (lname, root1.label())
            shannon1 = self.manager.prover.proveAddResolution(rclause, antecedents, comment)
            antecedents = [shannon1, upImplication1]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up1 = prover.proveAddResolution([-litid, self.root.id], antecedents, comment)

        root0, downImplication0 = self.manager.applyRestrictDown(self.root, nlit)
        root0, upImplication0 = self.manager.applyRestrictUp(self.root, nlit)
        if root0 == self.manager.leaf1:
            # Down Implication will be tautology
            # Up Implication will be [lit, self.root.id]
            # Shannon will be tautology
            up0 = upImplication0
            shannon0 = None
        elif root0 == self.manager.leaf0:
            # Down Implication will be [lit, -self.root.id]
            # Up Implication will be tautology
            # Shannon will be [lit]
            rclause = [litid]
            antecedents = [downImplication0, self.validation]
            comment = "Shannon Expansion: Add %s" % (lname)
            shannon0 = self.manager.prover.proveAddResolution(rclause, antecedents, comment)
            up0 = shannon0
        else:
            # Down Implication will be [lit, -self.root.id, root1.id]
            # Up Implication will be   [lit, -root1.id, self.root.id]
            # Shannon will be [lit, root1.id]
            rclause = [litid, root0.id]
            antecedents = [downImplication0, self.validation]
            comment = "Shannon Expansion: Add -%s --> %s" % (lname, root0.label())
            shannon0 = self.manager.prover.proveAddResolution(rclause, antecedents, comment)
            antecedents = [shannon0, upImplication0]
            comment = "Resolve with upward implication for N%d" % self.root.id
            up0 = prover.proveAddResolution([litid, self.root.id], antecedents, comment)

        antecedents = [up1, up0]
        comment = "Deletion of clause [%d] during existential quantfication" % self.root.id
        prover.proveDeleteResolution(self.validation, antecedents, comment)
        prover.qcollect(lit.variable.qlevel+1)

        comment = "Davis Putnam reduction of variable %s" % lname
        if root1 == self.manager.leaf1:
            newRoot = root1
            prover.proveDeleteDavisPutnam(litid, [shannon0], [], comment)
            validation = resolver.tautologyId
        elif root0 == self.manager.leaf1:
            newRoot = root0
            prover.proveDeleteDavisPutnam(litid, [shannon1], [], comment)
            validation = resolver.tautologyId
        else:
            antecedents = [shannon1, shannon0]
            comment = "Introduce intermediate disjunction of %s and %s" % (root1.label(), root0.label())
            distid = prover.proveAddResolution([root1.id, root0.id], antecedents, comment)
            comment = "Delete Shannon expansion clauses"
            prover.proveDeleteDavisPutnam(litid, [shannon1, shannon0], [distid], comment)
            newRoot, justifyOr = self.manager.applyOrJustify(root1, root0)
            deleteAntecedents = []
            if justifyOr != resolver.tautologyId:
                deleteAntecedents.append(justifyOr)
            if newRoot != self.manager.leaf1:
                addAntecedents = []
                if root1 != self.manager.leaf0:
                    check1, justify1 = self.manager.justifyImply(root1, newRoot)
                    if justify1 != resolver.tautologyId:
                        addAntecedents.append(justify1)
                if root0 != self.manager.leaf0:
                    check0, justify0 = self.manager.justifyImply(root0, newRoot)
                    if justify0 != resolver.tautologyId:
                        addAntecedents.append(justify0)
                addAntecedents.append(distid)
                comment = "Add unit clause for disjunction %s (= %s | %s)" % (newRoot.label(), root1.label(), root0.label())
                validation = self.manager.prover.proveAddResolution([newRoot.id], addAntecedents, comment)
                deleteAntecedents.append(validation)
            comment = "Remove intermediate disjunction"
            prover.proveDeleteResolution(distid, deleteAntecedents, comment)

        # Manager needs to be informed that quantification has completed
        self.manager.markQuantified(lit.variable)

        if newRoot == self.manager.leaf1:
            return None

        return Term(self.manager, newRoot, validation, mode = self.mode)


class SolverException(Exception):

    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "Solver Exception: " + str(self.value)


class Solver:
    
    verbLevel = 1
    manager = None
    # How many terms have been generated
    termCount = 0
    # Mapping from input Ids to BDD representation of literal
    litMap = {}

    # Dictionary of Ids of terms remaining to be combined
    activeIds = {}
    # Have found formula to be True, False, or Unknown (None)
    outcome = None
    permuter = None
    prover = None
    writer = None
    # Mapping from quantifier levels to tuple (vars,isExistential)
    quantMap = {}

    def __init__(self, reader = None, prover = None, permuter = None, verbLevel = 1):
        self.verbLevel = verbLevel
        if prover is None:
            prover = proof.Prover(verbLevel = verbLevel)
        self.prover = prover
        self.writer = prover.writer
        #  mapping from each variable to (qlevel,isExistential)
        qmap = { v : (qlevel, isExistential) for (v, qlevel, isExistential) in reader.varList }
        # Construct quantifer level mapping
        self.quantMap = {}
        for (v,qlevel,isExistential) in reader.varList:
            if qlevel in self.quantMap:
                self.quantMap[qlevel][0].append(v)
            else:
                self.quantMap[qlevel] = ([v], isExistential)
        clauseCount = 0
        # Print input clauses
        for clause in reader.clauses:
            clauseCount += 1
            self.prover.createClause(clause, [], "Input clause %d" % clauseCount, isInput = True)

        if clauseCount == 0:
            self.writer.write("No clauses in CNF File\n")
            raise SolverException("Empty CNF file")

        self.prover.inputDone()

        self.manager = bdd.Manager(prover = self.prover, rootGenerator = self.rootGenerator,
                                   nextNodeId = reader.nvar+1, verbLevel = verbLevel)
        # Generate BDD representations of literals
        if permuter is None:
            # Default is identity permutation
            permuter = util.Permuter(list(range(1, reader.nvar+1)))
        self.permuter = permuter
        # Construct literal map
        self.litMap = {}
        for vlevel in range(1, reader.nvar+1):
            inputId = self.permuter.forward(vlevel)
            qlevel,isExistential = qmap[inputId]
            var = self.manager.newVariable(qlevel, name = "input-%d" % inputId, id = inputId, existential = isExistential)
            t = self.manager.literal(var, 1)
            self.litMap[ inputId] = t
            e = self.manager.literal(var, 0)
            self.litMap[-inputId] = e
        # Generate BDD representations of clauses
        self.termCount = 0
        self.activeIds = {}
        for clause in reader.clauses:
            self.termCount += 1
            litList = [self.litMap[v] for v in clause]
            if self.prover.mode == proof.ProverMode.noProof:
                root, validation = self.manager.constructClauseNoProof(self.termCount, litList)
            elif self.prover.mode == proof.ProverMode.refProof:
                root, validation = self.manager.constructClause(self.termCount, litList)
            elif self.prover.mode == proof.ProverMode.dualProof:
                root, validation = self.manager.constructClauseEquivalent(self.termCount, litList)
            else:
                root, validation = self.manager.constructClauseReverse(self.termCount, litList)
            term = Term(self.manager, root, validation, mode = prover.mode)
            self.activeIds[self.termCount] = term
        self.outcome = None

    # Determine whether term is constant.  Optionally matching specified value
    def termIsConstant(self, id):
        root = self.activeIds[id].root
        return root == self.manager.leaf1 or root == self.manager.leaf0

    # Extract two terms, conjunct them and insert new term
    def combineTerms(self, id1, id2):
        termA = self.activeIds[id1]
        termB = self.activeIds[id2]
        self.termCount += 1
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) & T%d (Node %s) --> T%d" % (id1, termA.root.label(), id2, termB.root.label(), self.termCount))
        newTerm = termA.combine(termB)
        comment = "T%d (Node %s) & T%d (Node %s) --> T%s (Node %s)" % (id1, termA.root.label(), id2, termB.root.label(),
                                                                      self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        if self.verbLevel >= 3:
            print("  T%d (Node N%d, QL=%d) support = %s" % (self.termCount, newTerm.root.id, newTerm.root.qlevel, self.manager.getSupportIds(newTerm.root)))

        if self.prover.mode in [proof.ProverMode.satProof, proof.ProverMode.dualProof]:
            if self.prover.mode == proof.ProverMode.satProof:
                if newTerm.root == termA.root:
                    newTerm.validation = termA.validation
                elif newTerm.root == termB.root:
                    newTerm.validation = termB.validation
                else:
                    comment = "Assertion of T%d (N%d)" % (self.termCount, newTerm.root.id)
                    newTerm.validation = self.prover.proveAdd([newTerm.root.id], comment)
            justificationA = [newTerm.validation]
            implA = self.manager.justifyImply(newTerm.root, termA.root)[1]
            if implA is not resolver.tautologyId:
                justificationA.append(implA)
            implB = self.manager.justifyImply(newTerm.root, termB.root)[1]
            justificationB = [newTerm.validation]
            if implB is not resolver.tautologyId:
                justificationB.append(implB)
            if newTerm.root != termA.root:
                comment = "Delete unit clauses for T%d" % id1
                self.prover.proveDeleteResolution(termA.validation, justificationA, comment)
            if newTerm.root != termB.root:
                comment = "Delete unit clauses for T%d" % id2
                self.prover.proveDeleteResolution(termB.validation, justificationB, comment)

        del self.activeIds[id1]
        del self.activeIds[id2]
        if self.prover.opened and self.verbLevel >= 3:
            self.writer.write(comment + '\n')
        self.activeIds[self.termCount] = newTerm
        if newTerm.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Conjunction: Formula FALSE\n")
            self.outcome = False
            self.manager.summarize()
            return -1
        return self.termCount

    # Used in refutation proofs, and when no proof
    def equantifyTerm(self, id, varList):
        term = self.activeIds[id]
        del self.activeIds[id]
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        vstring = " ".join(sorted([str(v) for v in varList]))
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) EQuant(%s) --> T%d" % (id, term.root.label(), vstring, self.termCount+1))
        newTerm = term.equantifySimple(clause, self.prover)
        if newTerm is None:
            comment = "T%d (Node %s) EQuant(%s) --> ONE" % (id, term.root.label(), vstring)
            return -1
        self.termCount += 1
        if self.prover.mode == proof.ProverMode.refProof:
            comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
            self.prover.comment(comment)
            if self.verbLevel >= 3:
                print(comment)
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC(generateClauses = self.prover.mode != proof.ProverMode.noProof)
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return self.termCount

    # Used in dual proofs
    def uquantifyTermDual(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        nlit = self.litMap[-var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) UQuant(%s)" % (id, term.root.label(), str(var)))
            print("  lit = %s,  nlit = %s" % (lit.label(), nlit.label()))
        newTerm = term.uquantifyDual(lit, nlit, self.prover)
        if newTerm is None:
            if self.verbLevel >= 1:
                self.writer.write("Universal Quantification: Formula FALSE\n")
            self.outcome = False
            self.manager.summarize()
            return -1
        self.termCount += 1
        self.activeIds[self.termCount] = newTerm
        comment = "T%d (Node %s) UQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, newTerm.root.label())
        self.prover.comment(comment)
        # This could be a good time for garbage collection
        self.manager.checkGC(generateClauses = False)
        return self.termCount

    # Used in refutation proofs
    def uquantifyTermRefutation(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) Restrict1(%s)" % (id, term.root.label(), str(var)))
        term1 = term.restrictRefutation(lit, self.prover)
        if term1 is not None:
            if term1.root == self.manager.leaf0:
                if self.verbLevel >= 1:
                    self.writer.write("Positive cofactor FALSE\n")
                self.outcome = False
                self.manager.summarize()
                return -1
            self.termCount += 1
            id1 = self.termCount
            self.activeIds[id1] = term1

        nlit = self.litMap[-var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) Restrict0(%s)" % (id, term.root.label(), str(var)))
        term0 = term.restrictRefutation(nlit, self.prover)
        if term0 is not None:
            if term0.root == self.manager.leaf0:
                if self.verbLevel >= 1:
                    self.writer.write("Negative cofactor FALSE\n")
                self.outcome = False
                self.manager.summarize()
                return -1
            self.termCount += 1
            id0 = self.termCount
            self.activeIds[id0] = term0

        if term1 is None and term0 is None:
            msg = "Got ONE for both cofactors of %s" % (term.root.label())
            raise SolverException(msg)

        if term1 is None:
            newId = id0
        elif term0 is None:
            newId = id1
        else:
            newId = self.combineTerms(id1, id0)
        # Manager needs to be informed that quantification has completed
        self.manager.markQuantified(lit.variable)
        # This could be a good time for garbage collection
        clauseList = self.manager.checkGC()
        if len(clauseList) > 0:
            self.prover.deleteClauses(clauseList)
        return newId

    # Used in satisfaction and dual proofs
    def equantifyTermDualSatisfaction(self, id, var):
        term = self.activeIds[id]
        del self.activeIds[id]
        lit = self.litMap[var]
        nlit = self.litMap[-var]
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) EQuant(%s)" % (id, term.root.label(), str(var)))
            print("  lit = %s,  nlit = %s" % (lit.label(), nlit.label()))
        if self.prover.mode == proof.ProverMode.satProof:
            newTerm = term.equantifySatisfaction(lit, nlit, self.prover)
        else:
            newTerm = term.equantifyDual(lit, nlit, self.prover)
        newId = -1
        if newTerm is None:
            if self.verbLevel >= 3:
                print("T%d (Node %s) EQuant(%s) --> ONE" % (id, term.root.label(), str(var)))
        else:
            self.termCount += 1
            comment = "T%d (Node %s) EQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), str(var), self.termCount, newTerm.root.label())
            self.prover.comment(comment)
            if self.verbLevel >= 3:
                print(comment)
            self.activeIds[self.termCount] = newTerm
            newId = self.termCount
        # This could be a good time for garbage collection
        self.manager.checkGC(generateClauses = False)
        return newId



    # Used in satisfaction proofs, and when no proof
    def uquantifyTerm(self, id, varList):
        term = self.activeIds[id]
        del self.activeIds[id]
        litList = [self.litMap[v] for v in varList]
        clause = self.manager.buildClause(litList)
        vstring = " ".join(sorted([str(v) for v in varList]))
        if self.verbLevel >= 3:
            print("Computing T%d (Node %s) UQuant(%s)" % (id, term.root.label(), vstring))
        newTerm = term.uquantify(clause, self.prover)
        if newTerm.root == self.manager.leaf0:
            if self.verbLevel >= 1:
                self.writer.write("Universal Quantification: Formula FALSE\n")
            self.outcome = False
            self.manager.summarize()
            return -1
        self.termCount += 1
        if self.prover.mode == proof.ProverMode.satProof:
            comment = "T%d (Node %s) UQuant(%s) --> T%d (Node %s)" % (id, term.root.label(), vstring, self.termCount, newTerm.root.label())
            newTerm.validation = self.manager.prover.proveAdd([newTerm.root.id], comment)
            antecedents = [newTerm.validation]
            check, implication = self.manager.justifyImply(newTerm.root, term.root)
            if not check:
                raise bdd.BddException("Implication failed %s -/-> %s" % (newTerm.root.label(), term.root.label()))
            if implication != resolver.tautologyId:
                antecedents += [implication]
            self.manager.prover.proveDeleteResolution(term.validation, antecedents, "Delete unit clause for T%d" % (id))
        self.activeIds[self.termCount] = newTerm
        # This could be a good time for garbage collection
        self.manager.checkGC(generateClauses = False)
        return self.termCount

    def processClusters(self, cfile):
        try:
            infile = open(cfile, 'r')
        except:
            self.writer.write("ERROR: Could not open cluster file '%s'\n" % cfile)
            return False
        clusterCount = 0
        clauseCount = 0
        for line in infile:
            line = trim(line)
            cnum = clusterCount + 1
            slist = line.split()
            try:
                clist = [int(s) for s in line.split()]
            except:
                self.writer.write("ERROR: Invalid clause number in cluster #%d\n" % cnum)
                return False
            if len(clist) == 0:
                continue
            id = clist[0]
            for nextId in clist[1:]:
                id = self.combineTerms(id, nextId)
                if id < 0:
                    self.writer.write("ERROR: Conjunction of input clauses for cluster #%d is unsatisfiable\n" % cnum)
                    return False
            clauseCount += len(clist)
            clusterCount += 1
            if self.verbLevel >= 3:
                self.writer.write("Combined %d clauses to form cluster #%d (T%d)\n" % (len(clist), cnum, id))
        if self.verbLevel >= 2:
            self.writer.write("Combined %d clauses to form %d clusters\n" % (clauseCount, clusterCount))
        infile.close()
        return True

    def placeInQuantBucket(self, buckets, id):
        if id < 0:
            return
        term = self.activeIds[id]
        level = term.root.qlevel-1
        if level > 0:
            buckets[level].append(id)

    # Bucket elimination based on quantification levels
    def runQuantBucket(self):
        levels = sorted(self.quantMap.keys(), key = lambda x : -x)
        buckets = { level : [] for level in levels }
        # Insert ids into lists according quantification level
        ids = sorted(self.activeIds.keys())
        for id in ids:
            if self.verbLevel >= 3:
                self.writer.write("Initial cluster #%d.  Size: %d\n" % (id, self.activeIds[id].size))
            self.placeInQuantBucket(buckets, id)
        for blevel in levels:
            vars, isExistential = self.quantMap[blevel]
            if self.verbLevel >= 3:
                self.writer.write("Quantifying %s level %d.  Vars = %s.  Bucket size = %d\n" %
                                  ("existential" if isExistential else "universal", blevel, str(vars), len(buckets[blevel])))
            if isExistential:
                # Conjunct all terms in bucket
                while len(buckets[blevel]) > 1:
                    id1 = buckets[blevel][0]
                    id2 = buckets[blevel][1]
                    buckets[blevel] = buckets[blevel][2:]
                    newId = self.combineTerms(id1, id2)
                    if newId < 0:
                        # Hit False case
                        return
                    self.placeInQuantBucket(buckets, newId)
                if blevel > 0 and len(buckets[blevel]) > 0:
                    id = buckets[blevel][0]
                    buckets[blevel] = []
                    if self.prover.mode in [proof.ProverMode.satProof, proof.ProverMode.dualProof]:
                        # Satisfaction
                        if len(vars) > 1:
                            raise SolverException("Must serialize existential quantifiers")
                        var = vars[0]
                        newId = self.equantifyTermDualSatisfaction(id, var)
                        if newId >= 0:
                            self.placeInQuantBucket(buckets, newId)
                    else:
                        # Refutation, or no proof
                        newId = self.equantifyTerm(id, vars)
                        self.placeInQuantBucket(buckets, newId)
            else:
                # Universal quantification
                if self.prover.mode in [proof.ProverMode.refProof, proof.ProverMode.dualProof]:
                    # Require vars to be single variable
                    if len(vars) > 1:
                        raise SolverException("Must serialize universal quantifiers")
                    v = vars[0]
                    for id in buckets[blevel]:
                        if self.prover.mode == proof.ProverMode.refProof:
                            newId = self.uquantifyTermRefutation(id, v)
                        else:
                            newId = self.uquantifyTermDual(id, v)
                        if newId < 0:
                            # Formula is False
                            return
                        self.placeInQuantBucket(buckets, newId)
                else:
                    # Satisfaction, or no proof
                    for id in buckets[blevel]:
                        newId = self.uquantifyTerm(id, vars)
                        if newId < 0:
                            # Formula is False
                            if self.verbLevel >= 0:
                                if self.prover.mode == proof.ProverMode.satProof:
                                    self.writer.write("ERROR: Formula is FALSE\n")
                                else:
                                    self.writer.write("Formula is FALSE\n")
                                return
                        self.placeInQuantBucket(buckets, newId)

        # Get here only haven't hit 0
        if self.prover.mode in [proof.ProverMode.satProof, proof.ProverMode.dualProof]:
            # Make sure all clauses cleared away
            self.prover.qcollect(1)

        if self.verbLevel >= 0:
            if self.prover.mode == proof.ProverMode.refProof:
                self.writer.write("ERROR: Formula is TRUE\n")
            else:
                self.writer.write("Formula is TRUE\n")
            self.manager.summarize()

    # Provide roots of active nodes to garbage collector
    def rootGenerator(self):
        rootList = [t.root for t in self.activeIds.values()]
        rootList += self.litMap.values()
        return rootList


      
def run(name, args):
    cnfName = None
    proofName = None
    permuter = None
    bpermuter = None
    doBucket = True
    verbLevel = 1
    logName = None
    mode = proof.ProverMode.noProof
    clusterFile = None
    stretchExistential = False
    stretchUniversal = False

    optlist, args = getopt.getopt(args, "hbB:c:m:l:v:i:o:m:p:L:")
    for (opt, val) in optlist:
        if opt == '-h':
            usage(name)
            return
        if opt == '-b':
            doBucket = True
        elif opt == '-B':
            bpermuter = util.readPermutation(val)
            if bpermuter is None:
                return
        elif opt == '-c':
            clusterFile = val
        elif opt == '-m':
            if val == 's':
                mode = proof.ProverMode.satProof
            elif val == 'r':
                mode = proof.ProverMode.refProof
            elif val == 'n':
                mode = proof.ProverMode.noProof
            elif val == 'd':
                mode = proof.ProverMode.dualProof
            else:
                sys.stderr.write("Unknown proof mode '%s'\n" % val)
                usage(name)
                return
        elif opt == '-l':
            for v in val:
                if v == 'e':
                    stretchExistential = True
                elif v == 'u':
                    stretchUniversal = True
                else:
                    sys.stderr.write("Unknown linearization option '%s'\n" % v)
                    usage(name)
                    return
        elif opt == '-v':
            verbLevel = int(val)
        elif opt == '-i':
            cnfName = val
        elif opt == '-o':
            proofName = val
        elif opt == '-p':
            permuter = util.readPermutation(val)
            if permuter is None:
                return
        elif opt == '-L':
            logName = val
        else:
            sys.stderr.write("Unknown option '%s'\n" % opt)
            usage(name)
            return

    # If no quantification permuter specified, follow variable ordering
    # This will cause the quantifications to be performed from the bottom of the BDDs upward
    if bpermuter is None:
        bpermuter = permuter

    writer = util.Logger(logName)

    try:
        prover = proof.Prover(proofName, writer = writer, verbLevel = verbLevel, mode = mode)
    except Exception as ex:
        writer.write("Couldn't create prover (%s)\n" % str(ex))
        return

    start = datetime.datetime.now()

    if mode in [proof.ProverMode.satProof, proof.ProverMode.dualProof]:
        stretchExistential = True
    if mode in [proof.ProverMode.refProof, proof.ProverMode.dualProof]:
        stretchUniversal = True

    try:
        reader = util.QcnfReader(cnfName, bpermuter, stretchExistential, stretchUniversal)
    except Exception as ex:
        writer.write("Aborted: %s\n" % str(ex))
        return
    
    if reader.stretched and mode != proof.ProverMode.noProof:
        prover.generateLevels(reader.varList)

    solver = Solver(reader, prover = prover, permuter = permuter, verbLevel = verbLevel)

    if clusterFile is None or solver.processClusters(clusterFile):
        solver.runQuantBucket()


    delta = datetime.datetime.now() - start
    seconds = delta.seconds + 1e-6 * delta.microseconds
    if verbLevel > 0:
        writer.write("Elapsed time for SAT: %.2f seconds\n" % seconds)
    if writer != sys.stderr:
        writer.close()
    
if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])

    

    
