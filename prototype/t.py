import bdd

m = bdd.Manager()

avar = m.newVariable("a")
bvar = m.newVariable("b")
cvar = m.newVariable("c")
aplus = m.literal(avar, 1)
aminus = m.literal(avar, 0)
bplus = m.literal(bvar, 1)
bminus = m.literal(bvar, 0)
cplus = m.literal(cvar, 1)
cminus = m.literal(cvar, 0)

Ca0b0 = m.clause([aminus, bminus])
Ca0b1 = m.clause([aminus, bplus])
Ca1b0 = m.clause([aplus, bminus])
Ca1b1 = m.clause([aplus, bplus])

Ca0b0c0 = m.clause([aminus, bminus, cminus])
Ca1b1c1 = m.clause([aplus, bplus, cplus])

Aabc = m.reduceList([aplus, bplus, cplus], m.applyAnd, m.leaf1)
Oabc = m.reduceList([aplus, bplus, cplus], m.applyOr, m.leaf0)
Xabc = m.reduceList([aplus, bplus, cplus], m.applyXor, m.leaf0)
