#!/usr/bin/python

# Construct CNF representation of attempting to color Mycielski graph M_k with k-1 colors
import sys
import writer

# Undirected graphs
class Graph:
    name = None
    vertexCount = 2
    # List of edges.  Each represented by pair (i,j) s.t. i < j
    edgeList = [(1, 2)]


    def __init__(self, n, name = None):
        self.vertexCount = n
        self.edgeList = []

    def addEdge(self, pair):
        i,j = pair
        if i > j:
            i,j = j,i
        self.edgeList.append((i,j))

    # Generate SAT problem
    def colorCnf(self, k, froot, verbose = False):
        vars = k * self.vertexCount
        cwriter = writer.CnfWriter(vars, froot, verbose)
        title = "Graph:" if self.name is None else "Graph %s:" % self.name
        cwriter.doComment("%s %d nodes. %d edges. %d colors" % (title, self.vertexCount, len(self.edgeList), k))
        cwriter.doComment("At least one constraint for variables associated with each variable")
        for v in range(1,self.vertexCount+1):
            start = (v-1)*k + 1
            lits = [i + start for i in range(k)]
            cwriter.doClause(lits)
        cwriter.doComment("At most one constraint for corresponding pair of color variables for each edge")
        for e in self.edgeList:
            (s,t) = e
            starts = (s-1)*k + 1
            startt = (t-1)*k + 1
            for i in range(k):
                cwriter.doClause([-(starts+i), -(startt+i)])
        cwriter.finish()

class Mycielski:

    order = 1
    graph = None

    def __init__(self, k):
        self.order = k
        if k == 1:
            self.graph = Graph(1, name="Mycielski-1")
        elif k == 2:
            self.graph = Graph(2, name="Mycielski-2")
            self.graph.addEdge((1,2))
        else:
            gm1 = Mycielski(k-1)
            n = gm1.graph.vertexCount
            self.graph = Graph(2*n + 1, name="Mycielski-%d" % k)
            for e in gm1.graph.edgeList:
                vi,vj = e
                ui = vi+n
                uj = vj+n
                self.graph.addEdge((vi,vj))
                self.graph.addEdge((vi,uj))
                self.graph.addEdge((vj,ui))
            # Add new edges
            lastu = 2*n+1
            for u in range(n+1, 2*n+1):
                self.graph.addEdge((u,lastu))

    def colorCnf(self, froot):
        self.graph.colorCnf(self.order-1, froot, verbose = False)

def run(name, args):
    if len(args) == 0 or args[0] == '-h':
        print("Usage: %s k" % name)
        return
    k = int(args[0])
    froot = "mycielski-%d" % k
    m = Mycielski(k)
    m.colorCnf(froot)

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
