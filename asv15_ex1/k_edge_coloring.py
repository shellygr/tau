"""
k-edge-coloring exercise.
"""
from z3 import *

Petersen_V = range(10)
Petersen_E = [
    (0 , 1),
    (1 , 2),
    (2 , 3),
    (3 , 4),
    (4 , 0),

    (0 , 5),
    (1 , 6),
    (2 , 7),
    (3 , 8),
    (4 , 9),

    (5 , 7),
    (7 , 9),
    (9 , 6),
    (6 , 8),
    (8 , 5),
 ]

simple_V = [0, 1, 2, 3]
simple_E = [
    (0, 1),
    (1, 2),
    (2, 0),
    (2, 3),
]


def get_k_edge_coloring(k, V, E):
    assert V == range(len(V))
    colors = range(k)

    variables = {}
    for v1, v2 in E:
        variables[(v1, v2)] = [Bool('v_{}_v_{}_color_{}'.format(v1, v2, c)) for c in colors]

    s = Solver()

    # every edge has at least one color
    for v1, v2 in E:
        s.add(Or([variables[(v1, v2)][c] for c in colors]))

    # every edge has at most one color
    for v1, v2 in E:
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                s.add(Or(Not(variables[(v1, v2)][c1]),
                         Not(variables[(v1, v2)][c2])))

    # every adjacent edge has different color
    for v in V:
        for c in colors:
            conds = []
            relevant_edges = filter(lambda (v1, v2): v1 == v or v2 == v, E)
            #if len(relevant_edges) < 2:
            #    continue
            if len(relevant_edges) > 1:
                s.add(Or([Not(variables[(v1, v2)][c]) for v1, v2 in relevant_edges]))

            #for v1, v2 in relevant_edges:
            #    print "Adding edge " + str((v1, v2)) + " with color " + str(c)
            #    conds.append(Not(variables[(v1, v2)][c]))
            #s.add(Or(conds))
    #for v1, v2 in E:
    #    for c in colors:
    #        s.add(Or(Not(variables[v1][c]),
    #                 Not(variables[v2][c])))

    print "Solver is:"
    print s
    print

    print "Checking SAT"
    res = s.check()
    if res == unsat:
        print "UNSAT, No K coloring"
        return None
    elif res == unknown:
        print "Unknown"
        return None
    else:
        assert res == sat
        print "SAT, Found K coloring"
        m = s.model()
        coloring = dict()
        for v1, v2 in E:
            for c in colors:
                if is_true(m[variables[(v1, v2)][c]]):
                    coloring[(v1, v2)] = c
                    break
        return coloring


def get_k_edge_coloring_core(k, V, E):
    #
    # Your solution here...
    #
    pass


def draw_graph(V, E, coloring={}, filename='graph', engine='circo', directed=False):
    try:
        from graphviz import Graph, Digraph
    except ImportError:
        print "You don't have graphviz python interface installed. Sorry."
        return

    COLORS = ['blue', 'red', 'green', 'pink', 'yellow']
    if directed:
        dot = Digraph(engine=engine)
    else:
        dot = Graph(engine=engine)
    for v in V:
        if v in coloring:
            dot.node(str(v), style="filled", fillcolor=COLORS[coloring[v]])
        else:
            dot.node(str(v))
    for v1, v2 in E:
        if (v1, v2) in coloring:
            dot.edge(str(v1), str(v2), color=COLORS[coloring[(v1, v2)]])
        else:
            dot.edge(str(v1), str(v2))
    dot.render(filename, cleanup=True, view=True)


if __name__ == '__main__':
    c = get_k_edge_coloring(3, simple_V, simple_E)
    if c != None:
        draw_graph(simple_V, simple_E, c, 'simple')
    else:
        print "No coloring"

    #c = get_k_edge_coloring(3, Petersen_V, Petersen_E)
    #draw_graph(Petersen_V, Petersen_E, c, 'Petersen')

    pass
