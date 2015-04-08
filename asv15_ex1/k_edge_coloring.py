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

            # Get the list of all edges covering this node
            relevant_edges = filter(lambda (v1, v2): v1 == v or v2 == v, E)

            # Only create rules when there is more than a single edge covering this node
            if len(relevant_edges) > 1:
                # What we want here is a boolean formula that would allow at most one edge of the
                # same color within the list of all edges covering the current node.
                # For translating such constraint to boolean form, we would add a constraint that
                # each pair of edges within the list does not have the same color. For example,
                # if E1, E2 and E3 all have a common node V, the constrains would be:
                # (Or(Not(E1, c), Not(E2, c)), (Or(Not(E1, c), Not(E3, c)), (Or(Not(E2, c), Not(E3, c))
                for v1, v2 in relevant_edges:
                    # TODO: This naive solution probably creates some duplicates, can we cut them down?
                    for v1_tag, v2_tag in relevant_edges:

                        # Do not add constraint for the same edge
                        if (v1, v2) == (v1_tag, v2_tag):
                            continue

                        s.add(Or(Not(variables[(v1, v2)][c]),
                                 Not(variables[(v1_tag, v2_tag)][c])))

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

    # Helper variable - for finding the core
    edge_variables = [Bool(str(i)) for i in range(len(E))]
    # every adjacent edge has different color
    for v in V:
        for c in colors:

            # Get the list of all edges covering this node
            relevant_edges = filter(lambda (v1, v2): v1 == v or v2 == v, E)

            # Only create rules when there is more than a single edge covering this node
            if len(relevant_edges) > 1:
                # What we want here is a boolean formula that would allow at most one edge of the
                # same color within the list of all edges covering the current node.
                # For translating such constraint to boolean form, we would add a constraint that
                # each pair of edges within the list does not have the same color. For example,
                # if E1, E2 and E3 all have a common node V, the constrains would be:
                # (Or(Not(E1, c), Not(E2, c)), (Or(Not(E1, c), Not(E3, c)), (Or(Not(E2, c), Not(E3, c))
                for v1, v2 in relevant_edges:
                    # TODO: This naive solution probably creates some duplicates, can we cut them down?
                    for v1_tag, v2_tag in relevant_edges:

                        # Do not add constraint for the same edge
                        if (v1, v2) == (v1_tag, v2_tag):
                            continue

                        cur_edge = -1
                        for i in range(len(E)):
                            if E[i] == (v1, v2):
                                cur_edge = i


                        s.add(Or(Not(variables[(v1, v2)][c]),
                                 Not(variables[(v1_tag, v2_tag)][c]),
                                 Not(edge_variables[cur_edge])))

    print "Solver is:"
    print s
    print

    print "Checking SAT"
    res = s.check(edge_variables)
    if res == unsat:
        print "UNSAT, No K coloring"
        core = s.unsat_core()
        print "UNSAT core:", core
        coloring = {}
        for x in core:
            i = int(str(x))
            coloring[E[i]] = 1
        return coloring
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


def test_graph(V, E, k, graph_name):
    c = get_k_edge_coloring_core(k, V, E)
    if c is not None:
        draw_graph(V, E, c, '{}_{}_colors'.format(graph_name, k))
    else:
        print 'No coloring found for graph ' + graph_name + ' with ' + str(k) + ' colors'


if __name__ == '__main__':
    # Impossible
    test_graph(simple_V, simple_E, 2, 'simple')
    # Solvable
    test_graph(simple_V, simple_E, 3, 'simple')
    # Impossible
    test_graph(Petersen_V, Petersen_E, 3, 'petersen')
    # Solvable
    test_graph(Petersen_V, Petersen_E, 4, 'petersen')
    # TODO: More tests. Is the core functionality working?

    pass
