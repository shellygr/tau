"""
Transport planning problem exercise.
"""
from z3 import *
import pprint

example_problem = dict(
    nc=4,
    np=3,
    na=2,
    src=[2, 1, 0],
    dst=[0, 3, 2],
    start=[3, 3]
)

example_solution = dict(
    city_packages=[[[2], [1], [0], []],
                   [[2], [1], [0], []],
                   [[2], [], [], []],
                   [[2], [], [], []],
                   [[0], [], [], []],
                   [[0], [], [], []],
                   [[0], [], [2], [1]]],
    city_airplanes=[[[], [], [], [0, 1]],
                    [[], [0], [1], []],
                    [[], [0], [1], []],
                    [[0, 1], [], [], []],
                    [[1], [0], [], []],
                    [[], [], [1], [0]],
                    [[], [], [1], [0]]],
    airplane_packages=[[[], []],
                       [[], []],
                       [[1], [0]],
                       [[1], [0]],
                       [[1], [2]],
                       [[1], [2]],
                       [[], []]],
)


def print_problem(nc, np, na, src, dst, start):
    print "There are {} cities".format(nc)
    print "There are {} packages".format(np)
    print "There are {} airplanes".format(na)
    print

    assert len(src) == len(dst) == np
    assert len(start) == na

    for i in range(np):
        print "Package P{} starts at city C{} and should be transported to city C{}".format(
            i, src[i], dst[i])
    print

    for i in range(na):
        print "Airplane A{} starts at city C{}".format(i, start[i])
    print


def print_plan(city_packages, city_airplanes, airplane_packages):
    assert len(city_packages) == len(city_airplanes)
    assert len(city_packages) == len(airplane_packages)

    times = range(len(city_packages))
    nc = len(city_packages[0])
    print "plan:"

    def print_row(row):
        print ' | '.join([''] + ['{:^20}'.format(x) for x in row] + [''])

    def format_airplane(i, t):
        return 'A{}[{}]'.format(
            i,
            ','.join(['P{}'.format(j) for j in airplane_packages[t][i]])
        )

    print_row(['time'] + ['C{}'.format(i) for i in range(nc)])
    for t in times:
        print_row([t] + [
            ','.join(['P{}'.format(j) for j in city_packages[t][i]] +
                     [format_airplane(j, t) for j in city_airplanes[t][i]])
            for i in range(nc)
        ])
    print


def get_transport_plan(nc, np, na, src, dst, start):
    # Declaring sorts
    airplane = DeclareSort('A')
    package = DeclareSort('P')
    city = DeclareSort('C')
    boolean = BoolSort()
    time = IntSort()

    # Declaring functions, predicates
    loc = Function('loc', airplane, time, city)
    at = Function('at', package, city, time, boolean)
    on = Function('on', package, airplane, time, boolean)
    move = Function('move', airplane, time, boolean)
    load = Function('load', package, airplane, time, boolean)
    unload = Function('unload', package, airplane, time, boolean)

    # Declaring consts
    p = Const('p', package)
    cts = [Const('c{}'.format(idx), city) for idx in range(nc)]
    pks = [Const('p{}'.format(idx), package) for idx in range(np)]
    aps = [Const('a{}'.format(idx), airplane) for idx in range(na)]

    a, a_tag = Consts('a a_tag', airplane)
    c, c_tag = Consts('c c_tag', city)
    t = Const('t', time)

    # Model
    m = None

    # TODO: Calculate
    t_max = 3
    while m is None:

        # Defining Predicates and Functions
        s = Solver()
        s.set(soft_timeout=60000)

        # s.add(ForAll([t], And(t >= 0, t <= t_max)))

        # All packages start at their source cities
        for idx in range(np):
            s.add(at(pks[idx], cts[src[idx]], 0))

        # All packages end at their destination cities
        for idx in range(np):
            s.add(at(pks[idx], cts[dst[idx]], t_max))

        # All airplanes must begin in their source cities
        for idx in range(na):
            s.add(loc(aps[idx], 0) == cts[start[idx]])

        # At t==0, no package is loaded on no airplane!
        s.add(ForAll([p], ForAll([a], Not(on(p, a, 0)))))

        for idx in range(na):
            for jdx in range(idx):
                s.add(aps[idx] != aps[jdx])

        for idx in range(nc):
            for jdx in range(idx):
                s.add(cts[idx] != cts[jdx])

        for idx in range(np):
            for jdx in range(idx):
                s.add(pks[idx] != pks[jdx])

        # move(airplane a, time t) := loc(a, t) != loc(a, t+1)
        s.add(ForAll([a], ForAll([t], move(a, t) == (loc(a, t) != loc(a, t + 1)))))

        # For any package at any time there exists one and only airplane/city where it is located on/at.
        for idx in range(np):
            for t in range(t_max):
                s.add(Xor(
                    And(
                        ForAll([a], Not(on(pks[idx], a, t))),
                        Exists([c_tag], And(
                            at(pks[idx], c_tag, t),
                            ForAll([c], Or(Not(at(pks[idx], c, t)), c == c_tag))))),
                    And(
                        ForAll([c], Not(at(pks[idx], c, t))),
                        Exists([a_tag], And(
                            on(pks[idx], a_tag, t),
                            ForAll([a], Or(Not(on(pks[idx], a, t)), a == a_tag)))))))

        # Any plane at any time must be present at one and only city
        for idx in range(na):
            for t in range(t_max):
                s.add(Exists([c_tag], And(loc(aps[idx], t) == c_tag,
                                          ForAll([c], Or(loc(aps[idx], t) != c, c == c_tag)))))

        # Rule of load: Airplane must be at the same city as the package and not move. Package must load to airplane at t+1.
        for idx in range(np):
            for jdx in range(na):
                for t in range(t_max):
                    s.add(load(pks[idx], aps[jdx], t) ==
                          And(Not(move(aps[jdx], t)), at(pks[idx], loc(aps[jdx], t), t), on(pks[idx], aps[jdx], t+1)))

        # Rule of unload: Airplane must not move and hold a package. Package must unload to airplane's location at t+1.
        for idx in range(np):
            for jdx in range(na):
                for t in range(t_max):
                    s.add(unload(pks[idx], aps[jdx], t) ==
                          And(Not(move(aps[jdx], t)), on(pks[idx], aps[jdx], t), at(pks[idx], loc(aps[jdx], t), t + 1)))

        # Rule of Movement: Any plane at any time must either move or load/unload any number of packages (but not both)
        for idx in range(na):
            for t in range(t_max):
                s.add(Xor(move(aps[idx], t),
                          Or(Exists([p], load(p, aps[idx], t)), Exists([p], unload(p, aps[idx], t)))))

        res = s.check()
        if res == sat:
            print "SAT\n"
            m = s.model()

        elif res == unknown:
            print "Got unknown from Z3 for t_max = %d, trying a larger t_max\n" % (t_max)
        else:
            print "UNSAT for t_max = %d, trying a larger t_max\n" % (t_max)
        t_max += 1

    city_packages = []
    city_airplanes = []
    airplane_packages = []

    for t in range(t_max + 1):
        city_packages.insert(t, [])
        city_airplanes.insert(t, [])
        airplane_packages.insert(t, [])
        for nc_idx in range(nc):
            city_packages[t].insert(nc_idx, [])
            city_airplanes[t].insert(nc_idx, [])

            # Build city_packages
            for np_idx in range(np):
                if is_true(m.eval(at(pks[np_idx], cts[nc_idx], t))):
                    print "Package %d in city %d in time %d" % (np_idx, nc_idx, t)
                    city_packages[t][nc_idx].append(np_idx)

            # Build city_airplanes
            for na_idx in range(na):
                airplane_packages[t].insert(na_idx, [])

                if is_true(m.eval(loc(aps[na_idx], t) == cts[nc_idx])):
                    print "Airplane %d at city %d in time %d" % (na_idx, nc_idx, t)
                    city_airplanes[t][nc_idx].append(na_idx)

        # Build airplane_packages
        for na_idx in range(na):
            for np_idx in range(np):
                if is_true(m.eval(on(pks[np_idx], aps[na_idx], t))):
                    print "Package %d on airplane %d in time %d" % (np_idx, na_idx, t)
                    airplane_packages[t][na_idx].append(np_idx)

    #pprint.pprint (city_packages)
    #pprint.pprint (airplane_packages)
    return city_packages, city_airplanes, airplane_packages


if __name__ == '__main__':
    print_problem(**example_problem)

    city_packages, city_airplanes, airplane_packages = get_transport_plan(**example_problem)
    #get_transport_plan(**example_problem)

    print_plan(city_packages, city_airplanes, airplane_packages)
    #print_plan(**example_solution)

    #
    # Uncomment after you implement get_transport_plan:
    #
    # city_packages, city_airplanes, airplane_packages = get_transport_plan(**example_problem)
    # print
    # print_plan(city_packages, city_airplanes, airplane_packages)

    #
    # Add more tests here...
    #