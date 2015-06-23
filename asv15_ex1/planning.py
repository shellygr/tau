"""
Transport planning problem exercise.
"""
from z3 import *


# This is the simplest possible problem - one package, two cities,
# one airplane. The airplane and the package starts at the same city
simple_problem_1 = dict(
    nc=2,
    np=1,
    na=1,
    src=[0],
    dst=[1],
    start=[0]
)

# Simple problem - one package, two cities, one airplane.
# The airplane starts in a different city so this needs an extra step
simple_problem_2 = dict(
    nc=2,
    np=1,
    na=1,
    src=[0],
    dst=[1],
    start=[1]
)

# Simple problem - one package, two cities, two airplanes.
# The airplane starts in a different city so this needs an extra step
simple_problem_3 = dict(
    nc=2,
    np=1,
    na=2,
    src=[0],
    dst=[1],
    start=[1, 1]
)

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
    # move = Function('move', airplane, time, boolean)

    # Declaring consts
    cts = [Const('c{}'.format(idx), city) for idx in range(nc)]
    pks = [Const('p{}'.format(idx), package) for idx in range(np)]
    aps = [Const('a{}'.format(idx), airplane) for idx in range(na)]

    t = Const('t', time)

    # Model
    m = None

    t_max = 1
    while m is None:

        # Defining Predicates and Functions
        s = Solver()
        s.set(soft_timeout=60000)

        # Start and finish restrictions for packages
        for np_idx in range(np):
            # All packages start at their source cities
            s.add(at(pks[np_idx], cts[src[np_idx]], 0))

            # All packages end at their destination cities
            s.add(at(pks[np_idx], cts[dst[np_idx]], t_max))

            # Packages are not loaded on start and on end
            for na_idx in range(na):
                s.add(Not(on(pks[np_idx], aps[na_idx], 0)))
                s.add(Not(on(pks[np_idx], aps[na_idx], t_max)))

        # Start and finish restrictions for packages
        for na_idx in range(na):
            # All airplanes start at their source cities
            s.add(loc(aps[na_idx], 0) == cts[start[na_idx]])

        # move(airplane a, time t) := loc(a, t) != loc(a, t+1) # leads to getting unknown
        # for na_idx in range(na): s.add(ForAll(t, move(aps[na_idx], t) == (loc(aps[na_idx], t) != loc(aps[na_idx], t + 1))))

        # Package restrictions to ensure package can only exist at one place in a time
        for t_idx in range(t_max + 1):
            for np_idx in range(np):

                # For each two cities, make sure the package only exists in one city at a time
                for nc_kdx in range(nc):
                    for nc_idx2 in range(nc_kdx + 1, nc):
                        s.add(Not(And(at(pks[np_idx], cts[nc_kdx], t_idx), at(pks[np_idx], cts[nc_idx2], t_idx))))

                    # Now make sure package cannot be both in a city and on an airplane at the same time
                    for na_idx in range(na):
                        s.add(Not(And(at(pks[np_idx], cts[nc_kdx], t_idx), on(pks[np_idx], aps[na_idx], t_idx))))

                # For each two airplanes, make sure the package is only loaded on one airplane at a time
                for na_idx1 in range(nc):
                    for na_idx2 in range(na_idx1 + 1, na):
                        s.add(Not(And(on(pks[np_idx], aps[na_idx1], t_idx), on(pks[np_idx], aps[na_idx2], t_idx))))

        # Package movement restrictions: package can only stay in the same place, or move city after
        # it was on an airplane
        for np_idx in range(np):
            for nc_idx in range(nc):
                # First direction
                s.add(ForAll(t, Or(Not(at(pks[np_idx], cts[nc_idx], t + 1)),
                                   Or(
                                       Or([And(on(pks[np_idx], ap, t),
                                               loc(ap, t) == cts[nc_idx],
                                               loc(ap, t + 1) == cts[nc_idx])
                                           for ap in aps]), at(pks[np_idx], cts[nc_idx], t)))))

                # Second direction
                s.add(ForAll(t, Or(Not(at(pks[np_idx], cts[nc_idx], t)),
                                   Or(
                                       Or([And(on(pks[np_idx], ap, t + 1),
                                               loc(ap, t + 1) == cts[nc_idx],
                                               loc(ap, t) == cts[nc_idx])
                                           for ap in aps]), at(pks[np_idx], cts[nc_idx], t + 1)))))

        # Load and unload restrictions
        for np_idx in range(np):
            for na_idx in range(na):
                # Rule of load: Airplane must be at the same city as the package and not move.
                # Package must load to airplane at t+1.
                s.add(ForAll(t, Implies(on(pks[np_idx], aps[na_idx], t + 1),
                                        Or(on(pks[np_idx], aps[na_idx], t),
                                           And(at(pks[np_idx], loc(aps[na_idx], t), t),
                                               loc(aps[na_idx], t) == loc(aps[na_idx], t + 1))))))

                # Rule of unload: Airplane must not move and hold a package.
                # Package must unload to airplane's location at t+1.
                s.add(ForAll(t, Implies(on(pks[np_idx], aps[na_idx], t),
                                        Or(on(pks[np_idx], aps[na_idx], t + 1),
                                           And(loc(aps[na_idx], t) == loc(aps[na_idx], t + 1),
                                               at(pks[np_idx], loc(aps[na_idx], t), t + 1))))))

        res = s.check()
        if res == sat:
            print "SAT in t_max = %d\n" % t_max
            m = s.model()
        elif res == unknown:
            print "Got unknown from Z3 for t_max = %d, trying a larger t_max\n" % (t_max)
        else:
            print "UNSAT for t_max = %d, trying a larger t_max\n" % (t_max)
        t_max += 1

    # Now, extract the plan from the model
    city_packages = []
    city_airplanes = []
    airplane_packages = []

    for t_idx in range(t_max):
        city_packages.insert(t_idx, [])
        city_airplanes.insert(t_idx, [])
        airplane_packages.insert(t_idx, [])
        for nc_idx in range(nc):
            city_packages[t_idx].insert(nc_idx, [])
            city_airplanes[t_idx].insert(nc_idx, [])

            # Build city_packages
            for np_idx in range(np):
                if is_true(m.eval(at(pks[np_idx], cts[nc_idx], t_idx))):
                    #print "Package %d in city %d in time %d" % (np_idx, nc_idx, t_idx)
                    city_packages[t_idx][nc_idx].append(np_idx)

            # Build city_airplanes
            for na_idx in range(na):
                if is_true(m.eval(loc(aps[na_idx], t_idx) == cts[nc_idx])):
                    #print "Airplane %d at city %d in time %d" % (na_idx, nc_idx, t_idx)
                    city_airplanes[t_idx][nc_idx].append(na_idx)

        # Build airplane_packages
        for na_idx in range(na):
            airplane_packages[t_idx].insert(na_idx, [])
            for np_idx in range(np):
                if is_true(m.eval(on(pks[np_idx], aps[na_idx], t_idx))):
                    #print "Package %d on airplane %d in time %d" % (np_idx, na_idx, t_idx)
                    airplane_packages[t_idx][na_idx].append(np_idx)

    return city_packages, city_airplanes, airplane_packages


if __name__ == '__main__':
    problem = example_problem

    print_problem(**problem)

    city_packages, city_airplanes, airplane_packages = get_transport_plan(**problem)
    # get_transport_plan(**example_problem)
    print_plan(city_packages, city_airplanes, airplane_packages)
    # print_plan(**example_solution)

    #
    # Uncomment after you implement get_transport_plan:
    #
    # city_packages, city_airplanes, airplane_packages = get_transport_plan(**example_problem)
    # print
    # print_plan(city_packages, city_airplanes, airplane_packages)

    #
    # Add more tests here...
    #