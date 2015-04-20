"""
Transport planning problem exercise.
"""
from z3 import *


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
    t = Const('t', time)
    p = Const('p', package)
    cts = [Const('c{}'.format(idx), city) for idx in range(nc)]
    pks = [Const('p{}'.format(idx), package) for idx in range(np)]
    aps = [Const('a{}'.format(idx), airplane) for idx in range(na)]

    a, a_tag = Consts('a a_tag', airplane)
    c, c_tag = Consts('c c_tag', city)

    # Defining Predicates and Functions
    s = Solver()
    s.set(soft_timeout=5000)

    t_max = 3
    s.add(And(t >= 0, t <= t_max))

    # All packages start at their source cities
    for idx in range(np):
        s.add(at(pks[idx], cts[src[idx]], 0))

    # All packages end at their destination cities
    for idx in range(np):
        s.add(at(pks[idx], cts[dst[idx]], t_max))

    # All airplanes must begin in their source cities
    for idx in range(na):
        s.add(loc(aps[idx], 0) == cts[start[idx]])

    # move(airplane a, time t) := loc(a, t) != loc(a, t+1)
    s.add(ForAll([a], ForAll([t],
          And(
              Implies(move(a, t), loc(a, t) == loc(a, t + 1)),
              Implies(loc(a, t) == loc(a, t + 1), move(a, t))))))

    # At any time for any package there exists one and only airplane/city where it is located on/at.
    s.add(ForAll([t], ForAll([p],
                             Or(
                                 And(
                                     ForAll([a], Not(on(p, a, t))),
                                     Exists([c_tag], And(
                                         at(p, c_tag, t),
                                         ForAll([c], Implies(at(p, c, t), c == c_tag))))),
                                 And(
                                     ForAll([c], Not(at(p, c, t))),
                                     Exists([a_tag], And(
                                         on(p, a_tag, t),
                                         ForAll([a], Implies(on(p, a, t), a == a_tag)))))))))

    # Any plane at any time must be present at one and only city
    s.add(ForAll([a], ForAll([t], Exists([c_tag],
                                         And(
                                             loc(a, t) == c_tag,
                                             ForAll([c], Implies(loc(a, t) == c, c == c_tag)))))))

    # Rule of load: Airplane must be at the same city as the package and not move. Package must load to airplane at t+1.
    s.add(ForAll([p], ForAll([a], ForAll([t],
                                         And(
                                             Implies(
                                                 load(p, a, t),
                                                 And(Not(move(a, t)), at(p, loc(a, t), t), on(p, a, t+1))),
                                             Implies(
                                                 And(Not(move(a, t)), at(p, loc(a, t), t), on(p, a, t+1)),
                                                 load(p, a, t)))))))

    # Rule of unload: Airplane must not move and hold a package. Package must unload to airplane's location at t+1.
    s.add(ForAll([p], ForAll([a], ForAll([t],
                                         And(
                                             Implies(
                                                 unload(p, a, t),
                                                 And(Not(move(a, t)),
                                                     on(p, a, t),
                                                     at(p, loc(a, t), t+1))),
                                             Implies(
                                                 And(Not(move(a, t)),
                                                     on(p, a, t),
                                                     at(p, loc(a, t), t+1)),
                                                 unload(p, a, t)))))))

    # Rule of Movement: Any plane at any time must either move or load/unload any number of packages (but not both)
    s.add(ForAll([a], ForAll([t], Xor(move(a, t), Exists([p], Or(load(p, a, t), unload(p, a, t)))))))


"""
    # All packages start at their source cities
    s.add(a1 != a2)
    s.add(p1 != p2 != p3)
    s.add(c1 != c2 != c3 != c4)
    s.add(at(p1, c1, 0))
    s.add(at(p2, c4, 0))
    s.add(at(p3, c3, 0))

    # There exists a time where all packages end at their destination cities and it is minimal
    s.add(at(p1, c3, t))
    s.add(at(p2, c2, t))
    s.add(at(p3, c1, t))
    s.add(Implies(Exists[t0], And(at(p1, c3, t0), at(p2, c2, t0), at(p3, c1, t0)), t0 >= t))  # assert FV[f] == t

    res = s.check()
    if res == sat:
        print "SAT\n"
        m = s.model()
    elif res == unknown:
        print "Got unknown"
    else:
        print "UNSAT\n"
    city_packages = []
    city_airplanes = []
    airplane_packages = []
    return city_packages, city_airplanes, airplane_packages
"""

if __name__ == '__main__':
    print_problem(**example_problem)

    #city_packages, city_airplanes, airplane_packages = get_transport_plan(**example_problem)
    get_transport_plan(**example_problem)

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
