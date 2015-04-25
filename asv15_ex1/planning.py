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


def get_transport_plan(nc, np, na, src, dst, start, t_max=30):
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
    c, c_tag = Consts('c c_tag', city)
    a, a_tag = Consts('a a_tag', airplane)

    cts = [Const('c{}'.format(idx), city) for idx in range(nc)]
    pks = [Const('p{}'.format(idx), package) for idx in range(np)]
    aps = [Const('a{}'.format(idx), airplane) for idx in range(na)]

    # Defining Predicates and Functions
    s = Solver()
    s.set(soft_timeout=900000)

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
    for idx in range(na):
        s.add(ForAll([t], move(aps[idx], t) == (loc(aps[idx], t) != loc(aps[idx], t + 1))))

    # Any plane at any time must be present at one and only city
    for idx in range(na):
        for jdx in range(nc):
            s.add(ForAll([t], And(loc(aps[idx], t) == c_tag, Or(loc(aps[idx], t) != cts[jdx], cts[jdx] == c_tag))))

    for idx in range(np):
        for jdx in range(na):
            for kdx in range(nc):
                s.add(ForAll([t],
                             Xor(
                                 And(
                                     Not(on(pks[idx], aps[jdx], t)),
                                     And(Exists([c_tag],
                                         at(pks[idx], c_tag, t),
                                         Implies(
                                             at(pks[idx], cts[kdx], t),
                                             cts[kdx] == c_tag)))),
                                 And(
                                     Not(at(pks[idx], cts[kdx], t)),
                                     And(
                                         on(pks[idx], a_tag, t),
                                         Implies(
                                             on(pks[idx], aps[jdx], t),
                                             aps[jdx] == a_tag))))))

    '''
    # move(airplane a, time t) := loc(a, t) != loc(a, t+1)
    s.add(ForAll([a], ForAll([t], move(a, t) == (loc(a, t) != loc(a, t + 1)))))

    # Any plane at any time must be present at one and only city
    s.add(ForAll([a], ForAll([t], Exists([c_tag],
                                         And(loc(a, t) == c_tag, ForAll([c], Or(loc(a, t) != c, c == c_tag)))))))

    # For any package at any time there exists one and only airplane/city where it is located on/at.
    s.add(ForAll([p], ForAll([t],
                             Xor(
                                 And(
                                     ForAll([a], Not(on(p, a, t))),
                                     Exists([c_tag], And(
                                         at(p, c_tag, t),
                                         ForAll([c], Implies(
                                             at(p, c, t),
                                             c == c_tag))))),
                                 And(
                                     ForAll([c], Not(at(p, c, t))),
                                     Exists([a_tag], And(
                                         on(p, a_tag, t),
                                         ForAll([a], Implies(
                                             on(p, a, t),
                                             a == a_tag)))))))))

    # Rule of load: Airplane must be at the same city as the package and not move. Package must load to airplane at t+1.
    s.add(ForAll([p], ForAll([a], ForAll([t],
                                         load(p, a, t) == And(Not(move(a, t)), at(p, loc(a, t), t), on(p, a, t+1))))))

    # Rule of unload: Airplane must not move and hold a package. Package must unload to airplane's location at t+1.
    s.add(ForAll([p], ForAll([a], ForAll([t],
                                         unload(p, a, t) == And(Not(move(a, t)), on(p, a, t), at(p, loc(a, t), t+1))))))

    # Rule of Movement: Any plane at any time must either move or load/unload any number of packages (but not both)
    s.add(ForAll([a], ForAll([t], Xor(move(a, t), Exists([p], Or(load(p, a, t), unload(p, a, t)))))))
    '''

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
