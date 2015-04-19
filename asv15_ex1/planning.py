"""
Transport planning problem exercise.
"""
from z3 import *


example_problem = dict(
    nc=4,
    np=3,
    na=2,
    src=[2,1,0],
    dst=[0,3,2],
    start=[3,3]
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
    on = Function('on', package, city, time, boolean)
    move = Function('move', airplane, time, boolean)
    load = Function('load', package, airplane, time, boolean) #:= !move(a, t) and At(p,loc(a,t),t)
    unload = Function('unload', package, city, airplane, time, boolean) #:= !move(a, t) and on(p,a,t) and loc(a, t) = c

    # Declaring consts
    a, a1 = Consts('a a1', airplane)
    c, c1 = Consts('c c1', city)
    p, p1 = Consts('p p1', package)
    t, t1 = Consts('t t1', time)

    s = Solver()
    # Defining Predicates and Functions
    # move(airplane a, time t) := loc(a, t) != loc(a, t+1)
    s.add(ForAll[a], ForAll[t], And(
        Implies(move(a, t), loc(a, t) == loc(a, t+1)), Implies(loc(a, t) == loc(a, t+1), move(a, t))))

    # load(package p, airplane a, time t) := !move(a, t) and At(p,loc(a,t),t)
    s.add(ForAll[p], ForAll[a], ForAll[t],
          And(Implies(load(p, a, t), And(Not(move(a, t)), at(p, loc(a, t), t))),
          Implies(And(Not(move(a,t)), at(p, loc(a, t), t)), load(p, a, t))))

    # unload(package p, city c, airplane a, time t) := !move(a, t) and on(p,a,t) and loc(a, t) = c
    s.add(ForAll[p], ForAll[c], ForAll[a], ForAll[t],
          And(Implies(unload(p, c, a, t), And(Not(move(a, t)), And(on(p, a, t), loc(a, t) == c))),
          Implies(And(Not(move(a, t)), And(on(p, a, t), loc(a, t) == c)), unload(p, c, a, t))))

    # Adding the Constraints
    # Any plane must be present at one and only city at any time
    s.add(ForAll[a], ForAll[t], Exists[c1], And(loc(a, t) == c1, ForAll[c], Implies(loc(a, t) == c, c == c1)))
    pass


if __name__ == '__main__':
    print_problem(**example_problem)
    print_plan(**example_solution)

    #
    # Uncomment after you implement get_transport_plan:
    #
    # city_packages, city_airplanes, airplane_packages = get_transport_plan(**example_problem)
    # print
    # print_plan(city_packages, city_airplanes, airplane_packages)

    #
    # Add more tests here...
    #
