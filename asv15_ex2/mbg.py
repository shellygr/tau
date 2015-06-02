bottom = "bottom"
top = "top"
iota = set()


def join(a, b):
    print "DBG: Join: " + str(a) + ", " + str(b)
    if a == bottom:
        return b
    elif b == bottom:
        return a
    elif a == b:
        return a
    else:
        return a | b


def meet(a, b):
    if a == top:
        return b
    elif b == top:
        return a
    elif a == b:
        return a
    else:
        return a & b


def remove_existing_value(vs, var_name):
    return set(v for v in vs if v[0] != var_name)


def assign_const(vs, var_name, value):
    print "DBG: assign_const: " + str(vs) + " := " + str(value)
    # Note: for debugging purpose, it is possible to assign 'value' instead of 'top'
    return remove_existing_value(vs, var_name) | set([(var_name, top)])


def assign_var(vs, var_name, assigned_var_name):
    # Do we know this variable?
    for v in vs:
        if v[0] == assigned_var_name:
            print "DBG: Variable " + var_name + " found, its value is " + str(v[1])
            # This variable exists - assign its value to our variable
            return remove_existing_value(vs, var_name) | set([(var_name, v[1])])

    # This is an unknown variable - this may be garbage
    return remove_existing_value(vs, var_name) | set([(var_name, bottom)])
