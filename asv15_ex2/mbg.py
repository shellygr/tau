bottom = "bottom"
top = "top"
is_debug = False


def dbg_print(msg):
    if is_debug:
        print "DBG: " + msg


def join(a, b):
    dbg_print("Join: " + str(a) + ", " + str(b))
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
    dbg_print("assign_const: " + str(var_name) + " := " + str(value))
    # Note: for debugging purpose, it is possible to assign 'value' instead of 'top'
    return remove_existing_value(vs, var_name)


def assign_var(vs, var_name, assigned_var_name):
    dbg_print(str(var_name) + " := " + str(assigned_var_name))
    # Do we know this variable?
    for v in vs:
        if v[0] == assigned_var_name:
            dbg_print("Variable " + assigned_var_name + " found")
            # This variable is assigned with a may-be-garbage variable - this may be garbage
            return vs | set([var_name])

    # The assigned variable is not garbage - remove it from the list
    return remove_existing_value(vs, var_name)
