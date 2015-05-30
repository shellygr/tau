bottom = "bottom"
top = "top"
iota = 0


def join(a, b):
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


def assign_const(v, var_name, value):
    print "assign_const: " + str(v)
    v[var_name] = value
    return v


def assign_var(v, var_name, assigned_var_name):
    v[var_name] = v[assigned_var_name]
    return v