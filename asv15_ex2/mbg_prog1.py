from chaotic import chaotic
from mbg import join, bottom, top, assign_const, assign_var

# int a, b, c
# a = 5
# b = c

# Edges
succ = {1: {2}, 2: {3}, 3: {4}, 4: {5}, 5: {}}
# Transfer function
tr = {
    (1, 2): lambda v: assign_const(v, 'a', 5),
    (2, 3): lambda v: assign_var(v, 'b', 'c'),
    (3, 4): lambda v: assign_var(v, 'c', 'b'),
    (4, 5): lambda v: assign_var(v, 'a', 'c'),
    (5, 5): lambda v: v}
# Textual description of the edges
tr_txt = {
    (1, 2): "a := 5",
    (2, 3): "b := c",
    (3, 4): "c := b",
    (4, 5): "a := c",
    (5, 5): "nop"}

chaotic(succ, 1, set([ 'a', 'b', 'c' ]), join, bottom, tr, tr_txt)

