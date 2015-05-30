from chaotic import chaotic
from mbg import join, bottom, top, iota, assign_const, assign_var

# int a
# a = 5
# b = 6

# Edges
succ = {1: {2}, 2: {3}, 3: {}}
# Transfer function
tr = {(1, 2): lambda v: assign_const(v, 'a', 1), (2, 3): lambda v: assign_var(v, 'b', 'a'), (3, 3): lambda v: v}
# Textual description of the edges
tr_txt = {(1, 2): "a := 5", (2, 3): "b := a", (3, 3): "nop"}

chaotic(succ, 1, iota, join, bottom, tr, tr_txt)

