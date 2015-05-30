Abstract domain for "May-Be-Garbage" analysis:
We shall have the following states:
Bottom - variable is not assigned any value
Top - variable is assigned

Transitions:
a = b -->
1. if b = top -> top
2. if b = bottom -> bottom
In short, for a = b we will assign a = b

Programs:
mbg_prog1.py code:
int a
a = 5





