

def chaotic(succ, s, i, join, bottom, tr, tr_txt):
    """
    succ is the successor nodes in the CFG
    s in nodes is the start vertex
    i is the initial value at the start
    bottom is the minimum value
    tr is the transfer function
    tr_txt is the edge annotations
    """
    wl = [s]
    df = dict([(x, bottom) for x in succ])
    df[s] = i
    while wl != []:
        print "worklist is {}\n".format(wl)
        u = wl.pop()
        print "Handling:", u
        for v in succ[u]:
            new = join(tr[(u,v)](df[u]), df[v])
            if (new != df[v]):
                print "    Changing the dataflow value at {} from {} to {}".format(v, df[v], new)
                df[v] = new
                wl.append(v)
                print "    Adding {} to the worklist".format(v)
                wl.sort(key=lambda x:-x) # sort in backward key order
            else:
                print "    New dataflow value at {} equal to the old value".format(v)
            print
        print
    print "Worklist empty"
    print

    print "Dataflow results"
    for node in succ:
        print "    {}: {}".format(node, df[node])

    import os
    f = open("temp_chaotic.dt", "w")
    f.write("digraph cfg {\n")
    # write nodes and df values
    for node in succ:
        f.write("    {} [label=\"{}: {}\"]\n".format(
            node, node, df[node]))

    for u in succ:
        for v in succ[u]:
            f.write("\t" + str(u) + "->" + str(v) + " [label=\"" + tr_txt[(u,v)]+"\"]\n")
    f.write("\t}\n")
    f.close()
    os.system("dot temp_chaotic.dt -Tpng > chaotic.png")
    os.system("xdg-open chaotic.png") # to open the png file
