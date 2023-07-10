# This algorithm is simply to demonstrate the impossibility of generating all complete cap sets
# without the use of clever tricks like isomorph rejection and canonical labeling.
# There are trillions of distinct cap sets in 4D, and exponentially more in higher dimensions.

setters = [[0, 2, 1], [2, 1, 0], [1, 0, 2]]

def setter(c1, c2):
    return [setters[c1[0]][c2[0]], setters[c1[1]][c2[1]], setters[c1[2]][c2[2]], setters[c1[3]][c2[3]]]

def card(c):
    res = []
    for i in range(4):
        res.append(c % 3)
        c //= 3
    return res

def cardId(c):
    return c[0] + c[1] * 3 + c[2] * 9 + c[3] * 27

def all_caps(cap, elim):
    complete = True
    for i in range(cap[-1] + 1, 81):
        ic = card(i)
        if i in elim:
            continue
        complete = False
        elim2 = elim.copy()
        for j in cap:
            elim2.add(cardId(setter(ic, card(j))))
        all_caps(cap + [i], elim2)
    if complete and len(cap) + len(elim) == 81:
        print("Found complete cap with " + str(len(cap)) + " cards")
        if len(cap) == 19:
            print(cap, elim)
            exit()

all_caps([0, 1, 3], {2, 6, 8})