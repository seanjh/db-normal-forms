class fdep(object):
    def __init__(self, x_chars, y_chars):
        # x --> y
        self.x = set([c.lower() for c in x_chars])
        self.y = set([c.lower() for c in y_chars])

    def __eq__(self, other):
        return self.x == other.x and self.y == other.y

    def __ne__(self, other):
        return not self.__eq__(other)

    def __str__(self):
        return '%s-->%s' % (
            ''.join([str(v) for v in self.x]), 
            ''.join([str(v) for v in self.y])
            )


# a = ['s', 'c', 'z']
a = ['a', 'b', 'c', 'd', 'e', 'g', 'h']
# a = ['a', 'b', 'c', 'd', 'e']
# a = ['a', 'b', 'c', 'd']
full_set = frozenset(a)


f_deps = [
    fdep('ce', 'bh'),
    fdep('abc', 'dh'),
    fdep('c', 'a'),
    fdep('d', 'b'),
    fdep('ch', 'e'),
    fdep('bc', 'dh'),
    fdep('c', 'b'),
    fdep('ac', 'h')
]

# https://courses.cit.cornell.edu/cs5320/lect14.pdf 3nf slide
# f_deps = [
#     fdep('z', 'c'),
#     fdep('sc', 'z')
# ]

# f_deps = [
#     fdep('ab', 'c'),
#     fdep('c', 'd'),
#     fdep('c', 'a'),
#     fdep('ab', 'd'),
#     fdep('d', 'a')
# ]


def f_plus(f_deps):
    fplus = []
    for i in range(len(f_deps)):
        for j in range(i+1,len(f_deps)):
            new_x = f_deps[i].x.union(f_deps[j].x)
            new_y = f_deps[i].y.union(f_deps[j].y)
            tmp = fdep(new_x, new_y)
            if tmp not in fplus:
                fplus.append(tmp)
    return fplus


def closure(a_set, f_deps):
    for dep in f_deps:
        if dep.x.issubset(a_set):
            a_set = a_set.union(dep.y)
    return a_set

def get_keys(sets, f_deps):
    c_keys = []
    all_f_deps = []
    s_keys = []
    for s in sets:
        tmp = closure(s, f_deps)
        all_f_deps.append(fdep(s, tmp))
        if is_full_set(tmp, full_set):
            s_keys.append([ch for ch in s])
            if not is_ck_superset(s, c_keys):
                c_keys.append([ch for ch in s])
    return c_keys, s_keys, all_f_deps


def is_full_set(chars, full_set):
    return set([c for c in chars]) == full_set


def is_ck_superset(chars, ck_list):
    for key in ck_list:
        if chars.issuperset(set(key)):
            return True
    return False

# ones
fd_set = [set(val) for val in a]

# pairs
for i in range(len(a)):
    for j in range(i+1, len(a)):
        tmp = set([a[i], a[j]])
        if not tmp in fd_set:
            fd_set.append(tmp)

# threes
for i in range(len(a)):
    for j in range(i+1, len(a)):
        for k in range(j+1, len(a)):
            tmp = set([a[i], a[j], a[k]])
            if not tmp in fd_set:
                fd_set.append(tmp)
            # x_set.add(set([a[i], a[j], a[k]]))
            # print a[i], a[j], a[k]

# fours
for i in range(len(a)):
    for j in range(i+1, len(a)):
        for k in range(j+1, len(a)):
            for l in range(k+1, len(a)):
                tmp = set([a[i], a[j], a[k], a[l]])
                if not tmp in fd_set:
                    fd_set.append(tmp)
                # x_set.add(set([a[i], a[j], a[k], a[l]]))
                # print a[i], a[j], a[k], a[l]

# fives
for i in range(len(a)):
    for j in range(i+1, len(a)):
        for k in range(j+1, len(a)):
            for l in range(k+1, len(a)):
                for m in range(l+1, len(a)):
                    tmp = set([a[i], a[j], a[k], a[l], a[m]])
                    if not tmp in fd_set:
                        fd_set.append(tmp)
                    # x_set.add(set([a[i], a[j], a[k], a[l], a[m]]))
                    # print a[i], a[j], a[k], a[l], a[m]

# sixes
for i in range(len(a)):
    for j in range(i+1, len(a)):
        for k in range(j+1, len(a)):
            for l in range(k+1, len(a)):
                for m in range(l+1, len(a)):
                    for n in range(m+1, len(a)):
                        tmp = set([a[i], a[j], a[k], a[l], a[m], a[n]])
                        if not tmp in fd_set:
                            fd_set.append(tmp)
                        # x_set.add(set([a[i], a[j], a[k], a[l], a[m], a[n]]))
                        # print a[i], a[j], a[k], a[l], a[m], a[n]


def is_trivial(left_set, right_set):
    return right_set.issubset(left_set)


def is_superkey(left_chars, super_keys):
    return left_chars in [set(k) for k in super_keys]


def is_bcnf(f_deps, s_keys):
    results = []
    for fd in f_deps: 
        results.append(fd.x in s_keys)
    for i, r in enumerate(results):
        if not r:
            print '%s violates BCNF' % f_deps[i]
    return sum(results) == len(f_deps)


def is_3nf(f_deps, s_keys, c_keys):
    results = []
    for fd in f_deps:
        results.append(
            not is_superkey(fd.x, s_keys) and
            not is_trivial(fd.x, fd.y) and
            not is_prime_attribute(fd.x, fd.y, c_keys)
        )
    for i, r in enumerate(results):
        if r:
            print '%s violates 3NF' % f_deps[i]
    return sum(results) == 0
            # print '%s violates 3nf' % fd
            # return False


def is_prime_attribute(x_set, a_set, cks):
    diff = a_set.difference(x_set)
    for ch in diff:
        for k in cks:
            if ch in k:
                return True
    return False


cks, sks, all_fdeps = get_keys(fd_set, f_deps)
for d in all_fdeps:
    out_str = str(d)
    if is_trivial(d.x, d.y):
        out_str += ' T'
    if is_superkey(d.x, sks):
        out_str += ' S'
    print '%s' % out_str

# sort'em
[k.sort() for k in cks]
[k.sort() for k in sks]

print 'Super Keys:'
for k in sks:
    print '\t%s' % ''.join(k)
print 'Candidate Keys:'
for k in cks:
    print '\t%s' % ''.join(k)

print 'In BCNF: %s' % is_bcnf(f_deps, sks)
print 'In 3NF: %s' % is_3nf(f_deps, sks, cks)


