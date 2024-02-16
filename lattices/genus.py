def get_product(set_list):
    '''
    Returns all elements in the cartesian product of the sets in set_list
    '''
    if len(set_list) == 0:
        return [[]]
    if len(set_list) == 1:
        return [[x] for x in set_list[0]]
    return [[x] + y for x in set_list[0] for y in get_product(set_list[1:])]

def get_dets(det_set, sign, num):
    '''
    Returns all possible sequences of length num of signs whose product is sign.
    These correspond to the quadratic character of the determinants of Jordan factors.
    '''
    dets = []
    b = len(det_set)
    num_opts = b**(num - 1)
    for n in range(num_opts):
        idxs = ZZ(n).digits(b, padto=num - 1)
        det = [det_set[idx] for idx in idxs]
        sgn = sign*prod(det)^(-1)
        det += [sgn]
        dets.append(det)
    return dets  

def oddity(s):
    '''
    Copmute the oddity for a list of quintuples that describe a 2-adic genus symbol
    '''
    odd = sum([t[-1] for t in s])
    k = len([t for t in s if t[0] % 2 == 1 and t[2] in [3,5]])
    odd += 4*k
    odd %= 8
    return odd

def expected_oddity(n_plus, n_minus, odd_symbols):
    '''
    Returns the oddity of the 2-adic genus symbol, given the signature and the p-adic genus symbols at the odd primes.
    This follows from the oddity condition.
    '''
    excess = sum([symb.excess() for symb in odd_symbols])
    return (excess + n_plus - n_minus) % 8

def all_local_genus_symbols(rank, det, p):
    '''
    Returns all possible p-adic genus symbols for a lattice of a given rank and determinant
    '''
    val_det, unit_det = ZZ(det).val_unit(p)
    symbs = []
    det_set = [1,-1]
    sign = unit_det.kronecker(p)
    val_det, unit_det = ZZ(det).val_unit(p)
    decs = WeightedIntegerVectors(val_det, range(1,val_det+1))
    ranks = [[rank-sum(dec)] + list(dec) for dec in decs if sum(dec) <= rank]
    for dec in ranks:
        scls = [i for i in range(len(dec)) if dec[i] > 0]
        rks = [dec[i] for i in scls]
        dets = get_dets(det_set, sign, len(scls))
        for det_list in dets:
            assert prod(det_list) == sign
            blocks = [[scls[j], rks[j], det_list[j]] for j in range(len(rks))]
            blocks.sort()
            symbs.append(blocks)
    return [Genus_Symbol_p_adic_ring(p,symb) for symb in symbs]

def listify_symbol(x):
    return reduce(lambda x,y : x+y, x.canonical_symbol())

def get_unique(symbs):
    '''
    Returns a list containing only one symbol from every equivalence class
    '''
    symb_dict = {}
    for i,s in enumerate(symbs):
        symb_dict[tuple(listify_symbol(s))] = i
    return [symbs[i] for i in symb_dict.values()]

def all_diadic_genus_symbols(n_plus, n_minus, det, odd_symbols):
    '''
    Returns all the possible 2-adic genus symbols of a global genus symbol having a signature (n_plus, m_minus),
    determinant det and p-adic genus symbols odd_symbols at the odd primes p dividing the determinant
    '''
    rank = n_plus + n_minus
    val_det, unit_det = ZZ(det).val_unit(p)
    symbs = []
    det_set = [1,3]
    sign = unit_det.kronecker(p)
    decs = WeightedIntegerVectors(val_det, range(1,val_det+1))
    ranks = [[rank-sum(dec)] + list(dec) for dec in decs if sum(dec) <= rank]
    exp_oddity = expected_oddity(n_plus, n_minus, odd_symbols)
    for dec in ranks:
        scls = [i for i in range(len(dec)) if dec[i] > 0]
        rks = [dec[i] for i in scls]
        dets = get_dets([1,-1], sign, len(scls))
        for det_list in dets:
            assert prod(det_list) == sign
            blocks = [[scls[j], rks[j], det_set[(1 - det_list[j]) // 2]] for j in range(len(rks))]
            blocks.sort()
            # We do not obtain all oddities.
            comps = []
            for block in blocks:
                oddities = []
                # if the scaling is trivial, we cannot have any oddity
                if block[0] == 0:
                    oddities = [[0,0]]
                elif block[1] == 1:
                    if block[2] == 1: 
                        oddities = [[1,1],[1,7]]
                    else:
                        oddities = [[1,3],[1,5]]
                elif block[1] == 2:
                    if block[2] == 1:
                        oddities = [[0,0],[1,0],[1,2],[1,6]]
                    else:
                        oddities = [[0,0], [1,2],[1,4],[1,6]]
                elif block[1] % 2 == 0:
                    oddities = [[0,0],[1,0], [1,2], [1,4], [1,6]]
                else:
                    oddities = [[1,1],[1,3],[1,5],[1,7]]
                comps.append([block + odd for odd in oddities])
            # !! TODO - replace by something that generated only those with the correct oddity
            for cmps in get_product(comps):
                if (oddity(cmps) - exp_oddity) % 8 == 0:
                    symbs.append(cmps)
    gen_symbs = [Genus_Symbol_p_adic_ring(p,symb) for symb in symbs]
    assert all([s.is_even() for s in gen_symbs])
    return get_unique(gen_symbs)

def all_genus_symbols(n_plus, n_minus, det):
    '''
    Returns all the genus symbols of even lattices with signature (n_plus, n_minus) and determinant det
    '''
    rank = n_plus + n_minus
    primes = (2*det).prime_divisors()
    odd_primes = primes[1:]
    global_symbs = []
    odd_symbs = get_product([all_local_genus_symbols(rank, det, p) for p in odd_primes])
    for odd_symbols in odd_symbs:
        diadic = all_diadic_genus_symbols(n_plus, n_minus, det, odd_symbols)
        for symb2 in diadic:
            g = GenusSymbol_global_ring((n_plus, n_minus), [symb2] + odd_symbols)
            global_symbs.append(g)
    return global_symbs
    
