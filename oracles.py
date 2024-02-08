""" A dummy oracle implementation satisfying Assumptions 1-5 of the paper. """

from globals import group, G1, ZR, pair, f2
import json
import os
import random
import shutil
import sys

#### Environmental setup  #####################################################

# Public/private key pair for the ocapture oracle (not to be confused with 
# the public/private keys of the backend servers)
_sk = group.random(ZR)
pk = f2 ** _sk

envsetup_done = False
uids = []
eds = []

def envsetup(n):
    """ Set up the environment for n *potential* voters. """

    global uids, eds, envsetup_done

    if envsetup_done:
        return uids, eds
    
    else:
        # Assign randomly shuffled uids to each potential voter such that the 
        # uid assigned to the i^th voter is uids[i]
        for i in range(n):
            uids.append(i)
        random.shuffle(uids)

        # Assign dummy ed to each potential voter
        names = ["Name%s"%i for i in range(n//5)]    # n/5 unique names
        sexes = [0,1]
        ages = list(range(100))
        addresses = ["Address%s"%i for i in range(n//3)]  # each addr has 3 voters
        for i in range(n):
            name = random.choice(names)
            sex = random.choice(sexes)
            age = random.choice(ages)
            address = random.choice(addresses)
            h = group.hash(name.encode() + str(sex).encode() + str(age).encode() + address.encode(), type=G1)
            eds.append((h, name, sex, age, address))        

        envsetup_done = True
        return uids, eds

#### Oracles ##################################################################

def ocapture(V, ctx):
    bV = V.encode()       # convert to binary data
    bctx = ctx.encode()   # convert to binary data
    with open('lenagray.png', 'rb') as f: # insert a dummy photo
        bphoto = f.read()
    m = bV + bctx + bphoto 
    h = group.hash(m, type=G1)
    sigma = h ** _sk
    md = (V, ctx)
    return (h, sigma) + md

def olive(p, ctx):
    try:
        assert _check_authentic(p)
        (h, sigma, V, ctxdash) = p
        return ctxdash == ctx
    except AssertionError:
        return False

def omatch(p1, p2):
    try:
        assert _check_authentic(p1)
        assert _check_authentic(p2)
        (h1, sigma1, V1, ctx1) = p1
        (h2, sigma2, V2, ctx2) = p2
        return V1 == V2
    except AssertionError:
        return False

def oelg(p, ed):
    try:
        assert _check_authentic(p)
        (h, sigma, V, ctx) = p
        i = int(V[1:])
        eddash = eds[i]
        for j in range(len(eddash)):
            assert eddash[j] == ed[j]
        h, name, sex, age, address = eddash
        housecode = int(address[7:])
        return (age > 18 and housecode % 2 == 0)
    except AssertionError:
        return False

def ouid(p):
    try:
        assert _check_authentic(p)
        (h, sigma, V, ctx) = p
        i = int(V[1:])
        return uids[i]
    except AssertionError:
        return None

#### Lower-level code #########################################################

def _check_authentic(p):
    (h, sigma, V, ctx) = p
    bV = V.encode()
    bctx = ctx.encode()
    with open('lenagray.png', 'rb') as f: # check hash with the same dummy photo
        bphoto = f.read()
    m = bV + bctx + bphoto
    return h == group.hash(m, type=G1) and pair(sigma, f2) == pair(h, pk)

#### Testing code #############################################################

if __name__ == "__main__":
    n = int(sys.argv[1])
    print("Environment setup beginning.")
    envsetup(n)
    print("Environment setup done.")

    # Test assumption 1: consistent photographs
    i = random.choice(range(n))
    p1 = ocapture("V%s"%i, "ctx1")
    p2 = ocapture("V%s"%i, "ctx2")
    assert omatch(p1, p2)
    print("Assumption 1 (consistent photographs) tested successfully.")

    # Test assumption 2: no identical twins
    i1 = random.choice(range(n))
    i2 = random.choice(range(n))
    assert i1 != i2
    p1 = ocapture("V%s"%i1, "ctx")
    p2 = ocapture("V%s"%i2, "ctx")
    assert not omatch(p1, p2)
    print("Assumption 2 (no identical twins) tested successfully.")

    # Test assumption 3: unforgeable photographs
    i = random.choice(range(n))
    p1 = ocapture("V%s"%i, "ctx")
    assert olive(p1, "ctx")
    (h, sigma, V, ctx, photo) = p1
    p2 = (h, sigma, "V%s"%i, "ctx2", photo)  # changing ctx with the same photograph
    p2dash = p1                            # copying the same contents as p1 completely
    p2ddash = ocapture("V%s"%0, "ctx2")    # capturing some other voter's photograph in ctx2
    assert i != 0   
    assert not (omatch(p1, p2) and olive(p2, "ctx2"))
    assert not (omatch(p1, p2dash) and olive(p2dash, "ctx2"))
    assert not (omatch(p1, p2ddash) and olive(p2ddash, "ctx2"))
    print("Assumption 3 (unforgeable photographs) tested successfully.")

    # Test assumption 4: consistent eligibility
    i = random.choice(range(n))
    p1 = ocapture("V%s"%i, "ctx1")
    p2 = ocapture("V%s"%i, "ctx2")
    assert omatch(p1, p2)
    assert oelg(p1, eds[i]) == oelg(p2, eds[i])
    eddummy = ("NameDum", "SexDum", "AgeDum", "Addr34")
    assert oelg(p1, eddummy) == oelg(p2, eddummy)
    print("Assumption 4 (consistent eligibility) tested successfully.")

    # Test assumption 5: deduplicated identifiers
    i = random.choice(range(n))
    p1 = ocapture("V%s"%i, "ctx1")
    p2 = ocapture("V%s"%i, "ctx2")
    assert omatch(p1, p2)
    assert ouid(p1) == ouid(p2)
    print("Assumption 5 (deduplicated identifiers) tested successfully.")