from elgamal import elgamal_th_keygen, elgamal_encrypt, elgamal_share_decrypt, elgamal_combine_decshares, elgamal_share_decryption_batchpf, elgamal_share_decryption_batchverif, elgamal_th_decrypt, elgamal_th_decrypt_with_pf
from globals import group, ZR, G1
from misc import timer
from oracles import ocapture, olive, omatch, oelg, ouid, envsetup
from perm import gen_rand_perm
from pok import pk_elg_enc, pk_elg_enc_verif, pk_elg_dec_share, pk_elg_dec_share_verif, pk_elg_eq, pk_elg_eq_verif
import random
from secretsharing import share2_2, reconstruct2_2
from shuffle import shuffle_mult, pf_shuffle_mult, pf_shuffle_mult_verif

#### Constants ####

# Number of backend servers
kappa = 4

# Contexts
ctxR = "ctxR"
ctxC = "ctxC"
ctxpR = "ctxpR"
ctxpC = "ctxpC"

# Receipt types
AcceptReg = "Accept"
DupReg = "DupReg"
RejectReg = "Reject"
AcceptCast = "Accept"
DupCast = "DupCast"
RejectCast = "Reject"

#### Bulletin board ####

# ERR = []
# ER = []
# CI = []
# EV = []

# # For efficient lookup on ERRacc and ERacc using uid and vid respectively, we maintain these additional index data structures, essentially dictionaries with uid/vid as keys and the index of the ERRacc/ERacc entry containing that uid/vid as the value.
# I_ERR = {}
# I_ER = {}

def get(L, I, id):
    """ Efficiently get the element from list L containing id, using I as the index data structure. """
    try:
        i = I[id]
        return i, L[i]
    except KeyError:
        return None, None
    
def push(L, I, id, data):
    """ Efficiently push an element containing id and data to list L, using I as the index data structure. """
    if I.get(id) is not None:
        raise ValueError("uid %s already added" % id)
    else:
        L.append(data)
        I[id] = len(L) - 1

def exists(L, I, id, data):
    """ Efficiently check whether a data item containing id and data exists in list L, using I as the index data structure. """
    i, data_ = get(L, I, id)
    return data_ == data

#### Helpers for encrypting large data ####

repo = {}

def elgamal_encrypt_large(pk, d, randIn=None, randOut=None):
    """ Assume that d is a large data in the form (h, d1, d2, ..., dk), where dk denote the actual data items (some of them too big for the encryption scheme) and h their hash into the El Gamal message space. To encrypt such data, we simulate the strategy of encrypting the hash and secret-sharing the actual data among the backend servers by simply storing the actual data indexed by the hash in a repository (to be fetched during decryption). """
    h = d[0]
    repo[group.serialize(h)] = d[1:]
    return elgamal_encrypt(pk, h, randIn, randOut)

def elgamal_th_decrypt_large(sklist, c):
    h = elgamal_th_decrypt(sklist, c)
    rest = repo[group.serialize(h)]
    return (h,) + rest

def elgamal_th_decrypt_large_with_pf(pk, sklist, c, pfOut=False):
    if pfOut:
        h, pf = elgamal_th_decrypt_with_pf(pk, sklist, c, pfOut)
        rest = repo[group.serialize(h)]
        return (h,) + rest, pf
    else:
        h = elgamal_th_decrypt_with_pf(pk, sklist, c, pfOut)
        rest = repo[group.serialize(h)]
        return (h,) + rest

#### Protocol ####

def setup():
    skSs, pkS = elgamal_th_keygen(kappa)
    return skSs, pkS

def register(pkS, ERR, I_ERR, V, uid, ed, j, skSs):
    prp = ocapture(V, ctxpR)
    i, data = get(ERR, I_ERR, uid)
    j = group.init(G1, j)

    # Reject - unrecognised or incorrect uid
    if uid != ouid(prp):
        rr = (RejectReg, uid, prp)

    # Duplicate registration
    elif i is not None:
        uid, c_vid, c_j, c_ed, c_rp = data
        rp = elgamal_th_decrypt_large(skSs, c_rp)
        assert omatch(rp, prp) == True
        rr = (DupReg, prp, rp)

    # Accepted for registration
    else:
        rp = ocapture(V, ctxR)
        vid = group.random(G1)
        (c_vid, _r_vid), (c_j, _r_j), (c_ed, _r_ed), (c_rp, _r_rp) = [
            elgamal_encrypt(pkS, vid, randOut=True), 
            elgamal_encrypt(pkS, j, randOut=True), 
            elgamal_encrypt_large(pkS, ed, randOut=True), 
            elgamal_encrypt_large(pkS, rp, randOut=True)
        ]
        push(ERR, I_ERR, uid, (uid, c_vid, c_j, c_ed, c_rp))
        (cstar_vid, _rstar_vid), (cstar_j, _rstar_j), (cstar_ed, _rstar_ed) = [
            elgamal_encrypt(pkS, vid, randOut=True), 
            elgamal_encrypt(pkS, j, randOut=True), 
            elgamal_encrypt_large(pkS, ed, randOut=True)
        ]
        rhoenc1 = pk_elg_enc(pkS, c_rp, rp[0], _r_rp)
        rhoenc2 = [
            pk_elg_enc(pkS, cstar_vid, vid, _rstar_vid), 
            pk_elg_enc(pkS, cstar_j, j, _rstar_j),
            pk_elg_enc(pkS, cstar_ed, ed[0], _rstar_ed)
        ]
        rhoeq   = [
            pk_elg_eq(pkS, c_vid, cstar_vid, _r_vid, _rstar_vid),
            pk_elg_eq(pkS, c_j, cstar_j, _r_j, _rstar_j),
            pk_elg_eq(pkS, c_ed, cstar_ed, _r_ed, _rstar_ed)
        ]
        rhoeq1, rhoeq2 = zip(*[share2_2(rhoeq[i]) for i in range(len(rhoeq))])
        rr11 = (uid, rp, rhoenc1)
        rr12 = (c_vid, c_j, c_ed, c_rp, rhoeq1)
        rr21 = (vid, j, ed, rhoenc2)
        rr22 = (cstar_vid, cstar_j, cstar_ed, rhoeq2)

        rr = (AcceptReg, rr11, rr12, rr21, rr22)
    return ERR, I_ERR, rr

def indrraudit(pkS, ERR, I_ERR, rr, beta=None):
    """ Auditor steps for the IndRAudit protocol. The value `beta` is non-None only when rr is an Accept receipt. """

    # Reject registration receipt
    if rr[0] == RejectReg:
        (_, uid, prp) = rr
        ver = (ouid(prp) != uid)
    
    # Duplicate registration receipt
    elif rr[0] == DupReg:
        (_, prp, rp) = rr
        ver = olive(rp, ctxR) == True and omatch(rp, prp) == True

    # Accept registration receipt
    else:
        if beta == 0:
            (rr11, rr12, _, _) = rr[1:]
            (uid, rp, rhoenc1) = rr11
            (c_vid, c_j, c_ed, c_rp, rhoeq1) = rr12
            ver = pk_elg_enc_verif(pkS, c_rp, rp[0], rhoenc1) and \
                  exists(ERR, I_ERR, uid, (uid, c_vid, c_j, c_ed, c_rp))
        elif beta == 1:
            (_, _, rr21, rr22) = rr[1:]
            (vid, j, ed, rhoenc2) = rr21
            (cstar_vid, cstar_j, cstar_ed, rhoeq2) = rr22
            ver = pk_elg_enc_verif(pkS, cstar_vid, vid, rhoenc2[0]) and \
                  pk_elg_enc_verif(pkS, cstar_j, j, rhoenc2[1]) and \
                  pk_elg_enc_verif(pkS, cstar_ed, ed[0], rhoenc2[2])
        else:
            (_, rr12, _, rr22) = rr[1:]
            (c_vid, c_j, c_ed, c_rp, rhoeq1) = rr12
            (cstar_vid, cstar_j, cstar_ed, rhoeq2) = rr22
            rhoeq = [reconstruct2_2(rhoeq1[i], rhoeq2[i]) for i in range(len(rhoeq1))]
            ver = pk_elg_eq_verif(pkS, c_vid, cstar_vid, rhoeq[0]) and \
                  pk_elg_eq_verif(pkS, c_j, cstar_j, rhoeq[1]) and \
                  pk_elg_eq_verif(pkS, c_ed, cstar_ed, rhoeq[2])
    return ver

def univaudit_ERR(pkS, alpha, ERR, skSs):
    # Skipping the distinctness check for simplicity as it does not affect the 
    # performance characteristics we wish to benchmark.

    for attempt in range(alpha):
        # Here, we are choosing i as a random element interactively and with 
        # replacement, as opposed to the protocol description that requires audited 
        # indices to be selected non-interactively and without replacement. This 
        # is done purely as a simplification as it does not affect the performance # characteristics we wish to benchmark.
        i = random.choice(range(len(ERR)))
        (uid, c_vid, c_j, c_ed, c_rp) = ERR[i]
        rp = elgamal_th_decrypt_large_with_pf(pkS, skSs, c_rp)
        ver = (ouid(rp) == uid)
    return ver

def prepareER(pkS, ERR, skSs):
    uid, c_vid, c_j, c_ed, c_rp = zip(*ERR)
    cinvecs = (c_vid, c_j, c_ed, c_rp)

    n = len(c_vid)
    kappa = len(skSs)
    _pis, _repis, pf_shufs = [], [], []
    
    for k in range(kappa):
        with timer("mix-server %s: generating shuffle and proofs of shuffle" % k):
            _pi, _repi = gen_rand_perm(n)
            coutvecs, _rvecs = shuffle_mult(pkS, cinvecs, _pi)
            pf_shuf = (coutvecs, pf_shuffle_mult(pkS, cinvecs, coutvecs, _pi, _repi, _rvecs))
            _pis.append(_pi)
            _repis.append(_repi)
            pf_shufs.append(pf_shuf)
            cinvecs = coutvecs

    cdash_vid, cdash_j, cdash_ed, cdash_rp = cinvecs
    decshares_vid, pf_vid, decshares_j, pf_j = [], [], [], []
    for k in range(kappa):
        with timer("mix-server %s: partial decryption of vid and j" % k):
            decshares_vid.append([elgamal_share_decrypt(pkS, cdash_vid[i], skSs[k]) for i in range(n)])
            pf_vid.append(
                (decshares_vid[k], 
                elgamal_share_decryption_batchpf(pkS, decshares_vid[k], cdash_vid, k, skSs[k]))
            )

            decshares_j.append([elgamal_share_decrypt(pkS, cdash_j[i], skSs[k]) for i in range(n)])
            pf_j.append(
                (decshares_j[k], 
                elgamal_share_decryption_batchpf(pkS, decshares_j[k], cdash_j, k, skSs[k]))
            )

    with timer("mix-server {each}: combining partial decryptions of vid and j".format(each = ",".join([str(i) for i in range(kappa)]))):
        viddash = elgamal_combine_decshares(pkS, cdash_vid, decshares_vid)
        jdash = elgamal_combine_decshares(pkS, cdash_j, decshares_j)

    # EO's eligibility approvals/dismissals, plus dummy booth number assignment
    elg = []; l = []
    for i in range(len(viddash)):
        rp = elgamal_th_decrypt_large(skSs, cdash_rp[i])
        ed = elgamal_th_decrypt_large(skSs, cdash_ed[i])
        elg.append(oelg(rp, ed))
        l.append(0)

    # Create ER and index.
    ER = []; I_ER = {}
    for i in range(len(viddash)):
        push(ER, I_ER, viddash[i], (viddash[i], jdash[i], cdash_ed[i], cdash_rp[i], elg[i], l[i]))

    pf_ER = (pf_shufs, pf_vid, pf_j, cdash_vid, cdash_j)

    return ER, I_ER, pf_ER

def univaudit_prepareER(pkS, ERR, ER, pf_ER):
    (pf_shufs, pf_vid, pf_j, cdash_vid, cdash_j) = pf_ER
    uid, c_vid, c_j, c_ed, c_rp = zip(*ERR)
    (viddash, jdash, cdash_ed, cdash_rp, _, _) = zip(*ER)

    # skipping the distinctness check for simplicity

    cinvecs = (c_vid, c_j, c_ed, c_rp)
    cdashvecs = (cdash_vid, cdash_j, cdash_ed, cdash_rp)
    vershuf = True
    for k in range(kappa):
        with timer("auditor: verifying proofs of shuffle by mix-server %s" % k):
            _coutvecs, _pf_shuf = pf_shufs[k]
            vershuf_k = pf_shuffle_mult_verif(pkS, cinvecs, _coutvecs, _pf_shuf)
            vershuf = vershuf and vershuf_k
            cinvecs = _coutvecs
    
    vervid, verj = True, True
    decshares_vid, decshares_j = [], []
    for k in range(kappa):
        with timer("auditor: verifying partial decryptions by mix-server %s" % k):
            _decshares_vid, _pf_vid = pf_vid[k]
            vervid = vervid and elgamal_share_decryption_batchverif(pkS, _decshares_vid, cdash_vid, k, _pf_vid)
            _decshares_j, _pf_j = pf_j[k]
            verj = verj and elgamal_share_decryption_batchverif(pkS, _decshares_j, cdash_j, k, _pf_j)
            decshares_vid.append(_decshares_vid)
            decshares_j.append(_decshares_j)

    verUA = vershuf and vervid and verj
    return verUA

def cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, V, vid, ev, rhoev, skSs):
    i, ERdata = get(ER, I_ER, vid)

    # Rejected - unrecognised vid
    if i is None:
        cr = (RejectCast, vid)

    else:
        viddash, jdash, cdash_ed, cdash_rp, elg, l = ERdata
        rp, rhorp = elgamal_th_decrypt_large_with_pf(pkS, skSs, cdash_rp, pfOut=True)
        ed, rhoed = elgamal_th_decrypt_large_with_pf(pkS, skSs, cdash_ed, pfOut=True)
        
        pcp = ocapture(V, ctxpC)

        # Rejected - wrong vid
        if omatch(rp, pcp) != True:
            cr = (RejectCast, vid, pcp)

        # Rejected - deemed ineligible
        elif elg != True:
            cr = (RejectCast, vid, pcp, ed, rhoed)

        else:
            j, casting_data = get(CI, I_CI, vid)
            _, evdash = get(EV, I_EV, vid)

            # Duplicate cast
            if j is not None:
                c_cp, c_rhoev = casting_data
                cp = elgamal_th_decrypt_large(skSs, c_cp)
                rhoev = elgamal_th_decrypt_large(skSs, c_rhoev)
                if valid(rhoev, evdash):
                    cr = (DupCast, pcp, cp)

            # Accepted for casting
            else:
                cp = ocapture(V, ctxC)
                c_cp = elgamal_encrypt_large(pkS, cp)
                c_rhoev = elgamal_encrypt_large(pkS, rhoev)
                push(CI, I_CI, vid, (c_cp, c_rhoev))
                push(EV, I_EV, vid, ev)
                cr = (AcceptCast, vid, ev)
    return ER, I_ER, CI, I_CI, EV, I_EV, cr

def indcraudit(pkS, ER, I_ER, CI, I_CI, EV, I_EV, cr, rr, skSs):
    if cr[0] == RejectCast and len(cr) == 2:
        vid = cr[1]
        ver = (get(ER, I_ER, vid)[0] is None)

    elif cr[0] == RejectCast and len(cr) == 3:
        vid, pcp = cr[1:]
        (rr11, _, rr21, _) = rr[1:]
        _, rp, _ = rr11
        vidr, _, _, _ = rr21
        ver = (vid != vid) or (omatch(pcp, rp) == 0)

    elif cr[0] == RejectCast and len(cr) == 5:
        vid, pcp, ed, rhoed = cr[1:]
        i, data = get(ER, I_ER, vid)
        viddash, jdash, cdash_ed, cdash_rp, elg, l = data
        status_pfdec = True
        decshares, pfshares = rhoed
        for k in range(len(skSs)):
            status_pfdec = status_pfdec and pk_elg_dec_share_verif(pkS, cdash_ed, decshares[k], k, pfshares[k])
        ver = (i is not None) and status_pfdec and (oelg(pcp, ed) == 0)

    elif cr[0] == DupCast:
        pcp, cp = cr[1:]
        ver = omatch(cp, pcp) == 1 and olive(cp, ctxC) == 1

    else:
        vid, ev = cr[1:]
        i, _ = get(ER, I_ER, vid)
        _, evuploaded = get(EV, I_EV, vid)
        ver = (i is not None) and (evuploaded == ev)
    
    return ver

def univaudit_ER(pkS, alpha, ER, CI, I_CI, EV, skSs):
    # Skipping the distinctness check for simplicity as it does not affect the 
    # performance characteristics we wish to benchmark.

    ver = True

    for attempt in range(alpha):
        # Here, we are choosing i as a random element interactively and with 
        # replacement, as opposed to the protocol description that requires audited 
        # indices to be selected non-interactively and without replacement. This 
        # is done purely as a simplification as it does not affect the performance # characteristics we wish to benchmark.
        i = random.choice(range(len(ER)))

        (viddash, jdash, cdash_ed, cdash_rp, elg, l) = ER[i]
        _, data = get(CI, I_CI, viddash) 
        c_cp, c_rhoev = data

        rp = elgamal_th_decrypt_large_with_pf(pkS, skSs, cdash_rp)
        ed = elgamal_th_decrypt_large_with_pf(pkS, skSs, cdash_ed)
        cp = elgamal_th_decrypt_large_with_pf(pkS, skSs, c_cp)
        rhoev = elgamal_th_decrypt_large_with_pf(pkS, skSs, c_rhoev)

        if valid(rhoev, EV[i]):
            ver = ver and (omatch(cp, rp) == olive(cp, ctxC) == oelg(rp, ed) == 1)
    
    return ver

def valid(rhoev, ev):
    """ Dummy implementation that ignores rhoev and simulates ev with a simple unencrypted element. """
    return ev == group.init(ZR, 0) or  ev == group.init(ZR, 1)

#### Other helper functions ####

def receipt_size():
    return """
        Accept registration receipt size estimate: 
        - 4 ZR elements per ciphertext (x7)         = 28 ZR elements
        - 5 ZR elements for uid, rp, vid, j and ed  =  5 ZR elements
        - 2 ZR elements for rhoenc1                 =  2 ZR elements
        - 2 ZR elements per rhoenc2 component (x3)  =  6 ZR elements
        - 2 ZR elements per rhoeq1 component  (x3)  =  6 ZR elements
        - 2 ZR elements per rhoeq1 component  (x3)  =  6 ZR elements
        TOTAL                                       = 53 ZR elements.

        Assuming an elliptic curve where order q ~ 250 bits, each ZR element
        takes 250 bits, so the overall size requirement is 13250 bits ~ 1.65 KB,
        which can fit within standard QR codes.
        
        All other receipts are smaller.
    """

def test():
    """ Test the correctness of all components. """

    uids, eds = envsetup(n=100)
    skSs, pkS = setup()

    # Registration of a random voter using the correct uid.
    ERR = []; I_ERR = {}
    i  = random.choice(range(len(eds)))
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    assert rr[0] == AcceptReg
    assert indrraudit(pkS, ERR, I_ERR, rr, beta=0)
    print("IndRAudit passed for Accept receipt for beta=0.")
    assert indrraudit(pkS, ERR, I_ERR, rr, beta=1)
    print("IndRAudit passed for Accept receipt for beta=1.")
    assert indrraudit(pkS, ERR, I_ERR, rr, beta=2)
    print("IndRAudit passed for Accept receipt for beta=2.")
    print("Accept receipt size estimate:", receipt_size())

    # Registration of a random voter using incorrect uid.
    ERR = []; I_ERR = {}
    i  = random.choice(range(len(eds)))
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i-1], eds[i], 0, skSs)
    assert rr[0] == RejectReg
    assert indrraudit(pkS, ERR, I_ERR, rr)
    print("IndRAudit passed for Reject receipt.")

    # Registration of a random voter trying to register twice.
    ERR = []; I_ERR = {}
    i  = random.choice(range(len(eds)))
    ERR, I_ERR, _rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    assert rr[0] == DupReg
    assert indrraudit(pkS, ERR, I_ERR, rr)
    print("IndRAudit passed for DupReg receipt.")

    # Checking univaudit ERR passing (for now with alpha same as n)
    ERR = []; I_ERR = {}
    for i in range(3):
        i  = random.choice(range(len(eds)))
        ERR, _, _ = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    assert univaudit_ERR(pkS, 3, ERR, skSs)
    print("UnivAudit's ERR audit steps passed.")
    
    # Checking preparation of ER
    ERR = []; I_ERR = {}
    for i in range(3):
        i  = random.choice(range(len(eds)))
        ERR, _, _ = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    assert univaudit_prepareER(pkS, ERR, ER, pf_ER)
    print("UnivAudit's prepareER audit steps passed.")

    # Vote casting by an eligible voter.
    ERR = []; I_ERR = {}; CI = []; I_CI = {}; EV = []; I_EV = {}
    while True:
        i  = random.choice(range(len(eds)))
        p = ocapture("V%s" % i, "ctx")
        if oelg(p, eds[i]) == 1:
            break
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    assert rr[0] == AcceptReg
    rr11, rr12, rr21, rr22 = rr[1:]
    vid, ed, j, rhoenc2 = rr21
    ev = group.init(ZR, 1)   # 0 or 1 are valid votes 
    rhoev = (group.hash("sample proof", G1), "sample proof")
    ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % i, vid, ev, rhoev, skSs)
    assert cr[0] == AcceptCast
    assert indcraudit(pkS, ER, I_ER, CI, I_CI, EV, I_EV, cr, rr, skSs)
    print("IndCAudit passed for Accept receipt for an eligible voter.")

    # Vote casting by an ineligible voter.
    ERR = []; I_ERR = {}; CI = []; I_CI = {}; EV = []; I_EV = {}
    while True:
        i  = random.choice(range(len(eds)))
        p = ocapture("V%s" % i, "ctx")
        if oelg(p, eds[i]) == 0:
            break
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    assert rr[0] == AcceptReg
    rr11, rr12, rr21, rr22 = rr[1:]
    vid, ed, j, rhoenc2 = rr21
    ev = group.init(ZR, 1)   # 0 or 1 are valid votes 
    rhoev = (group.hash("sample proof", G1), "sample proof")
    ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % i, vid, ev, rhoev, skSs)
    assert cr[0] == RejectCast
    assert indcraudit(pkS, ER, I_ER, CI, I_CI, EV, I_EV, cr, rr, skSs)
    print("IndCAudit passed for Reject receipt for an ineligible voter.")

    # Vote casting by an eligible voter casting twice.
    ERR = []; I_ERR = {}; CI = []; I_CI = {}; EV = []; I_EV = {}
    while True:
        i  = random.choice(range(len(eds)))
        p = ocapture("V%s" % i, "ctx")
        if oelg(p, eds[i]) == 1:
            break
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    assert rr[0] == AcceptReg
    rr11, rr12, rr21, rr22 = rr[1:]
    vid, ed, j, rhoenc2 = rr21
    ev = group.init(ZR, 1)   # 0 or 1 are valid votes 
    rhoev = (group.hash("sample proof", G1), "sample proof")
    ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % i, vid, ev, rhoev, skSs)
    ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % i, vid, ev, rhoev, skSs)
    assert cr[0] == DupCast
    assert indcraudit(pkS, ER, I_ER, CI, I_CI, EV, I_EV, cr, rr, skSs)
    print("IndCAudit passed for DupCast receipt for an eligible voter casting twice.")

    # Vote casting by a voter using someone else's vid.
    ERR = []; I_ERR = {}; CI = []; I_CI = {}; EV = []; I_EV = {}
    i  = random.choice(range(len(eds)))
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    i2  = random.choice(range(len(eds)))
    ERR, I_ERR, _ = register(pkS, ERR, I_ERR, "V%s" % i2, uids[i], eds[i], 0, skSs)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    assert rr[0] == AcceptReg
    rr11, rr12, rr21, rr22 = rr[1:]   # using the first voter's registration receipt and hence vid
    vid, ed, j, rhoenc2 = rr21
    ev = group.init(ZR, 1)   # 0 or 1 are valid votes 
    rhoev = (group.hash("sample proof", G1), "sample proof")
    ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % i2, vid, ev, rhoev, skSs)
    assert cr[0] == RejectCast
    assert indcraudit(pkS, ER, I_ER, CI, I_CI, EV, I_EV, cr, rr, skSs)
    print("IndCAudit passed for Reject receipt for a voter using someone else's vid.")

    # Vote casting by a voter using unknown vid.
    ERR = []; I_ERR = {}; CI = []; I_CI = {}; EV = []; I_EV = {}
    i  = random.choice(range(len(eds)))
    ERR, I_ERR, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    vid = group.random(G1)
    ev = group.init(ZR, 1)   # 0 or 1 are valid votes 
    rhoev = (group.hash("sample proof", G1), "sample proof")
    ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % i, vid, ev, rhoev, skSs)
    assert cr[0] == RejectCast
    assert indcraudit(pkS, ER, I_ER, CI, I_CI, EV, I_EV, cr, rr, skSs)
    print("IndCAudit passed for Reject receipt for a voter using unknown vid.")

    # Vote casting by a voter using someone else's vid.
    ERR = []; I_ERR = {}; CI = []; I_CI = {}; EV = []; I_EV = {}
    vids = []; iis = []
    for it in range(3):   # Registration
        while True:
            i  = random.choice(range(len(eds)))
            p = ocapture("V%s" % i, "ctx")
            if oelg(p, eds[i]) == 1:
                break
        ERR, _, rr = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
        rr11, rr12, rr21, rr22 = rr[1:]
        vid, ed, j, rhoenc2 = rr21
        vids.append(vid)
        iis.append(i)
    ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)  # PrepareER
    for it in range(3):      # Casting with correct vid
        ev = group.init(ZR, 1)   # 0 or 1 are valid votes 
        rhoev = (group.hash("sample proof", G1), "sample proof")
        ER, I_ER, CI, I_CI, EV, I_EV, cr = cast(pkS, ER, I_ER, CI, I_CI, EV, I_EV, "V%s" % iis[it], vids[it], ev, rhoev, skSs)
    assert univaudit_ER(pkS, 3, ER, CI, I_CI, EV, skSs)
    print("UnivAudit's ER audit steps passed.")

def bench(n):
    
    uids, eds = envsetup(n)
    skSs, pkS = setup()

    ERR = []; I_ERR = {}
    with timer("registration"):
        for i in range(n):
            i  = random.choice(range(n))
            ERR, _, _ = register(pkS, ERR, I_ERR, "V%s" % i, uids[i], eds[i], 0, skSs)
    with timer("prepareER", report_subtimers=["mix-server 0"]):
        ER, I_ER, pf_ER = prepareER(pkS, ERR, skSs)
    with timer("univaudit_prepareER", report_subtimers=["auditor"]):
        ver_prepareER = univaudit_prepareER(pkS, ERR, ER, pf_ER)
    assert ver_prepareER

if __name__ == "__main__":
    import sys
    
    if sys.argv[1] == "test": 
        print("Testing...")
        test()
    else:
        n = int(sys.argv[2])
        print("Benchmarking for n=%s" % n)
        bench(n)