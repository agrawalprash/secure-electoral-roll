# Following the proof of shuffle ideas in the following papers:
# 1. D. Wikstrom, "A commitment-consistent proof of a shuffle", ACISP 2009, https://eprint.iacr.org/2011/168.pdf
# 2. B. Terelius, D. Wikstrom, "Proofs of restricted shuffles", AFRICACRYPT 2010, https://www.csc.kth.se/~dog/research/papers/TW10Conf.pdf
# 3. I. Damgard, M. Jurik, "A generalization of Paillier's public key system with applications to electronic voting", Intl. J. of Information Security, 2010, https://link.springer.com/content/pdf/10.1007/s10207-010-0119-9.pdf?pdf=inline%20link

from math import ceil
from copy import copy
import random

from charm.toolbox.pairinggroup import ZR, G1
import gmpy2

from globals import group, g1, h1, iden, kappa_e
from perm import gen_rand_perm, permute
from elgamal import elgamal_th_keygen, elgamal_encrypt, elgamal_reencrypt

# Random state for the gmpy2 random operations
rs = gmpy2.random_state(random.randint(0,100000))

#### Utilities ############################################################################

def commkey(n):
    # Ensuring we generate at least two generators because the generating set of the Paillier 
    # ciphertext is of size 2. Protocol 15 of the first paper above (step 2) then requires that 
    # the commitment key must support at least two elements. 
    return n, h1, [group.random(G1) for i in range(max(n,2))]

def commit_vector(ck, vs, s):
    n, h1, gs = ck
    res = h1 ** group.init(ZR, int(s))
    for i in range(len(vs)):
        res *= gs[i] ** (group.init(ZR, int(vs[i])))
    return res

def commit_matrix(ck, M, svec):
    return [commit_vector(ck, M[i], svec[i]) for i in range(len(M))]

def commit_perm(ck, repi, svec):
    """ Use the above matrix formulation to commit to a *permutation matrix*, but much more efficiently.
    
    The input is the inverse of the permutation one wants to commit, aka the "reverse permutation."
    """
    n, h1, gs = ck
    return [(h1 ** svec[i]) * gs[repi[i]] for i in range(n)]

def permmat(pi, n):
    """ Obtain an nxn matrix representation of a permutation pi such that M[e_1, ..., e_n] = [e_{pi(1)}, ..., e_{pi(n)}]. """
    M = []
    for i in range(n):
        M.append([])
        for j in range(n):
            M[-1].append(0)
    for i in range(n):
        M[i][pi[i]] = 1
    return M

def applyperm(evec, pi):
    """ Apply a given permutation function pi to the given list evec to obtain a new list evecdash. """
    return [evec[pi[i]] for i in range(len(evec))]

def dot(u, v, mod=None):
    """ Given vectors u:=(u1,...,un) and v:=(v1,...,vn), compute their dot product u1v1 + ... + unvn. 
    
    If `mod' is not None, it is interpreted as the modulus under which the operation is to be performed.
    """
    if mod is None:
        return sum(u[i]*v[i] for i in range(len(u)))
    else:
        res = gmpy2.t_mod(u[0] * v[0], mod)
        for i in range(1, len(u)):
            res = gmpy2.t_mod(res + u[i]*v[i], mod)
    return res

def expprod(basevec, expvec, mod=None):
    """ Given base vector (b1,...,bk) and exponent vector (e1,...,ek), compute the product b1^e1...bk^ek. 
    
    The optional argument `mod' is used to specify the modulus of exponentiation (only to be specified 
    when the exponentiation operation is to be performed by gmp). 
    """

    if mod is None:
        res = basevec[0] ** expvec[0]
        for i in range(1, len(basevec)):
            res *= basevec[i] ** expvec[i]
    else:
        res = gmpy2.powmod(basevec[0], gmpy2.mpz(expvec[0]), mod)
        for i in range(1, len(basevec)):
            res = gmpy2.t_mod(res * gmpy2.powmod(basevec[i], gmpy2.mpz(expvec[i]), mod), mod)
    return res

#### PoK of the opening of a permutation matrix commitment ########################

def compute_perm_nizkproof(ck, evec, _pi, _svec):
    n, h1, gs = ck
    t = sum(_svec)
    edashvec = applyperm(evec, _pi)
    sdashvec = [group.random(ZR) for i in range(n)]
    k = dot(_svec, evec)
    B = [(h1 ** sdashvec[0]) * (g1 ** edashvec[0])]
    for i in range(1, n):
        B.append((h1 ** sdashvec[i]) * (B[i-1] ** edashvec[i]))
    w = sdashvec[0]
    for i in range(1,n):
        w = sdashvec[i] + w*edashvec[i]
    return B, t, k, edashvec, sdashvec, w

def commitmsg_perm_nizkproof(ck, B):
    n, h1, gs = ck
    rt = group.random(ZR)
    rk = group.random(ZR)
    redash, rsdash = [], []
    for i in range(n):
        redash.append(group.random(ZR))
        rsdash.append(group.random(ZR))
    rw = group.random(ZR)
    C1 = h1 ** rt
    C2 = h1 ** rk
    for i in range(n):
        C2 *= gs[i] ** redash[i]
    CB = [(h1 ** rsdash[0]) * (g1 ** redash[0])]
    for i in range(1,n):
        CB.append((h1 ** rsdash[i]) * (B[i-1] ** redash[i]))
    CU = h1 ** rw
    return C1, C2, CB, CU, rt, rk, redash, rsdash, rw

def respmsg_perm_nizkproof(ck, t, k, edashvec, sdashvec, w, rt, rk, redash, rsdash, rw, c):
    n, h1, gs = ck
    zt = rt - t*c
    zk = rk - k*c
    zedash, zsdash = [], []
    for i in range(n):
        zedash.append(redash[i] - edashvec[i]*c)
        zsdash.append(rsdash[i] - sdashvec[i]*c)
    zw = rw - w*c
    return zt, zk, zedash, zsdash, zw

def lhs_perm_nizkverif(ck, a, evec, B):
    n, h1, gs = ck
    LC1 = group.init(G1, iden)
    A = group.init(G1, iden)
    GS = group.init(G1, iden)
    for i in range(n):
        A *= a[i]
        GS *= gs[i]
    LC1 = A * (GS ** (-1))
    LC2 = group.init(G1, iden)
    for i in range(n):
        LC2 *= a[i] ** evec[i]
    LB = B
    LW = LB[-1]
    eprod = group.init(ZR, 1)
    for i in range(n):
        eprod *= evec[i]
    LW *= g1 ** (-eprod)
    return LC1, LC2, LB, LW

def rhs_perm_nizkverif(ck, B, zt, zk, zedash, zsdash, zw):
    n, h1, gs = ck
    ZC1 = h1 ** zt
    ZC2 = h1 ** zk
    for i in range(n):
        ZC2 *= gs[i] ** zedash[i]
    ZB = [(h1 ** zsdash[0]) * (g1 ** zedash[0])]
    for i in range(1, n):
        ZB.append((h1 ** zsdash[i]) * (B[i-1] ** zedash[i]))
    ZW = h1 ** zw
    return ZC1, ZC2, ZB, ZW

def perm_nizkproof(ck, a, evec, _pi, _svec):
    """ Proof of knowledge of the opening of a permutation matrix commitment (see protocol 1
    of paper 2 above): 
    
    PK{(t, k, (e1',...,en')): 
        h1^t gs1^1 ... gsn^1 = a1^1 ... an^1 AND 
        h1^k gs1^e1' ... gsn^en' = a1^e1 ... an^en AND
        e1' ... en' = e1 ... en 
    }

    which can be proved as:

    PK{(t, k, (e1',...,en'), (s1',...,sn'), w): 
        (a1 ... an)/(gs1 ... gsn) = h1^t                     AND 
        a1^e1 ... an^en           = h1^k gs1^e1' ... gsn^en' AND
        b1                        = h1^s1' g1^e1'            AND 
        b2                        = h1^s2' b1^e2'            AND 
        ...                                                  AND 
        bn                        = h1^sn' (bn-1)^en'        AND
        bn/(g1^(e1...en))         = h1^w 
    }

    where (e1,...,en) are supplied by the verifier,
          a = (h1^s1, gs_{piinv(1)},...,h1^sn, gs_{piinv(n)}), 
          t = dot((1,...,1), (s1,...,sn)) = sum((s1,...,sn))
          k = dot((s1,...,sn),(e1,...,en)),
          (e1',...,en') = (e_{pi(1)},...,e_{pi(n)}),
          (s1',...,sn') <-$-- Zq
          w = sn'+(...s3'+(s2'+s1'e1'e2')e3'...)en' 

    Note that unlike the original paper, the permutation here is expressed as a function rather
    than as a matrix, but this does not affect the proof at all since the proof only depends on 
    a list obtained by *applying* the permutation to an input list.
    """

    # Compute
    evec = [group.init(ZR, int(e)) for e in evec]
    B, t, k, edashvec, sdashvec, w = compute_perm_nizkproof(ck, evec, _pi, _svec)

    # Commit
    C1, C2, CB, CU, rt, rk, redash, rsdash, rw = commitmsg_perm_nizkproof(ck, B)

    # Challenge
    c = group.hash((a, evec) + (C1, C2) + tuple(CB) + (CU, ), type=ZR)

    # Response
    zt, zk, zedash, zsdash, zw = respmsg_perm_nizkproof(ck, t, k, edashvec, sdashvec, w, rt, rk, redash, rsdash, rw, c)

    return B, c, zt, zk, zedash, zsdash, zw

def perm_nizkverif(ck, a, evec, pf):
    """ Verify the proof of knowledge of the opening of a permutation matrix commitment.
    
    Recall the POK:

    PK{(t, k, (e1',...,en'), (s1',...,sn'), w): 
        (a1 ... an)/(gs1 ... gsn) = h1^t AND 
        a1^e1 ... an^en = h1^k gs1^e1' ... gsn^en' AND
        b1 = h1^s1' g1^e1' AND b2 = h1^s2' b1^e2' AND .... AND bn = h1^sn' (bn-1)^en' AND
        bn/(g1^(e1...en)) = h1^w 
    }
    """
    n, h1, gs = ck
    B, c, zt, zk, zedash, zsdash, zw = pf

    # LHS of the equation
    evec = [group.init(ZR, int(e)) for e in evec]
    LC1, LC2, LB, LW = lhs_perm_nizkverif(ck, a, evec, B)

    # RHS of the equation, but evaluated using the z-values received from the prover
    ZC1, ZC2, ZB, ZW = rhs_perm_nizkverif(ck, B, zt, zk, zedash, zsdash, zw)

    verif = (
        ((LC1 ** c) * ZC1, 
         (LC2 ** c) * ZC2) + 
        tuple([(LB[i] ** c) * ZB[i] for i in range(n)]) + 
        ((LW ** c) * ZW, )
    )

    return c == group.hash((a,evec) + verif, type=ZR)

#### Proof of an El Gamal shuffle ################################################################

def shuffle_elgamal_nizkproof(ck, elgpk, cinvec, coutvec, permcomm, evec, _pi, _svec, _rvec):
    """ Proof that coutvec is a permutation and re-encryption of cinvec under the El Gamal 
    encryption scheme (protocol 3 of paper 2 above): 
    
    PK{(t, k, (e1',...,en'), (s1',...,sn'), w, u): 
        // PoK of the opening of a permutation matrix commitment (see function perm_nizkproof)
        (permcomm1 ... permcommn)/(gs1 ... gsn) = h1^t AND 
        permcomm1^e1 ... permcommn^en = h1^k gs1^e1' ... gsn^en' AND
        b1 = h1^s1' g1^e1' AND b2 = h1^s2' b1^e2' AND .... AND bn = h1^sn' (bn-1)^en' AND
        bn/(g1^(e1...en)) = h1^w

        // PoK that ElGamal ciphertexts are re-encrypted and permuted under the committed permutation: c1^e1'...cn^en' = c1^e1...cn^en E(1,u) 
        c1[0]^e1...cn[0]^en = (g1^(-u) c1'[0]^e1' ... cn'[0]^en') AND  // El Gamal ciphertext's first component
        c1[1]^e1...cn[1]^en = (elgpk^(-u) c1'[1]^e1' ... cn'[1]^en')   // El Gamal ciphertext's second component
    }
    """
    _elgpk, _elgpklist = elgpk

    # Compute
    n, h1, gs = ck
    evec = [group.init(ZR, int(e)) for e in evec]
    B, t, k, edashvec, sdashvec, w = compute_perm_nizkproof(ck, evec, _pi, _svec)
    u = dot(_rvec, evec)

    # Commit
    C1, C2, CB, CU, rt, rk, redash, rsdash, rw = commitmsg_perm_nizkproof(ck, B)
    ru = group.random(ZR)
    CC = (g1 ** (-ru), _elgpk ** (-ru))
    for i in range(n):
        CC = (CC[0] * (coutvec[i][0] ** redash[i]), CC[1] * (coutvec[i][1] ** redash[i]))

    # Challenge
    c = group.hash((cinvec, coutvec, permcomm, evec) + (C1, C2) + tuple(CB) + (CU, ) + CC, type=ZR)

    # Response
    zt, zk, zedash, zsdash, zw = respmsg_perm_nizkproof(ck, t, k, edashvec, sdashvec, w, rt, rk, redash, rsdash, rw, c)
    zu = ru - u*c

    return B, c, zt, zk, zedash, zsdash, zw, zu

def shuffle_elgamal_nizkverif(ck, elgpk, cinvec, coutvec, permcomm, evec, pf):
    """ Verify the proof that coutvec is a permutation and re-encryption of cinvec under the 
    El Gamal encryption scheme.
    
    Recall the POK:

    PK{(t, k, (e1',...,en'), (s1',...,sn'), w, u): 
        // PoK of the opening of a permutation matrix commitment (see function perm_nizkproof)
        (permcomm1 ... permcommn)/(gs1 ... gsn) = h1^t AND 
        permcomm1^e1 ... permcommn^en = h1^k gs1^e1' ... gsn^en' AND
        b1 = h1^s1' g1^e1' AND b2 = h1^s2' b1^e2' AND .... AND bn = h1^sn' (bn-1)^en' AND
        bn/(g1^(e1...en)) = h1^w

        // PoK that ElGamal ciphertexts are re-encrypted and permuted under the committed permutation: c1^e1'...cn^en' = c1^e1...cn^en E(1,u) 
        c1[0]^e1...cn[0]^en = (g1^(-u) c1'[0]^e1' ... cn'[0]^en') AND  // El Gamal ciphertext's first component
        c1[1]^e1...cn[1]^en = (elgpk^(-u) c1'[1]^e1' ... cn'[1]^en')   // El Gamal ciphertext's second component
    }
    """
    _elgpk, _elgpklist = elgpk

    n, h1, gs = ck
    B, c, zt, zk, zedash, zsdash, zw, zu = pf

    # LHS of the equation
    evec = [group.init(ZR, int(e)) for e in evec]
    LC1, LC2, LB, LW = lhs_perm_nizkverif(ck, permcomm, evec, B)
    LCC1, LCC2 = group.init(G1, iden), group.init(G1, iden)  # Note that x = group.init(G1, iden) gives an identity element whereas x = iden does not!
    for i in range(n):
        LCC1 *= (cinvec[i][0] ** evec[i])
        LCC2 *= (cinvec[i][1] ** evec[i])

    # RHS of the equation, but evaluated using the z-values received from the prover
    ZC1, ZC2, ZB, ZW = rhs_perm_nizkverif(ck, B, zt, zk, zedash, zsdash, zw)
    ZCC1, ZCC2 = (g1 ** (-zu), _elgpk ** (-zu))
    for i in range(n):
        ZCC1 *= coutvec[i][0] ** zedash[i]
        ZCC2 *= coutvec[i][1] ** zedash[i]

    verif = (
        ((LC1 ** c) * ZC1, 
         (LC2 ** c) * ZC2) + 
        tuple([(LB[i] ** c) * ZB[i] for i in range(n)]) + 
        ((LW ** c) * ZW, ) +
        ((LCC1 ** c) * ZCC1, (LCC2 ** c) * ZCC2)
    )

    return c == group.hash((cinvec, coutvec, permcomm, evec) + verif, type=ZR)

#### Consistent shuffle of multiple lists #######################################

def shuffle_mult(pk, cinvecs, _pi):
    """ Permute and re-encrypt multiple lists of El Gamal ciphertexts under 
    the same permutation _pi. """

    coutvecs, _rvecs = [], []
    for cinvec in cinvecs:
        coutdashvec = applyperm(cinvec, _pi)
        _rvec = [group.random(ZR) for i in range(len(cinvec))]
        _rdashvec = applyperm(_rvec, _pi)
        coutvec = [elgamal_reencrypt(pk, coutdashvec[i], randIn=_rdashvec[i]) for i in range(len(coutdashvec))]
        coutvecs.append(coutvec)
        _rvecs.append(_rvec)
    return coutvecs, _rvecs

def pf_shuffle_mult(pk, cinvecs, coutvecs, _pi, _repi, _rvecs):
    """ Generate proof of consistent shuffle of multiple ciphertext lists. """
    
    # Commit to the permutation pi
    n = len(_pi)
    ck = commkey(n)
    _svec = [group.random(ZR) for i in range(n)]
    permcomm = commit_perm(ck, _repi, _svec)

    # Compute challenge (actually this step is to be done by the verifier)
    evec = [gmpy2.mpz_urandomb(rs, kappa_e) for i in range(n)]

    # Proof of knowledge of the opening of a permutation commitment
    comm_pf = perm_nizkproof(ck, permcomm, evec, _pi, _svec)

    # Proofs of shuffles consistent with the committed permutation
    shuffle_pfs = []
    for l in range(len(cinvecs)):
        cinvec, coutvec, _rvec = cinvecs[l], coutvecs[l], _rvecs[l]
        shuffle_pf = shuffle_elgamal_nizkproof(ck, pk, cinvec, coutvec, permcomm, evec, _pi, _svec, _rvec)
        shuffle_pfs.append(shuffle_pf)

    return ck, permcomm, evec, comm_pf, shuffle_pfs

def pf_shuffle_mult_verif(pk, cinvecs, coutvecs, pf):
    ck, permcomm, evec, comm_pf, shuffle_pfs = pf
    status = perm_nizkverif(ck, permcomm, evec, comm_pf)

    for l in range(len(cinvecs)):
        cinvec, coutvec, shuffle_pf = cinvecs[l], coutvecs[l], shuffle_pfs[l]
        status = status and shuffle_elgamal_nizkverif(ck, pk, cinvec, coutvec, permcomm, evec, shuffle_pf)

    return status

if __name__ == "__main__":
    # Generate cinvecs and coutvecs shuffling cinvecs
    n = 100
    _sklist, pk_ = elgamal_th_keygen(4)
    _mvec1 = [group.random(G1) for i in range(n)]
    _mvec2 = [group.random(G1) for i in range(n)]
    cinvec1 = [elgamal_encrypt(pk_, _mvec1[i]) for i in range(n)]
    cinvec2 = [elgamal_encrypt(pk_, _mvec2[i]) for i in range(n)]
    cinvecs = [cinvec1, cinvec2]
    _pi, _repi = gen_rand_perm(n)
    coutvecs, _rvecs = shuffle_mult(pk_, cinvecs, _pi)

    # Prove that the shuffle was consistently done under a common permutation
    pf = pf_shuffle_mult(pk_, cinvecs, coutvecs, _pi, _repi, _rvecs)
    print("pf_shuffle_mult_verif:", pf_shuffle_mult_verif(pk_, cinvecs, coutvecs, pf))