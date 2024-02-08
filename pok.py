from charm.toolbox.pairinggroup import ZR

from globals import group, g1, h1

#### PoK of correct Elgamal encryption. ######################################
# Given El Gamal public key pk, a ciphertext c:=(c0,c1)=(g1^r,m.h1^r), a 
# plaintext m, this protocol proves the knowledge of r:
#    PK{(r): c0 = g1^r and c1/m = h1^r}
##############################################################################

def pk_elg_enc(pk_, ciph, m, _r):
    ciph0, ciph1 = ciph
    pk, pklist = pk_
    stmt = (pk, ciph0, ciph1, m)

    # Commit
    _rr = group.random(ZR)
    a0 = (g1 ** _rr)
    a1 = (pk ** _rr)

    # Challenge
    c = group.hash(stmt + (a0, a1), type=ZR)

    # Response
    z = _rr - _r*c

    return c, z

def pk_elg_enc_verif(pk_, ciph, m, pf):
    ciph0, ciph1 = ciph
    pk, pklist = pk_
    stmt = (pk, ciph0, ciph1, m)
    (c,z) = pf

    verif0 = (g1 ** z) * (ciph0 ** c)
    verif1 = (pk ** z) * ((ciph1 * (m ** (-1))) ** c)
    # import pdb; pdb.set_trace()

    return c == group.hash(stmt + (verif0, verif1), type=ZR)

#### PoK of correct El Gamal decryption share ################################
# Given El Gamal public key pk = prod_{k=1}^{kappa} pkk, where pkk = g1^(skk), 
# a ciphertext c:=(c0,c1) and partial decryption mk = c0^{skk}, this protocol
# proves the following:
#    PK{(skk): pkk = g1^{skk} and mk = c0^{skk}}
##############################################################################

def pk_elg_dec_share(pk_, ciph, mk, k, _skk):
    ciph0, ciph1 = ciph
    pk, pklist = pk_
    stmt = (pk, ciph0, ciph1, mk, k)

    # Commit
    _rskk = group.random(ZR)
    apkk = (g1 ** _rskk)
    amk =  (ciph0 ** _rskk)

    # Challenge
    c = group.hash(stmt + (apkk, amk), type=ZR)

    # Response
    z = _rskk - _skk * c

    return c, z

def pk_elg_dec_share_verif(pk_, ciph, mk, k, pf):
    ciph0, ciph1 = ciph
    pk, pklist = pk_
    stmt = (pk, ciph0, ciph1, mk, k)
    (c,z) = pf

    verifpkk = (g1 ** z) * (pklist[k] ** c)
    verifmk = (ciph0 ** z) * (mk ** c)

    return c == group.hash(stmt + (verifpkk, verifmk), type=ZR)

#### PoK of plaintext equality of two El Gamal ciohertexts ###################
# Given El Gamal public key pk, and ciphertexts c0:=(c00,c01)=(g1^r0, m.h1^r0) 
# and c1:=(c10, c11)=(g1^r1, m.h1^r1), this protocol proves the following:
#     PK{(r): c00/c10 = g1^r and c01/c11 = h1^r}                   # r:= r0-r1
##############################################################################

def pk_elg_eq(pk_, ciph0, ciph1, _r0, _r1):
    ciph00, ciph01 = ciph0
    ciph10, ciph11 = ciph1
    pk, pklist = pk_
    stmt = (pk, ciph00, ciph01, ciph10, ciph11)

    # Commit
    _rr = group.random(ZR)
    a0 = g1 ** _rr
    a1 = pk ** _rr

    # Challenge
    c = group.hash(stmt + (a0, a1), type=ZR)

    # Response
    z = _rr - (_r0 - _r1) * c

    return c, z

def pk_elg_eq_verif(pk_, ciph0, ciph1, pf):
    ciph00, ciph01 = ciph0
    ciph10, ciph11 = ciph1
    pk, pklist = pk_
    stmt = (pk, ciph00, ciph01, ciph10, ciph11)
    c, z = pf

    verif0 = (g1 ** z) * ((ciph00/ciph10) ** c)
    verif1 = (pk ** z) * ((ciph01/ciph11) ** c)

    return c == group.hash(stmt + (verif0, verif1), type=ZR)

##############################################################################

if __name__ == "__main__":
    from charm.toolbox.pairinggroup import G1
    from elgamal import elgamal_th_keygen, elgamal_encrypt, elgamal_share_decrypt

    #### Testing proof of correct encryption #####
    _sklist, pk_ = elgamal_th_keygen(4)
    m = group.random(G1)
    ciph, _r = elgamal_encrypt(pk_, m, randOut=True)
    pf = pk_elg_enc(pk_, ciph, m, _r)
    print("pk_elg_enc_verif: ", pk_elg_enc_verif(pk_, ciph, m, pf))

    #### Testing proof of correct decryption share #####
    k = 2
    mk = elgamal_share_decrypt(pk_, ciph, _sklist[k])
    pf = pk_elg_dec_share(pk_, ciph, mk, k, _sklist[k])
    print("pk_elg_dec_share_verif: ", pk_elg_dec_share_verif(pk_, ciph, mk, k, pf))

    #### Testing proof of plaintext equality #####
    ciph0, _r0 = elgamal_encrypt(pk_, m, randOut=True)
    ciph1, _r1 = elgamal_encrypt(pk_, m, randOut=True)
    pf = pk_elg_eq(pk_, ciph0, ciph1, _r0, _r1)
    print("pk_elg_eq_verif: ", pk_elg_eq_verif(pk_, ciph0, ciph1, pf))