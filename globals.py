from math import ceil
from charm.toolbox.pairinggroup import PairingGroup, G1, G2, GT, ZR, pair

group = PairingGroup('BN254')
q = group.order()
logq = 254

def generators():
    f1, g1, h1 = [group.random(G1) for i in range(3)]
    f2 = group.random(G2)
    fT = group.random(GT)
    ef1f2 = pair(f1, f2)
    eg1f2 = pair(g1, f2)
    eh1f2 = pair(h1, f2)
    invf1 = f1 ** (-1)
    invg1 = g1 ** (-1)
    invh1 = h1 ** (-1)
    invf2 = f2 ** (-1)
    invef1f2 = ef1f2 ** (-1)
    inveg1f2 = eg1f2 ** (-1)
    inveh1f2 = eh1f2 ** (-1)
    iden = g1 ** 0
    idenT = eg1f2 ** (0)
    return (f1, g1, h1, f2, fT, ef1f2, eg1f2, eh1f2, invf1, invg1, invh1, invf2, invef1f2, inveg1f2, inveh1f2, iden, idenT)

def initgens():
    gens = generators()
    for gen in gens:
        gen.initPP()
    return gens

f1, g1, h1, f2, fT, ef1f2, eg1f2, eh1f2, invf1, invg1, invh1, invf2, invef1f2, inveg1f2, inveh1f2, iden, idenT = initgens()

# global function call depth - useful for printing 
CALLDEPTH = 0

# Parameters as per the last section of the paper "A commitment-consistent proof of a shuffle"
kappa = 2048 # equals log(N), where N is the RSA/Paillier modulus. 
kappa_e = 80 # space from which the challenge vectors are chosen
kappa_c = 80 # similar to the above (space from which a challenge is chosen)
kappa_r = 20 # soundness error slack
kappaby2 = ceil(kappa/2) # as per the Damgard-Jurik paper, this represents the space of exponent r in Enc(m;r) := (1=N)^m (h^N)^r mod N^2