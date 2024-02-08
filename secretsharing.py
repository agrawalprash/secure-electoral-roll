import random
from charm.toolbox.pairinggroup import ZR
from globals import group

#### Simple alpha-out-of-alpha secret sharing scheme #########################

def share(val, alpha):
    shares = [0]*alpha
    sum_shares = group.init(ZR, 0)
    for a in range(alpha-1):
        shares[a] = group.random(ZR)
        sum_shares = sum_shares + shares[a]
    shares[alpha-1] = val - sum_shares
    return shares

def reconstruct(shares):
    val = group.init(ZR, 0)
    for share in shares:
        val = val + share
    return val

#### Simple 2-by-2 secret sharing scheme for the ZR group ####################

def share2_2(vals):
    share1s, share2s = [], []
    for val in vals:
        share1 = group.random(ZR)
        share2 = val - share1
        share1s.append(share1)
        share2s.append(share2)
    return share1s, share2s

def reconstruct2_2(share1s, share2s):
    vals = []
    for i in range(len(share1s)):
        share1 = share1s[i]
        share2 = share2s[i]
        val = share1 + share2
        vals.append(val)
    return vals