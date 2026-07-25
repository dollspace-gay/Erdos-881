def cantor(Y):
    out=[]
    for n in range(Y+1):
        m,ok=n,True
        while m:
            if m%3==2: ok=False; break
            m//=3
        if ok: out.append(n)
    return out

def b3(n):
    if n==0: return '0'
    s=''
    while n: s=str(n%3)+s; n//=3
    return s

for Y in (200, 2000, 20000):
    A=set(cantor(Y))
    best=(0,0)
    for v in range(Y+1):
        r=sum(1 for x in A if x<=v and (v-x) in A)
        if r>best[0]: best=(r,v)
    print(f"Y={Y:6d} max r2={best[0]:4d} at v={best[1]:6d} (base3={b3(best[1])})")
