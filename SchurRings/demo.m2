restart
loadPackage"SchurRings"

----------------------------------------------------------------------------
---The number of lines in P^3 intersecting 4 generic lines------------------
----------------------------------------------------------------------------
S = schurRing(s,4)
m = s_1^4
sum (select(listForm m, i-> (f = first i; #f <= 2 and f#0 <= 2)) / (j -> S_(first j) * last j))

----------------------------------------------------------------------------
---The Koszul complex-------------------------------------------------------
----------------------------------------------------------------------------

---Over GL
S = schurRing(s,4,GroupActing => "GL")
rep = s_1
M = {1_S}
d = 5
sR = schurResolution(rep,M,d)

---Over GL x S_n
S = schurRing(s,3,GroupActing => "Sn")
T = schurRing(S,t,2)
rep = (s_3 + s_{2,1}) * t_1
M = {s_3 * 1_T}
d = 7
sR = schurResolution(rep,M,d)
exteriorPower(3,rep)
sR#3

----------------------------------------------------------------------------
---Square-free, S_n-invariant monomial ideals-------------------------------
----------------------------------------------------------------------------
S = schurRing(QQ,s,5,GroupActing => "Sn");
rep = s_5 + s_{4,1};
M = {s_5} | splice{5:rep}
sR = schurResolution(rep,M)

----------------------------------------------------------------------------
---Minors of generic matrices (secants of Segre varieties)------------------
----------------------------------------------------------------------------
S = schurRing(s,3)
T = schurRing(S,t,4)
rep = s_1 * t_1

--2x2 minors
M = {1_T} | apply(splice{1..8},i -> s_i * t_i)
schurResolution(rep,M)

--3x3 minors
M = {1_T} | apply(splice{1..5},i -> sum(apply(toList \ select(partitions i, j -> #j <=2), par -> S_par * T_par)))
schurResolution(rep,M)

----------------------------------------------------------------------------
---Equivariant resolution of Veronese variety (or twists of its ideal sheaf)
----------------------------------------------------------------------------
d = 8 --d-th Veronese embedding
k = 3 --dim(V) = k (should be 3)
r = 0 --twist of structure sheaf
time load"veroneseP2.m2"
time mat = matrix(toList koz / (i -> (toList i / (j-> if j != 0 then dim j else 0))))
koz#(3*d-2)#2
koz#(3*d-3)#2