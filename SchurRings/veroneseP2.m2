needsPackage"SchurRings"
S = schurRing(QQ,s,k)
T = schurRing(S,t,1)

recsyz = method()
recsyz (Thing) := (el) -> min(el,0)
recsyz (RingElement) := (el) ->
(
     T := ring el;
     listForm el/((u,v)->T_u*recsyz(v))//sum
     )

aS = schurRing(QQ,s,10)
aR = symmetricRingOf aS

parn = (partitions d)/(i->toList i)
m = matrix{apply(parn,i->i/(j->h_j)//product)}
Mat = transpose matrix{apply(parn,i->toH s_i)}
ikost = lift(contract(Mat,m),QQ)

ind = select(for i from 0 to #parn-1 list if #(parn#i)<=k then i,j->j=!=null)
pars = select(parn,i->#i<=k)

aQ = schurRing(QQ,q,k)
subkost = ikost^ind_ind
qmat = matrix{pars/(i->q_i)}
mpols = flatten entries (qmat * subkost)
mpols = drop(mpols,1)
aT = schurRing(aQ,t,1)

--time 
factors = for pol in mpols list
(
     di = lift(dim(pol),ZZ);
     sq = splice{k:di*d//k};
     rez = 1_aT + (-1)^di*t_{di}*q_(sq);
     rez = rez + sum for i from 1 to di//2 list 
     (
	  ePow = exteriorPower(i,pol);
	  if i!=di-i then 
	  (
	       transp = listForm(ePow)/(i->i#1*q_(reverse select(sq-(i#0|splice{k-#(i#0):0}),j->j!=0)))//sum;
	       (-1)^i*t_{i}*ePow + (-1)^(di-i)*t_{di-i}*transp
	       )
	  else (-1)^i*t_{i}*ePow
	  );
     rez
     );

--end
--time 
genfun = product factors

listForm genfun
wedpowers = (listForm genfun)/(i->lift(last i,aQ))//reverse
wedpowers = wedpowers/(i->toS(i,S))

p1 = 1 + sum for i from 1 to #wedpowers-1 list wedpowers#i * T_{i}

--compute last factor
A = QQ[x]
cyclo = x^d-1
for i from 1 to d-1 do if d%i == 0 then
     cyclo = cyclo // gcd(cyclo,x^i-1)
B = A/ideal(cyclo)

SS = schurRing(B,ss,k)
TS = schurRing(SS,ts,1)

pol = sum for i from 0 to d-1 list
(
     x^(i*(d-r)) * (product for j from 0 to d-1 list
     	  if j == i then 1 else
	     1 + sum for p from 1 to k list (-1)^p*x^(j*p)*SS_(splice{p:1})*TS_p)
     )       
pol = pol/d
pol = (listForm pol)/(i->(try(TS_(i#0#0//d)) else 1_TS)*(last i))//sum
--
p2 = toS(pol,T)

{*
p2 = 1 + sum for i from 1 to k-1 list
(
     subs = subsets(k-1,i);
     sum for ind in subs list
     (
	  conj = new Partition from (reverse(ind) - reverse(subs#0) + splice({i:1}));
	  (-1)^(sum ind)*S_((for j from 0 to i-1 list d-ind#j+j-1) | toList(conjugate conj))
	  ) * (-1)^(i-1) * T_{i}
     )
*}
reso = p1*p2

a = binomial(d+2,2)-3
b = 2
koz = new MutableList from for i from 0 to a list new MutableList from {0,0,0}
rev = reverse listForm reso
maxq0 = binomial(r+2,2)-1
minq2 = binomial(d+2,2)-binomial(d-r-1,2)-2
for syzy in rev do
(
     deg := sum (first syzy);
     rep := (-1)^deg * (last syzy);
     reppos := rep - recsyz(rep);
     repneg := reppos - rep;
     if repneg != 0 then koz#(deg-1)#1 = repneg;
     if deg <= maxq0 then koz#deg#0 = reppos
     else if deg >= minq2 then koz#(deg-2)#2 = reppos
     else if reppos != 0 then error"Something's wrong...";
     )
end
--q = 0
if d<r+1 then print("The following don't satisfy d>=b+q+1")
print(koz#(binomial(r+2,2)-1)#0," is nonzero")
print(koz#(binomial(r+2,2))#0," is zero")

--q = 1
if d<r+2 then print("The following don't satisfy d>=b+q+1")
print(koz#r#1," is zero")
print(koz#(r+1)#1," is nonzero")

print(try(koz#(binomial(d+1,2)+r)#1) else 0," is nonzero")
print(try(koz#(binomial(d+1,2)+r+1)#1) else 0," is zero")

--q = 2
if d<r+3 then print("The following don't satisfy d>=b+q+1")
print(koz#((r+3)*d-2-binomial(r+2,2))#2," is zero")
print(try(koz#((r+3)*d-1-binomial(r+2,2))#2) else 0," is nonzero")

print(koz#(binomial(d+2,2)-3)#2," is nonzero")
--koz#(binomial(d+2,2)-1-binomial(d-r-1,2)-2)#2 --zero
--koz#(binomial(d+2,2)-binomial(d-r-1,2)-2)#2 --nonzero
--mat = matrix(toList \ toList koz)
end

----------------------------------
----------------------------------
----------------------------------
----------------------------------
----------------------------------
----------------------------------

restart
d = 8 --d-th Veronese embedding
k = 3 --dim(V) = k (should be 3), called n in Ein-Lazarsfeld
r = 1 --twist of structure sheaf, called b in Ein-Lazarsfeld
time load"veroneseP2.m2"
time mat = matrix(toList koz / (i -> (toList i / (j-> if j != 0 then dim j else 0))));
mat


koz#10#1

{*for i from 1 to #factors do
(
     print(toString(pars#i)|"\n");
     print(factors#(i-1));
     print("\n");
     )*}

R = symmetricRingOf S
QQ[z_1,z_2,z_3]

g = method()
g(RingElement) := relt -> sub(toE relt,{e_1 => z_1+z_2+z_3, e_2 => z_1*z_2 + z_1*z_3 + z_2*z_3, e_3 => z_1*z_2*z_3, h_1 => 0, h_2 => 0, h_3 => 0, p_1 => 0, p_2 => 0, p_3 => 0})

g \ listForm(factors#0)/(i->toS(last i,S))
factor \ g \ listForm(p2)/(i->toS(last i,S))
sum oo
factor oo
