-- Franzi+Frank+Mike: 2 Oct 2012
-- trying to find code to split ideals with GB's whose lead terms are pure powers.

restart
debug loadPackage("PD", Reload=>true)
load "PD/example-stewart-gough.m2"
I
C = time minprimes I;
#C#0
#C#1  -- 10 components, which we need to split further
J = first C#1#1
select(J_*, 
nonPurePowers first oo

C#1/first/(i -> # findPurePowers i == numgens i)
C#1/first/findNonlinearPurePowers 

-- Write code to split an ideal whose GB in lex has all leadterms pure powers, all not linear
J = ideal findNonlinearPurePowers first C#1#-1
purePowers = J_*
------------------------------------------------
  varsList = purePowers / leadTerm / support // flatten
  J1 = sub(J, (first varsList) => sum varsList) -- sum varsList should be somewhat random
  L1 = ideal(J1_*/numerator)
  varsList = apply(varsList, f -> sub(f, ring L1))
  facs = factors (eliminate(L1, drop(varsList,1)))_0
  facs1 = apply(facs, (mult,h) -> (mult,sub(h, (first varsList) => (first varsList) - sum drop(varsList,1)))) -- change this once we use random
       
  L = ideal(J_*/numerator)
  R = ring J
    
  G = facs1_0_1 % L
  Pi = ideal gens gb(sub(L,R) + ideal (sub(G,R)))


J = first C#1#-1
splitTower J

J = first C#1#0
splitTower J

J = first C#1#1
splitTower J

J = first C#1#2
splitTower J
netList oo

J = first C#1#3
splitTower J
netList oo

J = first C#1#9
splitTower J
netList oo
