-- Original file is from M2-dev/mike/primary-decomp/jumping-cohom.m2, and
-- is part of a joint project of Anderson, Gray and Stillman
-- This file only outputs the examples, and doesn't include the experimntation in 
-- that file.  (Also, jumpingLocus here returns an ideal, and not a Sequence, as in 
-- the original file

-- Situation:
--  S = Cox ring of P^2 x P^2

invariants = method()

invariants(List, List) := (bidegree, group) -> (
     R := source group#0;
     c := symbol c;
     M := basis(bidegree, R);
     nvars := numColumns M;
     if nvars == 0 then return {};
     T := (coefficientRing R)[c_0..c_(nvars-1), generators R];
     oldvars := first entries sub(vars R, T);
     newvars := matrix{{T_0..T_(nvars-1)}};
     P := newvars * transpose sub(M, T);
     G := for g in group list map(T,T,newvars | sub(g.matrix,T));
     I := trim sum for g in G list (
	  trim ideal last coefficients(g P - P, Variables => oldvars)
	  );
     toGinvariant := map(T,T,(vars T) % I);
     Phat := toGinvariant P;
     ans := ideal last coefficients(Phat, Variables => first entries newvars);
     (sub(ans, R))_*
     )

-- The following routine is currently specialized to P^2 x P^2,
-- and the group action is specialzied to (a specific) Z/3 x Z/3.
-- Result is an ideal in a polynomial ring kk[b's, c's].
-- ASSUMPTIONS: srcdegree_0 is <= 3
--              srcdegree_1 >= 0
jumpingLocus = method()
jumpingLocus(List,List,Ring) := (srcdegree, formdegree,kk) -> (
     A := toField(kk[a]/(a^2+a+1));
     S := A[x_0..x_2, y_0..y_2, Degrees=>{3:{1,0}, 3:{0,1}}];
     sigma := map(S,S,{x_1,x_2,x_0,y_1,y_2,y_0});
     tau := map(S,S,{x_0,a*x_1,a^2*x_2,y_0,a^2*y_1,a*y_2});
     tau' := map(S,S,{x_0,a^2*x_1,a*x_2,y_0,a^2*y_1,a*y_2});
     M0 := invariants(formdegree, {sigma, tau});
     Msource := invariants({-srcdegree_0, srcdegree_1}, {sigma, tau'});
     Mtarget = invariants({-srcdegree_0 - formdegree_0, srcdegree_1 + formdegree_1},
	  {sigma, tau'});
     T := kk[b_1..b_(#Msource), c_1..c_(#M0), 
	  generators S, t_0, t_1, t_2]/(x_0*t_0-1, x_1*t_1-1, x_2*t_2-1);
     inv := map(T, S, {t_0, t_1, t_2, y_0, y_1, y_2});
     m0 := sum for i from 1 to #Msource list b_i * (inv Msource#(i-1));
     P := sum for i from 1 to #M0 list c_i * sub(M0#(i-1), T);
     Pm0 := m0*P;
     Tambient := ambient T;
     Pm0 = lift(Pm0, Tambient);
     Pm0 = sub(Pm0, {x_0 => 0, x_1 => 0, x_2 => 0});
     I := ideal for m in Mtarget list (
	  1/((size m)_kk) * contract(sub(inv m, Tambient), Pm0));
     U := kk[b_1..b_(#Msource), c_1..c_(#M0)];
     S' := kk (monoid S);
     Pparts := apply(M0, f -> sub(f, S'));
     -- once we can decompose the returned ideal, we will likely need Pparts too
     --(Pparts, sub(I,U))
     sub(I,U)
     )
end

restart
load "PD/example-jumpingcohom.m2"
kk = QQ
kk = ZZ/32003
I = jumpingLocus({-3,0},{3,3},kk) -- finishes in singular, minprimesMES .28 sec, decompose
I = jumpingLocus({-3,3},{3,3},kk) -- finishes in singular, finishes using birational maps (see below)
I = jumpingLocus({-6,0},{3,3},kk) -- finishes in singular, minprimesMES 1.5 sec, decompose takes long
     
I = jumpingLocus({-5,1},{3,3},kk)

I = jumpingLocus({-6,3},{3,3},kk) -- key one of interest BIG ENOUGH
I = jumpingLocus({-4,5},{3,3},kk)  -- doesn't finish in singular BIG ENOUGH
I = jumpingLocus({-4,2},{3,3},kk)  -- doesn't finish in singular NOT BIG ENOUGH

I = jumpingLocus({-5,1},{2,2},kk) -- finishes in minprimesMES 2.3 sec

-- ignore below, or perhaps remove this, once our decompose code is ready
C = time minprimesMES I
netList C_1
netList C_0
D = C_0/first/ contractToPolynomialRing/(i -> sub(i, ring I))
intersect D == I
time decompose I

-- example 2 above --
  I = jumpingLocus({-3,3},{3,3},kk) -- finishes in singular, finishes using birational maps
  -- notes: I is a complete intersection, degree = 16.  Therefore we only need find components that add up to degree 16
  use ring I
  I : diff(b_1, I_0) == I
  I1 = eliminate(I, b_1)
  I1 : diff(b_2, I1_1) == I1
  I2 = eliminate(I1, b_2)
  I2 : diff(b_4, I2_0) == I2
  I3 = eliminate(I2, b_4)
  codim I3 == 1
  numgens I3
  netList factors I3_0
  -- I3_0 is absolutely irreducible, and therefore I is prime
  