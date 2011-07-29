-- -*- coding: utf-8 -*-
newPackage(
	"ChernSegre",
    	Version => "0.1", 
    	Date => "July 25, 2011",
    	Authors => {{Name => "Christine Jost", 
		  Email => "jost@math.su.se", 
		  HomePage => "http://www.math.su.se/~jost"}},
    	Headline => "Computations of degrees of Chern and Segre classes of projective schemes",
    	DebuggingMode => true
    	)


export {segreClass}
segreClass = method(TypicalValue => RingElement);
segreClass Ideal := I -> (     
     checkUserInput I; 
     I = prepare I;
     (s,ambientDim) := internalSegre I;
     out := output (s,ambientDim);
     return out
     )
segreClass (Ideal, Symbol) := (I,H) -> (
     checkUserInput I;
     I = prepare I;
     (s, ambientDim) := internalSegre I;
     out := output (s, ambientDim, H);
     return out
     )
segreClass ProjectiveVariety := P -> (
     I := P.ring.ideal;
     checkUserInput I; 
     I = prepare I;
     (s,ambientDim) := internalSegre I;
     out := output (s,ambientDim);
     return out
     )
segreClass (ProjectiveVariety,Symbol) := (P,H) -> (
     I := P.ring.ideal;
     checkUserInput I;
     I = prepare I;
     (s, ambientDim) := internalSegre I;
     out := output (s, ambientDim, H);
     return out
     )
     

     


export {segreClassList}
segreClassList = method(TypicalValue => List);
segreClassList Ideal := I -> (
     checkUserInput I;
     I = prepare I;
     (s,ambientDim) := internalSegre I;
     return s
     )
segreClassList ProjectiveVariety := P -> (
     I := P.ring.ideal;
     checkUserInput I;
     I = prepare I;
     (s,ambientDim) := internalSegre I;
     return s
     )



export {chernClass}
chernClass = method(TypicalValue => RingElement);
chernClass Ideal := I -> (
     checkUserInput I; 
     I = prepare I;
     (c,ambientDim) := internalChern I;
     out := output (c,ambientDim);
     return out
     )
chernClass (Ideal, Symbol) := (I,H) -> (
     checkUserInput I;
     I = prepare I;
     (c, ambientDim) := internalChern I;
     out := output (c, ambientDim, H);
     return out;
     )
chernClass ProjectiveVariety := P -> (
     I := P.ring.ideal;
     checkUserInput I; 
     I = prepare I;
     (c,ambientDim) := internalChern I;
     out := output (c,ambientDim);
     return out
     )
chernClass (ProjectiveVariety, Symbol) := (P,H) -> (
     I := P.ring.ideal;
     checkUserInput I;
     I = prepare I;
     (c, ambientDim) := internalChern I;
     out := output (c, ambientDim, H);
     return out;
     )



export {chernClassList}
chernClassList = method(TypicalValue => List);
chernClassList Ideal := I -> (
     checkUserInput I;
     I = prepare I;
     (c,ambientDim) := internalChern I;
     return c
     )
chernClassList ProjectiveVariety := P -> (
     I := P.ring.ideal;
     checkUserInput I;
     I = prepare I;
     (c,ambientDim) := internalChern I;
     return c
     )



 
 
internalSegre = I -> (
    
     -- Obtain:
     -- the ring R 
     -- the dimension of the ambient space
     -- the dimension n of Z
     -- a list of the generators of I sorted by degree
     -- the maximal degree of the generators of I and
     -- a generator of I with minimal degree
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;
     gensI := flatten entries sort gens I;
     maxDeg := first max degrees I; 
     minDegGen := first gensI;
     
     s:= {};
     
     
     if I == ideal(0_R) then (
	  s = for i from 0 to dimension list if i==0 then 1 else 0;
	  return s;
	  );
     if I == ideal(1_R) then (
	  s = {};
	  return s;
	  );
    
     -- Pick random elements in I of degree maxdeg, as many as the dimension of the ambient space, store in the list f.
     f := for i from 1 to ambientDim list sum( gensI, g -> g * random(maxDeg - first(degree(g)), R) );      
     
     -- The for loop computes the degrees of the Segre classes of Z, stores them in the list s.
     for d from (ambientDim - dimension) to ambientDim do (
	  
	  -- Obtain the ideal J of the intersection of d hypersurfaces containing Z, where d = comdimension of Z, ..., dimension of the ambient space.
	  J := ideal(take(f,d));
	  
	  -- Compute the residual of Z in the intersection of the d hypersurfaces, using saturation. Compute the degree of the residual. 
	  residual := saturate(J,minDegGen);
	  residualDeg := if residual != ideal vars R then degree residual else 0;
	  
     	  -- Using the degree of the residual, compute the degree of the pth Segre class, where p = d - codimension of Z.
	  p := d - (ambientDim - dimension);
	  degSegreClass := maxDeg^d - residualDeg - sum( 0..(p-1), i -> binomial(d,p-i)*maxDeg^(p-i)*s_i );
	  
	  s = append(s, degSegreClass);
	    
	  );
     
     return (s, ambientDim);
     
     )





internalChern = I -> (
     
     -- Obtain:
     -- the ring R 
     -- the dimension of the ambient space
     -- the dimension n of Z
     -- a list of the generators of I sorted by degree
     -- the maximal degree of the generators of I and
     -- a generator of I with minimal degree
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;
     gensI := flatten entries sort gens I;
     maxDeg := first max degrees I; 
     minDegGen := first gensI;
     
     s := {};
     
     
     if I == ideal(0_R) then (
	  s = for i from 0 to dimension list if i==0 then 1 else 0;
	  return s;
	  );
     if I == ideal(1_R) then (
	  s = {};
	  return s;
	  );
    
     -- Pick random elements in I of degree maxdeg, as many as the dimension of the ambient space, store in the list f.
     f := for i from 1 to ambientDim list sum( gensI, g -> g * random(maxDeg - first(degree(g)), R) );      
     
     -- The for loop computes the degrees of the Segre classes of Z, stores them in the list s.
     for d from (ambientDim - dimension) to ambientDim do (
	  
	  -- Obtain the ideal J of the intersection of d hypersurfaces containing Z, where d = comdimension of Z, ..., dimension of the ambient space.
	  J := ideal(take(f,d));
	  
	  -- Compute the residual of Z in the intersection of the d hypersurfaces, using saturation. Compute the degree of the residual. 
	  residual := saturate(J,minDegGen);
	  residualDeg := if residual != ideal vars R then degree residual else 0;
	  
     	  -- Using the degree of the residual, compute the degree of the pth Segre class, where p = d - codimension of Z.
	  p := d - (ambientDim - dimension);
	  degSegreClass := maxDeg^d - residualDeg - sum( 0..(p-1), i -> binomial(d,p-i)*maxDeg^(p-i)*s_i );
	  
	  s = append(s, degSegreClass);
	    
	  );
     
     c := for i from 0 to dimension list sum( 0..i, p -> binomial( ambientDim + 1, i-p )*s_p );

     return (c,ambientDim);
     
     )




checkUserInput = I -> (
        
     -- Is the ring a polynomial ring?
     if not isPolynomialRing ring I then error "The ideal needs to be defined over a polynomial ring.";
     
     -- Is the ideal homogeneous?
     if not isHomogeneous I then error "The ideal has to be homogeneous.";
     
     -- Is the coefficientRing a field (to make dimension command work)?
     if not isField coefficientRing ring I then error "The coefficient ring needs to be a field.";
     )



prepare = I -> (
     
     --trim I
     I = trim I;     
     
     -- rename variables to avoid later collisions
     numGen := numgens ring I;
     coeffRing := coefficientRing ring I;
     z := symbol z;
     R := coeffRing[z_1 .. z_numGen];
     renamingMap := map(R, ring I, {z_1 .. z_numGen});
     I = renamingMap I;
     return I;
     )




output = method(TypicalValue => RingElement)
output (List,ZZ) := (s,ambientDim) -> (
     H := symbol H;
     -- produces the ring ZZ[H]/(H^ambientDim+1)
     tempRing := ZZ[H];
     tempIdeal := ideal((tempRing_0)^(ambientDim+1));
     outputRing := tempRing / tempIdeal;
     
     dim := #s-1;
     out := sum(0..dim, i -> s_i * H^(ambientDim - dim + i));
     return out
     )
output (List, ZZ, Symbol) := (s,ambientDim,H) -> (
     -- produces the ring ZZ[H]/(H^ambientDim+1)
     tempRing := ZZ[H];
     tempIdeal := ideal((tempRing_0)^(ambientDim+1));
     outputRing := tempRing / tempIdeal;
     
     dim := #s-1;
     out := sum(0..dim, i -> s_i * (outputRing_0)^(ambientDim - dim + i));
     return out
     )




beginDocumentation()
document { 
	Key => ChernSegre,
	Headline => "Computations of degrees of Chern and Segre classes of projective schemes",
	EM "ChernSegre", " computes degrees of Chern and Segre classes"
	}
document {
	Key => {segreClass, (segreClass,Ideal)},
	Headline => "computes degrees of the Segre classes",
	Usage => "segreClass I",
	Inputs => { "I" },
	Outputs => {{ "a list with degrees of Segre classes {deg s_0, ... , deg s_n} of the projective scheme given by the ideal", TT "I" }},
        SourceCode => {(segreClass,Ideal)},
	EXAMPLE {
	"1+1"
 --       segreClass ideal(x)
      	   }     	  
	}
document {
	Key => {chernClass, (chernClass,Ideal)},
	Headline => "computes degrees of the Chern classes",
	Usage => "chernClass I",
	Inputs => { "I" },
	Outputs => {{ "a list with degrees of Chern classes {deg c_0, ... , deg c_n} of the projective scheme given by the ideal", TT " I" }},
        SourceCode => {(chernClass,Ideal)},
	EXAMPLE {
	     "1+1"
	     }
	}
 document {
	Key => {segreClassList, (segreClassList,Ideal)},
	Headline => "computes degrees of the Segre classes",
	Usage => "segreClass I",
	Inputs => { "I" },
	Outputs => {{ "a list with degrees of Segre classes {deg s_0, ... , deg s_n} of the projective scheme given by the ideal", TT "I" }},
        SourceCode => {(segreClass,Ideal)},
	EXAMPLE {
	"1+1"
 --       segreClass ideal(x)
      	   }     	  
	}
document {
	Key => {chernClassList, (chernClassList,Ideal)},
	Headline => "computes degrees of the Chern classes",
	Usage => "chernClass I",
	Inputs => { "I" },
	Outputs => {{ "a list with degrees of Chern classes {deg c_0, ... , deg c_n} of the projective scheme given by the ideal", TT " I" }},
        SourceCode => {(chernClass,Ideal)},
	EXAMPLE {
	     "1+1"
	     }
	}
	
   


TEST ///
    R = QQ[x,y,z]
    I = (x)
    assert ( segreClass I == {1,-1} )
 ///
