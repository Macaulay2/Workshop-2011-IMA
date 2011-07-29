-- -*- coding: utf-8 -*-
newPackage(
	"ChernSegre",
    	Version => "0.1", 
    	Date => "July 25, 2011",
    	Authors => {{Name => "Christine Jost", 
		  Email => "jost@math.su.se", 
		  HomePage => "http://www.math.su.se/~jost"}},
    	Headline => "Degrees of Chern and Segre classes",
    	DebuggingMode => true
    	)


-- internal commenting!!!
-- write documentation
-- test all functions

export {segreClass}
segreClass = method(TypicalValue => RingElement);
segreClass (Ideal, Symbol) := (I,hyperplaneClass) -> (
     (segreList, ambientDim) := internalSegreClassList I;
     return output (segreList, ambientDim, hyperplaneClass)
     )
segreClass Ideal := I -> (     
     return segreClass (I, symbol H)
     )
segreClass (ProjectiveVariety,Symbol) := (projectiveVar,hyperplaneClass) -> (
     I := projectiveVar.ring.ideal;
     return segreClass(I, hyperplaneClass)
     )
segreClass ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return segreClass I
     )
     

     
export {segreClassList}
segreClassList = method(TypicalValue => List);
segreClassList Ideal := I -> (
     (segreList, ambientDim) := internalSegreClassList I;
     return segreList
     )
segreClassList ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return segreClassList I
     )


internalSegreClassList Ideal := I -> (
     checkUserInput I;
     localI := prepare I;
     return internalSegre localI;
     )


export {chernClass}
chernClass = method(TypicalValue => RingElement);
chernClass (Ideal, Symbol) := (I,hyperplaneClass) -> (
     (chernList, ambientDim) := internalChernClassList I;
     return output (chernList, ambientDim, hyperplaneClass)
     )
chernClass Ideal := I -> (     
     return chernClass (I, symbol H)
     )
chernClass (ProjectiveVariety,Symbol) := (projectiveVar, hyperplaneClass) -> (
     I := projectiveVar.ring.ideal;
     return chernClass(I, hyperplaneClass)
     )
chernClass ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return chernClass I
     )

     

     
export {chernClassList}
chernClassList = method(TypicalValue => List);
chernClassList Ideal := I -> (
     (chernList, ambientDim) := internalChernClassList I;
     return chernList
     )
chernClassList ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return chernClassList I
     )


internalChernClassList Ideal := I -> (
     checkUserInput I;
     localI := prepare I;
     return internalChern localI;
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
     
     s:= {};
     
     
     if I == ideal(0_R) then (
	  s = for i from 0 to dimension list if i==0 then 1 else 0;
	  return (s,ambientDim);
	  );
     if I == ideal(1_R) then (
	  s = {};
	  return (s,ambientDim);
	  );    
     
     
     
     gensI := flatten entries sort gens I;
     maxDeg := first max degrees I; 
     minDegGen := first gensI;
     

    
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
 
     
     -- Compute the Segre classes use them to compute the Chern-Fulton classes.     
     (segreList,ambientDim) = internalSegre(I);   
     dimension = #segreList - 1;
     return  for i from 0 to dimension list sum( 0..i, p -> binomial( ambientDim + 1, i-p )*segreList_p )
        
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
     localI = trim I;     
     
     -- rename variables to avoid later collisions
     numGen := numgens ring localI;
     coeffRing := coefficientRing ring localI;
     z := symbol z;
     R := coeffRing[z_1 .. z_numGen];
     renamingMap := map(R, ring localI, {z_1 .. z_numGen});
     return renamingMap localI;
     )



output (List, ZZ, Symbol) := (segreList,ambientDim,hyperplaneClass) -> (
     -- produces the ring ZZ[hyperplaneClass]/(hyperplaneClass^ambientDim+1)
     tempRing := ZZ[hyperplaneClass];
     outputRing := tempRing / ideal((tempRing_0)^(ambientDim+1));
     
     -- reserved symbol
     dimension := #segreList-1;
     return  sum(0..dimension, i -> segreList_i * (outputRing_0)^(ambientDim - dimension + i))
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
        -- sourceCode ??
	SourceCode => {(segreClass,Ideal)},
	EXAMPLE {
	     -- get lines \\\
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
