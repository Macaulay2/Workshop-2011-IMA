segreClass = method(TypicalValue => RingElement);
segreClass (Ideal, Symbol) := (I,hyperplaneClass) -> (
     (segreList, ambientDim) := internalSegreClassList I;
     return output (segreList, ambientDim, hyperplaneClass)
     )
segreClass Ideal := I -> (     
     H := symbol H;
     return segreClass (I, H)
     )
segreClass (ProjectiveVariety,Symbol) := (projectiveVar,hyperplaneClass) -> (
     I := projectiveVar.ring.ideal;
     return segreClass(I, hyperplaneClass)
     )
segreClass ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return segreClass I
     )

segreClassList = method(TypicalValue => List);
segreClassList Ideal := I -> (
     (segreList, ambientDim) := internalSegreClassList I;
     return segreList
     )
segreClassList ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return segreClassList I
     )

-- Analogously to the computation of the Segre classes, the computation of the Chern classes is done by 
-- the internal function internalChernClassList, which returns a list with the degrees of the Chern 
-- Classes and the dimension of the ambient space. The human-readable output as a polynomial in the Chow ring 
-- ZZ[H]/H^(k+1) of the ambient space P^k is produced by the internal function output.
-- The user can choose to give the input as a homogeneous ideal in a polynomial ring or as a projective
-- variety. Furthermore, the user can give the symbol used for the Chow ring ZZ[H]/H^(k+1) as an 
-- optional input. The default symbol is H for hyperplane class.
chernClass = method(TypicalValue => RingElement);
chernClass (Ideal, Symbol) := (I,hyperplaneClass) -> (
     (chernList, ambientDim) := internalChernClassList I;
     return output (chernList, ambientDim, hyperplaneClass)
     )
chernClass Ideal := I -> (  
     H := symbol H;   
     return chernClass (I, H)
     )
chernClass (ProjectiveVariety,Symbol) := (projectiveVar, hyperplaneClass) -> (
     I := projectiveVar.ring.ideal;
     return chernClass(I, hyperplaneClass)
     )
chernClass ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return chernClass I
     )

 
chernClassList = method(TypicalValue => List);
chernClassList Ideal := I -> (
     (chernList, ambientDim) := internalChernClassList I;
     return chernList
     )
chernClassList ProjectiveVariety := projectiveVar -> (
     I := projectiveVar.ring.ideal;
     return chernClassList I
     )




----------------------------------------------
-- Internal functions
----------------------------------------------



-- The functions internalSegreClassList and internalChernClassList call other internal functions 
-- which do the actual work. 
internalSegreClassList = I -> (
     -- check that the input is a homogeneous ideal in a polynomial ring over a field
     checkUserInput I;
     -- trim the ideal and make it an ideal over a ring only used internally
     localI := prepare I;
     -- compute the Segre classes
     return internalSegre localI;
     )
internalChernClassList = I -> (
     -- check that the input is a homogeneous ideal in a polynomial ring over a field
     checkUserInput I;
     -- trim the ideal and make it an ideal over a ring only used internally
     localI := prepare I;
     -- compute the Chern classes
     return internalChern localI;
     )

-- The function internalSegre is the main function in this package which does the actual computation of the 
-- Segre classes. It uses the algorithm described in [1].
-- Notation: This algorithm computes the degrees of the Segre classes s_0(Z,P^k), ..., s_n(Z,P^k) of an
-- n-dimensional closed subscheme Z of P^k. The subscheme Z is given by a homogeneous ideal I in the 
-- polynomial ring R.
-- Input:  I, a homogeneous ideal in a polynomial ring over a field
-- Output: segreList, a list containing the degrees of the Segre classes of Proj(R/I) = Z
--         ambientDim, the dimension k of the ambient space Proj(R)=P^k 
internalSegre = I -> (
    
     -- Obtain:
     -- the ring R 
     -- the dimension of the ambient space and
     -- the dimension n of Z
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;
     
     -- take care of the special cases I = (0) and I = (1)
     if I == ideal(0_R) then (
	  segreList := {};
	  return (segreList,ambientDim);
	  );
     if I == ideal(1_R) then (
	  segreList = {};
	  return (segreList,ambientDim);
	  ); 
        
     -- For the nonspecial cases, obtain:
     -- a list of the generators of I sorted by degree
     -- the maximal degree of the generators of I and
     -- a generator of I with minimal degree     
     
     gensI := flatten entries sort gens I;
     maxDeg := first max degrees I; 
     minDegGen := first gensI;
     
     -- initialize segreList as an empty list
     segreList= {};
    
     -- Pick random elements in I of degree maxdeg, as many as the dimension of the ambient space, store in the list f.
     f := for i from 1 to (ambientDim+1) list sum( gensI, g -> g * random(maxDeg - first(degree(g)), R) );    
     
     --- Compute the degree of the residual of Z in the intersection of d hypersurfaces, where d = codimension of Z, ... , dimension of the ambient space.
     degR = residualDegs(f, gensI, ambientDim, dimension, Strategy => Bertini);  
     
     -- The for loop computes the degrees of the Segre classes of Z
     for d from (ambientDim - dimension) to ambientDim do (
	  
     	  -- Using the degree of the residual, compute the degree of the pth Segre class, where p = d - codimension of Z.
	  p := d - (ambientDim - dimension);
	  degSegreClass := maxDeg^d - degR_(d - ambientDim + dimension) - sum( 0..(p-1), i -> binomial(d,p-i)*maxDeg^(p-i)*segreList_i );
	  
	  segreList = append(segreList, degSegreClass);
	    
	  );
     
     return (segreList, ambientDim);

     )





-- The function internalChern calls internalSegre to compute the Segre classes of the given subscheme of P^k. From these it computes the
-- Chern-Fulton classes using a simple formula (see e.g. [1]). The Chern-Fulton classes are identical to the Chern classes if the scheme 
-- is a smooth variety.
-- Input:  I, a homogeneous ideal in a polynomial ring over a field
-- Output: chernList, a list containing the degrees of the Chern classes of Proj(R/I)
--         ambientDim, the dimension k of the ambient space Proj(R)=P^k 
internalChern = I -> (
     
     -- Obtain:
     -- the ring R
     -- the dimension of the ambient space and
     -- the dimension n of Z
     R := ring I;
     ambientDim := dim Proj R;
     dimension := dim Proj(R/I) ;

     -- take care of the special cases I = (0) and I = (1) 
     if I == ideal(0_R) then (
	  chernList := apply(0..dimension, i-> binomial(dimension+1, i));
	  return (chernList,ambientDim);
	  );
     if I == ideal(1_R) then (
	  chernList = {};
	  return (chernList,ambientDim);
	  ); 

     (segreList,ambientDimDummy) := internalSegre(I); 
     chernList = for i from 0 to dimension list sum( 0..i, p -> binomial( ambientDim + 1, i-p )*segreList_p );
     return  (chernList, ambientDim)
        
     )


residualDegs = {Strategy => Symbolic} >> opts -> (f, gensI, ambientDim, dimension) -> (
     
     --- TO DO: Adapt to new version of Bertini
     --- Step 1: learn interfaces properly
     
     if (opts.Strategy == Bertini) then (
	  
	  R = ring first gensI;
	  
	  outConfig = "CONFIG \n" | "OUTPUTLEVEL: -1; \n" | "TRACKTYPE: 1; \n" | "WITNESSGENTYPE: 2; \n" | "END; \n \n";
	  outVarGroup = "hom_variable_group ";
	  variables = flatten entries vars R;
	  for i from 0 to (length(variables)-2) do outVarGroup = outVarGroup | toString(variables_i) | ", ";
	  outVarGroup = outVarGroup | toString(last variables) | "; \n";
	  outFunctionDecl = "function "; 
	  for i from 0 to (length(f)-2) do outFunctionDecl = outFunctionDecl | "f" | toString(i) | ", ";
	  outFunctionDecl = outFunctionDecl | "f" | toString(length(f)-1) | "; \n \n";
	  outFunctions = "";
	  for i from 0 to (length(f)-1) do outFunctions = outFunctions | "f" | toString(i) | "=" | toString(f_i) | "; \n";
	  outInput = "INPUT \n" | outVarGroup | outFunctionDecl |  outFunctions | "END; \n";
	 
     	  
	  out = outConfig | outInput;
	  
          g = openOut "/tmp/input_segre";
	  g << out;
	  close g;
	  
	  run "cd /tmp; bertini /tmp/input_segre;",;
	  
	  degR = apply(drop(drop(lines(get "/tmp/regenSummary"),1 + ambientDim-dimension),-1), myString->value((separate(" ", myString))_5));
	  
	  
	  myHelpVariable = dimension + 1 - #degR; 	 
	  
	  if (myHelpVariable > 0) then for i from 1 to myHelpVariable do (degR = degR | {0}); 
	  print degR;
	   
	  
	  	  	  
	  );
     
     return degR;
     
     );



-- The function checkUserInput checks that the given ideal I is a homogeneous ideal in a polynomial ring over a field.
checkUserInput = I -> (
        
     -- Is the ring a polynomial ring?
     if not isPolynomialRing ring I then error "The ideal needs to be defined over a polynomial ring.";
     
     -- Is the ideal homogeneous?
     if not isHomogeneous I then error "The ideal has to be homogeneous.";
     
     -- Is the coefficient ring a field (to make dimension command work)?
     if not isField coefficientRing ring I then error "The coefficient ring needs to be a field.";
     )


-- The function prepare does two things to prepare the later computations. Firstly, it trims the ideal I, taking away
-- nonnecessary generators. Then it creates a ring only used internally and an ideal in it isomorphic to I and returns this ideal. This 
-- step is done to avoid possible later conflicts in the choice of variables.
prepare = I -> (

     --trim I
     localI := trim I;     
     
     -- rename variables
     numGen := numgens ring localI;
     coeffRing := coefficientRing ring localI;
     z := symbol z;
     internalR := coeffRing[z_1 .. z_numGen];
     renamingMap := map(internalR, ring localI, {z_1 .. z_numGen});
     return renamingMap localI;
     )

-- The function output turns a list of degrees of characteristic classes into a polynomial in the Chow ring of the ambient space P^k.
-- This ring is generated by the hyperplane class.
-- Input:  segreList, a list {deg s_0, ..., deg s_n} of integers
--         ambientDim, the dimension k of ambient space P^k
--         hyperplaneClass, the symbol for the hyperplane class
-- Output: the polynomial (deg s_0)*hyperplaneClass^ambientDim + ... + (deg s_n)*hyperplaneClass^(ambientDim - n)
output = (segreList,ambientDim,hyperplaneClass) -> (
     -- produce the Chow ring ZZ[hyperplaneClass]/(hyperplaneClass^ambientDim+1)
     tempRing := ZZ[hyperplaneClass];
     outputRing := tempRing / ideal((tempRing_0)^(ambientDim+1));
     -- obtain the dimension n
     dimension := #segreList-1;
     -- create the polynomial (deg s_0)*hyperplaneClass^ambientDim + ... + (deg s_n)*hyperplaneClass^(ambientDim - n)
     return  sum(0..dimension, i -> segreList_i * (outputRing_0)^(ambientDim - dimension + i))
     )


