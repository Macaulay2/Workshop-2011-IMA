needsPackage "NAGtypes"

newPackage(
  "Bertini",
  Version => "0.1", 
  Date => "25 July 2011",
  Authors => {
    {Name => "Dan Bates",
     Email => "bates@math.colostate.edu",
     HomePage => "http://www.math.colostate.edu/~bates"},
    {Name => "Contributing Author: Anton Leykin",
     HomePage => "http://www.math.gatech.edu/~leykin"}
  },
  Headline => "Interface to Bertini",
  Configuration => { 
    "path" => "",
    "BERTINIexe"=>"bertini", 
    "keep files" => true
  },
  DebuggingMode => false,
  AuxiliaryFiles => true,
  CacheExampleOutput => true
)

export { 
  bertiniZeroDimSolve,
  bertiniParameterHomotopy,
  bertiniPosDimSolve,
  bertiniSample,
  bertiniComponentMemberTest,
  bertiniRefineSols
  }

--protect ErrorTolerance, protect addSlackVariables, protect Iterations,
--protect generalEquations, protect Bits, protect ResidualTolerance, 
--protect Append

protect StartSystem, protect StartSolutions, protect gamma
protect MPTYPE, protect PRECISION, protect ODEPREDICTOR, protect TRACKTOLBEFOREEG, protect TRACKTOLDURINGEG
protect FINALTOL, protect MAXNORM, protect MINSTEPSIZEBEFOREEG, protect MINSTEPSIZEDURINGEG, protect IMAGTHRESHOLD
protect COEFFBOUND, protect DEGREEBOUND, protect CONDNUMTHRESHOLD, protect RANDOMSEED, protect SINGVALZEROTOL
protect ENDGAMENUM, protect USEREGENERATION, protect SECURITYLEVEL, protect SCREENOUT, protect OUTPUTLEVEL
protect STEPSFORINCREASE, protect MAXNEWTONITS, protect MAXSTEPSIZE, protect MAXNUMBERSTEPS, protect MAXCYCLENUM
protect REGENSTARTLEVEL, protect runType, protect deg, protect dimen, protect numpts, protect tol, protect pts

needsPackage "NAGtypes"

--##########################################################################--
-- GLOBAL VARIABLES 
--##########################################################################--

 DBG = 0; -- debug level (10=keep temp files)
 path'BERTINI = (options Bertini).Configuration#"path";
 BERTINIexe=path'BERTINI|(options Bertini).Configuration#"BERTINIexe"; 
-- this is the executable string we need to make sure that calls to PHCpack actually run:    -- How shall we do this with Bertini ???
-- NOTE: the absolute path should be put into the init-PHCpack.m2 file 

-- QUESTION: do we need to prepend "rootPath" to all the file names to resolve issues with cygwin??? (question from PHCpack interface)

needsPackage "SimpleDoc"

-- Bertini interface for NAG4M2
-- used by ../NumericalAlgebraicGeometry.m2

-- need to include proper attribution each time Bertini is run...how to do???
-- (license calls for a line in the output that states which Bertini version was used)

-- The following six methods are just front ends for various Bertini functions.
-- Each just calls bertiniSolve() with the appropriate input data and toggle (corresp. to the type of run).
-- bertiniSolve then does all the work of building the input file, calling bertini, and calling the appropriate output parser. 

bertiniZeroDimSolve = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1})
bertiniZeroDimSolve List := o -> F -> (  
--F is the list of polynomials.
         L := {runType=>0};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

bertiniParameterHomotopy = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1})
bertiniParameterHomotopy List := o -> F -> (
--F is the list of polynomials
         L := {runType=>1};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         )

--  The following will NOT be funcitonal until we have (and include as output) a numerical irreducible decomposition data type. 
bertiniPosDimSolve = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1})
bertiniPosDimSolve List := o -> F -> (  
--F is the list of polynomials
         L := {runType=>2};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

bertiniSample = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,dimen=>-1,deg=>-1,numpts=>-1})
bertiniSample List := o -> F -> (  
--F is the list of polynomials
         L := {runType=>3};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

--  The following will NOT be functional until we have (and include in the arg list) a numerical irreducible decomposition data type.
bertiniComponentMemberTest = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,pts=>{}})
bertiniComponentMemberTest List := o -> F -> (  
--F is the list of polynomials.
         L := {runType=>4};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 

bertiniRefineSols = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,pts=>{},tol=>-1})
bertiniRefineSols List := o -> F -> ( 
--F is the list of polynomials.
         L := {runType=>5};
         o2 := new OptionTable from L;
         o3 := o ++ o2;
         bertiniSolve(F,o3)
         ) 


---------------------------------------------------
-- bertiniSolve: This is the main control function:
---------------------------------------------------

bertiniSolve = method(TypicalValue => List, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,dimen=>-1,deg=>-1,numpts=>-1,pts=>{},tol=>-1,runType=>0})

bertiniSolve List := o -> F -> (  -- F is the list of polynomials
  	  dir := makeBertiniInput(F,o);   -- creates the input file 
  	  run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	  readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
          )


-- DAN PLAN (7/26/11)
--   allow many different options
--   these front ends funnel into a general input file maker, each sending the appropriate options to set the configs appropriately for the desired run
--   there is then a very basic call to run Bertini (done by Anton) 
--   then the output is read into M2 data types (still deciding on those), with each sort of run feeding into a different output file parser, since different sorts of runs yield different output files 
--   provide more flexibility for users, allowing them to exclude options for each of the front ends



-- protect StartSolutions, protect StartSystem (Anton/Jan suggested that perhaps we shouldn't be protecting any names???) 
makeBertiniInput = method(TypicalValue=>Nothing, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii,MPTYPE=>-1,PRECISION=>-1,ODEPREDICTOR=>-1,TRACKTOLBEFOREEG=>-1,TRACKTOLDURINGEG=>-1,FINALTOL=>-1,MAXNORM=>-1,MINSTEPSIZEBEFOREEG=>-1,MINSTEPSIZEDURINGEG=>-1,IMAGTHRESHOLD=>-1,COEFFBOUND=>-1,DEGREEBOUND=>-1,CONDNUMTHRESHOLD=>-1,RANDOMSEED=>-1,SINGVALZEROTOL=>-1,ENDGAMENUM=>-1,USEREGENERATION=>-1,SECURITYLEVEL=>-1,SCREENOUT=>-1,OUTPUTLEVEL=>-1,STEPSFORINCREASE=>-1,MAXNEWTONITS=>-1,MAXSTEPSIZE=>-1,MAXNUMBERSTEPS=>-1,MAXCYCLENUM=>-1,REGENSTARTLEVEL=>-1,dimen=>-1,deg=>-1,numpts=>-1,pts=>{},tol=>-1,runType=>0})  
--makeBertiniInput = method(TypicalValue=>Nothing)
makeBertiniInput List := o -> T -> (
--makeBertiniInput (List,MutableHashTable,MutableHashTable) := (T,p,o) -> (
-- IN:
--	T = polynomials of target system
--      o.StartSystem = start system
  v := gens ring T#0; -- variables
  dir := temporaryFileName(); -- build a directory to store temporary data 
  makeDirectory dir; 
  f := openOut (dir|"/input"); -- typical (but not only possible) name for Bertini's input file 

  -- The following block is the config section of the input file 
  f << "CONFIG" << endl; -- starting the config section of the input file 
  --f << "MPTYPE: 2;" << endl; -- multiprecision
  f << "MPTYPE: 0;" << endl; -- double precision (default?)
  if #o.StartSystem > 0 then
    f << "USERHOMOTOPY: 1;" << endl;
  f << endl << "END;" << endl << endl;

  -- The following block is the input section of the input file
  f << "INPUT" << endl << endl;
  if #o.StartSystem > 0 then  -- if user-defined, declaration type of vars is "variable"
    f << "variable "
  else f << "variable_group "; -- if not user-defined, dec type of vars if "variable_group"
  scan(#v, i->  -- now we list the variables in a single list  ...  What about an mhom structure???
       if i<#v-1 
       then f << toString v#i << ", "
       else f << toString v#i << ";" << endl
       );
  f << "function "; -- "function" section
  scan(#T, i-> -- here are the functions
       if i<#T-1
       then f << "f" << i << ", "
       else f << "f" << i << ";" << endl << endl
      );
  bertiniNumbers := p->( L := toString p; -- Anton: what are these??? 
       L = replace("ii", "I", L); 
       L = replace("e", "E", L);
       L
       );
  if #o.StartSystem == 0 
  then scan(#T, i -> f << "f" << i << " = " << bertiniNumbers T#i << ";" << endl)
  else (
       if #o.StartSystem != #T then error "expected equal number of equations in start and target systems";
       f << "pathvariable t;" << endl 
         << "parameter s;" << endl
         << "s = t;" << endl;
       scan(#T, i -> f << "f" << i 
	    << " = (" << bertiniNumbers T#i << ")*(1-s)+s*("<< bertiniNumbers o.gamma << ")*(" << bertiniNumbers o.StartSystem#i << ");" << endl 
	   );
       );
  f << endl << "END" << endl << endl;
  close f;
  
  if #o.StartSolutions > 0 then (
       f = openOut (dir|"/start"); -- THE name for Bertini's start solutions file 
       f << #o.StartSolutions << endl << endl;
       scan(o.StartSolutions, s->(
		 scan(s, c-> f << realPart c << " " << imaginaryPart c << ";" << endl );
		 f << endl;
		 ));
       close f;
       );
  stdio << dir;
  dir
  )

cleanupOutput = method(TypicalValue=>String)
cleanupOutput String := s -> (
-- cleanup output (Bertini and hom4ps2)
  t := replace("E", "e", s);
  t = replace("[(,)]","", t);
  t = replace("e\\+","e",t)
  )

readSolutionsBertini = method(TypicalValue=>List)
readSolutionsBertini (String,String) := (dir,f) -> (  -- dir=directory holding the output files, f=file name from which to grab solutions
  s := {};
  if f == "finite_solutions" then (
       --print "implementation unstable: Bertini output format uncertain";
       l := lines get (dir|"/"|f);
       nsols := value first separate(" ", l#0);
       l = drop(l,2);
       while #s < nsols do (	 
	    coords := {};
	    while #(first l) > 2 do ( 
	      	 coords = coords | {(
		   	   a := separate(" ",  cleanupOutput(first l));	 
		   	   (value a#0)+ii*(value a#1)
	      	   	   )};
    	      	 l = drop(l,1);
	      	 );	
	    l = drop(l,1);
            if DBG>=10 then << coords << endl;
	    s = s | {{coords}};
	    );	
       ) 
  else if f == "raw_solutions" then (
       l = lines get (dir|"/"|f);
       while #l>0 and #separate(" ", l#0) < 2 do l = drop(l,1);
       while #l>0 do (
	    if DBG>=10 then << "------------------------------" << endl;
	    coords = {};
	    while #l>0 and #separate(" ", l#0) >= 2 do ( 
	      	 coords = coords | {(
		   	   a = separate(" ",  cleanupOutput(first l));	 
		   	   (value a#0)+ii*(value a#1)
	      	   	   )};
    	      	 l = drop(l,1);
	      	 );
	    while #l>0 and #separate(" ", l#0) < 2 do l = drop(l,1);
            if DBG>=10 then << coords << endl;
	    s = s | {{coords}};
	    );     
    ) else error "unknown output file";
  s
  )

trackBertini = method(TypicalValue => List)
trackBertini (List,List,List,MutableHashTable) := List => (S,T,solsS,o) -> (
     -- tempdir := temporaryFileName() | "NumericalAlgebraicGeometry-bertini";
     -- mkdir tempdir; 	  
     dir := makeBertiniInput(T, StartSystem=>S, StartSolutions=>solsS, gamma=>o.gamma);
     compStartTime := currentTime();      
     run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");
     if DBG>0 then << "Bertini's computation time: " << currentTime()-compStartTime << endl;
     readSolutionsBertini(dir, "raw_solutions")
     )



--##########################################################################--
-- DOCUMENTATION
--##########################################################################--

beginDocumentation()

--doc ///
--  Key
--    Bertini
--  Headline
--    software for numerical algebraic geometry
--  Description
--    Text
--      Interfaces the functionality of the software {\tt Bertini}
--      to solve polynomial systems and perform calculations in
--      {\em numerical algebraic geometry}.  The software is available at
--      @HREF"http://www.nd.edu/~sommese/bertini/"@.
--      The site currently provides only executable versions named {\tt bertini} or {\tt bertini.exe} (for Cygwin).
--      The user must have the executable program {\tt phc} available,
--      preferably in the executation path.
--
--      Below is a simple example using the most popular function,
--      a basic zero-dimensional solve with no special options.
--    Example
--      R = CC[x,y]
--      F = {x^2-1,y^2-1}
--      solns = bertiniSolve(F)
--///;

--doc ///
--  Key 
--    bertiniSolve
--    (bertiniSolve,List)
--    (bertiniSolve,List,HashTable)
--  Headline
--    temporarily a method for doing a zero-dimensional Bertini run, soon to be deprecated
--  Usage
--    S = bertiniSolve F
--  Inputs
--    F:List
--      whose entries are polynomials (system need not be square) 
--  Outputs
--    S:List
--      whose entries are the solutions found by Bertini, with junk points removed if system is not square
--  Description
--    Text
--      For now, this function simply builds a Bertini style input file from F and calls Bertini on 
--      this input file.  Solutions are currently pulled from machine readable file finitesolutions
--      and returned as a list.
--    Example
--      R = CC[x,y]
--      F = {x^2-1,y^2-1}
--      S = bertiniSolve F
--///;



end
