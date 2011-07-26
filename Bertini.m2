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
  bertiniSolve
--  sharpenSolutions,
--  trackPaths,
--  gamma,
--  tDegree
  }

--protect ErrorTolerance, protect addSlackVariables, protect Iterations,
--protect generalEquations, protect Bits, protect ResidualTolerance, 
--protect Append

protect StartSystem, protect StartSolutions, protect gamma


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

bertiniSolve = method(TypicalValue => List)
bertiniSolve (List) := List => (F) -> (  -- F is the list of polynomials; o is the hash table of options.
  	  dir := makeBertiniInput F;  -- creates the input file 
  	  run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");  -- runs Bertini, storing screen output to bertini_session.log
	  readSolutionsBertini(dir,"finite_solutions")  -- grabs "finite_solutions" and puts all finite solutions in NAGTypes data types...Is finite_solutions the correct output file??? 
	  )


bertiniSolve (List,HashTable) := List => (F,o) -> (  -- F is the list of polynomials; o is the hash table of options.
  bertiniSolve F
  )

-- DAN PLAN (7/26/11)
--   build several user-accessible front ends (bertiniX, with X=ZerodimSolve, PosdimSolve, ComponentSample, ComponentMembershipTest, RefineEndpoints, etc.)
--     (these need to allow many different options)
--   these front ends funnel into a general input file maker, each sending the appropriate options to set the configs appropriately for the desired run
--   there is then a very basic call to run Bertini (done by Anton) 
--   then the output is read into M2 data types (still deciding on those), with each sort of run feeding into a different output file parser, since different sorts of runs yield different output files 



-- protect StartSolutions, protect StartSystem (Anton/Jan suggested that perhaps we shouldn't be protecting any names???) 
makeBertiniInput = method(TypicalValue=>Nothing, Options=>{StartSystem=>{},StartSolutions=>{},gamma=>1.0+ii}) -- need to greatly increase the list of options here!!!
makeBertiniInput List := o -> T -> (
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
trackBertini (List,List,List,HashTable) := List => (S,T,solsS,o) -> (
     -- tempdir := temporaryFileName() | "NumericalAlgebraicGeometry-bertini";
     -- mkdir tempdir; 	  
     dir := makeBertiniInput(T, StartSystem=>S, StartSolutions=>solsS, gamma=>o.gamma);
     compStartTime := currentTime();      
     run("cd "|dir|"; "|BERTINIexe|" >bertini_session.log");
     if DBG>0 then << "Bertini's computation time: " << currentTime()-compStartTime << endl;
     readSolutionsBertini(dir, "raw_solutions")
     )

end


