newPackage ("SearchObjects",
      	Version => "0.1", 
    	Date => "March 1, 2011",
    	Authors => {
	     {Name     => "Florian Geiss",
	      Email    => "fg@math.uni-sb.de",
	      HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	 
	     {Name     => "Frank-Olaf Schreyer", 
	      Email    => "schreyer@math.uni-sb.de", 
	      HomePage => "http://www.math.uni-sb.de/ag/schreyer/"}},
        Headline => "framework for searching random objects in algebraic geometry",
    	DebuggingMode => true
        )
       
export {
     "search",
     "pSearch",
     "Certify", 
     "RandomObject", 
     "SearchObject",
     "Attempts", 
     "Certification", 
     "Construction"}

if not version#"VERSION" >= "1.4.0.1" then error "this package requires Macaulay2 version 1.4.0.1 or newer"


SearchObject = new Type of MutableHashTable
globalAssignment SearchObject

pSearch=method()
pSearch SearchObject := Object -> args -> (
     -- if the args consist of a single element make it into a sequence
     if not instance(args, Sequence) then args = 1:args;
     cert := false;
     att := 1;
     -- stripp of attempts from the argument list
     argsConstr := toSequence (for x in args list (
	  if instance(x,Option) then (
	       if x#0 === Attempts then (att = x#1 ; continue )
	       else x
	       )
	  else x));
     -- strip off certify from the argument list
     argsCert:= toSequence (for x in argsConstr list (
	  if instance(x,Option) then (   
	       if x#0 === Certify then (cert = x#1 ; continue )
	       else x
	       )
	  else x));

     -- schedule the tasks
     tsks:=apply(att,i-> createTask(Object.Construction, argsConstr));
     tsks/schedule;
     object:=null;

     -- loop until either a (certified) object is found or all tasks have finished 
     while not all(tsks,isReady) do (
	  ind:=apply(#tsks,i->i);
	  ready:={};
	  -- loop until a task has finished
	  while #ready==0 do (ready=select(ind,i->isReady tsks_i));
	  -- check if there is a (certified) object among the results of the finished tasks
	  scan(tsks_ready,t->(
	       tmpObject:=taskResult t;
	       if tmpObject=!=null then 
	             if cert then 
		          if Object.Certification prepend(tmpObject,argsCert) then object=tmpObject else object=null
		     else 
		          object=tmpObject;));
	  -- remove finished tasks from list
     	  tsks=tsks_(ind - set ready);
	  if object=!=null then (
	       scan(tsks,t->cancelTask t);
	       tsks={};);
	  );
     return object;
     ) 

end
restart
uninstallPackage"SearchObjects"
installPackage"SearchObjects"

t1=createTask( ()->( t2=createTask(()-> (sleep 5; print"Hello"));
	  schedule t2
	  ))
schedule t1
isReady t1, isReady t2
schedule createTask(()->( schedule createTask(()->(
		    sleep 10;
		    print"Hello";))))

constructMatrix=()->(
     M:=random((ZZ/11)^4,(ZZ/11)^4);
     if rank M==2 then M else null)

certifyMatrix=()->true

sMatrix = new SearchObject from {
     Construction=>constructMatrix,
     Certification=>certifyMatrix
     }
t1=currentTime();
M=(pSearch sMatrix)(Attempts=>11^5);
t2=currentTime();
viewHelp
t2-t1

rank M
viewHelp
