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

taskList:={};

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
     
     -- wrap the following function around the actual computation:
     -- if a (certified) result is returned it cancels all other tasks and returns the result 
     checkRes:=(argsConstr,argsCert,cert,taskNr)->(
	  tmpobject:=Object.Construction(argsConstr);
	  -- in case of cert=true check if the objects passes certification 
	  if cert then 
	     if Object.Certification prepend(tmpObject,argsCert) then 
	        object=tmpObject 
	     else 
	        object=null 
	  else object=tmpObject;
	  if object=!=null then (
	       scan(#taskList,i->if i!=taskNr then cancelTask taskList_i);
	       print"pSearch finished successfully.")       
	  object)
     
     -- set up the task List
     taskList:=apply(att,i-> createTask(checkRes,(argsConstr,argsCert,cert,i)));
     -- set up a finishing task
     finishTask:=()->(
	  
     taskList/schedule;
     
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

constructMatrix=()->(
     M:=random((ZZ/13)^4,(ZZ/13)^4);
     if rank M==2 then M else null)

certifyMatrix=()->true

sMatrix = new SearchObject from {
     Construction=>constructMatrix,
     Certification=>certifyMatrix
     }

t1=currentTime(); M=(pSearch sMatrix)(Attempts=>13^5); t2=currentTime();
t2-t1
allowableThreads
Search=()->(counter=0; while(M=constructMatrix(); M===null and counter<13^5) do (counter=counter+1));
t1=currentTime(); Search(); t2=currentTime();
t2-t1
restart
t1'=currentTime(); 
counter=0;
while(
     M=constructMatrix();
     M===null and counter<11^5) do (counter=counter+1);
t2'=currentTime();
t2'-t1'

viewHelp
t2-t1

rank M
viewHelp
