-- Abraham Martin del Campo
-- 25/July/2011
-- ---------------------
-- This is a file where I implement Ravis LR-decomposition
-- ---------------------

--moveCheckers({3,5,4,2,1,0},{3,99,99,5,99,1},6)
restart
needsPackage "LRcheckergame";
playCheckers({1,1},{1,1},5,10)
playCheckers({1,1},{2,1},3,6)
playCheckers({1,1},{2,0},2,4)
playCheckers({1},{1},2,4)
playCheckers({1,1},{2,1},3,6)
playCheckers({2,1},{1,1},3,6)

playCheckers2 = method(TypicalValue => List)
playCheckers2(List,List,ZZ,ZZ) := (partn1,partn2,k,n) -> (
     reds:= new List;
     tree := new List;
     storeRed:=new List;
     splitcount := 0;
     if (partn1 > partn2) then (
	  redChkrs=redChkrPos(partition2bracket(partn2,k,n),partition2bracket(partn1,k,n),k,n);
     ) else (
         redChkrs=redChkrPos(partition2bracket(partn1,k,n),partition2bracket(partn2,k,n),k,n);
     );
     -- we check for red checkers above the diagonal. If one, give a null output
     --apply(#redChkrs, i->(
	--  if i+redChkrs#i < n-1 then return({toList(n:99),{}})
     --));
     blackChkrs:=new List;
     counter:=0;
     blackChkrs = reverse toList (0..(n-1)); --initial black positions.
     while blackChkrs != {} do (
	  (blackChkrs, redChkrs, splitcount) = toSequence moveCheckers(blackChkrs, redChkrs,n);
	  counter = counter+1;
	  tree=join(tree,toList(splitcount:counter));
	  storeRed = join(storeRed, {take(redChkrs,n)});
     	  blackChkrs = drop(blackChkrs,n);
	  redChkrs = drop(redChkrs,n);
     );
     -- here call the function makeTree
     storeRed
)
