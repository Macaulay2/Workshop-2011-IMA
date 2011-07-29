-- returns the position in list h of  x
pos = (h, x) -> position(h, i->i===x)
-- the following function retrieves the position of the vertices 
-- in the graph G for all vertices contained in the list S
-- vertices G does not return a sorted list of the vertices 
getPositionOfVertices = (G,S) -> apply(S, w -> pos(sort vertices G, w))
restart
pos = (h, x) -> position(h, i->i===x)
loadPackage "Graphs"
G=graph {{a,b},{a,c},{c,b},{c,d},{c,e},{d,e}}
Gvers= vertices G
n=# vertices G
--hastable for vertex labeling
--Ghash=new MutableHashTable
--for i from 1 to n do
--(
  --   Ghash#(Gvers#(i-1)) = i
    -- )
--peek Ghash



--input vertex label, out vertex index
getPos=(v)->pos(vertices G, v)
--input is integer locator, output neighbors
nbr=(v)->(graph G)#((vertices G)#v)
--input is index of vertex and ordering, output is position of neighbors of vertex in ordering
indNbr=(v,sigma)->apply(#nbr(v),i->
     pos(sigma,pos(vertices G,(toList nbr(v))#i))
     )





lexBFS=(G)->(    
S=new MutableList from apply (# vertices G, i->{});
Size=new MutableList from apply (# vertices G, i->0);
alpha=new MutableList from apply (# vertices G, i->0);
ainverse=new MutableList from apply (# vertices G, i->0);
S#0=toList (0..n-1);
j=0;
  for i from 0 to n-1 do
       (v=S#j#0;
       S#j=delete(v,S#j);
       --if S#j=={} then delete({},S);
       alpha#v=i;
       ainverse#i= v;
       Size#v = -1;
       for u from 0 to (#(graph G)#(Gvers_v))-1 when Size#u>=0 do 
	    (
		 
		 S#(Size#u) = delete(u,S#(Size#u));
		 Size#u = Size#u +1;
		 S#(Size#u) = append(S#(Size#u),u);
		 );
	if S#j=={} then j=j+1;
	print peek alpha
     );  
alpha)
alpha=lexBFS(G)
peek alpha

--input alpha, a list in lexbfs order
sigma=reverse alpha
chordal=0
for i from 1 to n-1 when chordal==0 do (
     neighbors=(graphG)#(Gvers_i);
     m=apply(#neighbors, i->pos(sigma,neighbors_i));
     mx=null;
     while m!={} and mx==null do if max m<i then mx=max m else delete(max m, m);
     if mx == null then continue;
     if mx!=null then
     	  (--finding the earlier neighbors of i excluding mx
	       	    earlyNbr=select(m,j->j< i);
	       
	  






j=0
  for i from 0 to n-1 do
       (v=S#j#0;
       S#j=delete(v,S#j);
       alpha#v=i;
       ainverse#i = v;
       Size#v = -1;
       for u from 0 to #(graph G)#(Gvers_v)-1 when Size#u>=0 do 
	    (
		 S#(Size#u) = delete(u,S#(Size#u));
		 Size#u = Size#u +1;
		 S#(Size#u) = append(S#(Size#u),u);
		 );
	j=j+1;
	while j >= 0 and S#j == {} do j= j-1;
	print peek alpha
     )     
peek(alpha)
peek(ainverse)
vertices G


G=graph {{a,b},{b,c},{c,d},{d,a}}


--Start by assuming that the graph is chordal
chordal=1
for v from 0 to n-1 do (
     nbrV = toList nbr(v);
     indNbrV= indNbr(v,toList sigma);
     
     --(graph G)#(Gvers_v);
     --indNbrV = apply(#nbrV, i->pos(toList sigma,nbrV_i));
     --minus one denotes null
     w=-1;
     if select(indNbrV,j->j<pos(toList sigma,v))!={} then posw = max(select(indNbrV,j->j<pos(toList sigma,v)));
     w=sigma#posw;
     print w;
     print indNbrV;
     --while indNbrV!={} and w==null do if max indNbrV<v then w=max
--indNbrV else delete(max indNbrV, indNbrV);
     if w == -1 then continue;
     if w!=-1 then
     	  (
	       --finding the earlier neighbors of v excluding w
	       earlyNbrV = select(indNbrV,j->j< pos(toList sigma,v));
	       earlyNbrV = delete(w,earlyNbrV);
	       --finding the earlier neighbors of w
	       nbrW = toList nbr(w);
     	       indNbrW = indNbr(w,toList sigma);
	       print earlyNbrV;
	       earlyNbrW = select(indNbrW,j->j< pos(toList sigma,w));
	       print indNbrW;
	       print earlyNbrW;
	       -- if earlyNbrV is not a subset of earlyNbrW then the graph is not a chordal
	       if isSubset(earlyNbrV,earlyNbrW) == false then
		  (	
		    chordal = 0;
		    break;
		   )	
	     )
	)			
chordal		--if w is not null and the loop exits, then it is a chordal graph
