restart
installPackage "Graphs"
installPackage "GraphicalModels"

------------------------------------------------------------
---gaussianRing:
gaussianRing 3 

G = mixedGraph(digraph {{b,{c,d}},{c,{d}}},bigraph {{a,d}})
gaussianRing G --passing a graph gives the variable names l's and p's

--gaussianRing does not take undirected graphs as input. It should. 

------------------------------------------------------------
---gaussianMatrices:
--needs to be able to only take as input only a ring R and a set of CI statements S, not necessarily a graph G.

--there is no such function for MixedGraphs: its code is embedded inside trekIdeal(Ring,MixedGraph,List)


------------------------------------------------------------