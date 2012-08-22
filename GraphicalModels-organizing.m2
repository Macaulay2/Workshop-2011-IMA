
---- New LIST OF ALL FUNCTIONS/METHODS IN THE ORDER THEY APPEAR IN THE PACKAGE:

--**************************--
--  INTERNAL ROUTINES        	  --
--**************************--
--*************************************--
--  Functions used by globalMarkov--
--*************************************--
bayesBall
--*************************************--
--  Functions used throughout          --
--*************************************--
cartesian
pos 
possibleValues 
prob 
setToBinary
subsetsBetween 
--***********************************************************************************--
--  Functions used within Markov relation routines to remove redundant statements    --
--***********************************************************************************--
equivStmts  
setit 
under 
sortdeps 
normalizeStmt 
minimize 
removeRedundants  

--**************************--
--  METHODS 	      	   	  --
--**************************--
--****************************************************************************************--
--  Methods for creating conditional independence statements from graphs and digraphs	  --
--****************************************************************************************--
pairMarkov Graph
pairMarkov Digraph
localMarkov Graph
localMarkov Digraph
globalMarkov Graph
globalMarkov Digraph
--**************************************************************************************************************************************--
--  Methods for creating polynomial rings that carry information about random variables and/or underlying graph, digraph or mixed graph --
--**************************************************************************************************************************************--
markovRing Sequence
gaussianRing ZZ
gaussianRing Graph 
gaussianRing Digraph
gaussianRing MixedGraph
--********************************************************************************************************************************--
--  Methods for creating matrices relevant for the graphical models (covariance matrix, matrices whose minors vanish on the model)--
--********************************************************************************************************************************--
undirectedEdgesMatrix Ring 
directedEdgesMatrix Ring 
bidirectedEdgesMatrix Ring
markovMatrices(Ring,List,List) 
markovMatrices(Ring,List)
covarianceMatrix(Ring)
gaussianMatrices(Ring,List)
--******************************************************************--
--  Methods for creating ideals that vanish for a graphical model   --
--******************************************************************--
conditionalIndependenceIdeal (Ring,List)
conditionalIndependenceIdeal (Ring,List,List)
gaussianParametrization (Ring,MixedGraph)
gaussianVanishingIdeal Ring
trekSeparation MixedGraph
trekIdeal (Ring,MixedGraph)
trekIdeal (Ring,Graph)
trekIdeal (Ring,Digraph)
--********************************************************************************************************************************--
--  Methods for manipulating polynomial maps frequently used in graphical models
--********************************************************************************************************************************--
marginMap(ZZ,Ring)
inverseMarginMap(ZZ,Ring) 
hiddenMap(ZZ,Ring)
identifyParameters (Ring,MixedGraph)


--********************************************************************************************************************************--
-- NEW LIST OF ALL THE TESTS WE HAD (in order they appear now, and marked 'ok' if they have been checked): 
--****************************************************************************************--
--  TESTS FOR Methods for creating conditional independence statements from graphs and digraphs	  --
--****************************************************************************************--
ok: pairMarkov Graph
ok: pairMarkov Digraph
ok: localMarkov Graph
ok: localMarkov Digraph
new, ok: globalMarkov Graph
ok: globalMarkov Digraph
--**************************************************************************************************************************************--
--  TESTS FOR Methods for creating polynomial rings that carry information about random variables and/or underlying graph, digraph or mixed graph --
--**************************************************************************************************************************************--
ok: markovRing Sequence
ok: gaussianRing ZZ
ok: gaussianRing Graph 
ok: gaussianRing Digraph
ok: gaussianRing MixedGraph
--********************************************************************************************************************************--
--  Methods for creating matrices relevant for the graphical models (covariance matrix, matrices whose minors vanish on the model)--
--********************************************************************************************************************************--
ok: undirectedEdgesMatrix Ring 
ok: directedEdgesMatrix Ring 
ok: bidirectedEdgesMatrix Ring
new, ok: markovMatrices(Ring,List,List) 
ok: markovMatrices(Ring,List)
ok (with graph, digraph, mixedgraph!): covarianceMatrix(Ring)
ok (two tests): gaussianMatrices(Ring,List)

--******************************************************************--
--  Methods for creating ideals that vanish for a graphical model   --
--******************************************************************--
ok: conditionalIndependenceIdeal (Ring,List)
ok (missing but ok): conditionalIndependenceIdeal (Ring,List,List)
ok: discreteVanishingIdeal (Ring,Graph)
ok: gaussianParametrization (Ring,MixedGraph)
ok (graph and digraph): gaussianVanishingIdeal Ring
ok: trekSeparation MixedGraph
ok: trekIdeal (Ring,MixedGraph)
ok (no need to test; just calls other tested methods): trekIdeal (Ring,Graph)
ok: trekIdeal (Ring,Digraph)
--********************************************************************************************************************************--
--  Methods for manipulating polynomial maps frequently used in graphical models
--********************************************************************************************************************************--
ok: marginMap(ZZ,Ring)
ok: inverseMarginMap(ZZ,Ring) 
ok: hiddenMap(ZZ,Ring)
ok: identifyParameters (Ring,MixedGraph)

