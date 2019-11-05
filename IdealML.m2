newPackage (
  "IdealML",
  Version=>"1.0",
  Authors => {{Name => "Lily Silverstein", Email => "lsilverstein@cpp.edu"}},
  Headline => "misc. M2 code used in my dissertation",
  PackageImports => {
      "Graphs",
      "HilbertML"
      },
  PackageExports => {
      "RandomMonomialIdeals" 
      },
  DebuggingMode => false
)

export {
    "degreeFeatures",
    "generatorGraph",
    "gradedModel",
    "graphFeatures",
    "hyperEdgeIdeal",
    "knightMovesIdeal",
    "lexSegment",
    "markovStep",
    "prim",
    "readIdeal",
    "spanningTreeWithExponents",
    "supportFeatures",
    "variableFeatures",
    "variableGraph",
    "variableGeneratorGraph",
    "writeData",
    "writeFeatures",
    "writeList"
    }



----------------------------------------
-- Methods for random families of ideals
----------------------------------------

hyperEdgeIdeal = method()

hyperEdgeIdeal (ZZ, ZZ) := (n, k) -> (
    if k < 2 then error(
	"edges must have cardinality two or greater!"
	) 
    else if n < k then error(
	"edges can't be larger than the number of vertices!"
	)
    else(
    oldVertices := toList(0..n-1);
    newVertices := {};
    newEdges := {};
    -- choose a random starting edge
    v := take(random(oldVertices), k);
    scan(v, vi -> (
	    oldVertices = delete(vi, oldVertices);
	    newVertices = append(newVertices, vi);
	    )
	);
    newEdges = append(newEdges, v);
    while #oldVertices > 0 do(
        x := first random(oldVertices);
	y := take(random(newVertices),k-1);
	oldVertices = delete(x, oldVertices);
	newVertices = append(newVertices, x);
        newEdges = append(newEdges, append(y,x));
	);
    newEdges)    
)

hyperEdgeIdeal (Ring, ZZ) := (R, k) -> (
    monomialIdeal apply(hyperEdgeIdeal(#(gens R), k), edge -> product(apply(edge, a -> R_a)))
    )

lexSegment = method();
lexSegment (ZZ, ZZ, ZZ) := (n, d, k) -> (
    z := symbol z;
    R := QQ(monoid[z_1..z_n, MonomialOrder => Lex]);
    monomialIdeal(take(flatten entries basis(d, R), k))
    )

knightMovesIdeal = method();
knightMovesIdeal (ZZ, ZZ, ZZ) := (m, n, k) -> (
    z := symbol z;
    R := QQ[z_{1,1}..z_{m, n}];
    monomialIdeal(take(random select(flatten flatten for i from 1 to m list for j from 1 to n list(
	{try(z_{i, j}*z_{i+2, j+1}) else 0, try(z_{i, j}*z_{i+1, j+2}) else 0,
	try(z_{i, j}*z_{i-1, j+2}) else 0, try(z_{i, j}*z_{i-2, j+1}) else 0}
    ), e -> e=!=0), k)) 
)


markovStep = method();
markovStep (MonomialIdeal, ZZ) := (I, degLimit) -> (
    G := random flatten entries mingens I;
    m := first G;
    newMon := if (first degree m)==degLimit then (
	first random gens ring I
	)
    else (
	{m*(first random gens ring I),m*(first random gens ring I)}
	);
    monomialIdeal flatten(delete(m, G)|{newMon})
)   

prim = method();
prim ZZ := n -> (
    if n < 2 then error(
	"there are no edges in a graph on "|toString(n)|" vertices!"
	) 
    else(
    oldVertices := toList(0..n-1);
    newVertices := {};
    newEdges := {};
    -- choose a random starting vertex
    v := first random(oldVertices);
    oldVertices = delete(v, oldVertices);
    newVertices = append(newVertices, v);
    while #oldVertices > 0 do(
	-- choose a random new vertex and a random old vertex
        x := first random(oldVertices);
        y := first random(newVertices);
        -- add vertex x and edge xy to the tree
        oldVertices = delete(x, oldVertices);
        newVertices = append(newVertices, x);
        newEdges = append(newEdges, {x, y});
	);
    newEdges)
    )
prim Ring := R -> (
    monomialIdeal apply(prim(#(gens R)), pair -> R_(pair#0)*R_(pair#1))
    )

spanningTreeWithExponents = method();
spanningTreeWithExponents (Ring, ZZ) := (R, deg) -> (
    monomialIdeal apply(prim(#(gens R)), pair -> (R_(pair#0))^(random(1,deg))*(R_(pair#1))^(random(1,deg)))
    )

gradedModel  = (R,D,p,N) -> (
    if p<0.0 or 1.0<p then error "p expected to be a real number between 0.0 and 1.0";
    if N<1 then stderr << "warning: N expected to be a positive integer" << endl;
    apply(N,i-> monomialIdeal randomHomogeneousMonomialSet(R,D,p))
)
-----------------------------
-- internally used for gradedModel
----------------------------
randomHomogeneousMonomialSet = (R,D,p) -> (
    if p<0.0 or 1.0<p then error "p expected to be a real number between 0.0 and 1.0";
    B := {};
    B = select(flatten entries basis(D,R),m-> random(0.0,1.0)<=p);
    if B==={} then {0_R} else B
)

---------------------------------
-- Methods for computing features
---------------------------------
degreeFeatures = method();
degreeFeatures (MonomialIdeal) := (I) -> (
    D := apply(mingensList I, g -> first degree g);
    if #D == 0 then {0,0,0,0} else {mean(D)//toRR, variance(D)//toRR, min(D), max(D)}
    )

supportFeatures = method();
supportFeatures (MonomialIdeal) := (I) -> (
    S := apply(mingensList I, g -> #(support g));
    if #S == 0 then {0,0,0,0} else {mean(S)//toRR, variance(S)//toRR, min(S), max(S)}
    )

variableFeatures = method();
variableFeatures (MonomialIdeal) := (I) -> (
    G := apply(mingensList I, g -> support g);
    if #G == 0 then {0,0,0,0,0} else(
	V := apply(#(gens ring I), i -> toRR(#select(G, s -> member((ring I)_i, s))/#G));
	{mean(V), variance(V), min(V), max(V)}|{#(flatten select(G, g-> #g == 1))}
	)
    )

isAdjacent := (L, x, y) -> (--local function used to define graphs
    for mon in L do (if gcd(x, mon) > 1 and gcd(y, mon) > 1 then return true);
    return false
    )

generatorGraph = method();
generatorGraph (MonomialIdeal) := (I) -> (
    L := mingensList I;
    m := #L;
    graph(flatten for i from 0 to m-2 list(
	for j from i+1 to m-1 list(
	    if gcd(L#i, L#j) > 1 then {L#i, L#j} else continue)))
    )

variableGraph = method();
variableGraph (MonomialIdeal) := (I) -> (
    V := gens ring I;
    n := #V;
    L := mingensList I;
    graph(flatten for i from 0 to n-2 list(
	for j from i+1 to n-1 list(
	    if isAdjacent(L, V#i, V#j) then {V#i, V#j} else continue)))
    )

variableGeneratorGraph = method();
variableGeneratorGraph (MonomialIdeal) := (I) -> (
    V := gens ring I;
    n := #V;
    L := mingensList I;
    m := #L;
    graph(flatten for i from 0 to n-1 list(
	for j from 0 to m-1 list(
	    if gcd(V#i, L#j) > 1 then {V#i, L#j} else continue)))
    )

graphFeatures = method();
graphFeatures (Graph) := (G) -> (
    if vertices(G) == {} then {0,0,0,0} else (
	degs := apply(vertices(G), v -> degree(G,v));
	{mean(degs)//toRR, variance(degs)//toRR, min(degs), max(degs)}
	)
    )
-------------------
-- I/O Functions --
-------------------
readIdeal = method();
readIdeal (String, Ring) := (line, R) -> (
    Iarray := value (separateRegexp("^(.)",(separateRegexp("..[0-9]+...$", line))#0))#1;
    Ilist := toList apply(Iarray, m -> toList m);
    if Ilist === {} then monomialIdeal(0_R) else monomialIdeal(apply(Ilist, m -> R_m))
    )

writeFeatures = method();
writeFeatures (MonomialIdeal) := (I) -> (
    demark(", ",
	apply(
	    {numgens(ring I),#(mingensList I)}|
	    supportFeatures I|
	    degreeFeatures I|
	    variableFeatures I|
	    graphFeatures(variableGraph I)|
	    graphFeatures(generatorGraph I),	    --graphFeatures(variableGeneratorGraph I),
	    f -> toString(f))
	)
    )

writeData = method();
writeData (MonomialIdeal, String) := (I, dirName) -> (
    prefix := "~/Desktop/MonLearning/Test/"|dirName|"/"|dirName;
    idealFile := openOutAppend(prefix|".ideals");
    idealFile << toString I << endl << close;
    featFile := openOutAppend(prefix|".features");
    featFile << "[" << writeFeatures(I) << "]" << endl << close;
    (allTrees, bestT) := allTreeScores(I);
    treesFile := openOutAppend(prefix|".pivotTrees");
    treesFile << writeList(allTrees) << endl << close;
    dimFile := openOutAppend(prefix|".dim");
    dimFile << dim I << endl << close;
    codimFile := openOutAppend(prefix|".codim");
    codimFile << codim I << endl << close;
    degFile := openOutAppend(prefix|".degree");
    degFile << degree I << endl << close;
    B := betti res I;
    pdimFile := openOutAppend(prefix|".pdim");
    pdimFile << pdim B << endl << close;
    regFile := openOutAppend(prefix|".reg");
    regFile << regularity B << endl << close;
    )

writeList = method();
writeList (List) := (L) -> (
    "["|demark(", ", apply(L, f -> toString(f)))|"]"
    )

-------------------
-- Local-Only Code
-------------------
mean = method();
mean (List) := (L) -> (
    sum(L)/#L
    )

variance = method();
variance (List) := (L) -> (
    m := mean L;
    sum(apply(L, i -> (i-m)^2))/#L
    )

mingensList = method();
mingensList (MonomialIdeal) := (I) -> (
    flatten first entries mingens I
    )

-----------
-- TESTS --
-----------

TEST ///
assert(instance(hyperEdgeIdeal(QQ[vars(0..9)],4), MonomialIdeal))
assert(dim lexSegment(3,3,10) == 0)
assert(dim lexSegment(4,4,3) == 3)
assert(numgens knightMovesIdeal(5,5,10) == 10)
assert(numgens prim(QQ[vars(0..6)]) == 6)
assert(numgens spanningTreeWithExponents(QQ[vars(0..6)], 5) == 6)
assert(#gradedModel(QQ[vars(0..6)], 5, 0.1, 1) == 1)
assert(instance(first gradedModel(QQ[vars(0..6)], 5, 0.1, 1), MonomialIdeal))
///
-------------------
-- DOCUMENTATION --
-------------------

beginDocumentation()

doc ///
 Key
  prim
  (prim, ZZ)
  (prim, Ring)
 Headline
  compute a random spanning tree of the complete graph using Prim's algorithm, or its edge ideal
 Usage
  L = prim n
  M = prim R
 Inputs
  n:ZZ
  R:Ring
 Outputs
  L:List
   the edges of the spanning tree, given as a list of pairs
  M:MonomialIdeal
   the edge ideal who generators are the 
   squarefree degree 2 monomials in $R$ 
   corresponding to a spanning tree on the variables of $R$
 Description
  Text
   If the input to this function is an integer $n\ge 2$, 
   it finds a spanning tree of the complete graph with
   vertices $0,\ldots,n-1$, and returns the list of edges.
  Example
   prim 10
  Text
   If the input is a ring, the variables of the ring are
   used as the vertices. The output is a monomial ideal of $R$ 
   generated by squarefree degree two monomials. These describe a
   a spanning tree of the complete graph whose vertices are
   the variables of $R$.
  Example
   R = QQ[x_1..x_10];
   prim R
 SeeAlso
  hyperEdgeIdeal
///

doc ///
 Key
  hyperEdgeIdeal
  (hyperEdgeIdeal, ZZ, ZZ)
  (hyperEdgeIdeal, Ring, ZZ)
 Headline
  compute a random regular $k$-regular hypergraph on $n$ vertices, or its edge ideal
 Usage
  L = hyperEdgeIdeal(n, k)
  M = hyperEdgeIdeal(R, k)
 Inputs
  n:ZZ
   number of vertices/variables
  k:ZZ
   cardinality of each hyperedge
  R:Ring
 Outputs
  L:List
   the edges of the hypergraph, given as a list of $k$-sets
  M:MonomialIdeal
   the edge ideal who generators are the squarefree degree $k$ monomials in $R$ 
   corresponding to a $k$-regular hypergraph
 Description
  Text
   If the input to this function is two integers $n,k\ge 2$,
   with $k\le n$, 
   it finds a connected hypergraph on the
   vertices $0,\ldots,n-1$, and returns the list of edges.
  Example
   hyperEdgeIdeal(10, 3)
   hyperEdgeIdeal(12, 7)
  Text
   If the input is a ring and an integer, the variables of the ring 
   are used as the vertices. The output is a monomial ideal in
   that ring, generated by squarefree
   degree $k$ monomials. These correspond to a connected hypergraph
   whose vertices are the variables of $R$.
  Example
   R = QQ[a..j];
   hyperEdgeIdeal(R, 5)
   hyperEdgeIdeal(R, 9)
  Text
   The algorithm to create this hypergraph is similar to Prim's
   algorithm for random spanning trees of the complete graph. It 
   starts with a random initial edge of size $k$. A random vertex not
   yet in the hypergraph is then chosen, and put in an edge with
   $k-1$ of the already chosen vertices. This process is continued,
   with each new edge containing precisely one newly added vertex,
   until every vertex appears in an edge. 
 Caveat
  An error will occur if $k$ is greater than the number of
  indeterminates of $R$, or if either quantity is less than 2.
 SeeAlso
  prim
///

doc ///
 Key
  markovStep
  (markovStep, MonomialIdeal, ZZ)
 Headline
  slightly alter the input ideal by applying a random process to its generating set
 Usage
  J = markovStep(I, deglimit)
 Inputs
  n:ZZ
   number of vertices/variables
  k:ZZ
   cardinality of each hyperedge
  R:Ring
 Outputs
  L:List
   the edges of the hypergraph, given as a list of $k$-sets
  G:List
   a list of squarefree degree $k$ monomials in $R$ that generate 
   the edge ideal of the hypergraph
 Description
  Text
   If the input to this function is two integers $n,k\ge 2$,
   with $k\le n$, 
   it finds a connected hypergraph on the
   vertices $0,\ldots,n-1$, and returns the list of edges.
  Example
   hyperEdgeIdeal(10, 3)
   hyperEdgeIdeal(12, 7)
  Text
   If the input is a ring and an integer, the variables of the ring 
   are used as the vertices. The output list contains squarefree
   degree two monomials in $R$ corresponding to the edges of
   a spanning tree of the complete graph whose vertices are
   the variables of $R$.
  Example
   R = QQ[a..j];
   G = hyperEdgeIdeal(R, 5)
   monomialIdeal(G)
  Text
   An error will occur if $k$ is greater than the number of
   indeterminates of $R$.
///


end


--
restart 
needsPackage("IdealML", FileName => "~/Desktop/MonLearning/IdealML.m2")

----------------
-- Example Usage
----------------

generateERdata = (n, D, p, N, name) -> (
    ideals = randomMonomialIdeals(n, D, p, N, Strategy => "Minimal");
    for i in ideals do(
    	writeData(i, name);
	);
    <<"completed "<<name<<endl;
    )
dir = "ER-n4-D4-0.1"
makeDirectory("Test/"|dir)
generateERdata(4,4,0.1,100,dir)


generateGradedModelData = (n, D, p, N, name) -> (
    ideals = gradedModel(n, D, p, N);
    for i in ideals do(
    	writeData(i, name);
	);
    <<"completed "<<name<<endl;
    )


