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
    "readIdeal",
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

-- to be added

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





