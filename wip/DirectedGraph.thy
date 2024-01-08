theory DirectedGraph
    imports CvRDT HOL.Set HOL.Fun
begin

type_synonym Vertex = "nat"
datatype  Edge = Edge "Vertex" "Vertex"

datatype DirectedGraph = DirectedGraph "Vertex set" "Edge set" 
datatype UpdateVertex = AddVertex Vertex | RemoveVertex Vertex
datatype UpdateEdge = AddEdge Edge | RemoveEdge Edge
datatype Update = UpdateEdge | UpdateVertex

definition "initial = DirectedGraph Set.empty Set.empty"

fun lookup_vertex :: "DirectedGraph \<Rightarrow> Vertex \<Rightarrow> bool" where
  "lookup_vertex (DirectedGraph v e) v1 = (v1 \<in> v)"

fun lookup_edge :: "DirectedGraph \<Rightarrow> Edge \<Rightarrow> bool" where
  "lookup_edge (DirectedGraph v e) (Edge v1 v2) = 
    (lookup_vertex (DirectedGraph v e) v1 &
    lookup_vertex (DirectedGraph v e) v2 &
    (Edge v1 v2) \<in> e)" 

end
