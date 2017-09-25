extern crate petgraph;
extern crate fnv;
#[cfg(test)]
extern crate capngraph;

use petgraph::graph;
use petgraph::Direction;
use petgraph::visit::{IntoNeighborsDirected, IntoNeighbors, GraphBase, NodeCount,
                          NodeIndexable, NodeCompactIndexable, EdgeRef, IntoNodeIdentifiers, Data,
                          GraphProp, IntoNodeReferences, IntoEdgeReferences};
use petgraph::Direction::*;
use std::slice::Iter;
use std::ops::{Index, IndexMut, Range};
use std::iter::{Map, Iterator, Enumerate};
use fnv::{FnvHashMap, FnvHashSet};

pub type Graph<N, E> = VecGraph<N, E>;

#[derive(Copy, Clone, Debug, PartialEq, Ord, PartialOrd, Eq, Hash)]
pub struct NodeIndex(u32);

impl NodeIndex {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn new(idx: usize) -> Self {
        NodeIndex(idx as u32)
    }
}

impl graph::GraphIndex for NodeIndex {
    fn index(&self) -> usize {
        self.0 as usize
    }

    fn is_node_index() -> bool { true }
}

impl From<usize> for NodeIndex {
    fn from(u: usize) -> Self {
        Self::new(u)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct EdgeIndex(usize, usize);

impl EdgeIndex {
    pub fn index(self) -> usize {
        // self.0 as usize
        unimplemented!()
    }
}

impl graph::GraphIndex for EdgeIndex {
    fn index(&self) -> usize {
        // self.0 as usize
        unimplemented!()
    }

    fn is_node_index() -> bool { false }
}

impl From<usize> for EdgeIndex {
    fn from(_u: usize) -> Self {
        unimplemented!()
    }
}

/// A directed adjacency-list graph implemented on Vectors. Indices are all `usize` as a result.
#[derive(Clone, Debug)]
pub struct VecGraph<N, E> {
    num_nodes: usize,
    num_edges: usize,
    node_weights: Vec<N>,
    pub incoming_edges: Vec<Vec<usize>>,
    pub incoming_weights: Vec<Vec<E>>,
    pub outgoing_edges: Vec<Vec<usize>>,
    pub outgoing_weights: Vec<Vec<E>>,
}

impl<N, E: Clone> VecGraph<N, E> {
    pub fn from_petgraph(g: graph::Graph<N, E>) -> Self {
        let (nodes, edges) = g.into_nodes_edges();
        let mut incoming_edges = vec![Vec::new(); nodes.len()];
        let mut outgoing_edges = vec![Vec::new(); nodes.len()];
        let mut incoming_weights = vec![Vec::new(); nodes.len()];
        let mut outgoing_weights = vec![Vec::new(); nodes.len()];

        let edges = edges.into_iter()
            .map(|edge| (edge.source().index(), edge.target().index(), edge.weight))
            .collect::<Vec<_>>();

        let num_edges = edges.len();
        for (source, target, w) in edges.into_iter() {
            incoming_edges[target].push(source);
            incoming_weights[target].push(w.clone());
            outgoing_edges[source].push(target);
            outgoing_weights[source].push(w);
        }

        VecGraph {
            num_nodes: nodes.len(),
            num_edges: num_edges,
            node_weights: nodes.into_iter().map(|node| node.weight).collect(),
            incoming_edges,
            incoming_weights,
            outgoing_edges,
            outgoing_weights,
        }
    }
}

impl<N: Default + Clone, E: Clone> VecGraph<N, E> {
    pub fn new_with_nodes(node_count: usize) -> Self {
        VecGraph {
            num_nodes: node_count,
            num_edges: 0,
            node_weights: vec![N::default(); node_count],
            incoming_edges: vec![Vec::new(); node_count],
            incoming_weights: vec![Vec::new(); node_count],
            outgoing_edges: vec![Vec::new(); node_count],
            outgoing_weights: vec![Vec::new(); node_count],
        }
    }

    pub fn from_edges(edges: Vec<(u32, u32, E)>) -> Self {
        let num_nodes = edges.iter().fold(0, |prev, &(a, b, _)| {
            ::std::cmp::max(a, ::std::cmp::max(b, prev))
        }) as usize + 1;
        let mut incoming_edges = vec![Vec::new(); num_nodes];
        let mut outgoing_edges = vec![Vec::new(); num_nodes];
        let mut incoming_weights = vec![Vec::new(); num_nodes];
        let mut outgoing_weights = vec![Vec::new(); num_nodes];


        let num_edges = edges.len();
        for (source, target, w) in edges.into_iter() {
            incoming_edges[target as usize].push(source as usize);
            incoming_weights[target as usize].push(w.clone());
            outgoing_edges[source as usize].push(target as usize);
            outgoing_weights[source as usize].push(w);
        }

        VecGraph {
            num_nodes,
            num_edges: num_edges,
            node_weights: vec![N::default(); num_nodes],
            incoming_edges,
            outgoing_edges,
            incoming_weights,
            outgoing_weights,
        }
    }

    pub fn update_edge(&mut self, a: NodeIndex, b: NodeIndex, weight: E) -> EdgeIndex {
        if self.contains_edge(a, b) {
            let b_pos = self.outgoing_edges[a.index()].iter().position(|&u| u == b.index()).unwrap();
            self.outgoing_weights[a.index()][b_pos] = weight.clone();
            let a_pos = self.incoming_edges[b.index()].iter().position(|&u| u == a.index()).unwrap();
            self.incoming_weights[b.index()][a_pos] = weight;
            EdgeIndex(a.index(), b_pos)
        } else {
            let idx = EdgeIndex(a.index(), b.index());
            self.incoming_weights[b.index()].push(weight.clone());
            self.outgoing_weights[a.index()].push(weight);
            self.incoming_edges[b.index()].push(a.index());
            self.outgoing_edges[a.index()].push(b.index());
            self.num_edges += 1;
            idx
        }
    }

    pub fn update_edge_with<F>(&mut self,
                               a: NodeIndex,
                               b: NodeIndex,
                               weight_fn: F,
                               weight_default: E)
                               -> EdgeIndex
        where F: Fn(&E) -> E
    {
        if self.contains_edge(a, b) {
            let b_pos = self.outgoing_edges[a.index()].iter().position(|&u| u == b.index()).unwrap();
            let new_weight = weight_fn(&self.outgoing_weights[a.index()][b_pos]);
            self.outgoing_weights[a.index()][b_pos] = new_weight.clone();
            let a_pos = self.incoming_edges[b.index()].iter().position(|&u| u == a.index()).unwrap();
            self.incoming_weights[b.index()][a_pos] = new_weight;
            EdgeIndex(a.index(), b_pos)
        } else {
            let idx = EdgeIndex(a.index(), b.index());
            self.incoming_weights[b.index()].push(weight_default.clone());
            self.outgoing_weights[a.index()].push(weight_default);
            self.incoming_edges[b.index()].push(a.index());
            self.outgoing_edges[a.index()].push(b.index());
            self.num_edges += 1;
            idx
        }
    }
}

impl<N, E> VecGraph<N, E> {
    pub fn node_indices(&self) -> Map<Range<usize>, fn(usize) -> NodeIndex> {
        (0..self.num_nodes).map(NodeIndex::new)
    }

    pub fn find_edge(&self, src: NodeIndex, dst: NodeIndex) -> Option<EdgeIndex> {
        self.outgoing_edges[src.index()].iter().position(|&idx| idx == dst.index()).map(|pos| EdgeIndex(src.index(), pos))
    }

    pub fn contains_edge(&self, src: NodeIndex, dst: NodeIndex) -> bool {
        self.find_edge(src, dst).is_some()
    }


    pub fn edge_indices<'a>(&'a self) -> EdgeIndices<'a, N, E> {
        EdgeIndices {
            outer: 0,
            inner: 0,
            graph: self,
        }
    }

    pub fn edge_count(&self) -> usize {
        self.num_edges
    }


    pub fn edge_indices_directed<'a, F>
        (&'a self,
         a: NodeIndex,
         dir: Direction)
         -> Map<Edges<'a, N, E>, fn(EdgeReference<'a, E>) -> EdgeIndex> {
        self.edges_directed(a, dir).map(edge_id::<E>)
    }

    pub fn edge_endpoints(&self, EdgeIndex(src, idx): EdgeIndex) -> Option<(NodeIndex, NodeIndex)> {
        Some((NodeIndex::new(src), NodeIndex::new(self.outgoing_edges[src][idx])))
    }

    pub fn filter_map<F, G, N2, E2: Clone>(&self, node_map: F, edge_map: G) -> Graph<N2, E2>
        where F: Fn(NodeIndex, &N) -> Option<N2>,
              G: Fn(EdgeIndex, &E) -> Option<E2>
              {
                  let mut new_nodes = Vec::with_capacity(self.node_count());
                  let mut blacklist = FnvHashSet::default();
                  let mut relabel = FnvHashMap::default();
                  for (i, weight) in self.node_weights.iter().enumerate() {
                      if let Some(w2) = node_map(NodeIndex::new(i), weight) {
                          relabel.insert(i, new_nodes.len());
                          new_nodes.push(w2);
                      } else {
                          blacklist.insert(i);
                      }
                  }

                  let mut num_edges = 0;
                  let mut incoming = vec![Vec::new(); new_nodes.len()];
                  let mut incoming_weights = vec![Vec::new(); new_nodes.len()];
                  let mut outgoing = vec![Vec::new(); new_nodes.len()];
                  let mut outgoing_weights = vec![Vec::new(); new_nodes.len()];
                  for eidx in self.edge_indices() {
                      let (src, dst) = self.edge_endpoints(eidx).unwrap();
                      if blacklist.contains(&src.index()) || blacklist.contains(&dst.index()) {
                          continue;
                      } else {
                          if let Some(w2) = edge_map(eidx, &self[eidx]) {
                              num_edges += 1;
                              incoming[relabel[&dst.index()]].push(relabel[&src.index()]);
                              incoming_weights[relabel[&dst.index()]].push(w2.clone());
                              outgoing[relabel[&src.index()]].push(relabel[&dst.index()]);
                              outgoing_weights[relabel[&src.index()]].push(w2.clone());
                          }
                      }
                  }

                  Graph {
                      num_nodes: new_nodes.len(),
                      num_edges: num_edges,
                      node_weights: new_nodes,
                      incoming_edges: incoming,
                      incoming_weights,
                      outgoing_edges: outgoing,
                      outgoing_weights,
                  }
              }
}

impl<N, E> GraphBase for VecGraph<N, E> {
    type EdgeId = EdgeIndex;
    type NodeId = NodeIndex;
}

pub struct Neighbors<'a, N: 'a, E: 'a> {
    g: &'a Graph<N, E>,
    source: usize,
    dir: Direction,
    internal: Iter<'a, usize>,
}

impl<'a, N, E> Neighbors<'a, N, E> {
    pub fn detach(self) -> NeighborWalker {
        let dir = self.dir;
        let count = match dir {
                Outgoing => self.g.outgoing_edges[self.source].len(),
                Incoming => self.g.incoming_edges[self.source].len(),
            };
        NeighborWalker {
            source: self.source,
            dir: dir,
            internal: 0..count,
        }
    }
}

impl<'a, N, E> Iterator for Neighbors<'a, N, E> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next().map(|&idx| NodeIndex::new(idx))
    }
}

#[derive(Clone, Debug)]
pub struct NeighborWalker {
    internal: ::std::ops::Range<usize>,
    dir: Direction,
    source: usize,
}

impl NeighborWalker {
    pub fn next<N, E>(&mut self, g: &Graph<N, E>) -> Option<(EdgeIndex, NodeIndex)> {
        if let Some(next) = self.internal.next() {
            let node = match self.dir {
                Outgoing => NodeIndex::new(g.outgoing_edges[self.source][next]),
                Incoming => NodeIndex::new(g.incoming_edges[self.source][next]),
            };
            Some((EdgeIndex(self.source, node.index()), node))
        } else {
            None
        }
    }

    pub fn next_node<N, E>(&mut self, g: &Graph<N, E>) -> Option<NodeIndex> {
        self.next(g).map(|(_, node)| node)
    }

    pub fn next_edge<N, E>(&mut self, g: &Graph<N, E>) -> Option<EdgeIndex> {
        self.next(g).map(|(edge, _)| edge)
    }
}

pub struct Edges<'a, N: 'a, E: 'a> {
    graph: &'a Graph<N, E>,
    source: usize,
    inner: usize,
    dir: Direction,
}


impl<'a, N, E> Iterator for Edges<'a, N, E> {
    type Item = EdgeReference<'a, E>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.dir {
            Outgoing => {
                if self.inner >= self.graph.outgoing_edges[self.source].len() {
                    None
                } else {
                    self.inner += 1;
                    let node = self.graph.outgoing_edges[self.source][self.inner-1];
                    Some(EdgeReference {
                        source: self.source,
                        dest: node,
                        weight: &self.graph.outgoing_weights[self.source][self.inner - 1],
                    })
                }
            },
            Incoming => {
                if self.inner >= self.graph.incoming_edges[self.source].len() {
                    None
                } else {
                    self.inner += 1;
                    let node = self.graph.incoming_edges[self.source][self.inner-1];
                    Some(EdgeReference {
                        source: node,
                        dest: self.source,
                        weight: &self.graph.incoming_weights[self.source][self.inner - 1],
                    })
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct EdgeReference<'a, E: 'a> {
    source: usize,
    dest: usize,
    weight: &'a E,
}

impl<'a, E> Clone for EdgeReference<'a, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, E> Copy for EdgeReference<'a, E> {}

impl<'a, E> EdgeRef for EdgeReference<'a, E> {
    type NodeId = NodeIndex;
    type EdgeId = EdgeIndex;
    type Weight = E;

    fn source(&self) -> NodeIndex {
        NodeIndex(self.source as u32)
    }

    fn target(&self) -> NodeIndex {
        NodeIndex(self.dest as u32)
    }

    fn weight(&self) -> &E {
        self.weight
    }

    fn id(&self) -> EdgeIndex {
        unimplemented!()
    }
}

fn edge_id<'a, E>(er: EdgeReference<'a, E>) -> EdgeIndex {
    er.id()
}

pub struct EdgeIndices<'a, N: 'a, E: 'a> {
    outer: usize,
    inner: usize,
    graph: &'a VecGraph<N, E>
}

impl<'a, N, E> Iterator for EdgeIndices<'a, N, E> {
    type Item = EdgeIndex;

    fn next(&mut self) -> Option<EdgeIndex> {
        while self.graph.outgoing_edges[self.outer].len() >= self.inner && self.graph.outgoing_edges.len() < self.outer {
            self.outer += 1;
            self.inner = 0;
        }

        if self.graph.outgoing_edges.len() >= self.outer {
            None
        } else {
            self.inner += 1;
            Some(EdgeIndex(self.outer, self.graph.outgoing_edges[self.outer][self.inner-1]))
        }
    }
}

impl<'a, N, E> IntoNeighbors for &'a Graph<N, E> {
    type Neighbors = Neighbors<'a, N, E>;

    fn neighbors(self, n: NodeIndex) -> Self::Neighbors {
        self.neighbors_directed(n, Direction::Outgoing)
    }
}

impl<'a, N, E> IntoNeighborsDirected for &'a Graph<N, E> {
    type NeighborsDirected = Neighbors<'a, N, E>;

    fn neighbors_directed(self, n: NodeIndex, d: Direction) -> Self::NeighborsDirected {
        match d {
            Direction::Outgoing => {
                Neighbors {
                    g: &self,
                    dir: d,
                    source: n.index(),
                    internal: self.outgoing_edges[n.index()].iter(),
                }
            }
            Direction::Incoming => {
                Neighbors {
                    g: &self,
                    dir: d,
                    source: n.index(),
                    internal: self.incoming_edges[n.index()].iter(),
                }
            }
        }
    }
}

impl<N, E> NodeCount for Graph<N, E> {
    fn node_count(&self) -> usize {
        self.num_nodes
    }
}

impl<N, E> NodeIndexable for Graph<N, E> {
    fn node_bound(&self) -> usize {
        self.num_nodes
    }

    fn to_index(&self, a: Self::NodeId) -> usize {
        a.index()
    }

    fn from_index(&self, i: usize) -> Self::NodeId {
        NodeIndex(i as u32)
    }
}

impl<N, E> NodeCompactIndexable for Graph<N, E> {}

impl<N, E> Index<EdgeIndex> for Graph<N, E> {
    type Output = E;
    fn index(&self, index: EdgeIndex) -> &E {
        &self.outgoing_weights[index.0][index.1]
    }
}
// impl<N, E> IndexMut<EdgeIndex> for Graph<N, E> {
    // fn index_mut(&mut self, index: EdgeIndex) -> &mut E {
        // &mut self.edges[index.index()].2
    // }
// }

impl<N, E> Index<NodeIndex> for Graph<N, E> {
    type Output = N;
    fn index(&self, index: NodeIndex) -> &N {
        &self.node_weights[index.index()]
    }
}

impl<N, E> IndexMut<NodeIndex> for Graph<N, E> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut N {
        &mut self.node_weights[index.index()]
    }
}

impl<'a, N, E> IntoNodeIdentifiers for &'a Graph<N, E> {
    type NodeIdentifiers = Map<Range<usize>, fn(usize) -> NodeIndex>;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.node_indices()
    }
}

impl<N, E> GraphProp for Graph<N, E> {
    type EdgeType = petgraph::Directed;
}

impl<N, E> Data for Graph<N, E> {
    type NodeWeight = N;
    type EdgeWeight = E;
}

impl<'a, N, E> IntoNodeReferences for &'a Graph<N, E> {
    type NodeRef = (NodeIndex, &'a N);
    type NodeReferences = Map<Enumerate<Iter<'a, N>>, fn((usize, &'a N)) -> Self::NodeRef>;
    fn node_references(self) -> Self::NodeReferences {
        fn mapper<NR>((i, w): (usize, NR)) -> (NodeIndex, NR) {
            (NodeIndex::new(i), w)
        }
        self.node_weights.iter().enumerate().map(mapper::<&'a N>)
    }
}

pub struct EdgeRefIter<'a, N: 'a, E: 'a> {
    internal: EdgeIndices<'a, N, E>,
    graph: &'a Graph<N, E>,
}

impl<'a, N, E> Iterator for EdgeRefIter<'a, N, E> {
    type Item = EdgeReference<'a, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next().map(|eidx| {
            let (src, dst) = self.graph.edge_endpoints(eidx).unwrap();
            EdgeReference {
                source: src.index(),
                dest: dst.index(),
                weight: &self.graph[eidx],
            }
        })
    }
}

impl<'a, N, E> IntoEdgeReferences for &'a Graph<N, E> {
    type EdgeRef = EdgeReference<'a, E>;
    // type EdgeReferences = Map<Enumerate<Iter<'a, (usize, usize, E)>>,
        // fn((usize, &'a (usize, usize, E))) -> Self::EdgeRef>;
    type EdgeReferences = EdgeRefIter<'a, N, E>;

    fn edge_references(self) -> Self::EdgeReferences {
        EdgeRefIter {
            internal: self.edge_indices(),
            graph: self,
        }
    }
}

pub trait IntoNeighborEdgesDirected: petgraph::visit::GraphRef + petgraph::visit::Data {
    type ER: EdgeRef<NodeId=Self::NodeId, EdgeId=Self::EdgeId, Weight=Self::EdgeWeight>;
    type NeighborEdgesDirected: Iterator<Item = Self::ER>;

    fn edges_directed(self, a: Self::NodeId, dir: Direction) -> Self::NeighborEdgesDirected;
}

impl<'a, N, E> IntoNeighborEdgesDirected for &'a Graph<N, E> {
    type NeighborEdgesDirected = Edges<'a, N, E>;
    type ER = EdgeReference<'a, E>;
    fn edges_directed(self, a: NodeIndex, dir: Direction) -> Edges<'a, N, E> {
        Edges {
            graph: self,
            source: a.index(),
            dir,
            inner: 0,
        }
    }
}

impl<'a, N, E> IntoNeighborEdgesDirected for &'a petgraph::Graph<N, E> {
    type NeighborEdgesDirected = petgraph::graph::Edges<'a, E, petgraph::Directed>;
    type ER = petgraph::graph::EdgeReference<'a, E>;

    fn edges_directed(self, a: Self::NodeId, dir: Direction) -> Self::NeighborEdgesDirected {
        petgraph::Graph::edges_directed(self, a, dir)
    }
}


#[cfg(test)]
mod test {
    use super::*;
    use capngraph;
    use std::collections::BTreeSet;

    #[test]
    fn grqc_correct() {
        let g = capngraph::load_graph("data/ca-GrQc.bin").unwrap();
        let vg = Graph::from_petgraph(g.clone());

        assert!(g.node_count() == vg.node_count());
        assert!(g.edge_count() == vg.edge_count());

        for node in g.node_indices() {
            let vnode = NodeIndex(node.index() as u32);
            assert!(g.edges_directed(node, Outgoing).count() ==
                    vg.edges_directed(vnode, Outgoing).count());
            assert!(g.edges_directed(node, Incoming).count() ==
                    vg.edges_directed(vnode, Incoming).count());

            let sum = g.edges_directed(node, Outgoing).map(|edge| *edge.weight()).sum::<f32>();
            let vsum = vg.edges_directed(vnode, Outgoing).map(|edge| *edge.weight()).sum::<f32>();

            // println!("{} {} {}", sum, vsum, (sum - vsum).abs());
            assert!((sum - vsum).abs() < 1e-3);

            let sum = g.edges_directed(node, Incoming).map(|edge| *edge.weight()).sum::<f32>();
            let vsum = vg.edges_directed(vnode, Incoming).map(|edge| *edge.weight()).sum::<f32>();

            // println!("{} {} {}", sum, vsum, (sum - vsum).abs());
            // println!("{:?}", g.edges_directed(node, Incoming).map(|edge| *edge.weight()).collect::<Vec<_>>());
            // println!("{:?}", vg.edges_directed(vnode, Incoming).map(|edge| *edge.weight()).collect::<Vec<_>>());

            assert!((sum - vsum).abs() < 1e-3);

            let down = g.neighbors_directed(node, Outgoing)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            let vdown = vg.neighbors_directed(vnode, Outgoing)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            assert!(down == vdown);

            let up = g.neighbors_directed(node, Incoming)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            let vup = vg.neighbors_directed(vnode, Incoming)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            assert!(up == vup);

            let up = g.edges_directed(node, Incoming)
                .map(|edge| edge.source().index())
                .collect::<BTreeSet<_>>();
            let vup = vg.edges_directed(vnode, Incoming)
                .map(|edge| edge.source().index())
                .collect::<BTreeSet<_>>();
            assert!(up == vup);

            let down = g.edges_directed(node, Outgoing)
                .map(|edge| edge.target().index())
                .collect::<BTreeSet<_>>();
            let vdown = vg.edges_directed(vnode, Outgoing)
                .map(|edge| edge.target().index())
                .collect::<BTreeSet<_>>();
            assert!(down == vdown);
        }
    }
}
