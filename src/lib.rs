#[cfg(test)]
extern crate capngraph;
extern crate fixedbitset;
extern crate fnv;
extern crate petgraph;

use fixedbitset::FixedBitSet;
use fnv::{FnvHashMap, FnvHashSet};
use petgraph::graph;
use petgraph::visit::{
    Data, EdgeRef, GraphBase, GraphProp, IntoEdgeReferences, IntoEdges, IntoNeighbors,
    IntoNeighborsDirected, IntoNodeIdentifiers, IntoNodeReferences, NodeCompactIndexable,
    NodeCount, NodeIndexable, VisitMap, Visitable,
};
use petgraph::Direction;
use petgraph::Direction::*;
use petgraph::{Directed, EdgeType, Undirected};
use std::iter::{Enumerate, Iterator, Map};
use std::marker::PhantomData;
use std::ops::{Index, IndexMut, Range};
use std::slice::Iter;
use std::vec::IntoIter;

pub type Graph<N, E, D = Directed> = VecGraph<N, E, D>;

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

    fn is_node_index() -> bool {
        true
    }
}

impl From<usize> for NodeIndex {
    fn from(u: usize) -> Self {
        Self::new(u)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct EdgeIndex(u32);

impl EdgeIndex {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    pub fn new(idx: usize) -> Self {
        EdgeIndex(idx as u32)
    }
}

impl graph::GraphIndex for EdgeIndex {
    fn index(&self) -> usize {
        self.0 as usize
    }

    fn is_node_index() -> bool {
        false
    }
}

impl From<usize> for EdgeIndex {
    fn from(u: usize) -> Self {
        EdgeIndex(u as u32)
    }
}

/// A directed adjacency-list graph implemented on Vectors. Indices are all `usize` as a result.
#[derive(Clone, Debug)]
pub struct VecGraph<N, E, D = Directed> {
    num_nodes: usize,
    num_edges: usize,
    node_weights: Vec<N>,
    edges: Vec<(usize, usize, E)>,
    incoming_edges: Vec<Vec<usize>>,
    outgoing_edges: Vec<Vec<usize>>,
    ty: PhantomData<D>,
}

impl<N, E: Clone, D> VecGraph<N, E, D>
where
    D: EdgeType,
{
    pub fn from_petgraph(g: graph::Graph<N, E, D>) -> Self {
        let (nodes, edges) = g.into_nodes_edges();
        let mut incoming_edges = vec![Vec::new(); nodes.len()];
        let mut outgoing_edges = vec![Vec::new(); nodes.len()];

        let edges = edges
            .into_iter()
            .map(|edge| (edge.source().index(), edge.target().index(), edge.weight))
            .collect::<Vec<_>>();

        for (i, &(source, target, _)) in edges.iter().enumerate() {
            incoming_edges[target].push(i);
            outgoing_edges[source].push(i);
        }

        VecGraph {
            num_nodes: nodes.len(),
            num_edges: edges.len(),
            node_weights: nodes.into_iter().map(|node| node.weight).collect(),
            edges: edges,
            incoming_edges: incoming_edges,
            outgoing_edges: outgoing_edges,
            ty: PhantomData,
        }
    }
}

impl<N: Default + Clone, E, D> VecGraph<N, E, D>
where
    D: EdgeType,
{
    pub fn new_with_nodes(node_count: usize) -> Self {
        VecGraph {
            num_nodes: node_count,
            num_edges: 0,
            node_weights: vec![N::default(); node_count],
            edges: vec![],
            incoming_edges: vec![Vec::new(); node_count],
            outgoing_edges: vec![Vec::new(); node_count],
            ty: PhantomData,
        }
    }

    pub fn from_edges(edges: Vec<(u32, u32, E)>) -> Self {
        let num_nodes = edges.iter().fold(0, |prev, &(a, b, _)| {
            ::std::cmp::max(a, ::std::cmp::max(b, prev))
        }) as usize
            + 1;
        let mut incoming_edges = vec![Vec::new(); num_nodes];
        let mut outgoing_edges = vec![Vec::new(); num_nodes];

        for (i, &(source, target, _)) in edges.iter().enumerate() {
            incoming_edges[target as usize].push(i);
            outgoing_edges[source as usize].push(i);
        }

        VecGraph {
            num_nodes,
            num_edges: edges.len(),
            node_weights: vec![N::default(); num_nodes],
            edges: edges
                .into_iter()
                .map(|(a, b, w)| (a as usize, b as usize, w))
                .collect(),
            incoming_edges,
            outgoing_edges,
            ty: PhantomData,
        }
    }

    pub fn oriented_from_edges(mut edges: Vec<(u32, u32, E)>, orientation: Direction) -> Self {
        let num_nodes = edges.iter().fold(0, |prev, &(a, b, _)| {
            ::std::cmp::max(a, ::std::cmp::max(b, prev))
        }) as usize
            + 1;
        let mut incoming_edges = vec![Vec::new(); num_nodes];
        let mut outgoing_edges = vec![Vec::new(); num_nodes];

        match orientation {
            Incoming => {
                edges.sort_unstable_by(|&(_, ref a, _), &(_, ref b, _)| a.cmp(b));
            }
            Outgoing => {
                edges.sort_unstable_by(|&(ref a, _, _), &(ref b, _, _)| a.cmp(b));
            }
        }

        for (i, &(source, target, _)) in edges.iter().enumerate() {
            incoming_edges[target as usize].push(i);
            outgoing_edges[source as usize].push(i);
        }

        VecGraph {
            num_nodes,
            num_edges: edges.len(),
            node_weights: vec![N::default(); num_nodes],
            edges: edges
                .into_iter()
                .map(|(a, b, w)| (a as usize, b as usize, w))
                .collect(),
            incoming_edges,
            outgoing_edges,
            ty: PhantomData,
        }
    }
}

impl<N, E, D> VecGraph<N, E, D>
where
    D: EdgeType,
{
    #[inline]
    pub fn is_directed() -> bool {
        D::is_directed()
    }

    pub fn new() -> Self {
        VecGraph {
            num_nodes: 0,
            num_edges: 0,
            node_weights: vec![],
            edges: vec![],
            incoming_edges: vec![],
            outgoing_edges: vec![],
            ty: PhantomData,
        }
    }

    pub fn with_capacity(node_count: usize, edge_count: usize) -> Self {
        VecGraph {
            num_nodes: 0,
            num_edges: 0,
            node_weights: Vec::with_capacity(node_count),
            edges: Vec::with_capacity(edge_count),
            incoming_edges: Vec::with_capacity(node_count),
            outgoing_edges: Vec::with_capacity(node_count),
            ty: PhantomData,
        }
    }

    pub fn add_node(&mut self, weight: N) -> NodeIndex {
        self.num_nodes += 1;
        self.node_weights.push(weight);
        self.incoming_edges.push(vec![]);
        self.outgoing_edges.push(vec![]);

        NodeIndex(self.num_nodes as u32 - 1)
    }

    pub fn node_indices(&self) -> Map<Range<usize>, fn(usize) -> NodeIndex> {
        (0..self.num_nodes).map(NodeIndex::new)
    }

    pub fn contains_edge(&self, src: NodeIndex, dst: NodeIndex) -> bool {
        self.find_edge(src, dst).is_some()
    }

    pub fn update_edge(&mut self, a: NodeIndex, b: NodeIndex, weight: E) -> EdgeIndex {
        if let Some(idx) = self.find_edge(a, b) {
            self[idx] = weight;
            idx
        } else {
            self.add_edge(a, b, weight)
        }
    }

    pub fn update_edge_with<F>(
        &mut self,
        a: NodeIndex,
        b: NodeIndex,
        weight_fn: F,
        weight_default: E,
    ) -> EdgeIndex
    where
        F: Fn(&E) -> E,
    {
        if let Some(idx) = self.find_edge(a, b) {
            self[idx] = weight_fn(&self[idx]);
            idx
        } else {
            self.add_edge(a, b, weight_default)
        }
    }

    pub fn edge_indices(&self) -> EdgeIndices {
        EdgeIndices {
            internal: (0..self.num_edges)
                .map(|idx| EdgeIndex(idx as u32))
                .collect::<Vec<_>>()
                .into_iter(),
        }
    }

    pub fn edge_count(&self) -> usize {
        self.num_edges
    }

    pub fn edge_indices_directed<'a, F>(
        &'a self,
        a: NodeIndex,
        dir: Direction,
    ) -> Map<Edges<'a, N, E, D>, fn(EdgeReference<'a, E>) -> EdgeIndex> {
        self.edges_directed(a, dir).map(edge_id::<E>)
    }

    pub fn edge_weights_mut(&mut self) -> impl Iterator<Item = &mut E> {
        self.edges.iter_mut().map(|(_, _, w)| w)
    }

    pub fn edge_endpoints(&self, index: EdgeIndex) -> Option<(NodeIndex, NodeIndex)> {
        self.edges
            .get(index.index())
            .map(|&(source, dest, _)| (NodeIndex(source as u32), NodeIndex(dest as u32)))
    }

    pub fn filter_map<F, G, N2, E2>(&self, node_map: F, edge_map: G) -> Graph<N2, E2>
    where
        F: Fn(NodeIndex, &N) -> Option<N2>,
        G: Fn(EdgeIndex, &E) -> Option<E2>,
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

        let mut new_edges = Vec::with_capacity(self.edge_count());
        let mut incoming = vec![Vec::new(); new_nodes.len()];
        let mut outgoing = vec![Vec::new(); new_nodes.len()];
        for (i, &(src, dst, ref weight)) in self.edges.iter().enumerate() {
            if blacklist.contains(&src) || blacklist.contains(&dst) {
                continue;
            } else {
                if let Some(w2) = edge_map(EdgeIndex(i as u32), weight) {
                    incoming[relabel[&dst]].push(new_edges.len());
                    outgoing[relabel[&src]].push(new_edges.len());
                    new_edges.push((relabel[&src], relabel[&dst], w2));
                }
            }
        }

        Graph {
            num_nodes: new_nodes.len(),
            num_edges: new_edges.len(),
            node_weights: new_nodes,
            edges: new_edges,
            incoming_edges: incoming,
            outgoing_edges: outgoing,
            ty: PhantomData,
        }
    }

    pub fn find_edge(&self, src: NodeIndex, dst: NodeIndex) -> Option<EdgeIndex> {
        if !Self::is_directed() && src > dst {
            self.find_edge(dst, src)
        } else {
            self.outgoing_edges[src.index()]
                .iter()
                .find(|&idx| self.edges[*idx].1 == dst.index())
                .map(|&idx| EdgeIndex(idx as u32))
        }
    }

    pub fn add_edge(&mut self, a: NodeIndex, b: NodeIndex, weight: E) -> EdgeIndex {
        if !Self::is_directed() && a > b {
            self.add_edge(b, a, weight)
        } else {
            let idx = EdgeIndex(self.num_edges as u32);
            self.incoming_edges[b.index()].push(self.num_edges);
            self.outgoing_edges[a.index()].push(self.num_edges);
            self.edges.push((a.index(), b.index(), weight));
            self.num_edges += 1;
            idx
        }
    }

    /// Remove an edge `e` from the network. This invalidates *ALL* edge indices greater than `e`.
    ///
    /// If you use this method, don't hold on to edge indices.
    ///
    /// This is EXPENSIVE. Avoid.
    pub fn remove_edge(&mut self, e: EdgeIndex) -> Option<(NodeIndex, NodeIndex, E)> {
        if e.index() >= self.num_edges {
            None
        } else {
            let (a, b, w) = self.edges.remove(e.index());
            self.incoming_edges[b].retain(|&ix| ix != e.index());
            self.outgoing_edges[a].retain(|&ix| ix != e.index());
            self.num_edges -= 1;

            for eids in &mut self.incoming_edges {
                for eid in eids {
                    if *eid > e.index() {
                        *eid -= 1;
                    }
                }
            }

            for eids in &mut self.outgoing_edges {
                for eid in eids {
                    if *eid > e.index() {
                        *eid -= 1;
                    }
                }
            }

            Some((NodeIndex(a as u32), NodeIndex(b as u32), w))
        }
    }

    pub fn raw_edgelist(&self) -> &[(usize, usize, E)] {
        &self.edges
    }

    pub fn raw_edges(&self, a: NodeIndex, dir: Direction) -> &[usize] {
        match dir {
            Direction::Outgoing => &self.outgoing_edges[a.index()],
            Direction::Incoming => &self.incoming_edges[a.index()],
        }
    }
}

impl<N, E, D> GraphBase for VecGraph<N, E, D> {
    type EdgeId = EdgeIndex;
    type NodeId = NodeIndex;
}

pub struct Neighbors<'a, N: 'a, E: 'a, D: 'a> {
    g: &'a Graph<N, E, D>,
    internal: Box<dyn Iterator<Item = (usize, Direction)> + 'a>,
}

impl<'a, N, E, D> Neighbors<'a, N, E, D> {
    pub fn detach(self) -> NeighborWalker {
        NeighborWalker {
            index: 0,
            internal: self
                .internal
                .map(|(idx, dir)| (EdgeIndex(idx as u32), dir))
                .collect(),
        }
    }
}

impl<'a, N, E, D> Iterator for Neighbors<'a, N, E, D> {
    type Item = NodeIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next().map(|(idx, dir)| {
            NodeIndex(match dir {
                Outgoing => self.g.edges[idx].1 as u32,
                Incoming => self.g.edges[idx].0 as u32,
            })
        })
    }
}

#[derive(Clone, Debug)]
pub struct NeighborWalker {
    internal: Vec<(EdgeIndex, Direction)>,
    index: usize,
}

impl NeighborWalker {
    pub fn next<N, E>(&mut self, g: &Graph<N, E>) -> Option<(EdgeIndex, NodeIndex)> {
        if self.index >= self.internal.len() {
            return None;
        }

        let (edge, dir) = self.internal[self.index];
        self.index += 1;
        let node = match dir {
            Outgoing => NodeIndex(g.edges[edge.index()].1 as u32),
            Incoming => NodeIndex(g.edges[edge.index()].0 as u32),
        };

        Some((edge, node))
    }

    pub fn next_node<N, E>(&mut self, g: &Graph<N, E>) -> Option<NodeIndex> {
        self.next(g).map(|(_, node)| node)
    }

    pub fn next_edge<N, E>(&mut self, g: &Graph<N, E>) -> Option<EdgeIndex> {
        self.next(g).map(|(edge, _)| edge)
    }
}

pub struct Edges<'a, N: 'a, E: 'a, D> {
    graph: &'a Graph<N, E, D>,
    internal: Iter<'a, usize>,
}

impl<'a, N, E, D> Iterator for Edges<'a, N, E, D> {
    type Item = EdgeReference<'a, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.internal.next().map(|&idx| {
            let (source, dest, ref weight) = self.graph.edges[idx];
            EdgeReference {
                source: source,
                dest: dest,
                weight: weight,
                index: idx,
            }
        })
    }
}

#[derive(Debug)]
pub struct EdgeReference<'a, E: 'a> {
    source: usize,
    dest: usize,
    weight: &'a E,
    index: usize,
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
        EdgeIndex(self.index as u32)
    }
}

fn edge_id<'a, E>(er: EdgeReference<'a, E>) -> EdgeIndex {
    er.id()
}

pub struct EdgeIndices {
    internal: IntoIter<EdgeIndex>,
}

impl Iterator for EdgeIndices {
    type Item = EdgeIndex;

    fn next(&mut self) -> Option<EdgeIndex> {
        self.internal.next()
    }
}

impl<'a, N, E, D> IntoNeighbors for &'a Graph<N, E, D>
where
    D: EdgeType,
{
    type Neighbors = Neighbors<'a, N, E, D>;

    fn neighbors(self, n: NodeIndex) -> Self::Neighbors {
        if D::is_directed() {
            self.neighbors_directed(n, Direction::Outgoing)
        } else {
            Neighbors {
                g: &self,
                internal: Box::new(
                    self.outgoing_edges[n.index()]
                        .iter()
                        .map(|&ix| (ix, Outgoing))
                        .chain(
                            self.incoming_edges[n.index()]
                                .iter()
                                .map(|&ix| (ix, Incoming)),
                        ),
                ),
            }
        }
    }
}

impl<'a, N, E, D> IntoNeighborsDirected for &'a Graph<N, E, D>
where
    D: EdgeType,
{
    type NeighborsDirected = Neighbors<'a, N, E, D>;

    fn neighbors_directed(self, n: NodeIndex, d: Direction) -> Self::NeighborsDirected {
        match d {
            Direction::Outgoing => Neighbors {
                g: &self,
                internal: Box::new(
                    self.outgoing_edges[n.index()]
                        .iter()
                        .map(move |&ix| (ix, d)),
                ),
            },
            Direction::Incoming => Neighbors {
                g: &self,
                internal: Box::new(
                    self.incoming_edges[n.index()]
                        .iter()
                        .map(move |&ix| (ix, d)),
                ),
            },
        }
    }
}

impl<N, E, D> NodeCount for Graph<N, E, D> {
    fn node_count(&self) -> usize {
        self.num_nodes
    }
}

impl<N, E, D> NodeIndexable for Graph<N, E, D> {
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

impl<N, E, D> NodeCompactIndexable for Graph<N, E, D> {}

impl<N, E, D> Index<EdgeIndex> for Graph<N, E, D> {
    type Output = E;
    fn index(&self, index: EdgeIndex) -> &E {
        &self.edges[index.index()].2
    }
}
impl<N, E, D> IndexMut<EdgeIndex> for Graph<N, E, D> {
    fn index_mut(&mut self, index: EdgeIndex) -> &mut E {
        &mut self.edges[index.index()].2
    }
}

impl<N, E, D> Index<NodeIndex> for Graph<N, E, D> {
    type Output = N;
    fn index(&self, index: NodeIndex) -> &N {
        &self.node_weights[index.index()]
    }
}

impl<N, E, D> IndexMut<NodeIndex> for Graph<N, E, D> {
    fn index_mut(&mut self, index: NodeIndex) -> &mut N {
        &mut self.node_weights[index.index()]
    }
}

impl<'a, N, E, D> IntoNodeIdentifiers for &'a Graph<N, E, D>
where
    D: EdgeType,
{
    type NodeIdentifiers = Map<Range<usize>, fn(usize) -> NodeIndex>;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.node_indices()
    }
}

impl<N, E, D> GraphProp for Graph<N, E, D>
where
    D: EdgeType,
{
    type EdgeType = D;
}

impl<N, E, D> Data for Graph<N, E, D> {
    type NodeWeight = N;
    type EdgeWeight = E;
}

impl<'a, N, E, D> IntoNodeReferences for &'a Graph<N, E, D>
where
    D: EdgeType,
{
    type NodeRef = (NodeIndex, &'a N);
    type NodeReferences = Map<Enumerate<Iter<'a, N>>, fn((usize, &'a N)) -> Self::NodeRef>;
    fn node_references(self) -> Self::NodeReferences {
        fn mapper<NR>((i, w): (usize, NR)) -> (NodeIndex, NR) {
            (NodeIndex::new(i), w)
        }
        self.node_weights.iter().enumerate().map(mapper::<&'a N>)
    }
}

impl<'a, N, E, D> IntoEdgeReferences for &'a Graph<N, E, D>
where
    D: EdgeType,
{
    type EdgeRef = EdgeReference<'a, E>;
    type EdgeReferences = Map<
        Enumerate<Iter<'a, (usize, usize, E)>>,
        fn((usize, &'a (usize, usize, E))) -> Self::EdgeRef,
    >;

    fn edge_references(self) -> Self::EdgeReferences {
        fn mapper<'a, E>(
            (idx, &(src, dst, ref weight)): (usize, &'a (usize, usize, E)),
        ) -> EdgeReference<'a, E> {
            EdgeReference {
                source: src,
                dest: dst,
                weight: weight,
                index: idx,
            }
        }

        self.edges.iter().enumerate().map(mapper::<E>)
    }
}

impl<'a, N, E> IntoEdges for &'a Graph<N, E, Directed> {
    type Edges = Box<dyn Iterator<Item = Self::EdgeRef> + 'a>;

    fn edges(self, a: NodeIndex) -> Self::Edges {
        Box::new(self.outgoing_edges[a.index()].iter().map(move |&ix| {
            let (source, dest, ref weight) = self.edges[ix];
            EdgeReference {
                source,
                dest,
                weight,
                index: ix,
            }
        }))
    }
}

impl<'a, N, E> IntoEdges for &'a Graph<N, E, Undirected> {
    type Edges = Box<dyn Iterator<Item = Self::EdgeRef> + 'a>;

    fn edges(self, a: NodeIndex) -> Self::Edges {
        Box::new(
            self.outgoing_edges[a.index()]
                .iter()
                .map(move |&ix| {
                    let (source, dest, ref weight) = self.edges[ix];
                    EdgeReference {
                        source,
                        dest,
                        weight,
                        index: ix,
                    }
                })
                .chain(self.incoming_edges[a.index()].iter().map(move |&ix| {
                    let (source, dest, ref weight) = self.edges[ix];
                    // flip the direction so that a == source always
                    EdgeReference {
                        source: dest,
                        dest: source,
                        weight,
                        index: ix,
                    }
                })),
        )
    }
}

pub trait IntoNeighborEdgesDirected: petgraph::visit::GraphRef + petgraph::visit::Data {
    type ER: EdgeRef<NodeId = Self::NodeId, EdgeId = Self::EdgeId, Weight = Self::EdgeWeight>;
    type NeighborEdgesDirected: Iterator<Item = Self::ER>;

    fn edges_directed(self, a: Self::NodeId, dir: Direction) -> Self::NeighborEdgesDirected;
}

impl<'a, N, E, D> IntoNeighborEdgesDirected for &'a Graph<N, E, D>
where
    D: EdgeType,
{
    type NeighborEdgesDirected = Edges<'a, N, E, D>;
    type ER = EdgeReference<'a, E>;
    fn edges_directed(self, a: NodeIndex, dir: Direction) -> Edges<'a, N, E, D> {
        Edges {
            graph: self,
            internal: match dir {
                Direction::Outgoing => self.outgoing_edges[a.index()].iter(),
                Direction::Incoming => self.incoming_edges[a.index()].iter(),
            },
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

impl<'a, N, E, D> Visitable for &'a Graph<N, E, D> {
    type Map = FixedBitSet;

    fn visit_map(&self) -> FixedBitSet {
        FixedBitSet::with_capacity(self.node_count())
    }

    fn reset_map(&self, map: &mut FixedBitSet) {
        map.clear()
    }
}

impl VisitMap<NodeIndex> for FixedBitSet {
    fn visit(&mut self, NodeIndex(ix): NodeIndex) -> bool {
        !self.put(ix as usize)
    }

    fn is_visited(&self, &NodeIndex(ix): &NodeIndex) -> bool {
        self.contains(ix as usize)
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
            assert!(
                g.edges_directed(node, Outgoing).count()
                    == vg.edges_directed(vnode, Outgoing).count()
            );
            assert!(
                g.edges_directed(node, Incoming).count()
                    == vg.edges_directed(vnode, Incoming).count()
            );

            let sum = g
                .edges_directed(node, Outgoing)
                .map(|edge| *edge.weight())
                .sum::<f32>();
            let vsum = vg
                .edges_directed(vnode, Outgoing)
                .map(|edge| *edge.weight())
                .sum::<f32>();

            assert!((sum - vsum).abs() < 1e-3);

            let sum = g
                .edges_directed(node, Incoming)
                .map(|edge| *edge.weight())
                .sum::<f32>();
            let vsum = vg
                .edges_directed(vnode, Incoming)
                .map(|edge| *edge.weight())
                .sum::<f32>();

            assert!((sum - vsum).abs() < 1e-3);

            let down = g
                .neighbors_directed(node, Outgoing)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            let vdown = vg
                .neighbors_directed(vnode, Outgoing)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            assert!(down == vdown);

            let up = g
                .neighbors_directed(node, Incoming)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            let vup = vg
                .neighbors_directed(vnode, Incoming)
                .map(|node| node.index())
                .collect::<BTreeSet<_>>();
            assert!(up == vup);

            let up = g
                .edges_directed(node, Incoming)
                .map(|edge| edge.source().index())
                .collect::<BTreeSet<_>>();
            let vup = vg
                .edges_directed(vnode, Incoming)
                .map(|edge| edge.source().index())
                .collect::<BTreeSet<_>>();
            assert!(up == vup);

            let down = g
                .edges_directed(node, Outgoing)
                .map(|edge| edge.target().index())
                .collect::<BTreeSet<_>>();
            let vdown = vg
                .edges_directed(vnode, Outgoing)
                .map(|edge| edge.target().index())
                .collect::<BTreeSet<_>>();
            assert!(down == vdown);
        }
    }

    #[test]
    fn test_undirected() {
        let mut vg = VecGraph::<(), (), Undirected>::new();

        let a = vg.add_node(());
        let b = vg.add_node(());
        let c = vg.add_node(());

        vg.add_edge(b, a, ());
        vg.add_edge(c, a, ());
        vg.add_edge(b, c, ());

        let a_neighbors = vg.neighbors(a).collect::<Vec<_>>();

        assert_eq!(a_neighbors, vec![b, c]);

        let a_edges = vg.edges(a).map(|eref| eref.target()).collect::<Vec<_>>();
        assert_eq!(a_edges, vec![b, c]);

        let b_edges = vg.edges(b).map(|eref| eref.target()).collect::<Vec<_>>();
        assert_eq!(b_edges, vec![c, a]);
    }

    #[test]
    fn test_remove_edge() {
        let g = capngraph::load_graph("data/ca-GrQc.bin").unwrap();
        let mut vg = Graph::from_petgraph(g.clone());

        let e = EdgeIndex(100);
        let (a, b) = vg.edge_endpoints(e).unwrap();

        let degree_a = vg.neighbors_directed(a, Outgoing).count();
        let degree_b = vg.neighbors_directed(b, Incoming).count();

        println!("{} {}", degree_a, degree_b);

        assert!(vg.neighbors_directed(a, Outgoing).any(|n| n == b));
        assert!(vg.neighbors_directed(b, Incoming).any(|n| n == a));

        vg.remove_edge(e);

        // they still have the other edges
        assert_eq!(vg.neighbors_directed(a, Outgoing).count(), degree_a - 1);
        assert_eq!(vg.neighbors_directed(b, Incoming).count(), degree_b - 1);

        // they no longer have the given edge
        assert!(!vg.neighbors_directed(a, Outgoing).any(|n| n == b));
        assert!(!vg.neighbors_directed(b, Incoming).any(|n| n == a));
    }
}
