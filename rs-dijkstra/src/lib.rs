use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Vertex {
    label: String,
}

struct Edge {
    weight: u32,
    src: Vertex,
    dst: Vertex,
}

struct Graph {
    vertexes: Vec<Vertex>,
    edges: Vec<Edge>,
}

impl Graph {
    fn new() -> Self {
        Graph {
            vertexes: Vec::new(),
            edges: Vec::new(),
        }
    }

    pub fn add_vertex(&mut self, label: &str) {
        let label = label.to_string().to_uppercase();
        self.vertexes.push(Vertex { label });
    }

    fn try_get_vertex(&self, label: &str) -> Option<&Vertex> {
        let label = label.to_string().to_uppercase();
        self.vertexes.iter().find(|v| v.label == label)
    }

    fn get_vertex_src_edges(&self, src: &Vertex) -> Vec<&Edge> {
        self.edges
            .iter()
            .filter(|e| e.src == *src)
            .collect::<Vec<&Edge>>()
    }

    pub fn add_edge(&mut self, weight: u32, src: &str, dst: &str) -> Result<(), ()> {
        let src = src.to_string().to_uppercase();
        let dst = dst.to_string().to_uppercase();
        let src = self.try_get_vertex(&src).ok_or(())?.clone();
        let dst = self.try_get_vertex(&dst).ok_or(())?.clone();
        self.edges.push(Edge { weight, src, dst });
        Ok(())
    }

    pub fn add_double_edge(&mut self, weight: u32, src: &str, dst: &str) -> Result<(), ()> {
        self.add_edge(weight, src, dst)?;
        self.add_edge(weight, dst, src)?;
        Ok(())
    }

    pub fn dijkstra(&self, src: &str, destination: &str) -> Option<HashMap<Vertex, u32>> {
        let src = src.to_string().to_uppercase();
        let destination = destination.to_string().to_uppercase();
        let mut distances: HashMap<Vertex, u32> = HashMap::new();
        let mut heap: BinaryHeap<Reverse<(u32, Vertex)>> = BinaryHeap::new();
        let initial_vertex = self.try_get_vertex(&src)?;
        distances.insert(initial_vertex.clone(), 0);
        heap.push(Reverse((0, initial_vertex.clone())));

        while let Some(Reverse((distance, vertex))) = heap.pop() {
            if vertex.label == destination {
                return Some(distances);
            }
            let to_vertex_distance = *distances.get(&vertex).unwrap_or(&u32::MAX);

            if to_vertex_distance < distance {
                // We've already found a faster path to `vertex`, so let's ignore this one.
                continue;
            }

            let edges = self.get_vertex_src_edges(&vertex);

            for edge in edges {
                let next = edge.dst.clone();
                let next_distance = distance + edge.weight;
                if next_distance < *distances.get(&next).unwrap_or(&u32::MAX) {
                    distances.insert(next.clone(), next_distance);
                    heap.push(Reverse((next_distance, next)));
                }
            }
        }
        Some(distances)
    }

    pub fn shortest_path(&self, src: &str, destination: &str) -> Option<u32> {
        let dijkstra_result = self.dijkstra(src, destination)?;
        let destination = destination.to_string().to_uppercase();
        let destination = self.try_get_vertex(&destination)?;
        dijkstra_result.get(destination).cloned()
    }
}

#[cfg(test)]
mod test {
    use crate::Graph;

    #[test]
    fn test_dijkstra() {
        let mut graph = Graph::new();
        graph.add_vertex("Farm");
        graph.add_vertex("Market");
        graph.add_vertex("Restaurant");
        graph.add_vertex("Factory");

        graph.add_double_edge(5, "Farm", "Factory").unwrap();
        graph.add_double_edge(2, "Farm", "Market").unwrap();
        graph.add_double_edge(9, "Farm", "Restaurant").unwrap();

        graph.add_edge(6, "Market", "Restaurant").unwrap();

        graph.add_double_edge(8, "Factory", "Restaurant").unwrap();

        let result = graph.dijkstra("Market", "Factory").unwrap();

        assert_eq!(result.len(), 4);
        assert_eq!(
            result
                .get(&graph.try_get_vertex("Market").unwrap().clone())
                .unwrap(),
            &0
        );
        assert_eq!(
            result
                .get(&graph.try_get_vertex("Farm").unwrap().clone())
                .unwrap(),
            &2
        );
        assert_eq!(
            result
                .get(&graph.try_get_vertex("Restaurant").unwrap().clone())
                .unwrap(),
            &6
        );
        assert_eq!(
            result
                .get(&graph.try_get_vertex("Factory").unwrap().clone())
                .unwrap(),
            &7
        );
    }

    #[test]
    fn test_shortest_path() {
        let mut graph = Graph::new();
        graph.add_vertex("Farm");
        graph.add_vertex("Market");
        graph.add_vertex("Restaurant");
        graph.add_vertex("Factory");

        graph.add_double_edge(5, "Farm", "Factory").unwrap();
        graph.add_double_edge(2, "Farm", "Market").unwrap();
        graph.add_double_edge(9, "Farm", "Restaurant").unwrap();

        graph.add_edge(6, "Market", "Restaurant").unwrap();

        graph.add_double_edge(8, "Factory", "Restaurant").unwrap();

        let result = graph.shortest_path("Market", "Factory").unwrap();
        assert_eq!(result, 7)
    }
}
