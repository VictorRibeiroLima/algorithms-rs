use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Path {
    vertexes: Vec<Vertex>,
    weight: u32,
}

impl Path {
    fn new_max() -> Self {
        Path {
            vertexes: Vec::new(),
            weight: u32::MAX,
        }
    }

    fn push(&mut self, vertex: Vertex, weight: u32) {
        self.vertexes.push(vertex);
        self.weight = weight;
    }

    fn weight(&self) -> u32 {
        self.weight
    }
}

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

    pub fn dijkstra(&self, src: &str, destination: &str) -> Option<HashMap<Vertex, Path>> {
        let src = src.to_string().to_uppercase();
        let destination = destination.to_string().to_uppercase();
        let mut distances: HashMap<Vertex, Path> = HashMap::new();
        let mut heap: BinaryHeap<Reverse<(u32, Vertex)>> = BinaryHeap::new();
        let initial_vertex = self.try_get_vertex(&src)?;
        let path = Path {
            vertexes: vec![initial_vertex.clone()],
            weight: 0,
        };
        distances.insert(initial_vertex.clone(), path);
        heap.push(Reverse((0, initial_vertex.clone())));

        while let Some(Reverse((distance, vertex))) = heap.pop() {
            if vertex.label == destination {
                return Some(distances);
            }
            let to_vertex_path = distances.get(&vertex).unwrap_or(&Path::new_max()).clone();

            if to_vertex_path.weight() < distance {
                // We've already found a faster path to `vertex`, so let's ignore this one.
                continue;
            }

            let edges = self.get_vertex_src_edges(&vertex);

            for edge in edges {
                let next = edge.dst.clone();
                let next_distance = distance + edge.weight;
                let mut distance_path: Path =
                    distances.get(&next).unwrap_or(&Path::new_max()).clone();
                if next_distance < distance_path.weight() {
                    distance_path.vertexes = to_vertex_path.vertexes.clone();
                    distance_path.push(next.clone(), next_distance);
                    distances.insert(next.clone(), distance_path);
                    heap.push(Reverse((next_distance, next)));
                }
            }
        }
        Some(distances)
    }

    pub fn shortest_path_weight(&self, src: &str, destination: &str) -> Option<u32> {
        let dijkstra_result = self.dijkstra(src, destination)?;
        let destination = destination.to_string().to_uppercase();
        let destination = self.try_get_vertex(&destination)?;
        let path = dijkstra_result.get(destination).cloned()?;
        Some(path.weight())
    }

    pub fn shortest_path(&self, src: &str, destination: &str) -> Option<Path> {
        let dijkstra_result = self.dijkstra(src, destination)?;
        let destination = destination.to_string().to_uppercase();
        let destination = self.try_get_vertex(&destination)?;
        let path = dijkstra_result.get(destination).cloned()?;
        Some(path)
    }
}

/*

   Market - 6 - Restaurant
     |         /       |
     |       /         |
     2     9           20
     |   /             |
     | /               |
   Farm - 5 --------Factory
*/
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

        graph.add_double_edge(20, "Factory", "Restaurant").unwrap();

        let result = graph.dijkstra("Market", "Factory").unwrap();

        assert_eq!(result.len(), 4);

        graph.try_get_vertex("FARM").unwrap();
        graph.try_get_vertex("MARKET").unwrap();
        graph.try_get_vertex("RESTAURANT").unwrap();
        graph.try_get_vertex("FACTORY").unwrap();
    }

    #[test]
    fn test_shortest_path_weight() {
        let mut graph = Graph::new();
        graph.add_vertex("Farm");
        graph.add_vertex("Market");
        graph.add_vertex("Restaurant");
        graph.add_vertex("Factory");

        graph.add_double_edge(5, "Farm", "Factory").unwrap();
        graph.add_double_edge(2, "Farm", "Market").unwrap();
        graph.add_double_edge(9, "Farm", "Restaurant").unwrap();

        graph.add_edge(6, "Market", "Restaurant").unwrap();

        graph.add_double_edge(20, "Factory", "Restaurant").unwrap();

        let result = graph.shortest_path_weight("Market", "Factory").unwrap();
        assert_eq!(result, 7)
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

        graph.add_double_edge(20, "Factory", "Restaurant").unwrap();

        let path = graph.shortest_path("Market", "Factory").unwrap();
        let weight = path.weight();
        let result = path.vertexes;
        assert_eq!(weight, 7);
        assert_eq!(result.len(), 3);
        println!("{:?}", result);
        assert_eq!(result[0].label, "MARKET");
        assert_eq!(result[1].label, "FARM");
        assert_eq!(result[2].label, "FACTORY");
    }

    #[test]
    fn test_shortest_path2() {
        let mut graph = Graph::new();
        graph.add_vertex("Farm");
        graph.add_vertex("Market");
        graph.add_vertex("Restaurant");
        graph.add_vertex("Factory");

        graph.add_double_edge(5, "Farm", "Factory").unwrap();
        graph.add_double_edge(2, "Farm", "Market").unwrap();
        graph.add_double_edge(9, "Farm", "Restaurant").unwrap();

        graph.add_edge(6, "Market", "Restaurant").unwrap();

        graph.add_double_edge(20, "Factory", "Restaurant").unwrap();

        let path = graph.shortest_path("Factory", "Restaurant").unwrap();
        let weight = path.weight();
        let result = path.vertexes;
        println!("{:?}", result);
        assert_eq!(weight, 13);
        assert_eq!(result.len(), 4);
        assert_eq!(result[0].label, "FACTORY");
        assert_eq!(result[1].label, "FARM");
        assert_eq!(result[2].label, "MARKET");
        assert_eq!(result[3].label, "RESTAURANT");
    }
}
