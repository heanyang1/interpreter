use std::{
    cmp::{Eq, Ordering},
    collections::HashMap,
    hash::Hash,
};

pub struct UnionFind<T>
where
    T: Hash + Eq + Clone,
{
    pub parent: Vec<usize>,
    pub rank: Vec<usize>,
    pub elems: Vec<T>,
    pub elem_index: HashMap<T, usize>,
}

impl<T> UnionFind<T>
where
    T: Hash + Eq + Clone,
{
    pub fn new(elems: Vec<T>) -> Self {
        let n = elems.len();
        let parent: Vec<usize> = (0..n as usize).collect();
        let rank = vec![0; n];
        let elem_index: HashMap<T, usize> = elems
            .iter()
            .enumerate()
            .map(|(x, y)| (y.clone(), x))
            .collect();
        UnionFind {
            parent,
            rank,
            elem_index,
            elems,
        }
    }

    pub fn get_idx(&self, x: &T) -> usize {
        self.elem_index.get(x).unwrap().clone()
    }

    pub fn find(&mut self, x: &T) -> &T {
        let idx = self.find_with_id(self.get_idx(x));
        &self.elems[idx]
    }

    fn find_with_id(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find_with_id(self.parent[x]);
        }
        self.parent[x]
    }

    pub fn union(&mut self, x: &T, y: &T) -> bool {
        let root_x = self.find_with_id(self.get_idx(x));
        let root_y = self.find_with_id(self.get_idx(y));
        if root_x == root_y {
            return false;
        }
        match self.rank[root_x as usize].cmp(&self.rank[root_y as usize]) {
            Ordering::Less => self.parent[root_x as usize] = root_y,
            Ordering::Greater => self.parent[root_y as usize] = root_x,
            Ordering::Equal => {
                self.parent[root_y as usize] = root_x;
                self.rank[root_x as usize] += 1;
            }
        }
        true
    }

    pub fn connected(&mut self, x: &T, y: &T) -> bool {
        self.find_with_id(self.get_idx(x)) == self.find_with_id(self.get_idx(y))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let uf = UnionFind::new(elems);
        assert_eq!(uf.parent, vec![0, 1, 2, 3, 4]);
        assert_eq!(uf.rank, vec![0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_find_single() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        assert_eq!(*uf.find(&0), 0);
        assert_eq!(*uf.find(&1), 1);
        assert_eq!(*uf.find(&2), 2);
    }

    #[test]
    fn test_union() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        assert!(uf.union(&0, &1));
        assert!(uf.union(&2, &3));
        assert!(uf.connected(&0, &1));
        assert!(!uf.connected(&0, &2));
        assert!(uf.union(&0, &2));
        assert!(uf.connected(&0, &2));
        assert!(uf.connected(&0, &3));
    }

    #[test]
    fn test_already_connected() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1);
        assert!(!uf.union(&0, &1));
    }

    #[test]
    fn test_connected() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        assert!(!uf.connected(&0, &1));
        uf.union(&0, &1);
        assert!(uf.connected(&0, &1));
    }

    #[test]
    fn test_path_compression() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1);
        uf.union(&1, &2);
        uf.union(&2, &3);
        assert!(uf.connected(&0, &3));
    }

    #[test]
    fn test_rank() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1);
        assert_eq!(uf.rank[0], 1);
    }

    #[test]
    fn test_union_rank_less() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        uf.parent[1] = 2;
        uf.rank[0] = 1;
        uf.rank[2] = 2;
        uf.union(&0, &1);
        let root = uf.get_idx(&0);
        assert_eq!(uf.parent[root], 2);
    }

    #[test]
    fn test_union_rank_greater() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        uf.parent[1] = 2;
        uf.rank[0] = 2;
        uf.rank[2] = 1;
        uf.union(&0, &1);
        assert_eq!(uf.parent[2], 0);
    }
}
