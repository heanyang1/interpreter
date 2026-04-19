use std::{
    cmp::{Eq, Ordering},
    collections::HashMap,
    fmt::Display,
    hash::Hash,
};

pub struct UnionFind<T>
where
    T: Hash + Eq + Clone + Display,
{
    pub parent: Vec<usize>,
    pub rank: Vec<usize>,
    pub elems: Vec<T>,
    pub elem_index: HashMap<T, usize>,
}

impl<T> UnionFind<T>
where
    T: Hash + Eq + Clone + Display,
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

    pub fn get_idx(&self, x: &T) -> Result<usize, String> {
        match self.elem_index.get(x) {
            Some(x) => Ok(x.clone()),
            None => Err(format!("{x} is not in the union-find")),
        }
    }

    pub fn find(&mut self, x: &T) -> Result<&T, String> {
        let idx = self.find_with_id(self.get_idx(x)?);
        Ok(&self.elems[idx])
    }

    fn find_with_id(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find_with_id(self.parent[x]);
        }
        self.parent[x]
    }

    pub fn union(&mut self, x: &T, y: &T) -> Result<bool, String> {
        let root_x = self.find_with_id(self.get_idx(x)?);
        let root_y = self.find_with_id(self.get_idx(y)?);
        if root_x == root_y {
            return Ok(false);
        }
        match self.rank[root_x as usize].cmp(&self.rank[root_y as usize]) {
            Ordering::Less => self.parent[root_x as usize] = root_y,
            Ordering::Greater => self.parent[root_y as usize] = root_x,
            Ordering::Equal => {
                self.parent[root_y as usize] = root_x;
                self.rank[root_x as usize] += 1;
            }
        }
        Ok(true)
    }

    pub fn connected(&mut self, x: &T, y: &T) -> Result<bool, String> {
        Ok(self.find_with_id(self.get_idx(x)?) == self.find_with_id(self.get_idx(y)?))
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
        assert_eq!(*uf.find(&0).unwrap(), 0);
        assert_eq!(*uf.find(&1).unwrap(), 1);
        assert_eq!(*uf.find(&2).unwrap(), 2);
    }

    #[test]
    fn test_union() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        assert!(uf.union(&0, &1).unwrap());
        assert!(uf.union(&2, &3).unwrap());
        assert!(uf.connected(&0, &1).unwrap());
        assert!(!uf.connected(&0, &2).unwrap());
        assert!(uf.union(&0, &2).unwrap());
        assert!(uf.connected(&0, &2).unwrap());
        assert!(uf.connected(&0, &3).unwrap());
    }

    #[test]
    fn test_already_connected() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        assert!(!uf.union(&0, &1).unwrap());
    }

    #[test]
    fn test_connected() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        assert!(!uf.connected(&0, &1).unwrap());
        uf.union(&0, &1).unwrap();
        assert!(uf.connected(&0, &1).unwrap());
    }

    #[test]
    fn test_path_compression() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        uf.union(&1, &2).unwrap();
        uf.union(&2, &3).unwrap();
        assert!(uf.connected(&0, &3).unwrap());
    }

    #[test]
    fn test_rank() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        assert_eq!(uf.rank[0], 1);
    }

    #[test]
    fn test_union_rank_less() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        uf.parent[1] = 2;
        uf.rank[0] = 1;
        uf.rank[2] = 2;
        uf.union(&0, &1).unwrap();
        let root = uf.get_idx(&0).unwrap();
        assert_eq!(uf.parent[root], 2);
    }

    #[test]
    fn test_union_rank_greater() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        uf.parent[1] = 2;
        uf.rank[0] = 2;
        uf.rank[2] = 1;
        uf.union(&0, &1).unwrap();
        assert_eq!(uf.parent[2], 0);
    }
}
