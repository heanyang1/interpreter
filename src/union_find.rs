use std::{
    cmp::{Eq, Ordering},
    collections::HashMap,
    fmt::Display,
    hash::Hash,
};

use crate::ast_util::Printer;

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

    pub fn union(&mut self, x: &T, y: &T) -> Result<&T, String> {
        let root_x = self.find_with_id(self.get_idx(x)?);
        let root_y = self.find_with_id(self.get_idx(y)?);
        if root_x == root_y {
            return Ok(&self.elems[root_x]);
        }
        match self.rank[root_x as usize].cmp(&self.rank[root_y as usize]) {
            Ordering::Less => {
                self.parent[root_x as usize] = root_y;
                Ok(&self.elems[root_y])
            }
            Ordering::Greater => {
                self.parent[root_y as usize] = root_x;
                Ok(&self.elems[root_x])
            }
            Ordering::Equal => {
                self.parent[root_y as usize] = root_x;
                self.rank[root_x as usize] += 1;
                Ok(&self.elems[root_x])
            }
        }
    }

    pub fn connected(&mut self, x: &T, y: &T) -> Result<bool, String> {
        Ok(self.find_with_id(self.get_idx(x)?) == self.find_with_id(self.get_idx(y)?))
    }
}

impl<T> Display for UnionFind<T>
where
    T: Hash + Eq + Clone + Display + std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "UnionFind {{")?;
        writeln!(
            f,
            "  elements: {}",
            Printer(", ").print_map(&self.elem_index)
        )?;
        writeln!(
            f,
            "  parent: {}",
            Printer(", ").print_it(self.parent.iter())
        )?;
        writeln!(f, "  rank: {}", Printer(", ").print_it(self.rank.iter()))?;
        write!(f, "}}")
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
        let root01 = uf.union(&0, &1).unwrap();
        assert_eq!(*root01, 0);
        let root23 = uf.union(&2, &3).unwrap();
        assert_eq!(*root23, 2);
        assert!(uf.connected(&0, &1).unwrap());
        assert!(!uf.connected(&0, &2).unwrap());
        let root012 = uf.union(&0, &2).unwrap();
        assert!(uf.connected(&0, &2).unwrap());
        assert!(uf.connected(&0, &3).unwrap());
    }

    #[test]
    fn test_already_connected() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        let root = uf.union(&0, &1).unwrap();
        assert_eq!(*root, 0);
        let root_same = uf.union(&0, &1).unwrap();
        assert_eq!(*root_same, 0);
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
    fn test_get_idx_not_found() {
        let elems = vec![0u32, 1, 2];
        let uf = UnionFind::new(elems);
        let result = uf.get_idx(&99);
        assert!(result.is_err());
    }

    #[test]
    fn test_find_not_found() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        let result = uf.find(&99);
        assert!(result.is_err());
    }

    #[test]
    fn test_union_not_found() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        let result = uf.union(&0, &99);
        assert!(result.is_err());
    }

    #[test]
    fn test_connected_not_found() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        let result = uf.connected(&0, &99);
        assert!(result.is_err());
    }

    #[test]
    fn test_union_rank_less() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        assert_eq!(uf.rank[0], 0);
        assert_eq!(uf.rank[1], 0);
        assert_eq!(uf.rank[2], 0);
        uf.parent[1] = 2;
        uf.rank[0] = 1;
        uf.rank[2] = 2;
        assert_eq!(uf.rank[0], 1);
        assert_eq!(uf.rank[2], 2);
        let root = uf.union(&0, &1).unwrap();
        assert_eq!(*root, 2);
        assert_eq!(uf.parent[0], 2);
    }

    #[test]
    fn test_union_rank_greater() {
        let elems = vec![0u32, 1, 2, 3, 4];
        let mut uf = UnionFind::new(elems);
        assert_eq!(uf.rank[0], 0);
        assert_eq!(uf.rank[1], 0);
        assert_eq!(uf.rank[2], 0);
        uf.parent[1] = 2;
        uf.rank[0] = 2;
        uf.rank[2] = 1;
        assert_eq!(uf.rank[0], 2);
        assert_eq!(uf.rank[2], 1);
        let root = uf.union(&0, &1).unwrap();
        assert_eq!(*root, 0);
        assert_eq!(uf.parent[2], 0);
    }

    #[test]
    fn test_union_rank_less_explicit() {
        let elems = vec![10u32, 20, 30, 40];
        let mut uf = UnionFind::new(elems);
        uf.parent[1] = 2;
        uf.rank[0] = 1;
        uf.rank[2] = 2;
        assert!(uf.rank[0] < uf.rank[2]);
        let _root = uf.union(&10, &20).unwrap();
    }

    #[test]
    fn test_union_rank_greater_explicit() {
        let elems = vec![10u32, 20, 30, 40];
        let mut uf = UnionFind::new(elems);
        uf.parent[1] = 2;
        uf.rank[0] = 2;
        uf.rank[2] = 1;
        assert!(uf.rank[0] > uf.rank[2]);
        let _root = uf.union(&10, &20).unwrap();
    }

    #[test]
    fn test_union_returns_root_element() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        let root = uf.union(&0, &1).unwrap();
        assert_eq!(*root, 0);
    }

    #[test]
    fn test_union_returns_root_element_rank_equal() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        let root = uf.union(&0, &1).unwrap();
        assert_eq!(*root, 0);
    }

    #[test]
    fn test_union_multiple_returns_correct_root() {
        let elems = vec![0u32, 1, 2, 3, 4, 5];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        uf.union(&2, &3).unwrap();
        let root = uf.union(&0, &2).unwrap();
        assert_eq!(*root, 0);
    }

    #[test]
    fn test_display() {
        let elems = vec![0u32, 1, 2];
        let uf = UnionFind::new(elems);
        let s = format!("{}", uf);
        assert!(s.contains("UnionFind"));
        assert!(s.contains("elements"));
        assert!(s.contains("parent"));
        assert!(s.contains("rank"));
    }

    #[test]
    fn test_display_after_union() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        uf.union(&2, &3).unwrap();
        let s = format!("{}", uf);
        println!("{s}");
        assert!(s.contains("parent: [0, 0, 2, 2]"));
        assert!(s.contains("rank: [1, 0, 1, 0]"));
    }

    #[test]
    fn test_display_with_path_compression() {
        let elems = vec![0u32, 1, 2, 3];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        uf.union(&1, &2).unwrap();
        uf.union(&2, &3).unwrap();
        let _ = uf.find(&0).unwrap();
        let s = format!("{}", uf);
        assert!(s.contains("parent: [0, 0, 0, 0]"));
    }

    #[test]
    fn test_display_rank_after_union() {
        let elems = vec![0u32, 1, 2];
        let mut uf = UnionFind::new(elems);
        uf.union(&0, &1).unwrap();
        let s = format!("{}", uf);
        assert!(s.contains("rank: [1, 0, 0]"));
    }

    #[test]
    fn test_display_empty() {
        let elems: Vec<u32> = vec![];
        let uf = UnionFind::new(elems);
        let s = format!("{}", uf);
        assert!(s.contains("elements: []"));
        assert!(s.contains("parent: []"));
        assert!(s.contains("rank: []"));
    }
}
