#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct SetCounter {
    k: usize,
    n: usize,
    max_t: usize,
    k_combinations: KCombination,
    done: bool,
    item: InclusionSet,
}

impl SetCounter {
    pub(super) fn new(n_items: usize, max_t: Option<usize>) -> Self {
        let mut k_combinations = KCombination::new(n_items, 0);
        let item = InclusionSet(k_combinations.next().unwrap());

        SetCounter {
            item,
            k_combinations,
            k: 0,
            done: false,
            n: n_items,
            max_t: max_t.map(|x| std::cmp::min(x, n_items)).unwrap_or(n_items),
        }
    }

    pub(super) fn increment(&mut self) {
        if let Some(x) = self.k_combinations.next() {
            self.item = InclusionSet(x);
        } else {
            self.k += 1;
            if self.k <= self.max_t {
                self.k_combinations = KCombination::new(self.n, self.k);
                self.item = InclusionSet(self.k_combinations.next().unwrap());
            } else {
                self.done = true;
            }
        }
    }

    pub(super) fn done(&self) -> bool {
        self.done
    }

    pub(super) fn included(&self) -> &InclusionSet {
        &self.item
    }

    pub(super) fn as_set<T>(&self, t: impl IntoIterator<Item = T>) -> impl Iterator<Item = T> {
        t.into_iter()
            .zip(&self.item.0)
            .filter_map(|(t, b)| if *b { Some(t) } else { None })
    }

    pub(super) fn current_size(&self) -> usize {
        self.item.size()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) struct InclusionSet(Vec<bool>);

impl InclusionSet {
    pub(super) fn as_set<T>(&self, t: impl IntoIterator<Item = T>) -> impl Iterator<Item = T> {
        t.into_iter()
            .zip(&self.0)
            .filter_map(|(t, b)| if *b { Some(t) } else { None })
    }

    fn size(&self) -> usize {
        self.0.iter().copied().map(usize::from).sum()
    }
}

impl Iterator for SetCounter {
    type Item = InclusionSet;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done() {
            return None;
        }
        let item = self.item.clone();
        self.increment();
        Some(item)
    }
}

///Struct that gets all K combinations from a set.
///Adapted from Algorithm 7.2.1.3C from Knuth's Art of Computer Programming Volume 4A
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct KCombination {
    a: Vec<bool>,
    w: Vec<usize>,
    r: usize,
    finished: bool,
}

impl KCombination {
    fn new(n: usize, t: usize) -> Self {
        assert!(n >= t);
        let s = n - t;
        let mut a = vec![false; n];
        for x in a[s..].iter_mut() {
            *x = true;
        }
        let w = vec![1; n + 1];
        let r = if s > 0 { s } else { t };

        KCombination {
            a,
            w,
            r,
            finished: false,
        }
    }

    fn c4(&mut self, j: usize) {
        self.a[j - 1] = true;
        self.a[j] = false;
        if self.r == j && j > 1 {
            self.r = j - 1;
        } else if self.r == j - 1 {
            self.r = j;
        }
    }

    fn c6(&mut self, j: usize) {
        self.a[j] = true;
        self.a[j - 1] = false;
        if self.r == j && j > 1 {
            self.r = j - 1;
        } else if self.r == j - 1 {
            self.r = j;
        }
    }
}

impl Iterator for KCombination {
    type Item = Vec<bool>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }

        let item = self.a.clone();
        let mut j = self.r;
        while self.w[j] == 0 {
            self.w[j] = 1;
            j += 1;
        }
        if j == self.a.len() {
            self.finished = true;
            return Some(item);
        }
        self.w[j] = 0;
        match (j.is_multiple_of(2), self.a[j]) {
            (false, true) => {
                self.c4(j);
            }
            (true, true) => {
                //c5
                if self.a[j - 2] {
                    self.c4(j);
                } else {
                    self.a[j - 2] = true;
                    self.a[j] = false;
                    if self.r == j {
                        self.r = std::cmp::max(j - 2, 1);
                    } else if self.r == j - 2 {
                        self.r = j - 1;
                    }
                }
            }
            (true, false) => self.c6(j),
            (false, false) => {
                //C7
                if self.a[j - 1] {
                    self.c6(j);
                } else {
                    self.a[j] = true;
                    self.a[j - 2] = false;
                    if self.r == j - 2 {
                        self.r = j;
                    } else if self.r == j - 1 {
                        self.r = j - 2;
                    }
                }
            }
        }

        Some(item)
    }
}

#[cfg(test)]
mod test {
    use super::KCombination;
    use ahash::HashSet;
    use num_integer::binomial;

    #[test]
    fn k_combinations() {
        let n = 5;
        for t in 0..=5 {
            let count = binomial(n, t);
            let set = KCombination::new(n, t).collect::<Vec<_>>();
            assert_eq!(count, set.len());
            let set = set.into_iter().collect::<HashSet<_>>();
            assert_eq!(count, set.len());

            println!("{set:?}");
        }
    }
}
