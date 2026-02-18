///Cartesian product of size `self.coord.len()` that goes from `0` to `max_value-1`.
pub(super) struct CartesianN {
    coord: Vec<usize>,
    done: bool,
    max_value: usize,
}

impl CartesianN {
    pub(super) fn new(number_of_items: usize, max_value: usize) -> Self {
        assert!(max_value > 0);
        Self {
            coord: vec![0; number_of_items],
            done: false,
            max_value,
        }
    }

    pub(super) fn reset_with_n_items(&mut self, number_of_items: usize) {
        self.coord = vec![0; number_of_items];
        self.done = false;
    }
}

impl Iterator for CartesianN {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let out = self.coord.clone();

        // increment like an odometer, least‑significant digit at the end
        let mut i = self.coord.len();
        loop {
            if i == 0 {
                self.done = true;
                break;
            }
            i -= 1;
            self.coord[i] += 1;
            if self.coord[i] < self.max_value {
                break;
            }
            self.coord[i] = 0;
        }

        Some(out)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Copy, Ord, PartialOrd, Hash)]
pub(super) struct SetCounter {
    i: usize,
    n: u32,
}

impl SetCounter {
    pub(super) fn new(n_items: u32) -> Self {
        SetCounter { i: 0, n: n_items }
    }

    pub(super) fn increment(&mut self) {
        self.i += 1;
    }

    pub(super) fn done(&self) -> bool {
        self.i >= 2_usize.pow(self.n)
    }

    pub(super) fn set_position(&mut self, i: usize) {
        self.i = i;
    }

    fn included(&self) -> impl Iterator<Item = bool> {
        let i = self.i;
        (0..self.n).map(move |x| i & (1 << x) != 0)
    }

    pub(super) fn current_size(&self) -> usize {
        self.included().map(usize::from).sum::<usize>()
    }

    pub(super) fn filter<T>(&self, iter: impl Iterator<Item = T>) -> impl Iterator<Item = T> {
        iter.zip(self.included())
            .filter_map(|(counter, included)| if included { Some(counter) } else { None })
    }
}
