#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) enum ArgumentIterator<A, B, C, D> {
    A(A),
    B(B),
    C(C),
    D(D),
}

impl<A, B, C, D, Item> Iterator for ArgumentIterator<A, B, C, D>
where
    A: Iterator<Item = Item>,
    B: Iterator<Item = Item>,
    C: Iterator<Item = Item>,
    D: Iterator<Item = Item>,
{
    type Item = Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ArgumentIterator::A(a) => a.next(),
            ArgumentIterator::B(b) => b.next(),
            ArgumentIterator::C(c) => c.next(),
            ArgumentIterator::D(d) => d.next(),
        }
    }
}
