use std::marker::PhantomData;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Default)]
pub struct LambdaType<T> {
    phantom: PhantomData<T>,
}
