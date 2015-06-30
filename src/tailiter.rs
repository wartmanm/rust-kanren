use tailiter::TailIterItem::*;

///! The return value of a `TailIterator`.
pub enum TailIterItem<T> {
    ///! Indicates that the `TailIterator` has no more results.  This is no different from an
    ///! ordinary iterator returning `None`.
    Done,
    ///! A single result value.  This is no different from an ordinary iterator returning `Some`.
    SingleItem(T),
    ///! Indicates that the  `TailIterator` has no more results not drawn from a child
    ///! `TailIterator`, and must be replaced.
    Tail(TailIterHolder<T>),
}

///! `TailIterator` enables something like tail call elimination for iterator chains, by making it
///! possible to remove iterators that combine the output of multiple iterators but have exhausted
///! all but the last one.
///!
///! This is done by returning a `Tail` holding the last remaining child `TailIterator`.  After
///! this takes place, the `TailIterator` is unusable and must be replaced with the tail.
pub trait TailIterator {
    type Item;
    fn next_inner(&mut self) -> TailIterItem<<Self as TailIterator>::Item>;
}

///! Wrapper for `TailIterator` objects.
///!
///! (Having a method that took `&mut Box<TailIterator>` didn't work, but this does.  I'm not
///! certain why.)
pub struct TailIterHolder<T> {
    iter: Box<TailIterator<Item=T>>,
}

impl<T> TailIterHolder<T> {
    ///! Return the next value from the wrapped `TailIterator`, replacing it with its tail as
    ///! necessary.
    pub fn next_boxed(&mut self) -> Option<T> {
        loop {
            let tail = match self.iter.next_inner() {
                Done => { return None; }
                SingleItem(x) => { return Some(x); }
                Tail(x) => { x }
            };
            self.iter = tail.iter;
        }
    }
    ///! Wrap a `TailIterator` in a `TailIterHolder`.
    pub fn new<I>(iter: I) -> TailIterHolder<T> where I : TailIterator<Item=T> + 'static {
        TailIterHolder { iter: Box::new(iter) }
    }

    pub fn map<F, Out>(self, f: F) -> TailIterHolder<Out> where F: Fn(T) -> Out + 'static, Out: 'static, T: 'static {
        TailIterHolder::new(TailMapper { f: f, iter: self })
    }


    ///! Depth-first flat map.
    pub fn flat_map<F, Out>(self, f: F) -> TailIterHolder<Out> where F: Fn(T) -> TailIterHolder<Out> + 'static, Out: 'static, T: 'static {
        TailIterHolder::new(TailFlatMapper { f: f, iter: self, current: None })
    }

    ///! Synonym for map() and flat_map().
    pub fn and<F, Out, J>(self, f: F) -> TailIterHolder<Out>
    where F: Fn(T) -> J + 'static, J: Into<TailIterHolder<Out>>, Out: 'static, T: 'static {
        self.flat_map(move |x| f(x).into())
    }
    
    ///! Breadth-first flat map.
    pub fn flat_imap<F, Out>(self, f: F) -> TailIterHolder<Out> where F: Fn(T) -> TailIterHolder<Out> + 'static, Out: 'static, T: 'static {
        TailIterHolder::new(TailFlatIMapper { f: f, iter: Some(self), out: Vec::new(), pos: 0 })
    }
}

impl<T> IntoIterator for TailIterHolder<T> {
    type Item = T;
    type IntoIter = Flattener<T>;
    fn into_iter(self) -> Flattener<T> {
        Flattener { holder: self }
    }
}

///! Flattens a `TailIterator` into a regular `Iterator`.
pub struct Flattener<T> {
    holder: TailIterHolder<T>
}

impl<T> Iterator for Flattener<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.holder.next_boxed()
    }
}

struct TailFlatMapper<F, In, Out>
where F: Fn(In) -> TailIterHolder<Out> {
    f: F,
    iter: TailIterHolder<In>,
    current: Option<TailIterHolder<Out>>,
}

impl<F, In, Out> TailIterator for TailFlatMapper<F, In, Out>
where F: Fn(In) -> TailIterHolder<Out> {
    type Item = Out;
    fn next_inner(&mut self) -> TailIterItem<Out> {
        loop {
            if let Some(ref mut current_inner) = self.current {
                if let Some(x) = current_inner.next_boxed() {
                    return SingleItem(x);
                }
            }
            if let Some(next) = self.iter.next_boxed() {
                self.current = Some((self.f)(next));
            } else {
                return Done;
            }
        }
    }
}

struct TailMapper<F, In, Out>
where F: Fn(In) -> Out {
    f: F,
    iter: TailIterHolder<In>,
}

impl<F, In, Out> TailIterator for TailMapper<F, In, Out>
where F: Fn(In) -> Out {
    type Item = Out;
    fn next_inner(&mut self) -> TailIterItem<Out> {
        if let Some(next) = self.iter.next_boxed() {
            SingleItem((self.f)(next))
        } else {
            Done
        }
    }
}

struct TailFlatIMapper<F, In, Out>
where F: Fn(In) -> TailIterHolder<Out> {
    f: F,
    iter: Option<TailIterHolder<In>>,
    out: Vec<TailIterHolder<Out>>,
    pos: usize,
}

impl<F, In, Out> TailIterator for TailFlatIMapper<F, In, Out>
where F: Fn(In) -> TailIterHolder<Out> {
    type Item = Out;
    fn next_inner(&mut self) -> TailIterItem<Out> {
        loop {
            if let Some(next) = self.iter.as_mut().and_then(|iter| iter.next_boxed()) {
                self.out.push((self.f)(next));
            } else {
                if self.out.len() == 1 {
                    return Tail(self.out.pop().unwrap());
                } else if self.out.is_empty() {
                    return Done;
                }
                self.iter = None;
            }
            self.pos = self.pos % self.out.len();
            if let Some(x) = self.out[self.pos].next_boxed() { 
                self.pos += 1;
                return SingleItem(x);
            } else {
                self.out.remove(self.pos);
            }
        }
    }
}
