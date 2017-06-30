#![feature(test)]

extern crate polymap;
extern crate rand;
extern crate test;

use rand::{thread_rng, Rng};

use test::{black_box, Bencher};

use polymap::PolyMap;

macro_rules! map_insert_rand_bench {
    ( $name:ident , $n:expr ) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut map = PolyMap::<usize>::new();
            let mut rng = thread_rng();

            for _ in 0..$n {
                map.insert(rng.gen::<usize>() % $n, 0u32);
            }

            b.iter(|| {
                let k = rng.gen::<usize>() % $n;

                map.insert(k, 0u32);
                let _: Option<u32> = map.remove(&k);
            });

            black_box(map);
        }
    }
}

macro_rules! map_find_rand_bench {
    ( $name:ident , $n:expr ) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut map = PolyMap::<usize>::new();
            let mut rng = thread_rng();

            let mut keys = (0..$n)
                .map(|_| rng.gen::<usize>() % $n).collect::<Vec<_>>();

            for &k in &keys {
                map.insert(k, 0u32);
            }

            rng.shuffle(&mut keys);

            let mut i = 0;

            b.iter(|| {
                let v: Option<&u32> = map.get(&keys[i]);
                i = (i + 1) % $n;
                black_box(v);
            });
        }
    }
}

map_insert_rand_bench!{ map_insert_rand_100,    100 }
map_insert_rand_bench!{ map_insert_rand_10_000, 10_000 }

map_find_rand_bench!{ map_find_rand_100,    100 }
map_find_rand_bench!{ map_find_rand_10_000, 10_000 }
