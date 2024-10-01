use criterion::*;
use rand::prelude::*;
use skl::{
  map::{sync::SkipMap, Map},
  *,
};
use std::{
  sync::{atomic::*, *},
  thread,
};

fn fixed_skiplist_round(l: &SkipMap, case: &(Vec<u8>, bool), exp: &Vec<u8>) {
  if case.1 {
    if let Some(v) = l.get(&case.0) {
      assert_eq!(v.value(), exp);
    }
  } else {
    l.insert(&case.0, exp).unwrap();
  }
}

fn random_key(rng: &mut ThreadRng) -> Vec<u8> {
  let mut key = vec![0; 16];
  rng.fill_bytes(&mut key);
  key
}

fn bench_read_write_fixed_skiplist_frac(b: &mut Bencher<'_>, frac: &usize) {
  let frac = *frac;
  let value = b"00123".to_vec();
  let list = Builder::new()
    .with_capacity(10 << 20)
    .alloc::<SkipMap>()
    .unwrap();
  let l = list.clone();
  let stop = Arc::new(AtomicBool::new(false));
  let s = stop.clone();
  let v = value.clone();
  let j = thread::spawn(move || {
    let mut rng = rand::thread_rng();
    while !s.load(Ordering::SeqCst) {
      let key = random_key(&mut rng);
      let case = (key, frac > rng.gen_range(0..11));
      fixed_skiplist_round(&l, &case, &v);
    }
  });
  let mut rng = rand::thread_rng();
  b.iter_batched_ref(
    || (random_key(&mut rng), frac > rng.gen_range(0..11)),
    |case| fixed_skiplist_round(&list, case, &value),
    BatchSize::SmallInput,
  );
  stop.store(true, Ordering::SeqCst);
  j.join().unwrap();
}

fn bench_read_write_fixed_skiplist(c: &mut Criterion) {
  let mut group = c.benchmark_group("fixed_skiplist_read_write");
  for i in 0..=10 {
    group.bench_with_input(
      BenchmarkId::from_parameter(i),
      &i,
      bench_read_write_fixed_skiplist_frac,
    );
  }
  group.finish();
}

fn bench_write_fixed_skiplist(c: &mut Criterion) {
  let list = Builder::new()
    .with_capacity(512 << 20)
    .with_freelist(Freelist::None)
    .alloc::<SkipMap>()
    .unwrap();
  let l = list.clone();
  let value = b"00123".to_vec();
  let stop = Arc::new(AtomicBool::new(false));
  let s = stop.clone();
  let v = value.clone();
  let j = thread::spawn(move || {
    let mut rng = rand::thread_rng();
    while !s.load(Ordering::SeqCst) {
      let case = (random_key(&mut rng), false);
      fixed_skiplist_round(&l, &case, &v);
    }
  });
  let mut rng = rand::thread_rng();
  c.bench_function("fixed_skiplist_write", |b| {
    b.iter_batched(
      || random_key(&mut rng),
      |key| {
        list.insert(&key, &value).unwrap();
      },
      BatchSize::SmallInput,
    )
  });
  stop.store(true, Ordering::SeqCst);
  j.join().unwrap();
}

criterion_group!(
  benches,
  bench_read_write_fixed_skiplist,
  bench_write_fixed_skiplist,
);
criterion_main!(benches);
