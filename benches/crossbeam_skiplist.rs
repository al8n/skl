use criterion::*;
use rand::prelude::*;
use std::{
  sync::{atomic::*, *},
  thread,
};

fn random_key(rng: &mut ThreadRng) -> Vec<u8> {
  let mut key = vec![0; 16];
  rng.fill_bytes(&mut key);
  key
}

fn crossbeam_skiplist_round(
  l: &crossbeam_skiplist::SkipMap<Arc<Vec<u8>>, Arc<Vec<u8>>>,
  case: &(Arc<Vec<u8>>, bool),
  exp: Arc<Vec<u8>>,
) {
  if case.1 {
    if let Some(v) = l.get(&case.0) {
      assert_eq!(v.value().as_slice(), exp.as_slice());
    }
  } else {
    l.insert(case.0.clone(), exp);
  }
}

fn bench_read_write_crossbeam_skiplist_frac(b: &mut Bencher<'_>, frac: &usize) {
  let frac = *frac;
  let value = Arc::new(b"00123".to_vec());
  let list = Arc::new(crossbeam_skiplist::SkipMap::new());
  let l = list.clone();
  let stop = Arc::new(AtomicBool::new(false));
  let s = stop.clone();
  let v = value.clone();
  let j = thread::spawn(move || {
    let mut rng = rand::thread_rng();
    while !s.load(Ordering::SeqCst) {
      let key = Arc::new(random_key(&mut rng));
      let case = (key, frac > rng.gen_range(0..11));
      crossbeam_skiplist_round(&l, &case, v.clone());
    }
  });
  let mut rng = rand::thread_rng();
  b.iter_batched_ref(
    || (Arc::new(random_key(&mut rng)), frac > rng.gen_range(0..11)),
    |case| crossbeam_skiplist_round(&list, case, value.clone()),
    BatchSize::SmallInput,
  );
  stop.store(true, Ordering::SeqCst);
  j.join().unwrap();
}

fn bench_read_write_crossbeam_skiplist(c: &mut Criterion) {
  let mut group = c.benchmark_group("crossbeam_skiplist_read_write");
  for i in 0..=10 {
    group.bench_with_input(
      BenchmarkId::from_parameter(i),
      &i,
      bench_read_write_crossbeam_skiplist_frac,
    );
  }
  group.finish();
}

fn bench_write_crossbeam_skiplist(c: &mut Criterion) {
  let list = Arc::new(crossbeam_skiplist::SkipMap::new());
  let l = list.clone();
  let value = Arc::new(b"00123".to_vec());
  let stop = Arc::new(AtomicBool::new(false));
  let s = stop.clone();
  let v = value.clone();
  let j = thread::spawn(move || {
    let mut rng = rand::thread_rng();
    while !s.load(Ordering::SeqCst) {
      let case = (Arc::new(random_key(&mut rng)), false);
      crossbeam_skiplist_round(&l, &case, v.clone());
    }
  });
  let mut rng = rand::thread_rng();
  c.bench_function("skiplist_write", |b| {
    b.iter_batched(
      || Arc::new(random_key(&mut rng)),
      |key| {
        list.insert(key, value.clone());
      },
      BatchSize::SmallInput,
    )
  });
  stop.store(true, Ordering::SeqCst);
  j.join().unwrap();
}

criterion_group!(
  benches,
  bench_read_write_crossbeam_skiplist,
  bench_write_crossbeam_skiplist,
);
criterion_main!(benches);
