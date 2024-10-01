use criterion::*;
use parking_lot::Mutex;
use rand::prelude::*;
use std::{
  collections::*,
  sync::{atomic::*, *},
  thread,
};

fn map_round(l: &Arc<Mutex<HashMap<Vec<u8>, Vec<u8>>>>, case: &(Vec<u8>, bool), exp: &Vec<u8>) {
  let mut l = l.lock();
  if case.1 {
    if let Some(v) = l.get(&case.0) {
      assert_eq!(v, exp);
    }
  } else {
    l.insert(case.0.clone(), exp.clone());
  }
}

fn random_key(rng: &mut ThreadRng) -> Vec<u8> {
  let mut key = vec![0; 16];
  rng.fill_bytes(&mut key);
  key
}

fn bench_read_write_map_frac(b: &mut Bencher<'_>, frac: &usize) {
  let frac = *frac;
  let value = b"00123".to_vec();
  let map = Arc::new(Mutex::new(HashMap::new()));
  let m = map.clone();
  let stop = Arc::new(AtomicBool::new(false));
  let s = stop.clone();

  let v = value.clone();
  let h = thread::spawn(move || {
    let mut rng = rand::thread_rng();
    while !s.load(Ordering::SeqCst) {
      let f = rng.gen_range(0..11);
      let case = (random_key(&mut rng), f < frac);
      map_round(&m, &case, &v);
    }
  });
  let mut rng = rand::thread_rng();
  b.iter_batched_ref(
    || {
      let f = rng.gen_range(0..11);
      (random_key(&mut rng), f < frac)
    },
    |case| map_round(&map, case, &value),
    BatchSize::SmallInput,
  );
  stop.store(true, Ordering::SeqCst);
  h.join().unwrap();
}

fn bench_read_write_map(c: &mut Criterion) {
  let mut group = c.benchmark_group("map_read_write");
  for i in 0..=10 {
    group.bench_with_input(
      BenchmarkId::from_parameter(i),
      &i,
      bench_read_write_map_frac,
    );
  }
  group.finish();
}

fn bench_write_map(c: &mut Criterion) {
  let list = Arc::new(Mutex::new(HashMap::new()));
  let value = b"00123".to_vec();
  let l = list.clone();
  let stop = Arc::new(AtomicBool::new(false));
  let s = stop.clone();
  let v = value.clone();
  let j = thread::spawn(move || {
    let mut rng = rand::thread_rng();
    let l = l.clone();
    while !s.load(Ordering::SeqCst) {
      let l = l.clone();
      let case = (random_key(&mut rng), false);
      map_round(&l, &case, &v);
    }
  });
  let mut rng = rand::thread_rng();
  c.bench_function("map_write", |b| {
    b.iter_batched(
      || random_key(&mut rng),
      |key| {
        let mut list = list.lock();
        list.insert(key, value.clone());
      },
      BatchSize::SmallInput,
    )
  });
  stop.store(true, Ordering::SeqCst);
  j.join().unwrap();
}

criterion_group!(benches, bench_write_map, bench_read_write_map,);
criterion_main!(benches);
