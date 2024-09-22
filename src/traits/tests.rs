macro_rules! map_unit_tests {
  ($prefix:literal: $ty:ty) => {
    #[test]
    fn test_empty() {
      run(|| empty_in(SkipList::new(Options::new()).unwrap()));
      
    }

    #[test]
    fn test_empty_unify() {
      run(|| empty_in(SkipList::new(UNIFY_TEST_OPTIONS).unwrap()));
    }

    #[test]
    #[cfg(feature = "memmap")]
    #[cfg_attr(miri, ignore)]
    fn test_empty_map_mut() {
      run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("test_skipmap_empty_map_mut");
        let open_options = OpenOptions::default()
          .create_new(Some(1000))
          .read(true)
          .write(true);
        let map_options = MmapOptions::default();

        let x = SkipList::map_mut(p, Options::new(), open_options, map_options).unwrap();
        empty_in(x);
      })
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_empty_map_anon() {
      run(|| {
        let map_options = MmapOptions::default().len(1000);
        empty_in(SkipList::map_anon(Options::new(), map_options).unwrap());
      })
    }

    #[test]
    #[cfg(feature = "memmap")]
    fn test_empty_map_anon_unify() {
      run(|| {
        let map_options = MmapOptions::default().len(1000);
        empty_in(SkipList::map_anon(TEST_OPTIONS, map_options).unwrap());
      })
    }
  };
}