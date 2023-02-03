#![no_main]

use libfuzzer_sys::fuzz_target;
use core::cell::Cell;

fuzz_target!(|data: (&[u8], usize)| {
    let _ = std::panic::catch_unwind(|| {
        let mut arr: Vec<(u8, u8)> = data.0.chunks_exact(2).map(|c| (c[0], c[1])).collect();
        let mut arr2 = arr.clone();
        let mut arr3 = arr.clone();
    
        let mut num_cmp = 0;
        glidesort::glidesort_by(&mut arr, |a, b| {
            num_cmp += 1;
            a.1.cmp(&b.1)
        });
        arr2.sort_by(|a, b| { a.1.cmp(&b.1) });
        assert_eq!(arr, arr2);
        
        // Sadly fuzzer doesn't actually work with catch_unwind yet :(
        /*
        // Simulate arbitrary exception.
        let mut except_point = data.1 % (num_cmp + 1);
        glidesort::glidesort_by(&mut arr3, |a, b| {
            if except_point == 0 {
                panic!("foo");
            }
            except_point -= 1;
            a.1.cmp(&b.1)
        });
        */
    });
});
