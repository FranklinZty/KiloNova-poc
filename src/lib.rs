#![warn(missing_debug_implementations, rust_2018_idioms)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

pub mod ccs;
pub mod genericfolding;

pub mod espresso;
pub mod util;

pub fn cat_two_arrays() {
    let a: &[u32] = &[1,2,3];
    let b: &[u32] = &[4,5,6];
    let ab = [&a[..], &b[..]].concat();
    println!("{:?}", ab);
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_cat_two_arrays() {
        cat_two_arrays();
    }
}