//use core::fmt;
//use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
//use rand_core::RngCore;
//use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

const MODULUS: [u64; 6] = [
    0xb9fe_ffff_ffff_aaab,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

// const R: [u64;6] = [
//     0x7609_0000_0002_fffd,
//     0xebf4_000b_c40c_0002,
//     0x5f48_9857_53c7_58ba,
//     0x77ce_5853_7052_5745,
//     0x5c07_1a97_a256_ec6d,
//     0x15f6_5ec3_fa80_e493,
// ];

/// INV = -(p^{-1} mod 2^64) mod 2^64
const INV: u64 = 0x89f3_fffc_fffc_fffd;


pub fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + (b as u128) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}

pub fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}
pub const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
    (ret as u64, (ret >> 64) as u64)
}

const fn subtract_p(x: [u64;6]) -> [u64;6] {
    let (r0, borrow) = sbb(x[0], MODULUS[0], 0);
    let (r1, borrow) = sbb(x[1], MODULUS[1], borrow);
    let (r2, borrow) = sbb(x[2], MODULUS[2], borrow);
    let (r3, borrow) = sbb(x[3], MODULUS[3], borrow);
    let (r4, borrow) = sbb(x[4], MODULUS[4], borrow);
    let (r5, borrow) = sbb(x[5], MODULUS[5], borrow);

    // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
    // borrow = 0x000...000. Thus, we use it as a mask!
    let r0 = (x[0] & borrow) | (r0 & !borrow);
    let r1 = (x[1] & borrow) | (r1 & !borrow);
    let r2 = (x[2] & borrow) | (r2 & !borrow);
    let r3 = (x[3] & borrow) | (r3 & !borrow);
    let r4 = (x[4] & borrow) | (r4 & !borrow);
    let r5 = (x[5] & borrow) | (r5 & !borrow);

    [r0, r1, r2, r3, r4, r5]
}

pub fn montgomery_reduce(
    t0: u64,
    t1: u64,
    t2: u64,
    t3: u64,
    t4: u64,
    t5: u64,
    t6: u64,
    t7: u64,
    t8: u64,
    t9: u64,
    t10: u64,
    t11: u64,
) -> [u64;6] {
    // The Montgomery reduction here is based on Algorithm 14.32 in
    // Handbook of Applied Cryptography
    // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

    let k = t0.wrapping_mul(INV);
    let (_, carry) = mac(t0, k, MODULUS[0], 0);
    let (r1, carry) = mac(t1, k, MODULUS[1], carry);
    let (r2, carry) = mac(t2, k, MODULUS[2], carry);
    let (r3, carry) = mac(t3, k, MODULUS[3], carry);
    let (r4, carry) = mac(t4, k, MODULUS[4], carry);
    let (r5, carry) = mac(t5, k, MODULUS[5], carry);
    let (r6, r7) = adc(t6, 0, carry);

    let k = r1.wrapping_mul(INV);
    let (_, carry) = mac(r1, k, MODULUS[0], 0);
    let (r2, carry) = mac(r2, k, MODULUS[1], carry);
    let (r3, carry) = mac(r3, k, MODULUS[2], carry);
    let (r4, carry) = mac(r4, k, MODULUS[3], carry);
    let (r5, carry) = mac(r5, k, MODULUS[4], carry);
    let (r6, carry) = mac(r6, k, MODULUS[5], carry);
    let (r7, r8) = adc(t7, r7, carry);

    let k = r2.wrapping_mul(INV);
    let (_, carry) = mac(r2, k, MODULUS[0], 0);
    let (r3, carry) = mac(r3, k, MODULUS[1], carry);
    let (r4, carry) = mac(r4, k, MODULUS[2], carry);
    let (r5, carry) = mac(r5, k, MODULUS[3], carry);
    let (r6, carry) = mac(r6, k, MODULUS[4], carry);
    let (r7, carry) = mac(r7, k, MODULUS[5], carry);
    let (r8, r9) = adc(t8, r8, carry);

    let k = r3.wrapping_mul(INV);
    let (_, carry) = mac(r3, k, MODULUS[0], 0);
    let (r4, carry) = mac(r4, k, MODULUS[1], carry);
    let (r5, carry) = mac(r5, k, MODULUS[2], carry);
    let (r6, carry) = mac(r6, k, MODULUS[3], carry);
    let (r7, carry) = mac(r7, k, MODULUS[4], carry);
    let (r8, carry) = mac(r8, k, MODULUS[5], carry);
    let (r9, r10) = adc(t9, r9, carry);

    let k = r4.wrapping_mul(INV);
    let (_, carry) = mac(r4, k, MODULUS[0], 0);
    let (r5, carry) = mac(r5, k, MODULUS[1], carry);
    let (r6, carry) = mac(r6, k, MODULUS[2], carry);
    let (r7, carry) = mac(r7, k, MODULUS[3], carry);
    let (r8, carry) = mac(r8, k, MODULUS[4], carry);
    let (r9, carry) = mac(r9, k, MODULUS[5], carry);
    let (r10, r11) = adc(t10, r10, carry);

    let k = r5.wrapping_mul(INV);
    let (_, carry) = mac(r5, k, MODULUS[0], 0);
    let (r6, carry) = mac(r6, k, MODULUS[1], carry);
    let (r7, carry) = mac(r7, k, MODULUS[2], carry);
    let (r8, carry) = mac(r8, k, MODULUS[3], carry);
    let (r9, carry) = mac(r9, k, MODULUS[4], carry);
    let (r10, carry) = mac(r10, k, MODULUS[5], carry);
    let (r11, _) = adc(t11, r11, carry);

    // Attempt to subtract the modulus, to ensure the value
    // is smaller than the modulus.
    subtract_p([r6, r7, r8, r9, r10, r11])
}

pub fn mul(x: [u64;6], y: [u64;6]) -> [u64;6] {
    let (t0, carry) = mac(0, x[0], y[0], 0);
    let (t1, carry) = mac(0, x[0], y[1], carry);
    let (t2, carry) = mac(0, x[0], y[2], carry);
    let (t3, carry) = mac(0, x[0], y[3], carry);
    let (t4, carry) = mac(0, x[0], y[4], carry);
    let (t5, t6) = mac(0, x[0], y[5], carry);

    let (t1, carry) = mac(t1, x[1], y[0], 0);
    let (t2, carry) = mac(t2, x[1], y[1], carry);
    let (t3, carry) = mac(t3, x[1], y[2], carry);
    let (t4, carry) = mac(t4, x[1], y[3], carry);
    let (t5, carry) = mac(t5, x[1], y[4], carry);
    let (t6, t7) = mac(t6, x[1], y[5], carry);

    let (t2, carry) = mac(t2, x[2], y[0], 0);
    let (t3, carry) = mac(t3, x[2], y[1], carry);
    let (t4, carry) = mac(t4, x[2], y[2], carry);
    let (t5, carry) = mac(t5, x[2], y[3], carry);
    let (t6, carry) = mac(t6, x[2], y[4], carry);
    let (t7, t8) = mac(t7, x[2], y[5], carry);

    let (t3, carry) = mac(t3, x[3], y[0], 0);
    let (t4, carry) = mac(t4, x[3], y[1], carry);
    let (t5, carry) = mac(t5, x[3], y[2], carry);
    let (t6, carry) = mac(t6, x[3], y[3], carry);
    let (t7, carry) = mac(t7, x[3], y[4], carry);
    let (t8, t9) = mac(t8, x[3], y[5], carry);

    let (t4, carry) = mac(t4, x[4], y[0], 0);
    let (t5, carry) = mac(t5, x[4], y[1], carry);
    let (t6, carry) = mac(t6, x[4], y[2], carry);
    let (t7, carry) = mac(t7, x[4], y[3], carry);
    let (t8, carry) = mac(t8, x[4], y[4], carry);
    let (t9, t10) = mac(t9, x[4], y[5], carry);

    let (t5, carry) = mac(t5, x[5], y[0], 0);
    let (t6, carry) = mac(t6, x[5], y[1], carry);
    let (t7, carry) = mac(t7, x[5], y[2], carry);
    let (t8, carry) = mac(t8, x[5], y[3], carry);
    let (t9, carry) = mac(t9, x[5], y[4], carry);
    let (t10, t11) = mac(t10, x[5], y[5], carry);

    montgomery_reduce(t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11)
}

fn main () {
    //let x: [u64;6] = [13402431016077863593, 2210141511517208575, 7435674573564081700, 7239337960414712511, 5412103778470702295, 1873798617647539866];
    //let y: [u64;6] = [13402431016077863594, 2210141511517208575, 7435674573564081700, 7239337960414712511, 5412103778470702295, 1873798617647539866];

    // let x: [u64;6] = [0,0,0,0,0,2];
    // let y: [u64;6] = [0,0,0,0,0,2];
    // let res1: [u64;6] = mul(x, y);
    //let res2 = montgomery_reduce(10,0,0,0,0,0,0,0,0,0,0,0);
    //  let res2 = montgomery_reduce(0xb9feffffffffaaab,0x1eabfffeb153ffff,0x6730d2a0f6b0f624,0x64774b84f38512bf,0x4b1ba7b6434bacd7,0x1a0111ea397fe69a,0,0,0,0,0,0);
    // let res2 = montgomery_reduce(13282407956253574712,7557322358563246340,14991082624209354397,6631139461101160670,10719928016004921607,1730705806359781376,0,0,0,0,0,0);
    // println!("{}",res2[0]);
    // println!("{}",res2[1]);
    // println!("{}",res2[2]);
    // println!("{}",res2[3]);
    // println!("{}",res2[4]);
    // println!("{}",res2[5]);
    // let res1: [u64;6] = mul(res2, R);
    //let res1 = mul([0xb9feffffffffaaab,0x1eabfffeb153ffff,0x6730d2a0f6b0f624,0x64774b84f38512bf,0x4b1ba7b6434bacd7,0x1a0111ea397fe69a], [1,0,0,0,0,0]);
    // let res1 = mul([0,1,0,0,0,0], [0,1,0,0,0,0]);
    // println!("{}",res1[0]);
    // println!("{}",res1[1]);
    // println!("{}",res1[2]);
    // println!("{}",res1[3]);
    // println!("{}",res1[4]);
    // println!("{}",res1[5]);

    let res2 = montgomery_reduce(13282407956253574712,7557322358563246340,14991082624209354397,6631139461101160670,10719928016004921607,1730705806359781376,0,0,0,0,0,0);
    println!("{}",res2[0]);
    println!("{}",res2[1]);
    println!("{}",res2[2]);
    println!("{}",res2[3]);
    println!("{}",res2[4]);
    println!("{}",res2[5]);
}   
