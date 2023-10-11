use rug::{Integer, Float};
use std::ops::{BitAnd, Shr};
use rug::integer::IsPrime;
use rug::ops::Pow;
use ring::rand::{SystemRandom, SecureRandom};
use rug::ops::DivRounding;
use std::io::{self, Write};

fn random_integer_between(lower: &Integer, upper: &Integer) -> Integer {
    assert!(lower <= upper);

    let diff = upper.clone() - lower.clone();
    let num_bits = diff.significant_bits() as usize;

    let mut random_bytes = vec![0u8; (num_bits + 7) / 8];
    let rng = SystemRandom::new();
    loop {
        rng.fill(&mut random_bytes).unwrap();
        let random_int = Integer::from_digits(&random_bytes, rug::integer::Order::Lsf);
        if random_int <= diff {
            return lower.clone() + random_int;
        }
    }
}

fn is_prime(n: &Integer) -> bool {
    !matches!(n.is_probably_prime(20), IsPrime::No)
}

fn read_input() -> String {
    let mut input = String::new();
    io::stdin()
        .read_line(&mut input)
        .unwrap();
    input
}

fn prime_factors(mut n: Integer) -> Vec<Integer> {
    let mut factors = Vec::new();
    let mut d = Integer::from(2);
    loop {
        if n.clone().div_floor(2) < d {
            if is_prime(&n) {
                factors.push(n.clone());
            }
            break;
        }
        if n.is_divisible(&d) {
            if !factors.contains(&d) {
                factors.push(d.clone());
            }
            n /= &d;
        }
        d = d.next_prime();
    }
    factors
}

fn find_generator(order: &Integer) -> Integer {
    let mut gen: Integer;
    loop {
        gen = random_integer_between(Integer::ONE, order);
        let prod: Integer= order.clone() - 1;
        let factors = prime_factors(prod.clone());
        if factors.iter().all(|x| gen.clone().pow_mod(&(prod.clone() / x), order).unwrap() != Integer::ONE.clone()) {
            break;
        }
    }
    gen
}

fn br_reduce(modulus: &Integer, dividend: &Integer) -> Integer {
    assert!(dividend.clone() < (modulus.clone().pow(2)));
    let k: u32 = Float::with_val(64, Float::parse(modulus.to_string()).unwrap()).log2().ceil().to_integer().unwrap().to_u32().unwrap();
    assert!(Integer::from(2).pow(k) > modulus.clone());
    let r = Integer::from(4).pow(k).div_floor(modulus.clone());
    let t = dividend.clone() - (modulus.clone() * ((dividend * r) >> (k * 2)));
    if t < modulus.clone() {
        return t;
    }
    t - modulus
}

fn mg_reduce(modulus: &Integer, a: &Integer, b: &Integer) -> Integer {
    let r = modulus.clone().next_power_of_two();
    assert!(r.clone().gcd(modulus) == 1);
    let r_inv = r.clone().invert(modulus).unwrap();
    let k: Integer = ((r.clone() * r_inv.clone()) - 1) / modulus.clone();
    let x: Integer = (a * r.clone()).modulo(modulus) * (b * r.clone()).modulo(modulus);
    let t: Integer = x.clone() + (modulus.clone() * (x.clone() * k.clone()).bitand(r.clone() - 1));
    let u: Integer = t.clone().shr((r - Integer::ONE).significant_bits());
    if u > modulus.clone() {
        return br_reduce(modulus, &((u - modulus) * r_inv));
    }
    br_reduce(modulus, &(u * r_inv))
}

fn ntt(input: &[Integer], mwm: &mut Option<Integer>, omg: &mut Option<Integer>, inverse: bool) -> (Vec<Integer>, Integer, Integer) {
    let length = Integer::from(input.len());
    let max_elem: Integer =  input
        .iter()
        .cloned()
        .max()
        .unwrap();
    if mwm.is_none() { 
        *mwm = Some(std::cmp::max(max_elem + 1, length.clone() + 1)); 
    } else {
        assert!(mwm.clone().unwrap() > length);
        assert!(mwm.clone().unwrap() > max_elem);
    }
    let mut n: Integer = if is_prime(&mwm.clone().unwrap()) { 
        mwm.clone().unwrap()
    } else { 
        mwm.clone().unwrap().next_prime() 
    };
    loop {
        if (n.clone() - Integer::ONE).is_divisible(&length) { break; }
        n = n.next_prime();
    }
    let k = (n.clone() - 1) / length.clone();
    if omg.is_none() {
        *omg = Some(find_generator(&n).pow_mod(&k, &n).unwrap());
    } else {
        assert!(omg.clone().unwrap().pow_mod(&length, &n).unwrap() == 1);
        let factors = prime_factors(length.clone());
        assert!(factors.iter().all(|x| omg.clone().unwrap().pow_mod(&(length.clone() / x), &n).unwrap() != Integer::ONE.clone()));
    };
    let output = input
        .iter()
        .enumerate()
        .map(|(outer, _)| 
             br_reduce(&n, &input
                            .iter()
                            .enumerate()
                            .fold(Integer::ZERO, |sum, (inner, element)| 
                                  sum + mg_reduce(&n, element, &omg.clone().unwrap().pow((outer * inner) as u32)))))
        .collect();
    if !inverse { return (output, n, omg.clone().unwrap()); }
    (output.iter().map(|x| mg_reduce(&n, x, &Integer::from(output.len()).invert(&n).unwrap())).collect(), n, omg.clone().unwrap())
}

fn circular_convolution(vec_x: &[Integer], vec_y: &[Integer]) -> (Vec<Integer>, Integer, Integer) {
    assert_eq!(vec_x.len(), vec_y.len());
    let max_ele = 
            vec_x
            .iter()
            .chain(vec_y.iter())
            .cloned()
            .collect::<Vec<_>>()
            .iter()
            .cloned()
            .max()
            .unwrap();
    let mut mwm = Some(max_ele.pow(2) * vec_x.len() + 1);
    let (ntt_x, nx, omg) = ntt(vec_x, &mut mwm, &mut None, false);
    let (ntt_y, ny, _) = ntt(vec_y, &mut mwm, &mut Some(omg.clone()), false);
    println!("NTT(X): {ntt_x:?}");
    println!("NTT(Y): {ntt_y:?}");
    assert_eq!(nx, ny);
    let ntt_mult: Vec<Integer>= ntt_x
        .iter()
        .zip(ntt_y.iter())
        .map(|(x, y)| mg_reduce(&nx, x, y))
        .collect();
    println!("NTT(X) ∘ NTT(Y): {ntt_mult:?}");
    ntt(&ntt_mult, &mut mwm, &mut Some(omg.clone()), true)
}

fn main() {
    println!("\nNumber-theoretic transform...\n");
    print!("Enter length of vector: ");
    io::stdout().flush().unwrap();
    let length: usize = read_input().trim().parse().unwrap();
    println!("Enter vector elements: ");
    let mut input: Vec<Integer> = vec![Integer::ZERO; length];
    input
        .iter_mut()
        .for_each(|x| *x = Integer::from_str_radix(&read_input(), 10).unwrap());
    print!("Enter minimum working modulus? Leave blank to skip... ");
    io::stdout().flush().unwrap();
    let readinput = read_input();
    let mut mwm = if readinput.trim().is_empty() { 
        None 
    } else { 
        Some(Integer::from_str_radix(&readinput, 10).unwrap()) 
    };
    print!("Enter nth root of unity? Leave blank to skip... ");
    io::stdout().flush().unwrap();
    let readinput = read_input();
    let mut omg = if readinput.trim().is_empty() { 
        None 
    } else { 
        Some(Integer::from_str_radix(&readinput, 10).unwrap()) 
    };
    let (forward_ntt, n1, omg1) = ntt(&input, &mut mwm, &mut omg, false);
    let (inverse_ntt, n2, omg2) = ntt(&input, &mut mwm, &mut Some(omg1.clone()), true);
    assert_eq!(n1, n2);
    println!("Forward NTT: {forward_ntt:?}, modulus: {n1}, nth root of unity: {omg1}");
    println!("Inverse NTT: {inverse_ntt:?}, modulus: {n2}, nth root of unity: {omg2}");
    println!("\nCircular convolution...\n");
    print!("Enter length of the vectors: ");
    io::stdout().flush().unwrap();
    let length: usize = read_input().trim().parse().unwrap();
    println!("Enter vector elements: ");
    let mut vec_x: Vec<Integer> = vec![Integer::ZERO; length];
    vec_x
        .iter_mut()
        .for_each(|x| *x = Integer::from_str_radix(&read_input(), 10).unwrap());
    println!("Enter vector elements: ");
    let mut vec_y: Vec<Integer> = vec![Integer::ZERO; length];
    vec_y
        .iter_mut()
        .for_each(|x| *x = Integer::from_str_radix(&read_input(), 10).unwrap());
    let (circ_conv, n, omg) = circular_convolution(&vec_x, &vec_y);
    println!("Circular convolution: {circ_conv:?}, modulus: {n}, nth root of unity: {omg}");
}
