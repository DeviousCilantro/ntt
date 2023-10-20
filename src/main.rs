use rug::{Integer, Float};
use std::ops::{BitAnd, Shr};
use rug::integer::IsPrime;
use rug::ops::Pow;
use ring::rand::{SystemRandom, SecureRandom};
use rug::ops::DivRounding;
use std::io::{self, Write};

// Generate a random rug::Integer ∈ ℤ ∩ [lower, upper]
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

// Check if an integer n is prime
fn is_prime(n: &Integer) -> bool {
    !matches!(n.is_probably_prime(20), IsPrime::No)
}

// Read input from stdin
fn read_input() -> String {
    let mut input = String::new();
    io::stdin()
        .read_line(&mut input)
        .unwrap();
    input
}

// Compute the unique prime factors of an integer n
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

// Find the generator of the prime field ℤ_n
fn find_generator(n: &Integer) -> Integer {
    let mut gen: Integer;
    loop {
        gen = random_integer_between(Integer::ONE, n);

        // Factorize (n - 1)
        let factors = prime_factors(n.clone() - 1);

        // If gen^[(n - 1) / p] ≢ 1 mod n ∀ p ∈ factors, then gen is a generator of ℤ 
        if factors.iter().all(|x| gen.clone().pow_mod(&((n.clone() - 1) / x), n).unwrap() != Integer::ONE.clone()) {
            break;
        }
    }
    gen
}

// Barrett-reduce x modulo n
fn br_reduce(n: &Integer, x: &Integer) -> Integer {

    // x has to be less than n^2
    assert!(x.clone() < (n.clone().pow(2)));

    // Choose k as ⌈log2 n⌉
    let k: u32 = Float::with_val(64, Float::parse(n.to_string()).unwrap())
        .log2()
        .ceil()
        .to_integer()
        .unwrap()
        .to_u32()
        .unwrap();

    // Ensure 2^k > n
    assert!(Integer::from(2).pow(k) > n.clone());

    // Compute r = ⌊4^k / n⌋
    let r = Integer::from(4).pow(k).div_floor(n.clone());

    // Compute t = x - (n * ⌊xr / 4^k⌋) using right shifts
    let t = x.clone() - (n.clone() * ((x * r) >> (k * 2)));

    // If t < n return t else return t - n
    if t < n.clone() {
        return t;
    }
    t - n
}

// Perform Montgomery multiplication on {a, b} reduced modulo n
fn mg_reduce(n: &Integer, a: &Integer, b: &Integer) -> Integer {

    // Compute the power of two closest to r
    let r = n.clone().next_power_of_two();

    // Ensure r is coprime to n
    assert!(r.clone().gcd(n) == 1);

    // Compute r_inv = r^(-1) mod n
    let r_inv = r.clone().invert(n).unwrap();

    // Compute k = (r * r_inv)  - 1) / n
    let k: Integer = ((r.clone() * r_inv.clone()) - 1) / n.clone();

    // Compute x = (ar mod n) * (br mod n)
    let x: Integer = (a * r.clone()).modulo(n) * (b * r.clone()).modulo(n);

    // Compute t = x + [n * (xk mod r)] using bitmasks
    let t: Integer = x.clone() + (n.clone() * (x.clone() * k.clone()).bitand(r.clone() - 1));

    // Compute u = t / r using rightshifts
    let u: Integer = t.clone().shr((r - Integer::ONE).significant_bits());

    // Return [(u - n) * r_inv] mod n if u > n else return (u * r_inv) mod n
    if u > n.clone() {
        return br_reduce(n, &((u - n) * r_inv));
    }
    br_reduce(n, &(u * r_inv))
}

// Compute the forward/inverse number-theoretic transform of a given vector naively
fn naive_ntt(input: &[Integer], mwm: &mut Option<Integer>, omg: &mut Option<Integer>, inverse: bool) -> (Vec<Integer>, Integer, Integer) {
    let l = Integer::from(input.len());

    // Find maximum element in input
    let max: Integer =  input
        .iter()
        .cloned()
        .max()
        .unwrap();

    // If no minimum working modulus passed, calculate mwm > max, mwm > l
    if mwm.is_none() { 
        *mwm = Some(std::cmp::max(max + 1, l.clone() + 1)); 
    } else {
        assert!(mwm.clone().unwrap() > l);
        assert!(mwm.clone().unwrap() > max);
    }

    // Calculate n = mwm if mwm is prime, else the smallest prime greater than mwm
    let mut n: Integer = if is_prime(&mwm.clone().unwrap()) { 
        mwm.clone().unwrap()
    } else { 
        mwm.clone().unwrap().next_prime() 
    };

    // Make n = k * l + 1
    loop {
        if (n.clone() - Integer::ONE).is_divisible(&l) { break; }
        n = n.next_prime();
    }
    let k = (n.clone() - 1) / l.clone();

    // If no primitive lth root of unity passed, calculate omg = g^k mod n
    // where g is a generator of ℤ_n
    if omg.is_none() {
        *omg = Some(find_generator(&n).pow_mod(&k, &n).unwrap());
    } else {
        // Ensure omg^l == 1
        assert!(omg.clone().unwrap().pow_mod(&l, &n).unwrap() == 1);

        // Factorize l
        let factors = prime_factors(l.clone());

        // Ensure omg^(l/x) mod n ≢ 1 mod n ∀ x ∈ factors
        assert!(factors.iter().all(|x| omg
                                   .clone()
                                   .unwrap()
                                   .pow_mod(&(l.clone() / x), &n)
                                   .unwrap() != Integer::ONE.clone()));
    };

    // Calculate output = NTT(input), where 
    // output[x] = Σ_(i = 0)^(l - 1) [input[i] * omg^(x * i)] (mod n)
    let output = input
        .iter()
        .enumerate()
        .map(|(outer, _)| 
             br_reduce(&n, &input
                       .iter()
                       .enumerate()
                       .fold(Integer::ZERO, |sum, (inner, element)| 
                             sum + mg_reduce(&n, element, &omg.clone()
                                             .unwrap()
                                             .pow((outer * inner) as u32))))).collect();

    // Return the forward transform if inverse flag is not passed
    if !inverse { return (output, n, omg.clone().unwrap()); }

    // Return the inverse transform if inverse flag is passed, output[x] = output[x] * l^(-1) (mod n)
    (output
     .iter()
     .map(|x| mg_reduce(&n, x, &l.clone().invert(&n).unwrap()))
     .collect(), n, omg.clone().unwrap())
}

// Compute the forward transform of a given vector via Cooley-Tukey butterfly interleaving
fn ctntt(input: &mut Vec<Integer>, n: &Integer, omg: &Integer) {
    let len = input.len();

    // Base case
    if len <= 1 {
        return;
    }

    // Partition the vector into odd-indexed and even-indexed elements
    let (mut even, mut odd): (Vec<Integer>, Vec<Integer>) = input
                              .chunks_exact(2)
                              .map(|chunk| (chunk[0].clone(), chunk[1].clone()))
                              .unzip();


    // Recursively compute the NTT of the even and odd parts,
    // updating the root of unity at each layer
    ctntt(&mut even, n, &mg_reduce(n, omg, omg));
    ctntt(&mut odd, n, &mg_reduce(n, omg, omg));

    // Initial exponent for root of unity is 0
    let mut w = Integer::from(1);

    // Alternate recombination method
    if false {
        for i in 0..len / 2 {
            let t = mg_reduce(n, &w, &odd[i]);
            input[i] = br_reduce(n, &(even[i].clone() + t.clone()));
            input[i + len / 2] = br_reduce(n, &(even[i].clone() - t.clone()));
            w = mg_reduce(n, &w, omg);
        }
    }

    // Recombine the NTT output using standard CT butterflies:
    // output[k] = A[k] + ω^k B[k] (mod n)
    // output[k + len / 2] = A[k] - ω^k B[k] (mod n)
    // where A[k] = NTT(even), B[k] = NTT(odd)
    even
        .iter()
        .zip(odd.iter())
        .enumerate()
        .for_each(|(i, (e, o))| {
            let t = mg_reduce(n, &w, o);
            w = mg_reduce(n, &w, omg);

            *input.get_mut(i).unwrap() = br_reduce(n, &(e.clone() + t.clone()));
            *input.get_mut(i + len / 2).unwrap() = br_reduce(n, &(e.clone() - t.clone()));
        });
}

// Compute the inverse transform of a given vector via Gentleman-Sande butterfly interleaving
fn _gsintt(_input: &mut [Integer], _n: &Integer, _omg: &Integer, _omg_inv: &Integer) {
    todo!()
}

// Perform a circular convolution on two vectors x, y i.e. NTT^(-1)[NTT(x) . NTT(y)]
// where '.' is the Hadamard product of two vectors, NTT^(-1) is the inverse transform
fn circular_convolution(vec_x: &[Integer], vec_y: &[Integer]) -> (Vec<Integer>, Integer, Integer) {
    // Ensure the vectors are of the same length
    assert_eq!(vec_x.len(), vec_y.len());

    // Find the maximum element across vec_x and vec_y
    let max = 
        vec_x
        .iter()
        .chain(vec_y.iter())
        .cloned()
        .collect::<Vec<_>>()
        .iter()
        .cloned()
        .max()
        .unwrap();

    // Compute minimum working modulus as max^2 * vec_x.len() + 1 to avoid overflow
    let mut mwm = Some(max.pow(2) * vec_x.len() + 1);

    // Compute NTT(x), NTT(y)
    let (ntt_x, nx, omg) = naive_ntt(vec_x, &mut mwm, &mut None, false);
    let (ntt_y, ny, _) = naive_ntt(vec_y, &mut mwm, &mut Some(omg.clone()), false);

    println!("NTT(X): {ntt_x:?}");
    println!("NTT(Y): {ntt_y:?}");

    // Ensure modulus is identical across NTT(x) and NTT(y), given identical mwm
    assert_eq!(nx, ny);

    // Perform a Hadamard product on NTT(x) and NTT(y) reduced modulo nx
    let ntt_mult: Vec<Integer>= ntt_x
        .iter()
        .zip(ntt_y.iter())
        .map(|(x, y)| mg_reduce(&nx, x, y))
        .collect();
    println!("NTT(X) ∘ NTT(Y): {ntt_mult:?}");

    // Return NTT^(-1)(ntt_mult) as the circular convolution
    naive_ntt(&ntt_mult, &mut mwm, &mut Some(omg.clone()), true)
}

fn main() {
    println!("\nNumber-theoretic transform...\n");

    print!("Enter length of vector: ");
    io::stdout().flush().unwrap();
    let l: usize = read_input().trim().parse().unwrap();

    println!("Enter vector elements: ");
    let mut input: Vec<Integer> = vec![Integer::ZERO; l];
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

    print!("Enter {}th root of unity? Leave blank to skip... ", input.len());
    io::stdout().flush().unwrap();
    let readinput = read_input();
    let mut omg = if readinput.trim().is_empty() { 
        None 
    } else { 
        Some(Integer::from_str_radix(&readinput, 10).unwrap()) 
    };

    // Calculate the forward/inverse transforms of the vector using the naive method
    let (forward_ntt, n1, omg1) = naive_ntt(&input, &mut mwm, &mut omg, false);
    let (inverse_ntt, n2, omg2) = naive_ntt(&input, &mut mwm, &mut Some(omg1.clone()), true);

    // If the vector length is a power of two, calculate the forward transform using
    // CT butterfly interleaving to verify correctness
    if (input.len() & (input.len() - 1)) == 0 { ctntt(&mut input, &n1, &omg1); }
    assert!(forward_ntt == input);

    println!("Forward NTT: {forward_ntt:?}, modulus: {n1}, {}th root of unity: {omg1}", input.len());
    println!("Inverse NTT: {inverse_ntt:?}, modulus: {n2}, {}th root of unity: {omg2}", input.len());

    println!("\nCooley-Tukey butterfly interleaving verified.");

    println!("\nCircular convolution...\n");
    print!("Enter length of the vectors: ");
    io::stdout().flush().unwrap();
    let l: usize = read_input().trim().parse().unwrap();

    println!("Enter vector elements: ");
    let mut vec_x: Vec<Integer> = vec![Integer::ZERO; l];
    vec_x
        .iter_mut()
        .for_each(|x| *x = Integer::from_str_radix(&read_input(), 10).unwrap());

    println!("Enter vector elements: ");
    let mut vec_y: Vec<Integer> = vec![Integer::ZERO; l];
    vec_y
        .iter_mut()
        .for_each(|x| *x = Integer::from_str_radix(&read_input(), 10).unwrap());

    let (circ_conv, n, omg) = circular_convolution(&vec_x, &vec_y);
    println!("Circular convolution = NTT^(-1)[NTT(X) ∘ NTT(Y)]: {circ_conv:?}, modulus: {n}, {}th root of unity: {omg}", circ_conv.len());
}
