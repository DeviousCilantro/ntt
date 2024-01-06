use rug::{Integer, Float};
use std::ops::{BitAnd, Shr};
use rug::integer::IsPrime;
use rug::ops::Pow;
use ring::rand::{SystemRandom, SecureRandom};
use rug::ops::DivRounding;
use std::io::{self, Write};
use std::fs::File;

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
    io::stdout().flush().unwrap();
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

    // Compute k = (r * r_inv) - 1) / n
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

// Find nearest prime modulus p for s-length vector such that s | p - 1 
fn find_modulus(input: &[Integer], mwm: &mut Option<Integer>) -> Integer {
    let s = Integer::from(input.len() * 2);

    // Find maximum element in input
    let max: Integer =  input
        .iter()
        .cloned()
        .max()
        .unwrap();

    // Calculate minimum working modulus mwm > max, mwm > l
    if mwm.is_none() {
        *mwm = Some(std::cmp::max(max + 1, s.clone() + 1)); 
    }

    // Calculate p = mwm if mwm is prime, else the smallest prime greater than mwm
    let mut p: Integer = if is_prime(&mwm.clone().unwrap()) { 
        mwm.clone().unwrap()
    } else { 
        mwm.clone().unwrap().next_prime() 
    };

    // Make p = k * s + 1
    loop {
        if (Integer::from(p.clone() - 1)).is_divisible(&s) { break; }
        p = p.next_prime();
    }

    p
}

// Compute the forward/inverse number-theoretic transform of a given vector naively
fn naive_ntt(input: &[Integer], n: &Integer, omg: &Integer, inverse: bool) -> Vec<Integer> {
    let s = Integer::from(input.len());

    // Ensure the s-th primitive root of unity omg = g^k mod n, 
    // where g is a generator of ℤ_n, is valid

    // Ensure omg^s == 1
    assert!(omg.clone().pow_mod(&s, n).unwrap() == 1);

    // Factorize s
    let factors = prime_factors(s.clone());

    // Ensure omg^(s/x) mod n ≢ 1 mod n ∀ x ∈ factors
    assert!(factors.iter().all(|x| omg
                               .clone()
                               .pow_mod(&(s.clone() / x), n)
                               .unwrap() != Integer::ONE.clone()));

    // Calculate output = NTT(input), where 
    // output[x] = Σ_(i = 0)^(l - 1) [input[i] * omg^(x * i)] (mod n)
    let output = input
        .iter()
        .enumerate()
        .map(|(outer, _)| 
             br_reduce(n, &input
                       .iter()
                       .enumerate()
                       .fold(Integer::ZERO, |sum, (inner, element)| 
                             sum + mg_reduce(n, element, &omg.clone()
                                             .pow((outer * inner) as u32))))).collect();

    // Return the forward transform if inverse flag is not passed
    if !inverse { return output; }

    // Return the inverse transform if inverse flag is passed, output[x] = output[x] * l^(-1) (mod n)
    output
        .iter()
        .map(|x| mg_reduce(n, x, &s.clone().invert(n).unwrap()))
        .collect()
}

fn compute_powers_of_psi(n: usize, psi: &Integer, q: &Integer) -> Vec<Integer> {
    let mut powers = Vec::with_capacity(n);
    let mut current_power = Integer::from(1);

    for _ in 0..n {
        powers.push(current_power.clone());
        current_power = mg_reduce(&q, &current_power, &psi);
    }

    powers
}

fn bit_reverse_order(vec: Vec<Integer>, n: usize) -> Vec<Integer> {
    let log_n = (n as f64).log2() as u32;
    let mut pairs: Vec<_> = vec.into_iter()
        .enumerate()
        .map(|(i, x)| {
            let rev_i = i.reverse_bits() >> (32 - log_n);
            (rev_i, x)
        })
    .collect();

    pairs.sort_by_key(|&(i, _)| i);
    pairs.into_iter().map(|(_, x)| x).collect()
}

fn iterative_ctntt(x: &mut Vec<Integer>, g: &Vec<Integer>, q: &Integer, butterflies: &mut Vec<Vec<Integer>>) {
    let n = x.len();
    let mut t = n / 2;
    let mut m = 1;

    // Initialize butterflies vector
    butterflies.clear();
    butterflies.push(x.clone());  // Store initial state

    while m < n {
        let mut k = 0;
        for i in 0..m {
            let s = &g[m + i];

            for j in k..(k + t) {
                let u = x[j].clone();
                let v = mg_reduce(&q, &x[j + t], &s);

                x[j] = br_reduce(&q, &Integer::from(u.clone() + &v));
                x[j + t] = br_reduce(&q, &Integer::from(u - &v));
            }

            k += 2 * t;
        }

        // Store the state after each iteration
        butterflies.push(x.clone());

        t /= 2;
        m *= 2;
    }
}


fn iterative_gsintt(x: &mut Vec<Integer>, g_inv: &Vec<Integer>, q: &Integer, n_inv: &Integer, butterflies: &mut Vec<Vec<Integer>>) {
    let n = x.len();
    let mut t = 1;
    let mut m = n / 2;

    // Initialize butterflies vector
    butterflies.clear();
    butterflies.push(x.clone());  // Store initial state

    while m > 0 {
        let mut k = 0;
        for i in 0..m {
            let s = &g_inv[m + i];

            for j in k..(k + t) {
                let u = x[j].clone();
                let v = x[j + t].clone();

                x[j] = br_reduce(&q, &Integer::from(u.clone() + &v));
                let w = br_reduce(&q, &Integer::from(u - &v));
                x[j + t] = mg_reduce(&q, &w, &s);
            }

            k += 2 * t;
        }

        // Store the state after each iteration
        butterflies.push(x.clone());

        t *= 2;
        m /= 2;
    }

    // Final normalization step
    for xi in x.iter_mut() {
        *xi = mg_reduce(&q, &xi, &n_inv);
    }

    // Store the final state
    butterflies.push(x.clone());
}

// Compute the forward transform of a given (2^n)-length vector ∀ n ∈ ℕ via Cooley-Tukey butterfly interleaving
fn recursive_ctntt(
    input: &mut Vec<Integer>, 
    n: &Integer, 
    omg: &Integer, 
    depth: usize, 
    butterflies: &mut Vec<Vec<Vec<Integer>>>,
) {
    let len = input.len();
    if len <= 1 {
        return;
    }

    // Now, separately map the even and odd index vectors to their corresponding values
    let (mut even, mut odd): (Vec<Integer>, Vec<Integer>) = input
                          .chunks_exact(2)
                          .map(|chunk| (chunk[0].clone(), chunk[1].clone()))
                          .unzip();

    // Recurse for even and odd parts
    recursive_ctntt(&mut even, n, &mg_reduce(n, omg, omg), depth + 1, butterflies);
    recursive_ctntt(&mut odd, n, &mg_reduce(n, omg, omg), depth + 1, butterflies);

    // Ensure the butterflies vector has enough sub-vectors for the current depth
    while butterflies.len() <= depth {
        butterflies.push(Vec::new());
    }

    // Store the current state before performing the butterfly operations
    butterflies[depth].push(input.clone());

    let mut w = Integer::from(1);

    // Butterfly operations
    for i in 0..len / 2 {
        let u = even[i].clone();
        let v = mg_reduce(n, &w, &odd[i]);

        let even_index = i;
        let odd_index = i + len / 2;

        input[even_index] = br_reduce(n, &(u.clone() + v.clone()));
        input[odd_index] = br_reduce(n, &(u - v));

        w = mg_reduce(n, &w, omg);

        if butterflies[depth].is_empty() {
            butterflies[depth].push(Vec::new());
        }
    }

    // Store the state after performing the butterfly operations
    butterflies[depth].push(input.clone());
}

// Compute the inverse transform of a given (2^n)-length vector ∀ n ∈ ℕ via Gentleman-Sande butterfly interleaving
fn recursive_gsintt(
    input: &mut [Integer], 
    n: &Integer, 
    omg_inv: &Integer, 
    depth: usize, 
    butterflies: &mut Vec<Vec<Vec<Integer>>>,
) {
    let len = input.len();

    // Base case
    if len <= 1 {
        return;
    }

    // Ensure the butterflies vector has enough sub-vectors for the current depth
    while butterflies.len() <= depth {
        butterflies.push(Vec::new());
    }

    // Store the current state before performing the butterfly operations
    butterflies[depth].push(input.to_vec());

    let mut w = Integer::from(1);

    // Partition the vector at the middle
    let (first, second) = input.split_at_mut(len / 2);

    // Combine using standard GS butterflies:
    for (_, (a, b)) in first.iter_mut().zip(second.iter_mut()).enumerate() {
        let u = a.clone();
        let v = b.clone();

        *a = br_reduce(n, &(u.clone() + v.clone()));

        let t = br_reduce(n, &(u - v));
        *b = mg_reduce(n, &w, &t);

        w = mg_reduce(n, &w, omg_inv);
    }

    // Partition the butterfly-operated vector at the middle
    let (first, second) = input.split_at_mut(len / 2);

    // Recursively compute the INTT of the first and second halves
    recursive_gsintt(first, n, &mg_reduce(n, omg_inv, omg_inv), depth + 1, butterflies);
    recursive_gsintt(second, n, &mg_reduce(n, omg_inv, omg_inv), depth + 1, butterflies);

    // Store the state after performing the butterfly operations
    butterflies[depth].push(input.to_vec());
}

// Naive polynomial multiplication
fn polynomial_multiply(a: &[Integer], b: &[Integer], modulus: &Integer, n: usize, nega: bool) -> Vec<Integer> {
    let mut result = vec![Integer::from(0); 2 * n - 1];

    // Polynomial multiplication
    for i in 0..n {
        for j in 0..n {
            result[i + j] += &a[i] * &b[j];
        }
    }

    // Modulo reduction for each coefficient
    for i in 0..2 * n - 1 {
        result[i] %= modulus;
    }

    // Reduction by x^n + 1 / x^n - 1
    if nega {
        for i in n..2 * n - 1 {
            result[i - n] = br_reduce(&modulus, &Integer::from(&result[i - n] - &result[i]));
        }
    }
    else {
        for i in n..2 * n - 1 {
            result[i - n] = br_reduce(&modulus, &Integer::from(&result[i - n] + &result[i]));
        }
    }

    result.truncate(n);
    result
}

// Perform a circular convolution on two vectors x, y i.e. NTT^(-1)[NTT(x) . NTT(y)]
// where '.' is the Hadamard product of two vectors, NTT^(-1) is the inverse transform
fn convolution(vec_x: &[Integer], vec_y: &[Integer], circular: bool) -> Vec<Integer> {
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

    // Find modulus
    let n = find_modulus(vec_x, &mut Some(max.clone() * max * vec_x.len() + 1));

    // Calculate root of unity
    let gen = find_generator(&n);
    let omg = gen.clone().pow_mod(&((n.clone() - 1) / Integer::from(vec_x.len())), &n).unwrap();
    let phi = gen.clone().pow_mod(&((n.clone() - 1) / Integer::from(vec_x.len() * 2)), &n).unwrap();

    let psi = compute_powers_of_psi(vec_x.len(), &phi, &n);
    let psi_rev = bit_reverse_order(psi.clone(), vec_x.len());

    println!("modulus: {:?}", &n);
    println!("nth root of unity: {omg}");
    println!("2nth root of unity: {phi}");
    println!("precomputed powers (bit-reversed): {:?}", &psi_rev);

    // Compute NTT(x), NTT(y)
    let mut ntt_x: Vec<Integer>;
    let mut ntt_y: Vec<Integer>;

    if circular {
        println!("Computing circular convolution...");
        // If the vector length is a power of two, calculate the forward transforms using
        // CT butterfly interleaving
        if (vec_x.len() & (vec_x.len() - 1)) == 0 {
            println!("\nUsing Cooley-Tukey butterfly interleaving...");
            ntt_x = vec_x.clone().to_vec();
            ntt_y = vec_y.clone().to_vec();
            let mut butterflies = Vec::new();
            recursive_ctntt(&mut ntt_x, &n, &omg, 0, &mut butterflies);
            let mut butterflies = Vec::new();
            recursive_ctntt(&mut ntt_y, &n, &omg, 0, &mut butterflies);
        } else {
            ntt_x = naive_ntt(vec_x, &n, &omg, false);
            ntt_y = naive_ntt(vec_y, &n, &omg, false);
        }

        println!("\nNTT(X): {ntt_x:?}");
        println!("NTT(Y): {ntt_y:?}");

        // Perform a Hadamard product on NTT(x) and NTT(y) reduced modulo n
        let mut ntt_mult: Vec<Integer>= ntt_x
            .iter()
            .zip(ntt_y.iter())
            .map(|(x, y)| mg_reduce(&n, x, y))
            .collect();
        println!("NTT(X) ∘ NTT(Y): {ntt_mult:?}");

        // Return NTT^(-1)(ntt_mult) as the circular convolution
        if (ntt_mult.len() & (ntt_mult.len() - 1)) == 0 {
            println!("\nUsing Gentleman-Sande butterfly interleaving...");
            let mut butterflies = Vec::new();
            recursive_gsintt(&mut ntt_mult, &n, &omg, 0, &mut butterflies);

            // Scale result by modular inverse of vector length
            ntt_mult.iter_mut().for_each(|x| *x = mg_reduce(&n, &Integer::from(vec_x.len()).invert(&n).unwrap(), x));

            assert_eq!(ntt_mult.sort(), polynomial_multiply(&vec_x, &vec_y, &n, vec_x.len(), false).sort());
            return ntt_mult;
        }

        return naive_ntt(&ntt_mult, &n, &omg, true);
    }

    println!("Computing negacyclic convolution...");

    ntt_x = vec_x.clone().to_vec();
    ntt_y = vec_y.clone().to_vec();

    let mut butterflies = Vec::new();

    iterative_ctntt(&mut ntt_x, &psi_rev, &n, &mut butterflies);

    let mut butterflies = Vec::new();
    iterative_ctntt(&mut ntt_y, &psi_rev, &n, &mut butterflies);

    println!("\nNTT(X): {ntt_x:?}");
    println!("NTT(Y): {ntt_y:?}");

    let mut ntt_mult: Vec<Integer>= ntt_x
        .iter()
        .zip(ntt_y.iter())
        .map(|(x, y)| mg_reduce(&n, x, y))
        .collect();

    println!("NTT(X) ∘ NTT(Y): {ntt_mult:?}");

    let mut butterflies = Vec::new();
    // Return NTT^(-1)(ntt_mult) as the negacyclic convolution
    iterative_gsintt(&mut ntt_mult, &compute_inverses(&psi_rev, &n), &n, &Integer::from(vec_x.len()).invert(&n).unwrap(), &mut butterflies);

    assert_eq!(ntt_mult, polynomial_multiply(&vec_x, &vec_y, &n, vec_x.len(), true));

    ntt_mult
}

// Compute modular multiplicative inverses of the powers of the root of unity
fn compute_inverses(powers: &Vec<Integer>, q: &Integer) -> Vec<Integer> {
    powers.iter().map(|x| x.clone().invert(q).unwrap()).collect()
}

fn main() {
    println!("\nNumber-theoretic transform...\n");

    print!("Enter length of vector: ");
    let l: usize = read_input().trim().parse().unwrap();

    println!("Enter vector elements: ");
    let mut input: Vec<Integer> = vec![Integer::ZERO; l];
    input
        .iter_mut()
        .for_each(|x| *x = Integer::from_str_radix(&read_input(), 10).unwrap());

    print!("Enter modulus? Leave blank to skip... ");
    let readinput = read_input();
    let n = if readinput.trim().is_empty() { 
        find_modulus(&input, &mut None)
    } else { 
        Integer::from_str_radix(&readinput, 10).unwrap()
    };

    print!("Enter {}th root of unity? Leave blank to skip... ", input.len());
    let readinput = read_input();
    let gen = find_generator(&n);
    let omg = if readinput.trim().is_empty() { 
        // calculate l-th root of unity
        // omg = g^k mod n where g is a generator of ℤ_n
        gen.clone().pow_mod(&((n.clone() - 1) / Integer::from(l)), &n).unwrap()
    } else { 
        Integer::from_str_radix(&readinput, 10).unwrap()
    };

    let phi = gen.clone().pow_mod(&((n.clone() - 1) / Integer::from(l * 2)), &n).unwrap();
    assert_eq!(omg, mg_reduce(&n, &phi, &phi));

    // Calculate the forward/inverse transforms of the vector using the naive method
    let forward_ntt = naive_ntt(&input, &n, &omg, false);
    let inverse_ntt = naive_ntt(&forward_ntt, &n, &omg, true);


    let psi = compute_powers_of_psi(input.len(), &phi, &n);
    let psi_rev = bit_reverse_order(psi.clone(), input.len());

    println!("modulus: {:?}", &n);
    println!("nth root of unity: {omg}");

    println!("naive forward_ntt: {:?}", forward_ntt);
    println!("naive inverse_ntt: {:?}", inverse_ntt);

    println!("2nth root of unity: {phi}");
    println!("precomputed powers (bit-reversed): {:?}", &psi_rev);

    let mut butterflies = Vec::new();
    iterative_ctntt(&mut input, &psi_rev, &n, &mut butterflies);
    println!("\niterative_ctntt: {:?}", input);
    println!("butterflies: {:?}", butterflies);
    let mut file = File::create("iterative_ctntt_calc.txt").expect("Unable to create file");
    for (index, vector) in butterflies.iter().enumerate() {
        writeln!(&mut file, "at iteration {}:", index).expect("Unable to write to file");
        writeln!(&mut file, "{:?}", vector).expect("Unable to write to file");
    }
    let mut butterflies = Vec::new();
    iterative_gsintt(&mut input, &compute_inverses(&psi_rev, &n), &n, &Integer::from(l).invert(&n).unwrap(), &mut butterflies);
    println!("\niterative_gsintt: {:?}", input);
    println!("butterflies: {:?}", butterflies);
    let mut file = File::create("iterative_gsintt_calc.txt").expect("Unable to create file");
    for (index, vector) in butterflies.iter().enumerate() {
        writeln!(&mut file, "at iteration {}:", index).expect("Unable to write to file");
        writeln!(&mut file, "{:?}", vector).expect("Unable to write to file");
    }

    let mut butterflies = Vec::new();

    // If the vector length is a power of two, calculate the forward+inverse transform using
    // CT/GS butterfly interleaving to verify correctness
    if (input.len() & (input.len() - 1)) == 0 { 
        let mut fwd = input.clone();

        recursive_ctntt(&mut fwd, &n, &omg, 0, &mut butterflies);
        println!("\nrecursive_ctntt: {:?}", fwd);
        println!("butterflies: {:?}", butterflies);
        let mut file = File::create("recursive_ctntt_calc.txt").expect("Unable to create file");

        for (index, stage) in butterflies.iter().enumerate() {
            writeln!(&mut file, "at depth {}:", index).expect("Unable to write to file");

            for (jndex, vector) in stage.iter().enumerate() {
                if jndex % 2 == 0 {
                    write!(&mut file, "{:?}\t", vector).expect("Unable to write to file");
                }
            }

            writeln!(&mut file).expect("Unable to write to file");
        }

        butterflies.reverse();

        for (index, stage) in butterflies.iter().enumerate() {
            let depth = butterflies.len() - 1 - index;
            writeln!(&mut file, "computed at depth {}:", depth).expect("Unable to write to file");

            for (jndex, vector) in stage.iter().enumerate() {
                if jndex % 2 != 0 {
                    write!(&mut file, "{:?}\t", vector).expect("Unable to write to file");
                }
            }

            writeln!(&mut file).expect("Unable to write to file");
        }        
        let mut butterflies = Vec::new();
        recursive_gsintt(&mut fwd, &n, &omg.clone().invert(&n).unwrap(), 0, &mut butterflies);

        // Scale by modular inverse of vector length
        fwd.iter_mut().for_each(|x| *x = mg_reduce(&n, &Integer::from(input.len()).invert(&n).unwrap(), x));

        println!("\nrecursive_gsintt: {:?}", fwd);
        println!("butterflies: {:?}", butterflies);

        let mut file = File::create("recursive_gsintt_calc.txt").expect("Unable to create file");

        for (index, stage) in butterflies.iter().enumerate() {
            writeln!(&mut file, "at depth {}:", index).expect("Unable to write to file");

            for (jndex, vector) in stage.iter().enumerate() {
                if jndex % 2 == 0 {
                    write!(&mut file, "{:?}\t", vector).expect("Unable to write to file");
                }
            }

            writeln!(&mut file).expect("Unable to write to file");
        }

        butterflies.reverse();

        for (index, stage) in butterflies.iter().enumerate() {
            let depth = butterflies.len() - 1 - index;
            writeln!(&mut file, "computed at depth {}:", depth).expect("Unable to write to file");

            for (jndex, vector) in stage.iter().enumerate() {
                if jndex % 2 != 0 {
                    write!(&mut file, "{:?}\t", vector).expect("Unable to write to file");
                }
            }

            writeln!(&mut file).expect("Unable to write to file");
        } 

        assert!(fwd.sort() == input.sort());

    }

    println!("\nConvolutions...\n");
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

    print!("Circular or negacylic? [c/n] ");
    io::stdout().flush().unwrap();
    let choice: char = read_input().trim().parse().unwrap();

    if choice == 'c' {
        let conv = convolution(&vec_x, &vec_y, true);
        println!("\nCircular convolution = NTT^(-1)[NTT(X) ∘ NTT(Y)]: {conv:?}");
    } else {
        let conv = convolution(&vec_x, &vec_y, false);
        println!("\nNegacyclic convolution = NTT^(-1)[NTT(X) ∘ NTT(Y)]: {conv:?}");
    }
}
