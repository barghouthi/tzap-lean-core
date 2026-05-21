//! Toy benchmark for phase-fold parity lookup strategies.
//!
//! This isolates the hot choice in `phase_fold_rand`:
//!
//!   current:    lookup parity, then lookup complement on miss
//!   canonical: canonicalize parity/complement, then do one lookup
//!
//! Build/run:
//!
//!   rustc -O scripts/phase_fold_lookup_demo.rs -o /tmp/phase_fold_lookup_demo
//!   /tmp/phase_fold_lookup_demo
//!   /tmp/phase_fold_lookup_demo --events 2000000 --complement-rate 80

use std::collections::HashMap;
use std::env;
use std::time::{Duration, Instant};

const DEFAULT_EVENTS: usize = 1_000_000;
const DEFAULT_GROUPS: usize = 10_000;
const DEFAULT_COMPLEMENT_RATE: u32 = 50;
const DEFAULT_REPEATS: usize = 7;

#[derive(Clone, Copy)]
struct Event {
    parity: u128,
    turn: u8,
}

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn next_u128(&mut self) -> u128 {
        ((self.next_u64() as u128) << 64) | self.next_u64() as u128
    }

    fn range(&mut self, n: usize) -> usize {
        (self.next_u64() as usize) % n
    }
}

fn canonical(parity: u128) -> (u128, bool) {
    let comp = !parity;
    if parity <= comp {
        (parity, false)
    } else {
        (comp, true)
    }
}

fn make_stream(events: usize, groups: usize, complement_rate: u32, seed: u64) -> Vec<Event> {
    let mut rng = Rng::new(seed);
    let bases: Vec<u128> = (0..groups).map(|_| rng.next_u128()).collect();
    let turns = [1u8, 2, 4, 6, 7];

    let mut stream = Vec::with_capacity(events);

    // Seed each group in its base orientation. After this, complemented
    // occurrences exercise the current implementation's second lookup path.
    for &base in bases.iter().take(events.min(groups)) {
        stream.push(Event {
            parity: base,
            turn: turns[rng.range(turns.len())],
        });
    }

    while stream.len() < events {
        let base = bases[rng.range(groups)];
        let parity = if (rng.next_u64() % 100) < complement_rate as u64 {
            !base
        } else {
            base
        };
        stream.push(Event {
            parity,
            turn: turns[rng.range(turns.len())],
        });
    }

    stream
}

fn current_two_lookup(stream: &[Event]) -> (usize, usize, u64) {
    let mut groups: HashMap<u128, u8> = HashMap::with_capacity(stream.len().min(16_384));
    let mut lookups = 0usize;
    let mut checksum = 0u64;

    for event in stream {
        lookups += 1;
        if let Some(acc) = groups.get_mut(&event.parity) {
            *acc = acc.wrapping_add(event.turn) & 7;
            checksum = checksum.wrapping_add(*acc as u64);
            continue;
        }

        let comp = !event.parity;
        lookups += 1;
        if let Some(acc) = groups.get_mut(&comp) {
            *acc = acc.wrapping_sub(event.turn) & 7;
            checksum = checksum.wrapping_add(*acc as u64);
            continue;
        }

        groups.insert(event.parity, event.turn & 7);
        checksum = checksum.wrapping_add(event.turn as u64);
    }

    (lookups, groups.len(), checksum)
}

fn canonical_one_lookup(stream: &[Event]) -> (usize, usize, u64) {
    let mut groups: HashMap<u128, u8> = HashMap::with_capacity(stream.len().min(16_384));
    let mut lookups = 0usize;
    let mut checksum = 0u64;

    for event in stream {
        let (key, is_complement) = canonical(event.parity);
        let signed_turn = if is_complement {
            0u8.wrapping_sub(event.turn)
        } else {
            event.turn
        };

        lookups += 1;
        if let Some(acc) = groups.get_mut(&key) {
            *acc = acc.wrapping_add(signed_turn) & 7;
            checksum = checksum.wrapping_add(*acc as u64);
        } else {
            groups.insert(key, signed_turn & 7);
            checksum = checksum.wrapping_add((signed_turn & 7) as u64);
        }
    }

    (lookups, groups.len(), checksum)
}

fn median(mut times: Vec<Duration>) -> Duration {
    times.sort_unstable();
    times[times.len() / 2]
}

fn time_runs(
    label: &str,
    repeats: usize,
    stream: &[Event],
    f: fn(&[Event]) -> (usize, usize, u64),
) -> (Duration, usize, usize, u64) {
    let mut times = Vec::with_capacity(repeats);
    let mut result = (0, 0, 0);

    for _ in 0..repeats {
        let start = Instant::now();
        result = f(stream);
        times.push(start.elapsed());
    }

    let med = median(times);
    println!(
        "{label:>20}: {:>9.2} ms  {:>12} lookups  {:>8} groups  checksum {}",
        med.as_secs_f64() * 1000.0,
        result.0,
        result.1,
        result.2
    );
    (med, result.0, result.1, result.2)
}

fn parse_args() -> (usize, usize, u32, usize) {
    let mut events = DEFAULT_EVENTS;
    let mut groups = DEFAULT_GROUPS;
    let mut complement_rate = DEFAULT_COMPLEMENT_RATE;
    let mut repeats = DEFAULT_REPEATS;

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        let value = args
            .next()
            .unwrap_or_else(|| panic!("missing value for {}", arg));
        match arg.as_str() {
            "--events" => events = value.parse().expect("invalid --events"),
            "--groups" => groups = value.parse().expect("invalid --groups"),
            "--complement-rate" => {
                complement_rate = value.parse().expect("invalid --complement-rate");
            }
            "--repeats" => repeats = value.parse().expect("invalid --repeats"),
            _ => panic!("unknown argument: {}", arg),
        }
    }

    assert!(events > 0, "--events must be positive");
    assert!(groups > 0, "--groups must be positive");
    assert!(repeats > 0, "--repeats must be positive");
    assert!(complement_rate <= 100, "--complement-rate must be 0..=100");

    (events, groups, complement_rate, repeats)
}

fn main() {
    let (events, groups, complement_rate, repeats) = parse_args();
    let stream = make_stream(events, groups, complement_rate, 1);

    println!(
        "Toy phase-fold lookup stream: {events} events, {groups} parity groups, \
         {complement_rate}% complements"
    );

    let current = time_runs(
        "current two-lookup",
        repeats,
        &stream,
        current_two_lookup,
    );
    let canonical = time_runs(
        "canonical one-lookup",
        repeats,
        &stream,
        canonical_one_lookup,
    );

    assert_eq!(current.2, canonical.2, "group counts should match");

    let lookup_reduction = 1.0 - canonical.1 as f64 / current.1 as f64;
    let probe_gain = current.1 as f64 / canonical.1 as f64;
    let speedup = current.0.as_secs_f64() / canonical.0.as_secs_f64();

    println!();
    println!("Lookup reduction: {:.1}%", lookup_reduction * 100.0);
    println!("Probe-model gain:  {probe_gain:.2}x fewer hash-table probes");
    println!("Median speedup:    {speedup:.2}x");
}
