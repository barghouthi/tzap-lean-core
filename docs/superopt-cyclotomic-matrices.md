# Exact cyclotomic matrices in SuperOpt

SuperOpt represents Clifford+T unitaries exactly. It does not use floating-point
numbers, numerical tolerances, or rounded matrix entries when constructing or
querying its synthesis table.

## Scalar representation

Let

\[
\omega = e^{i\pi/4}, \qquad \omega^4 = -1, \qquad \sqrt{2}=\omega-\omega^3.
\]

Every matrix entry is stored as

\[
\frac{a+b\omega+c\omega^2+d\omega^3}{(\sqrt{2})^k},
\]

where `a`, `b`, `c`, and `d` are `i32` coefficients. A matrix has one shared
denominator exponent `k`, so an entry occupies 16 bytes—the same size as the
former pair of `f64` values.

The current SuperOpt presets use windows of at most 40 gates. Coefficient
operations are checked, so exceeding the fixed-width representation fails
instead of silently producing an unsound rewrite.

## Gate operations

The supported gates have simple exact operations:

- `T`, `S`, `Z`, and their inverses multiply selected rows by a power of
  `omega`, implemented as coefficient permutations and sign changes.
- `H` replaces a row pair `(x,y)` with `(x+y,x-y)` and increments `k`.
- `X`, `CX`, and `CCX` permute rows.
- `CZ` and `CCZ` negate selected rows.

`Rz` is intentionally outside this representation. An Rz gate is a SuperOpt
window barrier and is left unchanged for phase folding or Rz decomposition.

## Canonical denominator

Equivalent circuits can accumulate different apparent denominator exponents;
for example, `H H` initially introduces two factors of `sqrt(2)` before
reducing to the identity. After each Hadamard, SuperOpt removes every common
factor of `sqrt(2)` from the matrix numerators.

For a numerator `(a,b,c,d)`, divisibility by `sqrt(2)` is equivalent to `a`
and `c` having the same parity and `b` and `d` having the same parity. Exact
division produces

\[
\left(\frac{b-d}{2},\frac{a+c}{2},\frac{b+d}{2},\frac{c-a}{2}\right).
\]

This gives each exact matrix a canonical shared denominator.

## Global phase and fingerprints

SuperOpt compares matrices up to global phase. Clifford+T global phases are
powers of `omega`, so the implementation tries all eight powers on the first
nonzero entry and selects the lexicographically smallest coefficient tuple.
The selected phase is then applied while hashing or comparing the full matrix.

Fingerprints are deterministic 128-bit hashes of the canonical integer data.
A hash hit is still confirmed by exact matrix comparison before any rewrite is
accepted, protecting soundness against hash collisions.

The on-disk synthesis-table format is versioned. Moving from rounded
floating-point fingerprints to exact cyclotomic fingerprints bumped the cache
format to version 2, causing older tables to be rebuilt automatically.
