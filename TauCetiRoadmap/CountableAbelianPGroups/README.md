# Roadmap: countable abelian p-groups and Ulm's theorem

**Summary.** Fix a prime `p` and an abelian group `G`, written additively. Multiplying by `p`
again and again, and intersecting at limit ordinals, gives a descending chain of subgroups
`p^α G` indexed by the ordinals. The chain stabilises at the largest subgroup `D` with `pD = D`,
and `G` is `p`-reduced when `D = 0`. The height of an element records how far down the chain it
survives. The `α`-th Ulm invariant of `G` is the dimension over the field with `p` elements of
`(p^α G)[p] / (p^(α+1) G)[p]`, where `H[p]` is the subgroup of elements of `H` killed by `p`.
This roadmap builds these objects with their basic theory and proves that the invariants classify
countable reduced `p`-groups.

The first headline is Ulm's theorem (1933): two countable reduced abelian `p`-groups are
isomorphic if and only if their Ulm invariants agree at every ordinal. The second is its extension
form: if two countable reduced `p`-groups have the same Ulm invariants, every height-preserving
isomorphism between finite subgroups extends to an isomorphism of the groups. The third computes
the invariants where a decomposition is known: in a direct sum of cyclic `p`-groups, the `k`-th
invariant is the number of summands of order `p^(k+1)`. The fourth is a consequence that mentions
no invariant: a countable reduced `p`-group `G` is isomorphic to every abelian group `H` with
`G × G ≅ H × H`.

The roadmap builds on Mathlib (the pointwise action on subgroups, the socle `G[p]` as a vector
space, recursion on ordinals, and dimension) and on Tau Ceti's additive `p`-group lemmas, which
count what adjoining one element adds to a finite subgroup. It supplies Ulm's theorem and an
ordinal rank on reduced abelian `p`-groups to the roadmap on the Borel completeness of algebraic
classes that CountableStructureSpacesPartII calls for.

Layer 0 builds the filtration, the `p`-divisible part and the length. Layer 1 treats heights.
Layer 2 defines the Ulm invariants and computes them for direct sums of cyclic groups. Layer 3
treats proper elements, invariants relative to a subgroup, and the one-step extension lemma of
Kaplansky and Mackey. Layer 4 proves Ulm's theorem by a back-and-forth argument.

## Conventions

- `G` and `H` are additive commutative groups, `[AddCommGroup G]`. A `p`-group is Mathlib's
  `IsAddPGroup p G`: every element is killed by some power of `p`. The definitions take a natural
  number `p`; a statement that needs it assumes that `p` is prime, `[Fact p.Prime]`.
- `p • H` is the image of a subgroup `H` under multiplication by `p`, Mathlib's pointwise action
  `AddSubgroup.pointwiseMulAction` of `ℕ` on `AddSubgroup G` (scoped in `Pointwise`); membership
  is `AddSubgroup.mem_smul_pointwise_iff_exists`.
- `G[p]` is Mathlib's `AddSubgroup.torsionBy G p`, the socle of `G` at `p`. It is a vector space
  over `ZMod p` by `AddSubgroup.torsionBy.zmodModule`, and every subgroup of it is a subspace by
  `AddSubgroup.toZModSubmodule`. For a subgroup `K` of `G`, `K[p]` means `K ⊓ G[p]`, regarded as
  a subspace of `G[p]`.
- The filtration `p^α G` is defined for an ordinal `α` of any universe, so that statements
  comparing two groups do not tie their universes together. Heights, the length and the
  `p`-divisible part of `G : Type u` are taken with ordinals in `Ordinal.{u}`.
- Dimensions are `Module.rank (ZMod p) _`, a cardinal in the universe of the group. A statement
  comparing invariants of groups in different universes uses `Cardinal.lift` on both sides.
- Heights take values in `WithTop Ordinal`; the value `⊤` is the height of the elements of the
  `p`-divisible part, in particular of `0`.
- Terminology follows Kaplansky 1954, §11, and Fuchs 2015, Ch. 10 §1 and Ch. 11 §1. The length is
  the ordinal at which `p^α G` stabilises. What Fuchs 2015, Ch. 1 §1, p. 4, calls the `σ`-th Ulm
  subgroup is `p^(ω·σ) G` for a `p`-group, and his Ulm length counts those subgroups; neither
  term is used below. The Ulm invariants are what Fuchs calls the Ulm–Kaplansky invariants.

## Layer 0: the transfinite filtration and the divisible part

### 0.1 The filtration

Define `pPow G p α`, written `p^α G`, by recursion on the ordinal `α` with `Ordinal.limitRecOn`:
`p^0 G = ⊤`, `p^(α+1) G = p • p^α G`, and `p^λ G = ⨅ β < λ, p^β G` for a limit ordinal `λ`
(kaplansky1954, §11, p. 26; fuchs2015, Ch. 10 §1, p. 299). Prove the three unfolding equations and
the membership forms `x ∈ p^(α+1) G ↔ ∃ y ∈ p^α G, p • y = x` and, for a limit `λ`,
`x ∈ p^λ G ↔ ∀ β < λ, x ∈ p^β G`. *Needs:* Mathlib `Ordinal.limitRecOn` with
`Ordinal.limitRecOn_zero`, `Ordinal.limitRecOn_add_one`, `Ordinal.limitRecOn_limit`;
`AddSubgroup.mem_smul_pointwise_iff_exists`.

- The family is antitone: `p^β G ≤ p^α G` for `α ≤ β`.
- For a natural number `n`, `x ∈ p^n G ↔ ∃ y, p ^ n • y = x`, and for every ordinal `α`,
  `x ∈ p^(α+n) G ↔ ∃ y ∈ p^α G, p ^ n • y = x`.
- Functoriality: a homomorphism `f : G →+ H` maps `p^α G` into `p^α H`, and an isomorphism
  `e : G ≃+ H` maps `p^α G` onto `p^α H`. Here `G` and `H` may live in different universes.
- For a subgroup `A` of `G`, the image of `p^α A` in `G` lies in `A ⊓ p^α G`.
- Products and sums: `p^α (G × H)` is the product of `p^α G` and `p^α H`, and an element of a
  direct sum `⨁ i, G i` lies in `p^α (⨁ i, G i)` exactly when each component lies in
  `p^α (G i)`.
- The index universe does not matter: `p^(Ordinal.lift α) G = p^α G`.
- Agreement with Mathlib's fixed-point approximants: for `G : Type u` and `α : Ordinal.{u}`,
  `p^α G` is `OrdinalApprox.gfpApprox f ⊤ α`, where `f` is the order homomorphism `H ↦ p • H` of
  `AddSubgroup G`. This is the form in which `OrdinalApprox.gfpApprox_ord_eq_gfp` and its
  companions apply in §0.2.

**Checks.**

- `G = ZMod (p ^ n)`: `p^k G` has `p ^ (n - k)` elements for `k ≤ n` and is trivial for `k ≥ n`,
  in particular at every infinite ordinal.
- `G = ℤ`: `p^n ℤ` is the multiples of `p ^ n`, and `p^ω ℤ = 0`, the intersection, although no
  `p^n ℤ` is trivial.
- `G = ℚ`: `p^α ℚ = ℚ` for every `α`.
- The subgroup clause is not an equality: for `G = ZMod (p ^ 2)` and `A = p • ⊤`, the subgroup
  `p^1 A` is trivial while `A ⊓ p^1 G = A` has `p` elements.
- The chain can continue past `ω`: in the group generated by `x, y₁, y₂, …` with the relations
  `p x = 0` and `pⁱ yᵢ = x`, the subgroup `p^ω G` is generated by `x` and has `p` elements, and
  `p^(ω+1) G` is trivial (kaplansky1954, §11, p. 31, remark (b); fuchs2015, Ch. 11, Example 1.8,
  p. 347, where it is the Prüfer group of length `ω + 1`).

### 0.2 The divisible part and reduced groups

The `p`-divisible part of `G` is the largest subgroup `D` with `p • D = D`: the greatest fixed
point `OrderHom.gfp` of the order homomorphism `H ↦ p • H`. Prove that it is the stable value of
the filtration: there is an ordinal `λ : Ordinal.{u}`, for `G : Type u`, with
`p^(λ+1) G = p^λ G`; for every such `λ` and every `α ≥ λ`, `p^α G = D`; and `D = ⨅ α, p^α G`
over `α : Ordinal.{u}` (kaplansky1954, §11, p. 26; fuchs2015, Ch. 10 §1, p. 299). Prove that the
least such `λ` has cardinality at most that of `G`: choosing `x_β` in `p^β G` outside
`p^(β+1) G` for each `β < λ` gives an injection of `λ` into `G`. *Needs:* §0.1; Mathlib
`OrderHom.gfp`, `OrdinalApprox.gfpApprox_ord_eq_gfp`, `OrdinalApprox.gfpApprox_anti_right`.

Define `IsPReduced G p`: the only subgroup `H` of `G` with `p • H = H` is the trivial one. Prove
that it is equivalent to `D = ⊥` and to `∃ α : Ordinal.{u}, p^α G = ⊥`.

- For a `p`-group `G`, a subgroup `H` satisfies `p • H = H` if and only if it is divisible, that
  is, `n • H = H` for every nonzero natural number `n`; so a `p`-group is `p`-reduced exactly when
  it has no nonzero divisible subgroup, and its `p`-divisible part is its largest divisible
  subgroup. Stated for nonzero integers `n`, the divisibility condition is the hypothesis of
  Mathlib's `AddCommGroup.divisibleByIntOfSMulTopEqTop`, applied to `H` as a group.
- Subgroups of a `p`-reduced group are `p`-reduced; `G × H` is `p`-reduced if and only if both
  factors are; a direct sum is `p`-reduced if and only if every summand is; the property is
  invariant under isomorphism.
- The quotient of `G` by its `p`-divisible part is `p`-reduced.

**Checks.**

- `ZMod (p ^ n)` is `p`-reduced. The Prüfer group `ℤ[1/p] / ℤ` satisfies `p • ⊤ = ⊤`, so it is
  its own `p`-divisible part and is not `p`-reduced.
- `ℤ` is `p`-reduced. For a prime `q ≠ p`, the group `ℤ[1/q]` is `p`-reduced although it is
  `q`-divisible: reducedness at `p` sees only `p`.
- The group of the last Check of §0.1 is `p`-reduced although `p^ω G ≠ 0`. A definition of
  reducedness as `p^ω G = 0` would reject it; that stronger condition says that `G` has no
  nonzero element of infinite height.

### 0.3 The length

The length of `G` at `p` is the least ordinal `λ : Ordinal.{u}` with `p^(λ+1) G = p^λ G`, which
exists by §0.2 (kaplansky1954, §11, p. 26; fuchs2015, Ch. 10 §1, p. 299). Prove that
`p^α G` is the `p`-divisible part if and only if the length is at most `α`; for a `p`-reduced
group, `p^α G = ⊥` if and only if the length is at most `α`. *Needs:* §0.2.

- The length has cardinality at most that of `G`. A finite group has finite length, and a
  countable group has countable length.
- The length is invariant under isomorphism; the length of `G × H` is the larger of the two
  lengths, and the length of a direct sum is the supremum of the lengths of the summands.

**Checks.**

- `ZMod (p ^ n)` has length `n`; `ℚ` has length `0`; `ℤ` has length `ω`.
- `⨁ n ≥ 1, ZMod (p ^ n)` has length `ω`, the supremum of the lengths `n`.
- The group of the last Check of §0.1 has length `ω + 1` (kaplansky1954, §11, p. 31, remark
  (b)).

### Examples

`ZMod (p ^ n)` (reduced, length `n`); `ℤ` (reduced at `p`, length `ω`, torsion-free); `ℚ` and the
Prüfer group (equal to their divisible parts, length `0`); `⨁ n ≥ 1, ZMod (p ^ n)` (reduced,
length `ω`, no element of infinite height); the Prüfer group of length `ω + 1` (reduced, with
`p^ω G` of order `p`).

### Dependencies

Mathlib only.

## Layer 1: heights

### 1.1 The height of an element

For `G : Type u` and `x : G`, the height of `x` at `p` is the element of `WithTop Ordinal.{u}`
equal to `α` when `x ∈ p^α G` and `x ∉ p^(α+1) G`, and to `⊤` when `x` lies in the `p`-divisible
part (kaplansky1954, §11, p. 28; fuchs2015, Ch. 10 §1, p. 300). It is well defined: for `x`
outside the `p`-divisible part, the least `β` with `x ∉ p^β G` is neither `0` nor a limit ordinal.
Prove the characterisation `(α : WithTop Ordinal) ≤ height x ↔ x ∈ p^α G` for every
`α : Ordinal.{u}`. *Needs:* §0.1, §0.2.

- The height of `x` is `⊤` if and only if `x` lies in the `p`-divisible part; the height of `0`
  is `⊤`; in a `p`-reduced group the height of `x` is `⊤` only for `x = 0`.
- An element outside the `p`-divisible part has height strictly less than the length.

**Checks.**

- In `ℤ`, the height of a nonzero `n` at `p` is the exponent of `p` in `n`, Mathlib's
  `padicValInt p n`.
- In `ZMod (p ^ n)`, the class of `p ^ k` has height `k` for `k < n`.
- In the Prüfer group of length `ω + 1`, the generator `x` has height `ω`: an infinite height
  that is not `⊤`. A height valued in `ℕ∞` could not tell `x` from `0`.

### 1.2 Height arithmetic

Prove the three rules of kaplansky1954, §11, p. 28: if the height of `x` is strictly less than
that of `y`, then `x + y` has the height of `x`; in general the height of `x + y` is at least the
smaller of the two heights; and if the height of `x` is not `⊤`, then `p • x` has strictly greater
height than `x`. Prove also that `-x` has the height of `x`, and that in a `p`-group `n • x` has
the height of `x` for every integer `n` prime to `p`. *Needs:* §1.1.

**Checks.**

- Equal heights can add to a larger one: in `ZMod (p ^ 2)` the classes of `1` and `p - 1` have
  height `0` and their sum has height `1`.
- Multiplication by `p` can raise the height by more than one: in the Prüfer group of length
  `ω + 1` the generator `y₁` satisfies `p • y₁ = x`, of height `ω`, while `y₁` has finite height.

### 1.3 Heights and homomorphisms

For groups `G` and `H` in one universe, a homomorphism `f : G →+ H` does not lower heights, and an
isomorphism preserves them. For a subgroup `A` of `G`, the height of `a ∈ A` computed in `A` is at
most its height computed in `G`, with equality when `A` is a direct summand of `G`.

Call a homomorphism `φ : S →+ T` between subgroups `S ≤ G` and `T ≤ H` height-preserving when
`φ s` has in `H` the height that `s` has in `G`, for every `s ∈ S`; heights are always computed
in the ambient groups (kaplansky1954, §11, p. 29, remark (c); fuchs2015, Ch. 11 §1, p. 345).
Prove that this is equivalent to `s ∈ p^α G ↔ φ s ∈ p^α H` for all `s ∈ S` and all
`α : Ordinal.{u}`, and that a height-preserving homomorphism out of a subgroup of a `p`-reduced
group is injective. *Needs:* §0.1, §1.1.

**Checks.**

- The injection `ZMod p → ZMod (p ^ 2)` sending `1` to `p` raises the height of `1` from `0` to
  `1`: injective homomorphisms need not preserve heights.
- The restriction of an isomorphism `G ≃+ H` to a subgroup is height-preserving onto its image.
- Height in a subgroup can be smaller: in `G = ZMod (p ^ 2)` the class of `p` has height `1`, and
  height `0` when computed in the subgroup it generates.

### Examples

Heights in `ℤ` (the `p`-adic valuation), in `ZMod (p ^ n)`, and in the Prüfer group of length
`ω + 1`, whose element `x` has height `ω`.

### Dependencies

Layer 0; Mathlib.

## Layer 2: the socle filtration and the Ulm invariants

### 2.1 The socle filtration

For each ordinal `α`, `(p^α G)[p] = p^α G ⊓ G[p]` is a subspace of the `ZMod p`-vector space
`G[p]` (kaplansky1954, §11, p. 27, where it is `P_α`). Prove that these subspaces form an
antitone family, that a homomorphism `G →+ H` maps `(p^α G)[p]` into `(p^α H)[p]`, and that for
products and direct sums the subspace is computed componentwise. *Needs:* §0.1; Mathlib
`AddSubgroup.torsionBy`, `AddSubgroup.torsionBy.nsmul_iff`, `AddSubgroup.torsionBy.zmodModule`,
`AddSubgroup.toZModSubmodule`.

- In a `p`-group, a subgroup `K` with `K[p] = ⊥` is trivial; hence `p^α G = ⊥` if and only if
  `(p^α G)[p] = ⊥`.

**Checks.**

- `G = ZMod (p ^ n)` with `n ≥ 1`: `(p^k G)[p]` is the subgroup of order `p` for `k < n` and is
  trivial for `k ≥ n`.

### 2.2 The Ulm invariants

Define `ulmInvariant G p α` as the dimension over `ZMod p` of the quotient of `(p^α G)[p]` by
`(p^(α+1) G)[p]` (kaplansky1954, §11, p. 27; fuchs2015, Ch. 11 §1, p. 344). *Needs:* §2.1; Mathlib
`Module.rank`, `Submodule.submoduleOf`.

- Invariance: for an isomorphism `e : G ≃+ H` between groups in universes `u` and `v`,
  `Cardinal.lift.{v} (ulmInvariant G p α) = Cardinal.lift.{u} (ulmInvariant H p α)`, by
  `LinearEquiv.lift_rank_eq`. The index universe does not matter:
  `ulmInvariant G p (Ordinal.lift α) = ulmInvariant G p α`.
- If `p^(α+1) G = p^α G` then the `α`-th invariant is `0`; in particular the invariants vanish
  from the length on.
- If a `p`-reduced group has length `α + 1`, its `α`-th invariant is the dimension of `p^α G`,
  which is killed by `p` and nonzero.
- Additivity: the invariant of `G × H` is the sum of the invariants, and the invariant of a direct
  sum `⨁ i, G i` is the `Cardinal.sum` of the invariants of the summands (kaplansky1954, §11,
  Exercise 31, p. 31).
- The invariants of a finite group are finite, and those of a countable group are at most `ℵ₀`.

**Checks.**

- `G = ZMod (p ^ n)` with `n ≥ 1`: the invariant at `n - 1` is `1` and every other invariant is
  `0` (kaplansky1954, §11, p. 27).
- At `p = 2`, the groups `ZMod 4 × ZMod 4` and `ZMod 2 × ZMod 8` both have `16` elements; their
  zeroth invariants are `0` and `1`.
- The cruder dimensions of `p^n G / p^(n+1) G` do not classify: they equal `ℵ₀` for every `n`
  both for `⨁ n ≥ 1, ZMod (p ^ n)` and for the sum of two copies of it, while the Ulm invariants
  are `1` and `2` (kaplansky1954, §11, p. 27).
- The Prüfer group of length `ω + 1` has invariant `1` at `0, 1, 2, …` and at `ω`, and `0` beyond
  (kaplansky1954, §11, p. 31, remark (b); fuchs2015, Ch. 11, Example 1.8, p. 347).

### 2.3 Direct sums of cyclic groups

Prove the cyclic case: for `n ≥ 1`, the Ulm invariant of `ZMod (p ^ n)` at `n - 1` is `1` and
every other invariant is `0`. Prove `ulmInvariant_directSum_zmod`: for a family of exponents
`n : ι → ℕ`, the `k`-th Ulm invariant of `⨁ i, ZMod (p ^ n i)`, for a natural number `k`, is the
cardinality of `{i // n i = k + 1}` (kaplansky1954, §11, p. 27). Prove that the invariants of
such a sum at infinite ordinals are `0`, because `p^ω` of the sum is trivial. *Needs:* §0.1,
§2.1, §2.2 (additivity).

- For a finite abelian `p`-group, Mathlib's `AddCommGroup.equiv_directSum_zmod_of_finite` gives a
  decomposition into cyclic groups of prime-power order, indexed by a type in `Type` with a prime
  for each summand; every summand of nonzero exponent has prime `p`, and after a `Cardinal.lift`
  the formula shows that the number of summands of each order is the same in every such
  decomposition.

**Checks.**

- `⨁ n ≥ 1, ZMod (p ^ n)` has `k`-th invariant `1` for every natural number `k`.
- Summands `ZMod (p ^ 0)` are trivial and contribute to no invariant.

### Examples

Cyclic groups; `ZMod 4 × ZMod 4` against `ZMod 2 × ZMod 8`; `⨁ n ≥ 1, ZMod (p ^ n)` and its
double; the Prüfer group of length `ω + 1`.

### Dependencies

Layer 0; Mathlib.

## Layer 3: proper elements and the Kaplansky–Mackey extension step

### 3.1 Proper elements

For a subgroup `S` of `G`, an element `x` is proper with respect to `S` when no element of the
coset `x + S` has greater height than `x` (kaplansky1954, §11, p. 28; fuchs2015, Ch. 11 §1,
p. 343, also requires `x ∉ S`; this roadmap follows Kaplansky). Prove: if `x` is proper with
respect to `S`, then for every `s ∈ S` the height of `x + s` is the smaller of the heights of `x`
and `s`; an element `x` of height `α ≠ ⊤` is proper
with respect to `S` if and only if `x ∉ p^(α+1) G ⊔ S`; and if `S` is finite, every coset of `S`
contains an element proper with respect to `S` (fuchs2015, Ch. 11 §1, p. 344). *Needs:* §1.1,
§1.2.

**Checks.**

- In `G = ZMod (p ^ 2)` with `S = G[p]`, every element of the coset `1 + S` is a unit of height
  `0`, so `1` is proper.
- In `G = ZMod p × ZMod (p ^ 2)` with `S` generated by `(1, 0)`, the element `(1, p)` has height
  `0` and is not proper: `(0, p)` lies in its coset and has height `1`, and `(0, p)` is proper.
- An element of `S` is proper with respect to `S` only if its height is `⊤`, since its coset
  contains `0`.

### 3.2 Relative invariants and Kaplansky's lemma

For a subgroup `S` of `G` and an ordinal `α`, put `S_α = S ⊓ p^α G` and let `S_α*` be the
subgroup of those `x ∈ S_α` with `p • x ∈ p^(α+2) G`. For `x ∈ S_α*` choose `y ∈ p^(α+1) G` with
`p • y = p • x`; then `x - y` lies in `(p^α G)[p]`, and its class modulo `(p^(α+1) G)[p]` does not
depend on `y`. Prove that this defines an injective `ZMod p`-linear map from `S_α* / S_(α+1)` to
`(p^α G)[p] / (p^(α+1) G)[p]`, which we call the Kaplansky map of `S` at `α` (kaplansky1954, §11,
p. 28). Prove that its range is the image of `(p^(α+1) G ⊔ S) ⊓ (p^α G)[p]`, and Kaplansky's
lemma: an element `v` of `(p^α G)[p]` has class outside the range if and only if `v` has height
`α` and is proper with respect to `S` (kaplansky1954, §11, Lemma 13 and its proof, pp. 28–29;
fuchs2015, Ch. 11 §1, p. 344). *Needs:* §2.1, §3.1.

The relative Ulm invariant of `G` at `α` with respect to `S` is the dimension of the cokernel of
the Kaplansky map, equivalently of the quotient of `(p^α G)[p]` by
`(p^(α+1) G ⊔ S) ⊓ (p^α G)[p]`; it is what fuchs2015, Ch. 11 §1, p. 344, calls the Hill invariant.

- For `S = ⊥` the relative invariant is the Ulm invariant.
- The dimension of `S_α* / S_(α+1)` plus the relative invariant is the Ulm invariant at `α`.
- A height-preserving isomorphism `e : S ≃+ T` between subgroups of `G` and `H` carries `S_α`
  onto `T_α` and `S_α*` onto `T_α*`, and induces an isomorphism of `S_α* / S_(α+1)` with
  `T_α* / T_(α+1)` (kaplansky1954, §11, p. 30).
- Transfer: if moreover `S` is finite and `G` and `H` have the same Ulm invariant at `α`, then
  the relative invariant of `G` with respect to `S` equals that of `H` with respect to `T` at
  `α` (kaplansky1954, §11, p. 30, Case II); so `G` has an element of order `p` and height `α`
  proper with respect to `S` if and only if `H` has one proper with respect to `T` (fuchs2015,
  Ch. 11, Lemma 1.4, p. 345, which assumes the equality of relative invariants).

**Checks.**

- `G = ZMod p × ZMod p`, `S` generated by `(1, 0)`, `α = 0`: `S_0* = S` and `S_1 = ⊥`, the
  Kaplansky map is the inclusion of a line in the plane `G[p]`, the relative invariant is `1`, and
  `(0, 1)` is an element of order `p` and height `0` proper with respect to `S`.
- `G = ZMod (p ^ 2)`, `S = G[p]`, `α = 0`: here `S_0 = S_0* = S_1 = S`, so the source of the
  Kaplansky map is trivial; the Ulm invariant at `0` is `0`, and so is the relative invariant.

### 3.3 The extension step

Prove `exists_extension_of_nsmul_mem`: let `G` and `H` be `p`-reduced `p`-groups with the same
Ulm invariants, `S ≤ G` and `T ≤ H` finite subgroups, `e : S ≃+ T` a height-preserving
isomorphism, and `x : G` with `p • x ∈ S`. Then there are finite subgroups `S' ≥ S` and `T' ≥ T`
with `x ∈ S'` and a height-preserving isomorphism `S' ≃+ T'` extending `e` (kaplansky1954, §11,
p. 30; cf. fuchs2015, Ch. 11, Lemma 1.5, pp. 345–346, which assumes neither finiteness nor equal
Ulm invariants but monomorphisms between relative invariants). Countability is not assumed.

A route: if `x ∈ S` there is nothing to prove. Otherwise, by §3.1, replace `x` by an element of
`x + S` that is proper with respect to `S`, of height `α` say, and among those one with `p • x`
of greatest height. Put `z = e (p • x)`. It suffices to find
`w ∈ H` of height `α`, proper with respect to `T`, with `p • w = z`. If `z` has height `α + 1`,
any `w ∈ p^α H` with `p • w = z` works. Otherwise `p • x = p • v` with `v ∈ p^(α+1) G`, the
element `x - v` has order `p` and height `α` and is proper with respect to `S`, the transfer of
§3.2 gives such an element `w₁` in `H` with respect to `T`, and `w = w₁ + w₂` works for any
`w₂ ∈ p^(α+1) H` with `p • w₂ = z`. The new subgroups are `S ⊔ zmultiples x` and
`T ⊔ zmultiples w`, finite with `p` times as many elements by Tau Ceti's
`TauCeti.natCard_sup_zmultiples_of_nsmul_mem`. *Needs:* §1.2, §1.3, §3.1, §3.2.

- Corollary: the same conclusion holds for every `x : G`, with no condition on `p • x`, by
  applying the step to `p ^ k • x` for decreasing `k`.

**Checks.**

- Equal invariants are needed: for `G = ZMod p × ZMod p`, `H = ZMod p`, `S` generated by `(1, 0)`
  and `T = H`, the isomorphism `S ≃+ T` is height-preserving and `x = (0, 1)` satisfies
  `p • x ∈ S`, but there is no room for `x` in `H`; the zeroth invariants are `2` and `1`.

### Examples

The plane `ZMod p × ZMod p` with a line `S`; `ZMod p × ZMod (p ^ 2)` with the subgroup generated
by `(1, 0)`.

### Dependencies

Layers 0, 1 and 2; Mathlib; Tau Ceti `TauCeti/GroupTheory/PGroup/Additive.lean`.

## Layer 4: Ulm's theorem

### 4.1 Ulm's theorem

Prove `nonempty_addEquiv_iff_ulmInvariant_eq`: for countable `p`-reduced `p`-groups `G` and `H`,
possibly in different universes, `G` and `H` are isomorphic if and only if
`Cardinal.lift (ulmInvariant G p α) = Cardinal.lift (ulmInvariant H p α)` for every ordinal `α`
of a fixed, arbitrary universe (kaplansky1954, §11, Theorem 14, p. 27, proof pp. 29–30;
fuchs2015, Ch. 11, Theorem 1.6, pp. 346–347; ulm1933).

A route: the forward direction is the invariance of §2.2. For the converse, first reduce to one
universe and to ordinals in that universe by §2.2 and `ULift`; a countable group has countable
length (§0.3), so countable ordinals carry all the information. Then enumerate `G` and `H` and
build an increasing chain of height-preserving isomorphisms between finite subgroups, starting
from the trivial one and applying the corollary of §3.3 alternately to the next element of `G`
and, with the roles exchanged, to the next element of `H`; the union is an isomorphism.
*Needs:* §0.3, §2.2, §3.3.

**Checks.**

- Finite groups: by §2.3, two finite abelian `p`-groups have the same invariants exactly when they
  have the same number of cyclic summands of each order, so the theorem contains the uniqueness
  half of their classification. At `p = 2`, `ZMod 4 × ZMod 4` and `ZMod 2 × ZMod 8` are not
  isomorphic.
- Reducedness is needed: the Prüfer group `ℤ[1/p] / ℤ` and the sum of two copies of it are
  countable `p`-groups whose Ulm invariants all vanish, as do those of the trivial group, and no
  two of the three are isomorphic (their socles have dimensions `1`, `2` and `0`).
- The `p`-group hypothesis is needed: `ℤ` is countable and `p`-reduced with every Ulm invariant
  `0`, like the trivial group.
- Countability is needed: the torsion subgroup of `∏ n ≥ 1, ZMod (p ^ n)` is a `p`-reduced
  `p`-group with invariant `1` at every natural number and `0` from `ω` on, like
  `⨁ n ≥ 1, ZMod (p ^ n)`, but it is not a direct sum of cyclic groups (kaplansky1954, §11,
  Exercise 33 (b), p. 32, which also shows how to make the cardinalities equal).

### 4.2 The extension form

Prove `exists_addEquiv_extending`: for countable `p`-reduced `p`-groups `G` and `H` in one
universe with the same Ulm invariants, every height-preserving isomorphism `e : S ≃+ T` between
finite subgroups `S ≤ G` and `T ≤ H` extends to an isomorphism `G ≃+ H`. It is the argument of
§4.1 started from `e` in place of the trivial isomorphism (kaplansky1954, §11, pp. 29–30, and
remark (c), p. 31, pointing to Exercise 38, p. 32, the case `G = H`). *Needs:* §3.3.

- Consequence: in a countable `p`-reduced `p`-group `G`, two elements `x` and `y` with
  `p ^ k • x` and `p ^ k • y` of equal height for every `k` are mapped one to the other by an
  automorphism of `G`. The heights of the elements of the subgroup generated by `x` are those of
  the `p ^ k • x`, by §1.2.

**Checks.**

- In `G = ZMod p × ZMod (p ^ 2)`, the elements `(1, 0)` and `(1, p)` have order `p` and height
  `0`, and the automorphism `(a, b) ↦ (a, b + p a)` maps the first to the second.
- In the same group `(1, 0)` and `(0, p)` have heights `0` and `1`; no automorphism maps one to
  the other.

### 4.3 Cancellation of squares

Prove `nonempty_addEquiv_of_prod_self`: a countable `p`-reduced `p`-group `G` and an abelian
group `H` with `G × G ≃+ H × H` are isomorphic (kaplansky1954, §11, Exercise 32 (b), p. 31, for
Problem II of §6, p. 13). The group `H` is countable, a `p`-group and `p`-reduced, since it
embeds in `H × H ≃+ G × G`. By additivity (§2.2) the invariants of `G × G` are those of `G`
doubled; two cardinals with equal doubles are equal; conclude by §4.1. *Needs:* §0.2 (products
and subgroups), §2.2, §4.1. Reducedness is a choice of scope: the statement holds for every
countable `p`-group (fuchs2015, Ch. 11 §1, Exercise 7 (a), p. 351), which also needs the
structure of divisible `p`-groups.

### Examples

`ZMod 4 × ZMod 4` against `ZMod 2 × ZMod 8`; the automorphisms of `ZMod p × ZMod (p ^ 2)`; the
Prüfer group of length `ω + 1`, which by §4.1 is the only countable `p`-reduced `p`-group with
invariant `1` at each of `0, 1, 2, …, ω` and `0` beyond (fuchs2015, Ch. 11, Example 1.8, p. 347).

### Dependencies

Layers 0 to 3; Mathlib.

## Downstream consumers

CountableStructureSpacesPartII, under its downstream consumers and its scope, leaves to a roadmap
on the Borel completeness of algebraic classes the theorem that countable torsion abelian groups
are not Borel complete, and records that this needs Ulm's theorem and a rank on the reduced
abelian `p`-groups. §4.1 is that theorem, and §0.3 supplies the length as an ordinal invariant of
a `p`-reduced group, countable when the group is. For a `p`-reduced `p`-group the Ulm length in
the sense of Fuchs is the least `σ` with `p^(ω·σ) G = 0`, so a family of such groups has bounded
Ulm length exactly when it has bounded length. The extension form §4.2 is what a back-and-forth
argument needs: partial isomorphisms between finite subgroups, extended one element at a time.

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

Ulm's theorem says when two countable reduced `p`-groups are isomorphic; it does not say which
functions occur as Ulm invariants. That is Zippin's theorem (fuchs2015, Ch. 11, Theorem 1.9,
p. 347), whose proof constructs groups of every countable length. Together with the splitting of
an abelian group into its divisible part and a reduced complement (KTheoryFiniteLocalFields
§0.0), the structure of divisible `p`-groups, and primary decomposition, it classifies all
countable torsion abelian groups. Kaplansky's other two test problems (kaplansky1954, §6,
Problems I and III, with Exercise 32 (b)) follow for countable `p`-reduced `p`-groups from §2.2
and §4.1 as §4.3 does. Past
countable groups lie Hill's totally projective groups and the theory of nice subgroups
(fuchs2015, Ch. 11 §2 onwards). A roadmap for this material would consume Layers 0 to 4 as they
stand.

## Scope and ownership

- **Owned here.** The filtration `p^α G` with its functoriality, the `p`-divisible part,
  `p`-reducedness and the length (Layer 0); heights, their arithmetic and height-preserving maps
  (Layer 1); the socle filtration, the Ulm invariants and their values on direct sums of cyclic
  groups (Layer 2); proper elements, the Kaplansky map, relative invariants and the extension
  step (Layer 3); Ulm's theorem, its extension form and the cancellation of squares (Layer 4).
- **Supplied by Mathlib and Tau Ceti at the pin.** The pointwise action on additive subgroups,
  the socle `G[p]` and its `ZMod p`-module structure, `IsAddPGroup`, ordinal recursion, the
  fixed-point approximants, dimension, direct sums, and the decomposition of finite abelian
  groups (Mathlib); the order of a subgroup with one element adjoined (Tau Ceti). Their exact
  names are in *Exact supplier contracts*. None of them is restated.
- **Left to ArithmeticStatisticsPartVII.** The decomposition of a group of bounded exponent into
  cyclic groups (its bounded-exponent splitting). This roadmap decomposes nothing: §2.3 computes
  the invariants of a group already given as a direct sum of cyclic groups.
- **Left to SelmerIwasawaCohomology.** The structure of a `p`-primary group with finite socle as
  a divisible group of finite rank plus a finite group (its §2.12a). The `p`-divisible part of
  §0.2 is defined here for every abelian group and no structure theorem for it is proved.
- **Left to FiniteGroupInvariants.** The invariant factors of a finite abelian group (its §0.9).
- **Left to KTheoryFiniteLocalFields.** The maximal divisible subgroup of an abelian group and the
  splitting off of a reduced complement (its §0.0). The `p`-divisible part of §0.2 is defined here
  independently; for a `p`-group it is that maximal divisible subgroup.
- **Not in scope.** The material listed under *Beyond this roadmap*.

## Exact supplier contracts

### From Mathlib

- `Mathlib/Algebra/GroupWithZero/Subgroup.lean`: `AddSubgroup.pointwiseMulAction`,
  `AddSubgroup.pointwise_smul_def`, `AddSubgroup.mem_smul_pointwise_iff_exists`: `a • S` is the
  image of `S` under the action of `a`, and `m ∈ a • S ↔ ∃ s ∈ S, a • s = m`.
- `Mathlib/Algebra/Module/Torsion/Basic.lean`: `AddSubgroup.torsionBy`,
  `AddSubgroup.torsionBy.nsmul_iff`, `AddSubgroup.torsionBy.zmodModule`: `x ∈ A[n] ↔ n • x = 0`,
  and `A[n]` is a module over `ZMod n`.
- `Mathlib/Algebra/Module/ZMod.lean`: `AddSubgroup.toZModSubmodule`: the order isomorphism
  between the additive subgroups and the submodules of a `ZMod n`-module.
- `Mathlib/GroupTheory/PGroup.lean`: `IsAddPGroup`: every element is killed by a power of `p`.
- `Mathlib/SetTheory/Ordinal/Arithmetic.lean`: `Ordinal.limitRecOn`, `Ordinal.limitRecOn_zero`,
  `Ordinal.limitRecOn_add_one`, `Ordinal.limitRecOn_limit`: recursion on ordinals by zero,
  successor and limit, with its three computation rules.
- `Mathlib/SetTheory/Ordinal/FixedPointApproximants.lean`: `OrdinalApprox.gfpApprox`,
  `OrdinalApprox.gfpApprox_zero`, `OrdinalApprox.gfpApprox_add_one`,
  `OrdinalApprox.gfpApprox_of_isSuccLimit`, `OrdinalApprox.gfpApprox_anti_right`,
  `OrdinalApprox.gfpApprox_ord_eq_gfp`: the descending approximants of the greatest fixed point
  of an order homomorphism of a complete lattice, indexed by the ordinals of the universe of the
  lattice, and their stabilisation at the greatest fixed point.
- `Mathlib/Order/FixedPoints.lean`: `OrderHom.gfp`: the greatest fixed point.
- `Mathlib/LinearAlgebra/Dimension/Basic.lean`: `Module.rank`, `LinearEquiv.lift_rank_eq`: the
  dimension as a cardinal, invariant under linear equivalence across universes.
- `Mathlib/Algebra/Module/Submodule/Map.lean`: `Submodule.submoduleOf`: a submodule viewed inside
  a larger one.
- `Mathlib/GroupTheory/FiniteAbelian/Basic.lean`: `AddCommGroup.equiv_directSum_zmod_of_finite`:
  a finite abelian group is a direct sum of cyclic groups of prime-power order.
- `Mathlib/GroupTheory/Divisible.lean`: `AddCommGroup.divisibleByIntOfSMulTopEqTop`: a group with
  `n • ⊤ = ⊤` for every nonzero integer `n` is divisible.
- `Mathlib/SetTheory/Cardinal/Defs.lean`: `Cardinal.lift`, `Cardinal.sum`: moving a cardinal to a
  higher universe, and the sum of a family of cardinals.
- `Mathlib/SetTheory/Ordinal/Basic.lean`: `Ordinal.lift`: moving an ordinal to a higher universe.
- `Mathlib/Algebra/Group/Subgroup/ZPowers/Basic.lean`: `AddSubgroup.zmultiples`: the subgroup
  generated by one element.
- `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`: `padicValInt`: the exponent of `p` in an
  integer.
- Lean core: `ULift`: a type moved to a higher universe.

### From Tau Ceti

- `TauCeti/GroupTheory/PGroup/Additive.lean`: `TauCeti.natCard_sup_zmultiples_of_nsmul_mem`,
  `TauCeti.subquotientEquivZModOfEqSupZmultiples`: for a prime `p`, a subgroup `N` and `x ∉ N`
  with `p • x ∈ N`, the subgroup `N ⊔ zmultiples x` has `p` times as many elements as `N`, and
  its quotient by `N` is `ZMod p`. Used in §3.3.

## References

- `kaplansky1954`: I. Kaplansky, *Infinite Abelian Groups*, University of Michigan Press, 1954.
  §6, p. 13 (Problem II); §11, pp. 26–32: the filtration and the length (p. 26), the Ulm
  invariants and Theorem 14 (p. 27), heights, proper elements and Lemma 13 (p. 28), the proof of
  Theorem 14 (pp. 29–30), the example of length `ω + 1` and Exercise 31 (p. 31), Exercises 32,
  33 and 38 (pp. 31–32).
- `fuchs2015`: L. Fuchs, *Abelian Groups*, Springer Monographs in Mathematics, Springer, 2015.
  Ch. 1 §1, p. 4 (Ulm subgroups); Ch. 10 §1, pp. 299–300 (the filtration, the length, heights);
  Ch. 11 §1, pp. 343–351 (proper elements, relative invariants, Lemma 1.4, Lemma 1.5,
  Theorem 1.6, Example 1.8, Theorem 1.9, Exercise 7).
- `ulm1933`: H. Ulm, *Zur Theorie der abzählbar-unendlichen Abelschen Gruppen*, Math. Ann. 107
  (1933), 774–803.
- L. Zippin, *Countable torsion groups*, Ann. of Math. 36 (1935), 86–99; I. Kaplansky and
  G. W. Mackey, *A generalization of Ulm's theorem*, Summa Brasil. Math. 2 (1951), 195–202. The
  original sources of the existence theorem and of the extension step; cited for attribution.
- Prior formalisation, consulted as a proof source and not as a specification: E. Roth,
  *UlmsTheorem*, <https://github.com/elanroth/UlmsTheorem> (Apache-2.0), also archived in Lean
  Pool. Its filtration, height, invariants, Kaplansky map, extension lemma and main theorem
  correspond to §0.1, §1.1, §2.2, §3.2, §3.3 and §4.1; its notion of a reduced `p`-group is the
  conjunction of `IsAddPGroup` and `IsPReduced`.
