module

import Mathlib

/-!
# Countable abelian p-groups and Ulm's theorem: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document is `README.md`.
This file suggests Lean forms for its headline theorems (§2.3, §4.1, §4.2, §4.3) and the
extension step (§3.3), each with `sorry`, together with the three definitions they need, each
with a real body: the transfinite filtration `p^α G`, `p`-reducedness, and the Ulm invariants.
-/

noncomputable section

open Pointwise

namespace TauCetiRoadmap.CountableAbelianPGroups

universe u v w

/-! ## Layer 0: the transfinite filtration and the divisible part -/

/-- 0.1 The transfinite filtration `p^α G` of an abelian group: `p^0 G = G`,
`p^(α+1) G = p • p^α G`, and `p^λ G = ⨅ β < λ, p^β G` at limit ordinals `λ`. The index may
live in any universe. -/
def pPow (G : Type u) [AddCommGroup G] (p : ℕ) (α : Ordinal.{w}) : AddSubgroup G :=
  α.limitRecOn ⊤ (fun _ H => p • H) (fun o _ IH => ⨅ (β : Ordinal.{w}) (h : β < o), IH β h)

/-- 0.2 An abelian group is `p`-reduced when its only subgroup `H` with `p • H = H` is the
trivial one. For a prime `p` and a `p`-group this says that there is no nonzero divisible
subgroup. -/
def IsPReduced (G : Type u) [AddCommGroup G] (p : ℕ) : Prop :=
  ∀ H : AddSubgroup G, p • H = H → H = ⊥

/-! ## Layer 2: the socle filtration and the Ulm invariants -/

/-- 2.2 The `α`-th Ulm invariant of `G` at `p`: the dimension over `ZMod p` of
`(p^α G)[p] ⧸ (p^(α+1) G)[p]`, formed inside the `ZMod p`-module `G[p]`. -/
def ulmInvariant (G : Type u) [AddCommGroup G] (p : ℕ) (α : Ordinal.{w}) : Cardinal.{u} :=
  letI : Module (ZMod p) (AddSubgroup.torsionBy G p) := AddSubgroup.torsionBy.zmodModule
  let P (β : Ordinal.{w}) :=
    AddSubgroup.toZModSubmodule p ((pPow G p β).addSubgroupOf (AddSubgroup.torsionBy G p))
  Module.rank (ZMod p) (P α ⧸ (P (α + 1)).submoduleOf (P α))

/-- 2.3 In a direct sum of cyclic groups `⨁ i, ZMod (p ^ n i)` the `k`-th Ulm invariant, for
a natural number `k`, is the number of summands of order `p ^ (k + 1)` (Kaplansky 1954, §11,
p. 27). -/
theorem ulmInvariant_directSum_zmod {ι : Type u} (p : ℕ) [Fact p.Prime] (n : ι → ℕ) (k : ℕ) :
    ulmInvariant (DirectSum ι fun i => ZMod (p ^ n i)) p (k : Ordinal.{w}) =
      Cardinal.mk {i : ι // n i = k + 1} := by
  sorry

/-! ## Layer 3: proper elements and the Kaplansky–Mackey extension step -/

/-- 3.3 The Kaplansky–Mackey extension step. Let `G` and `H` be reduced `p`-groups with the
same Ulm invariants, `e : S ≃+ T` a height-preserving isomorphism between finite subgroups,
and `x : G` with `p • x ∈ S`. Then `e` extends to a height-preserving isomorphism between
finite subgroups `S' ≥ S` and `T' ≥ T` with `x ∈ S'` (Kaplansky 1954, §11, p. 30; cf. Fuchs
2015, Ch. 11, Lemma 1.5). Countability is not assumed. -/
theorem exists_extension_of_nsmul_mem {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) [Fact p.Prime] (hG : IsAddPGroup p G) (hH : IsAddPGroup p H)
    (hGr : IsPReduced G p) (hHr : IsPReduced H p)
    (hinv : ∀ α : Ordinal.{u}, ulmInvariant G p α = ulmInvariant H p α)
    (S : AddSubgroup G) (T : AddSubgroup H) [Finite S] (e : S ≃+ T)
    (he : ∀ (y : S) (α : Ordinal.{u}), (y : G) ∈ pPow G p α ↔ (e y : H) ∈ pPow H p α)
    (x : G) (hx : p • x ∈ S) :
    ∃ (S' : AddSubgroup G) (T' : AddSubgroup H) (e' : S' ≃+ T') (hS : S ≤ S'),
      x ∈ S' ∧ Finite S' ∧
      (∀ (y : S') (α : Ordinal.{u}), (y : G) ∈ pPow G p α ↔ (e' y : H) ∈ pPow H p α) ∧
      ∀ y : S, (e' (AddSubgroup.inclusion hS y) : H) = e y := by
  sorry

/-! ## Layer 4: Ulm's theorem -/

/-- 4.1 **Ulm's theorem.** Two countable reduced abelian `p`-groups are isomorphic if and only
if their Ulm invariants agree at every ordinal (Ulm 1933; Kaplansky 1954, Theorem 14; Fuchs
2015, Ch. 11, Theorem 1.6). The groups may live in different universes, and the index universe is
arbitrary. -/
theorem nonempty_addEquiv_iff_ulmInvariant_eq {G : Type u} {H : Type v} [AddCommGroup G]
    [AddCommGroup H] [Countable G] [Countable H] (p : ℕ) [Fact p.Prime]
    (hG : IsAddPGroup p G) (hH : IsAddPGroup p H) (hGr : IsPReduced G p)
    (hHr : IsPReduced H p) :
    Nonempty (G ≃+ H) ↔ ∀ α : Ordinal.{w},
      Cardinal.lift.{v} (ulmInvariant G p α) = Cardinal.lift.{u} (ulmInvariant H p α) := by
  sorry

/-- 4.2 The extension form of Ulm's theorem. For countable reduced `p`-groups with the same
Ulm invariants, every height-preserving isomorphism between finite subgroups extends to an
isomorphism of the groups (the proof of Kaplansky 1954, Theorem 14, pp. 29–30, and Exercise 38). -/
theorem exists_addEquiv_extending {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    [Countable G] [Countable H] (p : ℕ) [Fact p.Prime] (hG : IsAddPGroup p G)
    (hH : IsAddPGroup p H) (hGr : IsPReduced G p) (hHr : IsPReduced H p)
    (hinv : ∀ α : Ordinal.{u}, ulmInvariant G p α = ulmInvariant H p α)
    (S : AddSubgroup G) (T : AddSubgroup H) [Finite S] (e : S ≃+ T)
    (he : ∀ (y : S) (α : Ordinal.{u}), (y : G) ∈ pPow G p α ↔ (e y : H) ∈ pPow H p α) :
    ∃ f : G ≃+ H, ∀ y : S, f y = e y := by
  sorry

/-- 4.3 Cancellation of squares: a countable reduced `p`-group `G` and an abelian group `H` with
`G × G ≃+ H × H` are isomorphic (Kaplansky 1954, §11, Exercise 32 (b), for Problem II of §6).
The hypotheses on `H` follow from those on `G`. -/
theorem nonempty_addEquiv_of_prod_self {G : Type u} {H : Type v} [AddCommGroup G]
    [AddCommGroup H] [Countable G] (p : ℕ) [Fact p.Prime] (hG : IsAddPGroup p G)
    (hGr : IsPReduced G p) (e : (G × G) ≃+ (H × H)) : Nonempty (G ≃+ H) := by
  sorry

end TauCetiRoadmap.CountableAbelianPGroups
