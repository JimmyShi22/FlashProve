-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Toy.lean: A TEST: THE PREMISES OF prove_law AND OF yes_bound ARE MET TOGETHER, at
the small batch protocol with tests of OnBytes/Prover/ToyWork.lean, with B := ∅; and what the two
laws then say there.

Why. A law whose premises nobody can meet says nothing. ToyWork's protocol has a test of one bit in
a local round, in the joining round and in a later shared round. Its wire's laws and the other
premises of (T1) are proved in OnBytes/Prover/ToyWorkAll.lean; here the four that the laws of
Johnson/Prover/Law/ add.

Main names.
  toy_puts   PutsApart at all caps: a nonce is its number.
  keptT, toy_fresh, toy_fresh_empty   a table that holds all of g₀'s answers at the trees' two
    oracles and nothing else; it is fresh for the chain; so is the empty table.
  toy_ext   the outer tree that is made under g₀ is kept rightly under every completion of keptT g₀.
  toy_acc   AccLaw at B := ∅: "accepts" (OnBytes/Prover/ToyWorkAll.lean).
  toy_capFail   capFail there: (1 - 1/2)^(cap i + 1), summed over i = 0, 1, 2, as written.
  toy_law   prove_law there, from the empty table: the search runs out with at most that
    probability.
  toy_yes   yes_bound there, from keptT g₀: the prover hands over nothing, or a string to which
    verifyOneProtocol says no, with at most that probability.

Limits. A toy: digests of four bits, tests of one bit, one slot. B := ∅ is possible because the
toy's interactive verifier accepts the honest strategy's run at all verifier messages whose tests
are passed: whether a protocol of the release is like that is not said here. It ties nothing to a
file of the release.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.YesProved
import OnBytes.Prover.ToyWorkAll

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover.ToyWork
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

theorem gr_apart (cap : ℕ) : GrApart gr cap := fun _ _ _ _ _ e => e

/-- PutsApart at all caps. -/
theorem toy_puts (cap : ℕ → ℕ) : PutsApart sh ann wq.sh cap 0 :=
  ⟨fun g hg => (by cases hg; exact gr_apart _), fun g hg => (by cases hg; exact gr_apart _),
    fun g hg => (by cases hg; exact gr_apart _), fun g hg => (by cases hg), trivial⟩

/-- All of g₀'s answers at the trees' two oracles, and nothing else. -/
def keptT (g₀ : Fam (typedOracleFamily 4 1 L)) : Table (typedOracleFamily 4 1 L) := fun o =>
  match o with
  | .leaf => fun q => some (g₀ .leaf q)
  | .node => fun q => some (g₀ .node q)
  | _ => fun _ => none

theorem toy_fresh (g₀ : Fam (typedOracleFamily 4 1 L)) :
    FreshFrom (L := L) Tag.onl sh ann (fun z => z) 0 (keptT g₀) := fun _ _ => rfl

theorem toy_fresh_empty :
    FreshFrom (L := L) Tag.onl sh ann (fun z => z) 0 (Table.empty (typedOracleFamily 4 1 L)) := fun _ _ => rfl

/-- The outer tree under a completion of keptT g₀ is the outer tree under g₀. -/
theorem xtG_kept (g₀ f : Fam (typedOracleFamily 4 1 L)) : xtG ((keptT g₀).over f) = xtG g₀ := rfl

/-- The outer tree that is made under g₀ is kept rightly under every completion of keptT g₀. -/
theorem toy_ext (g₀ : Fam (typedOracleFamily 4 1 L)) :
    ∀ f, ExtAt ((keptT g₀).over f) 2 wq.ext embE (cmsG g₀) y (xtG g₀) := fun f =>
  extAt ((keptT g₀).over f)

/-- AccLaw at B := ∅. -/
theorem toy_acc : AccLaw Q wq true y (σ true) ∅ := fun τ hp h _ => accepts τ hp h

theorem toy_capFail (cap : ℕ → ℕ) : capFail sh ann wq.sh cap 0 =
    (1 - ((2 : ℝ≥0∞) ^ 1)⁻¹) ^ (cap 0 + 1) + ((1 - ((2 : ℝ≥0∞) ^ 1)⁻¹) ^ (cap 1 + 1) +
      ((1 - ((2 : ℝ≥0∞) ^ 1)⁻¹) ^ (cap 2 + 1) + (0 + 0))) := rfl

theorem pr_empty :
    pr (unif (Rho sh)) {ρ | RoundsQueryLayout.zero sh ann wq.sh ρ ∈ (∅ : Set (Rho sh))} = 0 := by
  have : {ρ : Rho sh | RoundsQueryLayout.zero sh ann wq.sh ρ ∈ (∅ : Set (Rho sh))} = ∅ := rfl
  rw [this]
  exact (unif (Rho sh)).toOuterMeasure.empty

/-- **prove_law at the toy, from the empty table**: whatever roots and outer trees the prover is
handed. -/
theorem toy_law (cms : List (Dig 4)) (xt : ℕ → TreeK 4 L) (cap : ℕ → ℕ) :
    PrFrom (Table.empty (typedOracleFamily 4 1 L))
        (proveX (L := L) Tag.onl Q wq embS (fun z => z) some cms true y xt (σ true) co cap)
        {r | (∃ j, r = .ranOut j) ∨ ∃ π τ, r = .ok (π, τ) ∧ τ.rho ∈ (∅ : Set (Rho sh))} ≤
      capFail sh ann wq.sh cap 0 := by
  have h := prove_law (L := L) Tag.onl Q wq embS (fun z => z) some cms true y xt (σ true) co cap
    (Table.empty (typedOracleFamily 4 1 L)) toy_fresh_empty wq_okg fmt (toy_puts cap) (fun _ _ e => e) ∅
  rwa [pr_empty, add_zero] at h

/-- **yes_bound at the toy, from the table that holds the outer tree's answers.** -/
theorem toy_yes (g₀ : Fam (typedOracleFamily 4 1 L)) (cap : ℕ → ℕ) :
    ∫⁻ f, PrCoins ((keptT g₀).over f)
        (proveX (L := L) Tag.onl Q wq embS (fun z => z) some (cmsG g₀) true y (xtG g₀) (σ true) co
          cap)
        {r | ∀ π τ, r = .ok (π, τ) →
          (verifyOneProtocol (L := L) 2 3 Tag.onl Q wq embS (fun z => z) some embE 1 (cmsG g₀) true π).det
            ((keptT g₀).over f) ≠ true} ∂(U (typedOracleFamily 4 1 L)) ≤
      capFail sh ann wq.sh cap 0 := by
  have h := yes_bound (L := L) 2 3 Tag.onl Q wq embS (fun z => z) some embE 1 (cmsG g₀) true y
    (xtG g₀) (σ true) co cap (keptT g₀) (toy_fresh g₀) wq_okg fewJ few0 isLocal coherent fmt
    (by decide) fit (toy_puts cap) (fun _ _ e => e) (toy_ext g₀) ∅ toy_acc
  rwa [pr_empty, add_zero] at h

end OnBytes.Prover.ToyWork

#print axioms OnBytes.Prover.ToyWork.toy_puts
#print axioms OnBytes.Prover.ToyWork.toy_fresh
#print axioms OnBytes.Prover.ToyWork.toy_ext
#print axioms OnBytes.Prover.ToyWork.toy_acc
#print axioms OnBytes.Prover.ToyWork.toy_capFail
#print axioms OnBytes.Prover.ToyWork.toy_law
#print axioms OnBytes.Prover.ToyWork.toy_yes
