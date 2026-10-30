-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Carry.lean: steps between commit-and-prove arguments under which completeness, index binding and
index privacy (ZKCP/Gen.lean) carry over with stated added errors, and their composition. Generic in
the schemes.

A scheme that can be implemented is reached from a scheme that is easy to analyse by several
changes, each with its own theorem: the committer's coins come from a seed, the prover does less
work for an empty slot, and so on. This file fixes one form for such theorems, so that function
application combines them.

  `Carry R B A A' a z` Whatever extractor E, simulator Sim and bounds (α, ε, ζ) the scheme A has for
                       the relation R (`Gen.RelPair`) and batches of at most B, the scheme A' has
                       the same E and Sim with (α + a, ε, ζ + z). A and A' are over the same oracles
                       and have the same types of verification keys and proofs; their proving keys
                       may have different types.

`IsZKCPArgWith.overOne`, the step from a family of typed oracles to one hash function for a query
encoding (`OracleCoding`) and an extractor with `LocalTo` (Rom/Family.lean), is no `Carry`: oracles,
extractor and simulator change; the bounds do not.

Rom/SpecCarryP.lean defines the scheme with another prover (`withP`). ProverClose and
Spec.carry_withP (a prover replaced by one that cannot be told from it, as a `Carry`) are not in
this library.

Limits: a `Carry` is an implication. It says nothing about A' unless something is known about A. It
is about completeness, index binding and index privacy as ZKCP/Gen.lean defines them and about
nothing else (no sizes, no numbers of queries, no other properties).
A change of the verification key or of the format of a proof is no Carry, because
extractor and simulator have other types after it.
-/
import Rom.DeriveWith
import Rom.Blocks
import Rom.ExitPriv

open scoped ENNReal

namespace Rom

open ZKCP

variable {S : OSpec} {I X W PP IVK ISK ISK' ISK'' Pf : Type}

/-- A' has what A has, with the added errors (a, z): the same extractor and simulator; the
completeness error grows by a, the privacy error by z, index binding keeps its bound. -/
def Carry (R : Gen.RelPair I X W PP) (B : ℕ) (A : Gen.Arg S I X W IVK ISK Pf)
    (A' : Gen.Arg S I X W IVK ISK' Pf) (a : ℝ≥0∞) (z : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (E : Gen.Extractor S I X W IVK Pf)
      (Sim : Gen.Simulator S PP IVK X Pf) (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞),
    Gen.IsZKCPArgWith R A B E Sim α ε ζ →
    Gen.IsZKCPArgWith R A' B E Sim (α + a) ε (fun t n => ζ t n + z t n)

/-- the bounds of a theorem may be raised -/
theorem mono_with {R : Gen.RelPair I X W PP} {A : Gen.Arg S I X W IVK ISK Pf} {B : ℕ}
    {E : Gen.Extractor S I X W IVK Pf} {Sim : Gen.Simulator S PP IVK X Pf} {α α' : ℝ≥0∞}
    {ε ε' ζ ζ' : ℕ → ℕ → ℝ≥0∞} (h : Gen.IsZKCPArgWith R A B E Sim α ε ζ) (hα : α ≤ α')
    (hε : ∀ tC tP, ε tC tP ≤ ε' tC tP) (hζ : ∀ t n, ζ t n ≤ ζ' t n) :
    Gen.IsZKCPArgWith R A B E Sim α' ε' ζ' :=
  ⟨fun i b hb => (h.completeness i b hb).trans hα,
    fun tC tP St Ct Pt hC hP => (h.indexBinding tC tP St Ct Pt hC hP).trans (hε tC tP),
    fun i Z hZ tV Vt N hb =>
      ⟨((h.indexPrivacy i Z hZ tV Vt N hb).1).trans (hζ tV N),
        (h.indexPrivacy i Z hZ tV Vt N hb).2⟩⟩

namespace Carry

variable {R : Gen.RelPair I X W PP} {B : ℕ} {A : Gen.Arg S I X W IVK ISK Pf}
  {A' : Gen.Arg S I X W IVK ISK' Pf} {A'' : Gen.Arg S I X W IVK ISK'' Pf}
  {a a' : ℝ≥0∞} {z z' : ℕ → ℕ → ℝ≥0∞}

/-- a step applied to a theorem on A -/
theorem apply (s : Carry R B A A' a z) {E : Gen.Extractor S I X W IVK Pf}
    {Sim : Gen.Simulator S PP IVK X Pf} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞}
    (h : Gen.IsZKCPArgWith R A B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R A' B E Sim (α + a) ε (fun t n => ζ t n + z t n) := s E Sim α ε ζ h

/-- no change adds no error -/
theorem refl (R : Gen.RelPair I X W PP) (B : ℕ) (A : Gen.Arg S I X W IVK ISK Pf) :
    Carry R B A A 0 (fun _ _ => 0) :=
  fun _ _ _ _ _ h => mono_with h (add_zero _).ge (fun _ _ => le_rfl) fun _ _ => (add_zero _).ge

/-- The added errors of two steps add up. -/
theorem comp (s : Carry R B A A' a z) (s' : Carry R B A' A'' a' z') :
    Carry R B A A'' (a + a') (fun t n => z t n + z' t n) :=
  fun E Sim α ε ζ h =>
    mono_with (s' E Sim _ _ _ (s E Sim α ε ζ h)) (add_assoc _ _ _).le
      (fun _ _ => le_rfl) fun _ _ => (add_assoc _ _ _).le

/-- an added error may be raised -/
theorem mono (s : Carry R B A A' a z) (ha : a ≤ a') (hz : ∀ t n, z t n ≤ z' t n) :
    Carry R B A A' a' z' :=
  fun E Sim α ε ζ h =>
    mono_with (s E Sim α ε ζ h) (add_le_add le_rfl ha) (fun _ _ => le_rfl) fun t n =>
      add_le_add le_rfl (hz t n)

end Carry

/-- The committer replaced by a close one (`Rom.replaceC`, Rom/Blocks.lean). -/
theorem carry_withC (R : Gen.RelPair I X W PP) (B : ℕ) (A : Gen.Arg S I X W IVK ISK Pf)
    (C' : I → OComp S (IVK × ISK)) {b : ℝ≥0∞}
    (hC : ∀ i, Prob.tv ((C' i).runLazy (Table.empty S)) ((A.C i).runLazy (Table.empty S)) ≤ b) :
    Carry R B A (withC A C') b (fun _ _ => b) :=
  fun _ _ _ _ _ h => replaceC hC h

/-- `deriveWith` (Rom/DeriveWith.lean) as a `Carry`, under hA, hb, hP: the committer's coins derived
from one seed, for a prover that replays the key. -/
theorem carry_derivedWith (R : Gen.RelPair I X W PP) (B : ℕ) (A : Gen.Arg S I X W IVK ISK Pf)
    (σ : SeedOracle S) (P' : I × Fin (σ.sd + 1) → (b : List (X × W)) → OComp S (Gen.Slots Pf b))
    {b : ℝ≥0∞} (hA : ArgAvoids A σ.o) (hb : ∀ i, (A.C i).pathBias σ ≤ b) (hP : Replays A σ P') :
    Carry R B A (derivedWith A σ P') b (fun t _ => (t : ℝ≥0∞) / (σ.sd + 1 : ℕ) + b) :=
  fun _ _ _ _ _ h =>
    mono_with (deriveWith hA hb hP h) le_rfl (fun _ _ => le_rfl) fun _ _ => (add_assoc _ _ _).le

/-- From a family of typed oracles to one hash function (Rom/ExitBind.lean, Rom/ExitPriv.lean), for
a query encoding `m : OracleCoding S lam` (a bijection: Rom/Family.lean) and under `LocalTo`: the three
properties at once, with the same bounds; budgets now count queries to the hash function. -/
theorem IsZKCPArgWith.overOne {lam : ℕ} (m : OracleCoding S lam) {R : Gen.RelPair I X W PP}
    {A : Gen.Arg S I X W IVK ISK Pf} {B : ℕ} {E : Gen.Extractor S I X W IVK Pf}
    {Sim : Gen.Simulator S PP IVK X Pf} {α : ℝ≥0∞} {ε ζ : ℕ → ℕ → ℝ≥0∞} (hE : LocalTo E m)
    (h : Gen.IsZKCPArgWith R A B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R (schemeOverOneHashFunction m A) B (extractorOverOneHashFunction m E) (simOne m Sim) α ε ζ :=
  ⟨completeness_overOne m R A B α h.completeness,
    binding_overOne m R A E hE ε h.indexBinding,
    privacy_overOne m R A B Sim ζ h.indexPrivacy⟩

end Rom
