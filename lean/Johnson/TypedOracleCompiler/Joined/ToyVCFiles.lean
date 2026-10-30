-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/ToyVCFiles.lean: a test: a small key's file and a small proof's file over
records, each three joined hash chains, with the typed description of each and its soundness clauses
proved.

Statements on the verifier with records, over the second form of the compiler's verifier side, for a
key file's and a proof file's three hash chains, joined by seals. That this verifier writes what is
hashed as the prover's files have it is not shown in this folder.
By a reading of the programs' text it does not: behind the roots, `VC`
(Johnson/TypedOracleCompiler/RecCompile/Cms.lean) puts a code of the whole record, the seed too, into the first
query of each of its three compiled verifiers, while the programs hash the roots and the answers,
and recompute the seeds from the roots (so too the verifier written in Lean:
OnBytes/Params/Chains.lean; OnBytes/Key/Table.lean). `verifyAtFullKey` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) is
the form that has the answers alone there; nothing in this file is stated for it.

It serves Johnson/TypedOracleCompiler/Joined/ToyVC.lean, where these two files are the key and the session of one
interface with records, and every hypothesis of index binding (Johnson/TypedOracleCompiler/Joined/TopVC.lean) is met
together. The rounds, their wire records and the two places that are read are those of
OnBytes/TypedOracleCompiler/Joined/ToyFile.lean.

A record is a seed, which is a hash block, and an answer, which is one bit. The index is one bit,
and the answer IS the index. A seed whose bit is true is a collision seed: there nothing is decoded.

Main names:
  `Seed0`, `Rec0`, `coll0`, `dec0`   seeds, records, collision seeds, the decoder.
  `DT`, `CT`, `knowsT`, `decidesT`, `isLocalT`, `lgT_iff`   the key's file: its instance is a
                 record; it accepts if the seed is no collision seed and chain 1's string holds
                 true at the two places. Its language: the seed is no collision seed.
  `DB`, `CB`, `knowsB`, `decidesB`, `isLocalB`, `lgB_iff`, `r0B_of_accept`   the proof's file: its
                 instance is two bits and a record; it accepts if the first bit is the record's
                 answer, the second bit is true, and the string holds true at the two places. The
                 second bit enters the chain in round 1. Its language: the first bit is the answer
                 and the second is true.

Limits: a test. All errors are 0: a false statement is rejected outright. There are no external
strings. Digests have one bit, so a bound with 2^lam below the line is at least 1 here: the test is
of whether hypotheses can hold together, not of a number. Nothing here says that a real file's
description has these clauses.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.ToyLate

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open _root_.CompileK.Joined (KnowLate)
open scoped ENNReal

/-! ## Records -/

/-- seeds: hash blocks -/
abbrev Seed0 : Type := Blk

/-- records: a seed and an answer -/
abbrev Rec0 : Type := Seed0 × Bool

/-- the seed is a collision seed -/
def coll0 (s : Seed0) : Prop := s 0 0 = true

instance (s : Seed0) : Decidable (coll0 s) := inferInstanceAs (Decidable (s 0 0 = true))

/-- the decoder: the answer, unless the seed is a collision seed -/
def dec0 (r : Rec0) : Option Bool := if r.1 0 0 then none else some r.2

theorem dec0_of_coll {r : Rec0} (h : coll0 r.1) : dec0 r = none := if_pos h

theorem dec0_of_not_coll {r : Rec0} (h : r.1 0 0 = false) : dec0 r = some r.2 := by
  unfold dec0
  rw [h]
  rfl

/-! ## The key's file -/

/-- The key's verifier: the seed is no collision seed, and chain 1's string holds true at both
places. -/
@[reducible] def DT : Desc G Rec0 (oneExternalString 0 Unit) where
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => {p₁ ρ, p₃ ρ}
  accept := fun r _ τ =>
    !(r.1 0 0) && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)

theorem isLocalT : DT.proto.IsLocal := by
  intro r y y' τ τ' hρ _ _ hr
  have h1 : str₁ τ (bit (G.rho₁ τ.rho).1) = str₁ τ' (bit (G.rho₁ τ.rho).1) :=
    hr _ (Finset.mem_insert_self _ _)
  have h3 : str₁ τ (bit (G.rho₃ τ.rho).1) = str₁ τ' (bit (G.rho₃ τ.rho).1) :=
    hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  show (!(r.1 0 0) && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) =
    (!(r.1 0 0) && str₁ τ' (bit (G.rho₁ τ'.rho).1) && str₁ τ' (bit (G.rho₃ τ'.rho).1))
  rw [h1, h3, hρ]

/-- The three chains' descriptions of the key's file, made of its verifier's tests. -/
@[reducible] def CT : Links G (Rec0 × (oneExternalString 0 Unit).Str) where
  A₁ := Fin 2 → Bool
  A₂ := Fin 2 → Bool
  W₀ := Unit
  W₁ := Unit
  W₂ := Unit
  out₁ := fun a τ => if !(a.1.1 0 0) && sOf τ (bit (bOf₁ τ)) then some (sOf τ) else none
  out₂ := fun o _ => some o
  out₃ := fun o τ => if o (bit (bOf₃ τ)) then some () else none
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a _ => a.1.1 0 0 = false
  R₁ := fun _ _ => True
  R₂ := fun _ _ => True
  e₁ := fun _ _ _ => ()
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := err0 _
  ε₂ := err0 _
  ε₃ := err0 _
  d₀ := ()
  d₁ := ()

theorem knowsT : CT.Knows where
  know₁ := fun a _ => Doomed.of_forall _ _ fun τ b _ h _ => by
    have h' : (if (!(a.1.1 0 0) && sOf τ (bit (bOf₁ τ))) = true then some (sOf τ) else none) =
        some b := h
    by_cases hc : (!(a.1.1 0 0) && sOf τ (bit (bOf₁ τ))) = true
    · have h1 := (Bool.and_eq_true_iff.1 hc).1
      show a.1.1 0 0 = false
      cases hv : a.1.1 0 0
      · rfl
      · rw [hv] at h1
        cases h1
    · rw [if_neg hc] at h'
      cases h'
  know₂ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  know₃ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-- No chain of the key's description rejects exactly where the key's verifier accepts. -/
theorem isSome_allT_iff (r : Rec0) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) :
    (CT.all.out (r, y) τ).isSome = true ↔ DT.accept r y τ = true := by
  show ((if (!(r.1 0 0) && str₁ τ (bit (G.rho₁ τ.rho).1)) = true then some (str₁ τ) else none).bind
      fun b => (some b).bind fun c =>
        if c (bit (G.rho₃ τ.rho).1) = true then some () else none).isSome = true ↔
    (!(r.1 0 0) && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) = true
  cases hp : (!(r.1 0 0) && str₁ τ (bit (G.rho₁ τ.rho).1)) <;>
    cases hq : str₁ τ (bit (G.rho₃ τ.rho).1) <;> simp [hq]

theorem decidesT (r : Rec0) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) (h : DT.accept r y τ = true) :
    (CT.all.out (r, y) τ).isSome = true := (isSome_allT_iff r y τ).2 h

/-- The language of the key's file: the seed is no collision seed. -/
theorem lgT_iff (r : Rec0) (y : (oneExternalString 0 Unit).Str) : CT.Lg id r y ↔ r.1 0 0 = false :=
  ⟨fun h => (h trivial).elim fun _ hw => hw, fun h _ => ⟨(), h⟩⟩

/-! ## The proof's file -/

/-- what of an instance with its record the first query holds -/
def earlyB (a : Y2 × Rec0) : Y2 × Rec0 := (early a.1, a.2)

/-- The proof's verifier: the first bit is the record's answer, the second bit is true, and chain
1's string holds true at both places. -/
@[reducible] def DB : Desc G (Y2 × Rec0) (oneExternalString 0 Unit) where
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => {p₁ ρ, p₃ ρ}
  accept := fun a _ τ =>
    (a.1.1 == a.2.2) && a.1.2 && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)

theorem isLocalB : DB.proto.IsLocal := by
  intro a y y' τ τ' hρ _ _ hr
  have h1 : str₁ τ (bit (G.rho₁ τ.rho).1) = str₁ τ' (bit (G.rho₁ τ.rho).1) :=
    hr _ (Finset.mem_insert_self _ _)
  have h3 : str₁ τ (bit (G.rho₃ τ.rho).1) = str₁ τ' (bit (G.rho₃ τ.rho).1) :=
    hr _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  show ((a.1.1 == a.2.2) && a.1.2 && str₁ τ (bit (G.rho₁ τ.rho).1) &&
      str₁ τ (bit (G.rho₃ τ.rho).1)) =
    ((a.1.1 == a.2.2) && a.1.2 && str₁ τ' (bit (G.rho₁ τ'.rho).1) &&
      str₁ τ' (bit (G.rho₃ τ'.rho).1))
  rw [h1, h3, hρ]

/-- What the proof's verifier accepts has the first bit equal to the answer and the second true. -/
theorem r0B_of_accept {x : Y2} {r : Rec0} {y : (oneExternalString 0 Unit).Str} {τ : Tr G.sh}
    (h : DB.accept (x, r) y τ = true) : x.1 = r.2 ∧ x.2 = true := by
  have h' : ((x.1 == r.2) && x.2 && str₁ τ (bit (G.rho₁ τ.rho).1) &&
      str₁ τ (bit (G.rho₃ τ.rho).1)) = true := h
  have h2 := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h').1).1
  exact ⟨beq_iff_eq.1 h2.1, h2.2⟩

/-- The three chains' descriptions of the proof's file, made of its verifier's tests. -/
@[reducible] def CB : Links G ((Y2 × Rec0) × (oneExternalString 0 Unit).Str) where
  A₁ := Fin 2 → Bool
  A₂ := Fin 2 → Bool
  W₀ := Unit
  W₁ := Unit
  W₂ := Unit
  out₁ := fun a τ =>
    if (a.1.1.1 == a.1.2.2) && a.1.1.2 && sOf τ (bit (bOf₁ τ)) then some (sOf τ) else none
  out₂ := fun o _ => some o
  out₃ := fun o τ => if o (bit (bOf₃ τ)) then some () else none
  on₀ := fun _ => True
  on₁ := fun _ => True
  on₂ := fun _ => True
  R₀ := fun a _ => a.1.1.1 = a.1.2.2 ∧ a.1.1.2 = true
  R₁ := fun _ _ => True
  R₂ := fun _ _ => True
  e₁ := fun _ _ _ => ()
  e₂ := fun _ _ _ => ()
  e₃ := fun _ _ _ => ()
  ε₁ := err0 _
  ε₂ := err0 _
  ε₃ := err0 _
  d₀ := ()
  d₁ := ()

theorem knowsB : CB.KnowsLate earlyB 1 where
  know₁ := fun _ y => JDoomed.of_forall _ _ _ fun φ τ _ b _ h _ => by
    have h' : (if ((φ.1.1.1 == φ.1.2.2) && φ.1.1.2 && sOf τ (bit (bOf₁ τ))) = true
        then some (sOf τ) else none) = some b := h
    by_cases hc : ((φ.1.1.1 == φ.1.2.2) && φ.1.1.2 && sOf τ (bit (bOf₁ τ))) = true
    · have h2 := Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hc).1
      exact ⟨beq_iff_eq.1 h2.1, h2.2⟩
    · rw [if_neg hc] at h'
      cases h'
  know₂ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  know₃ := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  hands₁ := fun _ _ _ _ _ => trivial
  hands₂ := fun _ _ _ _ _ => trivial

/-- No chain of the proof's description rejects exactly where the proof's verifier accepts. -/
theorem isSome_allB_iff (a : Y2 × Rec0) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) :
    (CB.all.out (a, y) τ).isSome = true ↔ DB.accept a y τ = true := by
  show ((if ((a.1.1 == a.2.2) && a.1.2 && str₁ τ (bit (G.rho₁ τ.rho).1)) = true
      then some (str₁ τ) else none).bind
      fun b => (some b).bind fun c =>
        if c (bit (G.rho₃ τ.rho).1) = true then some () else none).isSome = true ↔
    ((a.1.1 == a.2.2) && a.1.2 && str₁ τ (bit (G.rho₁ τ.rho).1) &&
      str₁ τ (bit (G.rho₃ τ.rho).1)) = true
  cases hp : ((a.1.1 == a.2.2) && a.1.2 && str₁ τ (bit (G.rho₁ τ.rho).1)) <;>
    cases hq : str₁ τ (bit (G.rho₃ τ.rho).1) <;> simp [hq]

theorem decidesB (x : Y2) (r : Rec0) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh)
    (h : DB.accept (x, r) y τ = true) : (CB.all.out ((x, r), y) τ).isSome = true :=
  (isSome_allB_iff (x, r) y τ).2 h

/-- The language of the proof's file: the first bit is the record's answer, the second is true. -/
theorem lgB_iff (a : Y2 × Rec0) (y : (oneExternalString 0 Unit).Str) :
    CB.Lg id a y ↔ a.1.1 = a.2.2 ∧ a.1.2 = true :=
  ⟨fun h => (h trivial).elim fun _ hw => hw, fun h _ => ⟨(), h⟩⟩

/-- the proof's verifier accepts somewhere -/
theorem acceptsB : DB.accept ((true, true), (fun _ _ => false, true)) (fun p => p.elim0)
    (trOf (fun _ => true) fun _ _ => false) = true := rfl

/-- it rejects another index than the record's answer -/
theorem rejectsB (b : Bool) (s : Seed0) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) :
    DB.accept ((!b, true), (s, b)) y τ = false := by
  cases h : DB.accept ((!b, true), (s, b)) y τ
  · rfl
  · have h1 : (!b) = b := (r0B_of_accept h).1
    cases b <;> cases h1

end TypedOracleCompiler.Joined.Toy
