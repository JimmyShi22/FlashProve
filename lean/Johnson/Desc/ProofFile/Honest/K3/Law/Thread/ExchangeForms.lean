-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeForms.lean: the honest side of the kind "lookup"
(K3): THE ITEM "objects" AS THE TABLE OF JOINTS HAS IT: the sentence on forms at BOTH runs for which
the name stands ("objects" and "guests"), in both of the table's forms: in front of a segment's
second sending (`formsTQ`: the lookup on the calls) and behind it (`formsQ`: the lookup on the
digits). Theorems with proofs; no definition.

  `formsQ_of_in`      the twin of `formsTQ_of_in` (Honest/K3/Law/Thread/ExchangeObjects.lean): the
                      public test and "each form is worth 0" give the sentence
  `objectsQ_of_left`  the twin of `objects_of_left`: CONDITIONAL ON `Left`, a later ledger, the
                      reader's answer, the public test, and the dictionary at the sentence's own
                      mask row
  `formsTQ_none`, `formsQ_none`   a run whose reader answers with no form and no late slot: the
                      public test alone gives the sentence
  `objects_itemT`, `objects_itemQ`   the two runs' sentences give the item's text at the table's
                      list of runs for the name "objects"

Limits. That a filling's field formsT or forms IS that text is the filling's own equation: not
called here. No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeObjects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.K3 (HeardV)
open VerifiableInference.Desc.K9 (segAt? Readers formsIn formsInT)
open VerifiableInference.Desc.Sound (formsQ formsTQ worldOwn dataQ Stated MsgQ)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **On the library's side alone: the public test and "each form is worth 0" give the sentence.**
-/
theorem formsQ_of_in (Rd : Readers) (own : List (Nat × Nat)) (piece : Nat) (run : String) (s : FS)
    (rd : Nat × Nat → MsgQ) (hin : formsIn Rd own piece run s = true)
    (hz : ∀ a R, segAt? s = some a → Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      f.value Reading.gl (worldOwn a R.late (dataQ own a rd)) = 0) :
    formsQ Rd own piece run s rd := by
  unfold formsIn at hin
  cases ha : segAt? s with
  | none => simp [ha] at hin
  | some a =>
    cases hR : Rd.forms piece run s with
    | none => simp [ha, hR] at hin
    | some R =>
      rw [ha, hR] at hin
      obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hin
      exact ⟨a, R, ha, hR, h1, fun f hf => ⟨List.all_eq_true.1 h2 f hf, hz a R ha hR f hf⟩⟩

/-- **CONDITIONAL ON `Left`, a later ledger, the reader's answer, the public test AND THE DICTIONARY
at
the sentence's own mask row: the forms of the run "objects" are worth 0**, behind the segment's
second sending. hM takes `MasksAre` as a hypothesis: neither test on the book nor `CoinsAre` stands
in this sentence: a caller brings them (`objectsT_site`, `objectsQ_site`, ExchangeObjAt.lean, which
have them out of `left_objects`). No instance of these hypotheses is exhibited in this file. -/
theorem objectsQ_of_left {W : Type} (R : Course W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (gV : HeardV) (G : Fork) (hLeft : Left R planes keys gV G)
    (Rd : Readers) (own : List (Nat × Nat)) (piece : Nat) (s : FS) (rd : Nat × Nat → MsgQ)
    (a : VerifiableInference.Desc.K9.Part) (hseg : segAt? s = some a) (hL : Later G a.F)
    (hRead : Rd.forms piece "objects" s = some { forms := gV.rows.toList, late := [] })
    (hin : formsIn Rd own piece "objects" s = true) (hM : MasksAre R (dataQ own a rd).mask) :
    formsQ Rd own piece "objects" s rd := by
  refine formsQ_of_in Rd own piece "objects" s rd hin fun a' R' ha hR f hf => ?_
  obtain rfl : a = a' := Option.some.inj (hseg.symm.trans ha)
  obtain rfl := Option.some.inj (hRead.symm.trans hR)
  rw [worldOwn_nil]
  exact (hLeft.1 a.F _ _ hL hM).1 f hf

/-- A run whose reader answers with no form: the public test alone gives the sentence. -/
theorem formsTQ_none (Rd : Readers) (St : Stated) (own : List (Nat × Nat)) (piece : Nat)
    (run : String) (s : FS) (rd : Nat × Nat → MsgQ)
    (hRead : Rd.forms piece run s = some { forms := [], late := [] })
    (hin : formsInT Rd own piece run s = true) : formsTQ Rd St own piece run s rd :=
  formsTQ_of_in Rd St own piece run s rd hin fun _ R' _ hR f hf => by
    obtain rfl := Option.some.inj (hRead.symm.trans hR)
    exact absurd hf List.not_mem_nil

theorem formsQ_none (Rd : Readers) (own : List (Nat × Nat)) (piece : Nat) (run : String) (s : FS)
    (rd : Nat × Nat → MsgQ) (hRead : Rd.forms piece run s = some { forms := [], late := [] })
    (hin : formsIn Rd own piece run s = true) : formsQ Rd own piece run s rd :=
  formsQ_of_in Rd own piece run s rd hin fun _ R' _ hR f hf => by
    obtain rfl := Option.some.inj (hRead.symm.trans hR)
    exact absurd hf List.not_mem_nil

/-- **The two runs' sentences give the item's text**, in front of the second sending. wt: what the
text says besides at the name "weights". -/
theorem objects_itemT (Rd : Readers) (St : Stated) (own : List (Nat × Nat)) (piece : Nat) (s : FS)
    (rd : Nat × Nat → MsgQ) (wt : Prop) (h1 : formsTQ Rd St own piece "objects" s rd)
    (h2 : formsTQ Rd St own piece "guests" s rd) :
    (∀ p ∈ [(piece, "objects"), (piece, "guests")], formsTQ Rd St own p.1 p.2 s rd) ∧
      ("objects" = "weights" → wt) := by
  refine ⟨fun p hp => ?_, fun h => absurd h (by decide)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1
  · exact h2

/-- **The two runs' sentences give the item's text**, behind the second sending. -/
theorem objects_itemQ (Rd : Readers) (own : List (Nat × Nat)) (piece : Nat) (s : FS)
    (rd : Nat × Nat → MsgQ) (wt : Prop) (h1 : formsQ Rd own piece "objects" s rd)
    (h2 : formsQ Rd own piece "guests" s rd) :
    (∀ p ∈ [(piece, "objects"), (piece, "guests")], formsQ Rd own p.1 p.2 s rd) ∧
      ("objects" = "weights" → wt) := by
  refine ⟨fun p hp => ?_, fun h => absurd h (by decide)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact h1
  · exact h2

#print axioms ProofFile.Honest.K3.Law.Exchange.formsQ_of_in
#print axioms ProofFile.Honest.K3.Law.Exchange.objectsQ_of_left
#print axioms ProofFile.Honest.K3.Law.Exchange.formsTQ_none
#print axioms ProofFile.Honest.K3.Law.Exchange.formsQ_none
#print axioms ProofFile.Honest.K3.Law.Exchange.objects_itemT
#print axioms ProofFile.Honest.K3.Law.Exchange.objects_itemQ

end ProofFile.Honest.K3.Law.Exchange
