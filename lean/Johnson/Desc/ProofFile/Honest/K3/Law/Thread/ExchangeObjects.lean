-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeObjects.lean: the honest side of the kind
"lookup" (K3): WHAT THE LOOKUP'S ROW OWES BEHIND ITS SUB-PROTOCOL: the item "the forms of the run
objects are worth 0", in the form in which the table of joints has it in front of a segment's second
sending (`formsTQ`, Johnson/Desc/Sound/FormsQ.lean). Theorems with proofs; no definition.

That sentence says: a segment is open; the run's reader gives its forms and late slots at
the structure; the late slots pass a test; each form names only what is there, AND IS WORTH 0 in the
world whose mask row and cells are read off the witness's tables. Its "there are" is over the
segment's part and the reader's answer: it names no rounds. So it is the nearest of the owed items
to the honest side's `Left`: every heard row is worth 0, in the world of every later ledger, at
every mask row under whose slots lie the coins spent, at all entries.

  `formsTQ_of_in`    on the library's side alone: the public test for the promise (`formsInT`) and
                     "each form is worth 0" give the sentence
  `worldOwn_nil`     without late slots the forms' world IS the ledger's own world at the
                     data's mask row
  `objects_of_left`  CONDITIONAL ON `Left`; the segment's ledger being later than the one behind the
                     hearing; THE READER ANSWERING WITH THE HEARD ROWS AND NO LATE SLOT; the public
                     test; and THE DICTIONARY at the mask row that the sentence itself reads off the
                     witness's tables: the sentence

Who can pay the premises. The public test: the promise behind the sub-protocol. The reader's answer:
the library shows what the run "objects" returns (`objects_answer`, Johnson/Top/H/Keep/K3Late.lean:
the heard rows) and, where the reader is the run itself, what the reader then answers
(`objects_reader`, Johnson/Top/H/Keep/ReaderIsRun.lean), UNDER THE PREMISE THAT NO HEARD ROW NAMES
AN ENTRY OF AN ARRAY, which follows from the hearing's return (`hearV_ne`,
Honest/K3/Parts/NoEntries.lean); none of it is called here. The dictionary: whoever ties the book's
coins to the witness's mask row.

Limits. The run "guests", which the table counts to the same item at some places, is not spoken of.
No instance of these hypotheses is exhibited in this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRows
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.K3 (HeardV)
open VerifiableInference.Desc.K9 (segAt? Readers formsInT)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (formsTQ worldOwn dataQ Stated MsgQ GQ)

/-- **On the library's side alone: the public test and "each form is worth 0"
give the sentence.** -/
theorem formsTQ_of_in (Rd : Readers) (St : Stated) (own : List (Nat × Nat)) (piece : Nat)
    (run : String)
    (s : VerifiableInference.Desc.First.S) (rd : Nat × Nat → MsgQ)
    (hin : formsInT Rd own piece run s = true)
    (hz : ∀ a R, segAt? s = some a → Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      f.value Reading.gl (worldOwn a R.late (St.at1 s (dataQ own a rd))) = 0) :
    formsTQ Rd St own piece run s rd := by
  unfold formsInT at hin
  cases ha : segAt? s with
  | none => simp [ha] at hin
  | some a =>
    cases hR : Rd.forms piece run s with
    | none => simp [ha, hR] at hin
    | some R =>
      rw [ha, hR] at hin
      obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hin
      exact ⟨a, R, ha, hR, h1, fun f hf => ⟨List.all_eq_true.1 h2 f hf, hz a R ha hR f hf⟩⟩

/-- Without late slots the forms' world is the ledger's own world at the data's mask row. The arm
that yields 0 at `none` is the library's own text of `worldOwn`, restated: the proof is `rfl`. -/
theorem worldOwn_nil (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ) :
    worldOwn a [] D = a.F.worldOf Reading.gl D.mask fun t r i =>
      match a.L.arrayOf[t]? with
      | some b => D.cell b.1 b.2 r i
      | none => 0 := rfl

/-- **CONDITIONAL ON `Left`, a later ledger, the reader's answer, the public test AND THE DICTIONARY
at the sentence's own mask row: the forms of the run "objects" are worth 0.** hM takes `MasksAre` as
a hypothesis: neither test on the book nor `CoinsAre` stands in this sentence: a caller brings them
(`objectsT_site`, `objectsQ_site`, ExchangeObjAt.lean, which have them out of `left_objects`). No
instance of these hypotheses is exhibited in this file. -/
theorem objects_of_left {W : Type} (R : Course W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE) (gV : HeardV) (G : Fork) (hLeft : Left R planes keys gV G)
    (Rd : Readers) (St : Stated) (own : List (Nat × Nat)) (piece : Nat)
    (s : VerifiableInference.Desc.First.S) (rd : Nat × Nat → MsgQ)
      (a : VerifiableInference.Desc.K9.Part)
    (hseg : segAt? s = some a) (hL : Later G a.F)
    (hRead : Rd.forms piece "objects" s = some { forms := gV.rows.toList, late := [] })
    (hin : formsInT Rd own piece "objects" s = true)
    (hM : MasksAre R (St.at1 s (dataQ own a rd)).mask) :
    formsTQ Rd St own piece "objects" s rd := by
  refine formsTQ_of_in Rd St own piece "objects" s rd hin fun a' R' ha hR f hf => ?_
  obtain rfl : a = a' := Option.some.inj (hseg.symm.trans ha)
  obtain rfl := Option.some.inj (hRead.symm.trans hR)
  rw [worldOwn_nil]
  exact (hLeft.1 a.F _ _ hL hM).1 f hf

#print axioms ProofFile.Honest.K3.Law.Exchange.formsTQ_of_in
#print axioms ProofFile.Honest.K3.Law.Exchange.worldOwn_nil
#print axioms ProofFile.Honest.K3.Law.Exchange.objects_of_left

end ProofFile.Honest.K3.Law.Exchange
