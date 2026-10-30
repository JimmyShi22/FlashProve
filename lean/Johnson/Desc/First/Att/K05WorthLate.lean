-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05WorthLate.lean: kind K5: THE TABLE's SENTENCE ON A RUN's FORMS GIVES THEIR
WORTH IN THE WORLD OF A LATER LEDGER: worth_of_formsTQ (Johnson/Desc/First/Att/K05WorthAtTable.lean)
FOR A RUN THAT FILLS SLOTS ITSELF.

Why. worth_of_formsTQ asks that the reader names no late slot, and concludes at the world of the
record's own ledger. The lookup's run on the planes fills slots that are free at the record at which
its item is read: the table's world has under such a slot what the run WILL lay (worldOwn a R.late,
Johnson/Desc/Sound/FormsQ.lean); the law that spends the worth wants the world of the ledger behind
the run.

IS IT EMPTY HERE? At H := the record's ledger and R.late = [] it is worth_of_formsTQ (lateLaid_none).

Main names:
  `LateLaid F late H fs`: under every slot that a form of fs names, the table's hidden value (slotW F
    late) is the ledger H's own, at every mask row.
  `lateLaid_none`: LateLaid F [] F fs.
  `worth_of_formsTQ_late`: **AllZero in H.worldOf mask entry**, from formsTQ, the reader's answer R,
    LateLaid a.F R.late H fs and WorldTie.
  `WorldTie.mask_to`: WorldTie at another mask row that agrees at the slots that the forms name.
Limits. LateLaid is a premise: at H := the ledger behind the run and late := what the run lays it is
another file's law (lateLaid_affInT, Johnson/Top/H/Keep/LateLaidAt.lean).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05WorthAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated formsTQ slotW slotW_ledger value_eq)
open K5Law (AllZero)

/-- Under every slot that a form of fs names the table's hidden value is the ledger H's own. -/
def LateLaid (F : Fork) (late : List (ℕ × E × E)) (H : Fork) (fs : List Aff) : Prop :=
  ∀ f ∈ fs, ∀ y ∈ f.slots.toList, ∀ mk : ℕ → GQ,
    slotW F late mk y.1 =
      Reading.gl.val (H.vp.getD y.1 zeroE) - Reading.gl.val (H.mf.getD y.1 zeroE) * mk y.1

theorem lateLaid_none (F : Fork) (fs : List Aff) : LateLaid F [] F fs :=
  fun _ _ y _ mk => slotW_ledger F [] mk y.1 rfl

/-- **The table's sentence gives the worth in the world of a later ledger.** -/
theorem worth_of_formsTQ_late (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s : First.S) (rd : ℕ × ℕ → MsgQ) (h : formsTQ Rd St own piece run s rd)
    {a : VerifiableInference.Desc.K9.Part} (ha : segAt? s = some a)
    {R : VerifiableInference.Desc.K9.Read} (hR : Rd.forms piece run s = some R) (H : Fork)
    (mask : ℕ → GQ) (entry : ℕ → ℕ → ℕ → GQ) (fs : List Aff) (hsub : ∀ f ∈ fs, f ∈ R.forms)
    (hl : LateLaid a.F R.late H fs) (T : WorldTie St own s a rd mask entry fs) :
    AllZero Reading.gl (H.worldOf Reading.gl mask entry) fs := by
  obtain ⟨a', R', ha', hR', _, hf⟩ := h
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  intro f hm
  have h0 := (hf f (hsub f hm)).2
  rw [← h0]
  refine value_eq _ _ f (fun y hy => (T.entry f hm y hy).symm) (fun y hy => ?_)
  show Reading.gl.val (H.vp.getD y.1 zeroE) - Reading.gl.val (H.mf.getD y.1 zeroE) * mask y.1 = _
  rw [← T.mask f hm y hy]
  exact (hl f hm y hy _).symm

/-- The tie at another mask row that agrees at the slots that the forms name. -/
theorem WorldTie.mask_to {St : Stated} {own : List (ℕ × ℕ)} {s : First.S}
    {a : VerifiableInference.Desc.K9.Part} {rd : ℕ × ℕ → MsgQ} {mask mask' : ℕ → GQ}
    {entry : ℕ → ℕ → ℕ → GQ} {fs : List Aff} (T : WorldTie St own s a rd mask entry fs)
    (h : ∀ f ∈ fs, ∀ y ∈ f.slots.toList, mask y.1 = mask' y.1) :
    WorldTie St own s a rd mask' entry fs :=
  ⟨fun f hf y hy => (T.mask f hf y hy).trans (h f hf y hy), T.entry⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.lateLaid_none
#print axioms VerifiableInference.Desc.First.Att.P.worth_of_formsTQ_late
#print axioms VerifiableInference.Desc.First.Att.P.WorldTie.mask_to
