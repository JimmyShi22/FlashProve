-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ObjectsOn.lean: CONDITIONAL.

What is here. THE SENTENCE OF THE LOOKUP's RUN OF CLAIMS "objects" IS CARRIED FORWARD: from the
state in front of a step to the state behind it, at the same tables of the witness, where the step
turns the open feed-forward segment's ledger into a later one. The library's
Johnson/Road/K4/Riders/Objects.lean carries the sentence from behind to in front (`objects_back`)
and the public test from in front to behind (`objects_forward`); the honest side wants the sentence
carried forward. `objects_on` asks what `objects_back` asks, less the test in front, which the
sentence holds (`formsInT_of_formsTQ`), and with the four hypotheses more of `objects_forward`,
which gives the test behind. Each form is worth the same at both states by the library's
`value_ridesW` (Johnson/Desc/Sound/FormsQ.lean): the slots that it names are filled in front, and a
later ledger keeps what lies under a filled slot; it names no entry (hne); the stated data's mask
row is one at both states (hSt). The statements speak of two states; they name no thread and no
meaning of the table's items. Statements with their proofs; `objects_on`'s begins after the proof
text of `objects_back`.

Words. The sentence: `formsTQ` (Johnson/Desc/Sound/FormsQ.lean): each form that the reader lists at
the run names only what is there, and is worth 0 at the witness's tables rd. The public test:
`formsInT`: the sentence's half with code: what a form may name. The ledger: the open segment's
table of slots (`Fork`); a later ledger keeps what lies under a filled slot (`PscRun.Later`). A late
slot: one that the run itself is to fill. The free slot: `K9.mergeOf`: the one slot that no form may
name. The stated data: the witness's tables with the second sending's arrays set to their stated
functions of the first's (`Stated`).

Not shown here. NONE OF THE HYPOTHESES IS SHOWN HERE: Law/ObjectsOnKeeps.lean has them from K4's
clause of `keeps` and three tests with code. hne, THAT THE ROWS WHICH THE LOOKUP HEARD NAME NO
ENTRY, IS ASKED AS IN `objects_back`: the stated data may differ at the two states in the cells of
the arrays; a form that names no entry reads no cell. Nothing says that a form is worth 0 anywhere.
Nothing on the run "guests": the library's `guests_holds` has its sentence outright.
`formsInT_of_formsTQ` IS A SECOND TEXT: the library has it as `formsTQ_in`
(Johnson/Desc/Sound/BordersForms.lean); it is typed again so that this file imports one module. IT
IMPORTS Johnson/Road/K4/Riders/Objects.lean ALONE, and its imports reach no module under
Johnson/Goal/. No property is claimed.

  `formsInT_of_formsTQ`   the sentence holds the public test.
  `objects_on`   **the sentence forward.**
-/
import Johnson.Road.K4.Riders.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open OnBytes.Desc.First.K4 (Rest)
open OnBytes.Desc.First.K4.Riders (ObjRun objects_forward reader_objects rowsOwn rowsOwn_trees
  segAt_lay' rides_of dataQ_same)
open VerifiableInference.Desc (Claim K9.readerOf K9.mergeOf K9.RunOf K9.Read K9.Readers K9.formsInT
  K9.affInT)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.Sound (Stated formsTQ dataQ MsgQ value_ridesW)

variable {states : Nat → List (K9.RunOf S)} {b : Nat} {nm : String}
  {run : Nat → S → Except String (List Claim × S)} {s s' : S} {a : LayOwn} {g : Forest.Heard}
  {G : Fork} {own : List (Nat × Nat)} {Rd : K9.Readers}

/-- CONDITIONAL: on h. The sentence holds the public test: its clause on the late slots and, form by
form, its clause on what a form names are the test's own text. -/
theorem formsInT_of_formsTQ {St : Stated} {rd : Nat × Nat → MsgQ} {name : String}
    (h : formsTQ Rd St own b name s rd) : K9.formsInT Rd own b name s = true := by
  obtain ⟨A, R, hA, hs, hl, hf⟩ := h
  unfold K9.formsInT
  rw [hA, hs]
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hm => (hf f hm).1⟩

/-- CONDITIONAL: on every hypothesis named. **FORWARD, THE SENTENCE.** Under: a feed-forward segment
in front, `Rest`, a later ledger behind with the same arrays that the claims read; the run is an
`ObjRun`, found under its name; what the lookup heard lies in the segment, and ITS ROWS NAME NO
ENTRY; the free slot behind is sF, not below the ledger's next free number in front; the ledger in
front has its sizes, and nothing is filled from its next free number on; the readers give the
generic reader's answer at both states; the stated data's mask row is one at both: the sentence at
the state in front gives the sentence at the state behind, at the same witness. -/
theorem objects_on {St : Stated} {rd : Nat × Nat → MsgQ} {sF : Nat} (ha : s.here = .lay a)
    (R : Rest s s') (hG : s'.fork? = some G) (L : Later a.F G) (htr : G.trees = a.F.trees)
    (hfind : (states b).find? (fun r => r.1 == "objects") = some (nm, run)) (hrun : ObjRun run)
    (hh : a.lookHeard = some g) (hne : ∀ f ∈ g.rows.toList, f.ents.toList = [])
    (hm : K9.mergeOf s' = some sF) (hsF : a.F.next ≤ sF) (hS : Sized a.F)
    (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (e : Rd.forms b "objects" s = K9.readerOf states b "objects" s)
    (e' : Rd.forms b "objects" s' = K9.readerOf states b "objects" s')
    (hSt : ∀ D j, (St.at1 s' D).mask j = (St.at1 s D).mask j)
    (h : formsTQ Rd St own b "objects" s rd) : formsTQ Rd St own b "objects" s' rd := by
  have hin' : K9.formsInT Rd own b "objects" s' = true :=
    objects_forward ha R hG L htr hfind hrun hh hm hsF hS hfree e e' (formsInT_of_formsTQ h)
  obtain ⟨a', ha', hL', _, _, hlh⟩ := R.here a ha
  have hF' : a'.F = G := by
    have e0 : s'.fork? = some a'.F := by simp only [S.fork?, ha']
    exact Option.some.inj (e0.symm.trans hG)
  obtain ⟨A, hA, eF, eL, est, ebk⟩ := segAt_lay' ha
  obtain ⟨B, hB, fF, fL, fst, fbk⟩ := segAt_lay' ha'
  have c1 := e.trans (reader_objects hfind hrun ha hh)
  have c2 := e'.trans (reader_objects hfind hrun ha' (hlh.trans hh))
  rw [hF', rowsOwn_trees htr] at c2
  have hL : B.L = A.L := by rw [fL, eL, hL']
  have hst : B.d.st = A.d.st := by rw [fst, est, R.st]
  have hbk : B.d.book = A.d.book := by rw [fbk, ebk, R.book]
  have hLat : Later A.F B.F := by
    rw [eF, fF, hF']
    exact L
  have Rid := rides_of own hL hst hbk hLat
  obtain ⟨A', Rr, hA', hs, _, hf⟩ := h
  obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
  have hs' : Rd.forms b "objects" s' = some Rr := (c2.trans c1.symm).trans hs
  unfold K9.formsInT at hin'
  rw [hB, hs'] at hin'
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin'
  refine ⟨B, Rr, hB, hs', hlate, fun f hm' => ⟨List.all_eq_true.1 hall f hm', ?_⟩⟩
  have hf' : f ∈ g.rows.toList := by
    by_cases hb : rowsOwn a.F g = true
    · rw [if_pos hb] at c1
      obtain rfl : ({ forms := g.rows.toList, late := [] } : K9.Read) = Rr :=
        Option.some.inj (c1.symm.trans hs)
      exact hm'
    · rw [if_neg hb] at c1
      exact nomatch c1.symm.trans hs
  have h2 := (hf f hm').1
  unfold K9.affInT at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  have hv := value_ridesW own (K9.mergeOf s) Rr.late A B (St.at1 s (dataQ own A rd))
    (St.at1 s' (dataQ own B rd)) Rid.arrays Rid.filled f (List.all_eq_true.1 h3)
    (fun x hx => by
      rw [hne f hf'] at hx
      cases hx)
    (fun x _ => by
      rw [dataQ_same own hL hst hbk rd]
      exact hSt _ _)
  rw [hv]
  exact (hf f hm').2

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.formsInT_of_formsTQ
#print axioms ProofFile.Honest.K4.objects_on
