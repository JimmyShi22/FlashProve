-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsTObjects.lean: The kind "lookup" (K3): FROM THE TABLE OF JOINTS' SENTENCE
"the forms of the run objects are worth 0" IN ITS FORM IN FRONT OF A SEGMENT's SECOND SENDING
(formsTQ, Johnson/Desc/Sound/FormsQ.lean) TO THE FIRST ITEM OF THE
LOOKUP's ROW OUT (K3OutRows): the sister of Johnson/Top/H/Keep/FormsObjects.lean and
FormsObjectsLink.lean, for the lookups on a link's calls, whose item is formsT. Statements and
proofs.

OBJECT: formsTQ at a run "objects"; Meaning.formsT at meaningForms; K3OutRows.
Used by Johnson/Desc/First/Look/K3CallsObjects.lean and Johnson/Desc/First/Look/K3HeadObjects.lean.
LETTERS: Rd0 | Rd, St, own, pr, heard | seat, h, lm, first, nu, rd, s; the filling's; H, l; Ok;
  pass.
Compiled with the whole library.

Main names:
  formsTQ_objects_outRows: the end, at the sentence itself.
  formsT_objects_bare: at the filling and a link's readers.

Limits. PREMISES THAT STAY IN THE SECOND: hrun · hlink · hA · hfind | hpass as in
FormsObjectsLink.lean · hSt: the stated data keep the mask row · hDict: the one equation on the
mask row, read at the first sending's seats, at parts with Ok. ASKED IN THE CONCLUSION, OF THE
VERIFIER's STATE: its part has Ok · the rows of what was heard are bare.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.BordersForms
import Johnson.Top.H.Keep.FormsInObjects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Bare)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp S)
open VerifiableInference.Desc.K9 (Readers segAt? readersOfLink statesOfLink LinkHoles)

/-- **The end, at the sentence itself.** -/
theorem formsTQ_objects_outRows (Rd0 : Readers) (St : Stated) (own : List (ℕ × ℕ)) (pr : ℕ)
    (heard : S → Option Forest.Heard) (h : Forest.Shape) (lm first : ℕ) (ν : _root_.Fo.Pl → GQ)
    (rd : ℕ × ℕ → MsgQ) (s : S)
    (hRd : ∀ R g, Rd0.forms pr "objects" s = some R → heard s = some g →
      R.late = [] ∧ ∀ f ∈ g.rows.toList, f ∈ R.forms)
    (hDict : ∀ a j, segAt? s = some a → j < a.F.ns →
      (St.at1 s (dataQ own a rd)).mask j = ν (.mask j))
    (hf : formsTQ Rd0 St own pr "objects" s rd) :
    ∀ g F', s.fork? = some F' → heard s = some g →
      OnPublicFiles.K3OutRows h lm first ν Reading.gl g F' := by
  intro g F' hF hg
  obtain ⟨a, R, ha, hR, _, hv⟩ := hf
  obtain ⟨hl, hm⟩ := hRd R g hR hg
  obtain rfl : a.F = F' := Option.some.inj ((fork_of_segAt ha).symm.trans hF)
  refine OnPublicFiles.outRows_of_rows Reading.gl h lm first ν g a.F a.F (_root_.Fo.Later.refl _)
    (worldOwn a [] (St.at1 s (dataQ own a rd))).entry fun f hfm => ?_
  obtain ⟨hA, h0⟩ := hv f (hm f hfm)
  rw [hl] at h0 hA
  rw [← h0]
  refine value_eq _ _ f (fun _ _ => rfl) fun x hx => ?_
  have hlt : x.1 < a.F.ns := by
    unfold K9.affInT at hA
    have h1 := (Eq.mp (Bool.and_eq_true _ _) hA).2
    have h2 := List.all_eq_true.1 h1 x hx
    unfold K9.slotIn at h2
    exact of_decide_eq_true (Eq.mp (Bool.and_eq_true _ _) h2).1
  show Reading.gl.val (a.F.vp.getD x.1 zeroE) - Reading.gl.val (a.F.mf.getD x.1 zeroE) *
      ν (.mask x.1) = slotW a.F [] (St.at1 s (dataQ own a rd)).mask x.1
  rw [slotW_ledger a.F [] _ x.1 rfl, hDict a x.1 ha hlt]

section
variable (cs : OnBytes.Codes) {P Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (Rd : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
  (after : ℕ → First.S → Except String First.S) (N : Numbers)
  (wt : ℕ → P × First.S → Strs → Wit Cells Tok MsgT → Prop) (rw : ℕ → First.S → Bool)
  (ah : ℕ → String → Bool)

/-- **At the filling and a link's readers.** -/
theorem formsT_objects_bare (Mg : Meaning P (Wit Cells Tok MsgT)) (m pc pr : ℕ)
    (H : LinkHoles) (l : Link S Claim) (seat : K3.Seat S Claim) (hA : OnPublicFiles.AtS2 seat)
    (h : Forest.Shape) (lm first : ℕ) (ν : Wit Cells Tok MsgT → _root_.Fo.Pl → GQ)
    (Ok : K9.Part → Prop)
    (hrun : (pr, "objects") ∈ runs m pc "objects") (hlink : Rd m = readersOfLink H l)
    (pass : S → S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink l pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      OnPublicFiles.RunOver pass run (OnPublicFiles.objectsRun seat))
    (hSt : ∀ s D j, (St.at1 s D).mask j = D.mask j)
    (hDict : ∀ a w j, Ok a → j < a.F.ns →
      (dataQ (N.sent m 0) a (seatTab cs arr ms w)).mask j = ν w (.mask j)) :
    ∀ (z : P) (s : S) (y : Strs) (w : Wit Cells Tok MsgT),
      (meaningForms cs arr ms Rd runs St after N wt rw ah Mg).formsT m pc "objects" (z, s) y w →
      (∀ a, segAt? s = some a → Ok a) →
      ∀ g F', seat.fork s = some F' → seat.heard s = some g → (∀ f ∈ g.rows.toList, Bare f) →
        OnPublicFiles.K3OutRows h lm first (ν w) Reading.gl g F' := by
  intro z s y w hf hOk g F' hF hg hb
  have h1 := hf.1 (pr, "objects") hrun
  have hF' : s.fork? = some F' := (hA.fork s).symm.trans hF
  have hans : (Rd m).forms pr "objects" s = some { forms := g.rows.toList, late := [] } := by
    rw [hlink]
    exact OnPublicFiles.link_answers H l pr (by decide)
      (OnPublicFiles.objects_answers seat hA pass hpass hfind hF' hg hb)
  refine formsTQ_objects_outRows (Rd m) St (N.sent m 0) pr seat.heard h lm first (ν w)
    (seatTab cs arr ms w) s (fun R g' hR hg' => ?_)
    (fun a j ha hj => (hSt s _ j).trans (hDict a w j (hOk a ha) hj)) h1 g F' hF' hg
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  obtain rfl := Option.some.inj (hans.symm.trans hR)
  exact ⟨rfl, fun f hm => hm⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.formsTQ_objects_outRows
#print axioms VerifiableInference.Desc.Sound.formsT_objects_bare
