-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsObjects.lean: The kind "lookup" (K3): FROM THE TABLE OF JOINTS' SENTENCE
"the forms of the run objects are worth 0" (formsQ, Johnson/Desc/Sound/FormsQ.lean)
TO THE FIRST ITEM OF THE LOOKUP's ROW OUT (K3OutRows, Johnson/Top/H/K3RowOut.lean): under
two named premises: the reader's law; one equation on the segment's mask row. Statements and
proofs.

OBJECT: formsQ at a run "objects"; K3OutRows.
Used by Johnson/Top/H/Keep/FormsInObjects.lean, Johnson/Top/H/Keep/FormsInTObjects.lean,
  Johnson/Top/H/Keep/FormsObjectsLink.lean and 1 more.
LETTERS: Rd0, own, pr, heard, h, lm, first, nu, rd, s free.
Compiled with the whole library.

Main names:
  rowRes_masks: a row of the lookup's typed ends reads a reading of the places at the masks alone.
  outRows_of_rows: where every form of g.rows is worth 0 in the world of a ledger later than F', at
    the masks that nu reads and any entries: K3OutRows h lm first nu gl g F'. h IS FREE: nothing
    asks that it is g.shape.
  fork_of_segAt: what segAt? reads as the ledger is the record's own.
  formsQ_objects_outRows: THE END, at the sentence itself: no filling of the table's letters enters.
  objects_named: at the table's own map of names, at each sort of segment and both lookups, the item
    "objects" stands for the driver's run "objects" of the block in front.

Limits. TWO PREMISES STAY: hRd: the run's reader gives, where something was heard, no late slot and
every form of g.rows (paid at a link's readers: Johnson/Top/H/Keep/ReaderIsRun.lean) · hDict: entry
j of the mask row as the sentence reads it off the witness is what nu reads at the place "mask j",
below the ledger's number of slots. Nothing on "planes" or "keys".
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Borders
import Johnson.Top.H.K3RowOut
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open Cb.Fo.PlaneClaims (onMasks_rows)

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- A row of the typed ends reads the places at the masks alone. -/
theorem rowRes_masks (h : Forest.Shape) (lm first : ℕ) (rs : Rounds K) (ν : _root_.Fo.Pl → K)
    (r : SRow _root_.Fo.Pl K) (hr : r ∈ (endsOf h lm first rs).rows) :
    rowRes (muOf fun j => ν (.mask j)) r = rowRes ν r := by
  unfold rowRes
  rw [evalL_muOf (onMasks_rows h lm first rs r hr) ν]

/-- **The rows' forms worth 0 give the first item of the row out.** -/
theorem outRows_of_rows (h : Forest.Shape) (lm first : ℕ) (ν : _root_.Fo.Pl → K) (g : Heard)
    (F' H : Fork) (hH : _root_.Fo.Later F' H) (entry : ℕ → ℕ → ℕ → K)
    (hz : ∀ f ∈ g.rows.toList, f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) :
    K3OutRows h lm first ν ρ g F' := by
  intro rs hI y hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < g.rows.size := by rw [hI.nRows]; exact hi
  have e := hI.rows i hi' H hH (fun j => ν (.mask j)) entry
  have e1 : g.rows.getD i {} = g.rows[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
    rfl
  have e2 : (endsOf h lm first rs).rows.getD i ⟨[], 0⟩ = (endsOf h lm first rs).rows[i] :=
    List.getD_eq_getElem _ _ hi
  rw [e1, e2] at e
  have hm : g.rows[i] ∈ g.rows.toList := by
    rw [← Array.getElem_toList (h := by simpa using hi')]
    exact List.getElem_mem _
  rw [hz _ hm] at e
  rw [← rowRes_masks h lm first rs ν _ hr]
  exact e.symm

end

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp S)
open VerifiableInference.Desc.K9 (Readers segAt?)

/-- What segAt? reads as the ledger is the record's own. -/
theorem fork_of_segAt {s : S} {a : K9.Part} (h : segAt? s = some a) : s.fork? = some a.F := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        rw [← h]

/-- **THE END, AT THE SENTENCE ITSELF.** -/
theorem formsQ_objects_outRows (Rd0 : Readers) (own : List (ℕ × ℕ)) (pr : ℕ)
    (heard : S → Option Forest.Heard) (h : Forest.Shape) (lm first : ℕ) (ν : _root_.Fo.Pl → GQ)
    (rd : ℕ × ℕ → MsgQ) (s : S)
    (hRd : ∀ R g, Rd0.forms pr "objects" s = some R → heard s = some g →
      R.late = [] ∧ ∀ f ∈ g.rows.toList, f ∈ R.forms)
    (hDict : ∀ a j, segAt? s = some a → j < a.F.ns → (dataQ own a rd).mask j = ν (.mask j))
    (hf : formsQ Rd0 own pr "objects" s rd) :
    ∀ g F', s.fork? = some F' → heard s = some g →
      OnPublicFiles.K3OutRows h lm first ν Reading.gl g F' := by
  intro g F' hF hg
  obtain ⟨a, R, ha, hR, _, hv⟩ := hf
  obtain ⟨hl, hm⟩ := hRd R g hR hg
  obtain rfl : a.F = F' := Option.some.inj ((fork_of_segAt ha).symm.trans hF)
  refine OnPublicFiles.outRows_of_rows Reading.gl h lm first ν g a.F a.F (_root_.Fo.Later.refl _)
    (worldOwn a [] (dataQ own a rd)).entry fun f hfm => ?_
  obtain ⟨hA, h0⟩ := hv f (hm f hfm)
  rw [hl] at h0 hA
  rw [← h0]
  refine value_eq _ _ f (fun _ _ => rfl) fun x hx => ?_
  have hlt : x.1 < a.F.ns := by
    unfold K9.affIn at hA
    have h1 := (Eq.mp (Bool.and_eq_true _ _) hA).2
    have h2 := List.all_eq_true.1 h1 x hx
    unfold K9.slotIn at h2
    exact of_decide_eq_true (Eq.mp (Bool.and_eq_true _ _) h2).1
  show Reading.gl.val (a.F.vp.getD x.1 zeroE) - Reading.gl.val (a.F.mf.getD x.1 zeroE) *
      ν (.mask x.1) = slotW a.F [] (dataQ own a rd).mask x.1
  rw [slotW_ledger a.F [] _ x.1 rfl, hDict a x.1 ha hlt]

/-- **(P1) at the table's own map of names**: at each sort of segment the item "objects" of either
lookup stands for the driver's run "objects" of the block in front. -/
theorem objects_named (sub : ModelPart) :
    (1 + First.shift sub, "objects") ∈ First.runsOf sub (2 + First.shift sub) "objects" ∧
      (6 + First.shift sub, "objects") ∈ First.runsOf sub (7 + First.shift sub) "objects" := by
  cases sub <;> decide

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.OnPublicFiles.outRows_of_rows
#print axioms VerifiableInference.Desc.Sound.formsQ_objects_outRows
#print axioms VerifiableInference.Desc.Sound.objects_named
