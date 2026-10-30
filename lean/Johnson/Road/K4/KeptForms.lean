-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/KeptForms.lean: CONDITIONAL: BEHIND AN ACCEPTING DECISION OF K4's SUB-PROTOCOL: FROM
THE SENTENCE FormsT (Johnson/Desc/Plain/K04Plain.lean) AND THE TABLE OF JOINTS' PUBLIC TEST formsInT
TO THE TABLE's SENTENCE formsTQ AT K4's TWO RUNS: the converse of `forms_kept`
(Johnson/Road/K4/FormsKept.lean). One statement with its proof. No new argument: that proof's steps
as they stand, with `line_forms` (Johnson/Road/K4/ItemOfForms.lean) in the stead of `forms_line`.

Not shown here. THAT THE FORMS ARE WORTH 0 ANYWHERE: FormsT is a hypothesis (h). No example of the
hypotheses together has been through Lean. Nothing on soundness, on completeness or on any other
property. s is the state in front of the accepting decision, s' the state behind it. The other
hypotheses are those of `forms_kept`, and P:
  K: what the decision leaves (`kept_atS` gives it wherever `(blockAtS p).decide` accepts).
  A: `KeptAsks`: tests on the state in front and the plan's public test.
  hN: the lookup's promise on the names of its pad.
  hB: the reads' array is there at s' (`readsArrayB`): no proof of it is known from the promise as
    the honest side's thread lays it.
  hs1, hs2: at s' the link's two runs do what the kind's sub-protocol's do (`StatesAt`).
  hk: the lookup states its own claims.
  X: at the reads' array the stated function's cells are the true entries (`StatedAt`).
  P: the table's public test at both runs: `formsInT_own` with `inT_ofLink`
    (Johnson/Road/K4/InT/FormsInTOwn.lean) give it, under `InTAsks`, four of whose clauses have no
    known proof from that promise either.

-/
import Johnson.Road.K4.FormsKept
import Johnson.Road.K4.ItemOfForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith)
open OnBytes.Desc.First.K4.Slots (back_there)
open OnBytes.Desc.First.K4.Reads (front_row0_named back_row0_named)
open OnBytes.Desc.First.K4.Total (KeptAsks runs_return_behind run_pub)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open OnBytes.Road.K4.InT (StatesAt kept_open)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles statesOfLink readersOfLink formsInT)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated second dataQ formsTQ)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)

/-- **THE JOIN THE OTHER WAY, OUT OF WHAT K4's SUB-PROTOCOL LEAVES WHERE IT ACCEPTS**, under K A hN
hB · hs1 hs2 hk · X · P · h. -/
theorem kept_forms {Wt : Type} {St : Stated} (M : S → Bound GQ → Mats GQ) (H : LinkHoles)
    (l : Link S Claim) (own : List (ℕ × ℕ)) (rd : Wt → ℕ × ℕ → MsgQ) (w : Wt) {p : Par} {s s' : S}
    {P₀ : Pub} {o₀ : Own} {tl : HTailF2} (K : KeptAtS p s s') (A : KeptAsks p s s' P₀ o₀)
    (hN : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F)
    (hB : readsArrayB p.hp s' = true) (hs1 : StatesAt (statesOfLink l) 2 p "front" s')
    (hs2 : StatesAt (statesOfLink l) 2 p "back" s') (hk : p.k3Runs = true)
    (X : ∀ A' o c, segAt? s' = some A' → s'.own? = some o → A'.L.arrayOf[o.v.iU3]? = some c →
      second s' c = true → StatedAt St M s' tl o c (p.hp.nU.getD 2 0) (dataQ own A' (rd w)))
    (P : ∀ q ∈ [(2, "front"), (2, "back")], formsInT (readersOfLink H l) own q.1 q.2 s' = true)
    (h : ∀ A', segAt? s' = some A' →
      FormsT seatS (semQ tl M s' fun w => dataQ own A' (rd w)) (frontRun p) formsBack s' w) :
    ∀ q ∈ [(2, "front"), (2, "back")], formsTQ (readersOfLink H l) St own q.1 q.2 s' (rd w) := by
  obtain ⟨a, a', fo, o, G, t, u, ha, hfo, ha', eF, eo, ho', hG', hh⟩ := kept_open K
  obtain ⟨l1, l2, l3⟩ := A.leaves a fo ha hfo
  have hF := A.sized a ha
  have hfree := A.free a ha
  obtain ⟨⟨ff, G₁, hf, fb', G₂', hb₁⟩, fb, G₂, hb⟩ := runs_return_behind (rows := !p.k3Runs)
    (Pr := p.P) (P₀ := P₀) (o₀ := o₀) hh rfl rfl
    ⟨hF, l1, l2, A.skel o ho', A.y₀, A.rd₀, A.member⟩ hfree l3
  have hf0 : formsFrontWith (!p.k3Runs) { p.P with tokv := s.tokv } p.g o G = some (ff, G₁) := by
    rw [run_pub (!p.k3Runs) p.P { p.P with tokv := s.tokv } p.g o G rfl rfl]
    exact hf
  have efo : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh
  have N : _root_.Fo.Tp.PadNames o.H.fo a.F := by
    rw [efo]
    exact hN a fo ha hfo
  have hL : Later a.F G := OnBytes.Desc.First.K4.hearFl_later hh
  have sG : PscRun.Sized G := hL.sized hF
  have L1 : Later G G₁ := OnBytes.Desc.First.K4.formsFrontWith_later hf
  have S1 : PscRun.Sized G₁ := L1.sized sG
  obtain ⟨A', hseg, _, eAL⟩ := segAt_lay ha'
  have R : ReadsArrayIs p.hp s' a' o := readsArray_gives hh ha' hB
  have hK := R.cols
  obtain ⟨c, hc', h2⟩ := R.name
  have r1 := front_row0_named hh hK N hf0
  have r2 := back_row0_named hh hK N hb
  have tb : G₂.trees = G.trees := back_trees sG hb
  have hfr : frontRun p o a'.F = some (ff, G₁) := by
    rw [eF]
    have : formsFrontWith (!p.k3Runs) p.P p.g o G = frontRun p o G := by
      rw [hk]
      rfl
    rw [← this]
    exact hf
  have hrow : ∀ (fs : Array Aff), (∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
      y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < p.hp.nU.getD 2 0) →
      ∀ f ∈ fs.toList, f.ents.all (VerifiableInference.Desc.K9.ownRow a'.F) = true := by
    intro fs r f hf'
    rw [Array.all_eq_true_iff_forall_mem]
    intro y hy
    obtain ⟨e1, e3, _⟩ := r f hf' y (Array.mem_toList_iff.mpr hy)
    have := R.ownRow y.idx y.coef
    rw [← e1, ← e3] at this
    exact this
  have hent : ∀ (G' : Fork), G'.trees = G.trees → ∀ (fs : Array Aff),
      (∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
        y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < p.hp.nU.getD 2 0) →
      ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList, Fork.hasEnt G'.trees y = true :=
    fun G' hG'' fs r f hf' y hy => by
      obtain ⟨e1, e3, e4⟩ := r f hf' y hy
      have := R.ents_same (F' := G') (by rw [hG'', eF]) y.idx y.coef e4
      rw [← e1, ← e3] at this
      exact this
  have hc : A'.L.arrayOf[o.v.iU3]? = some c := by
    rw [eAL]
    exact hc'
  exact line_forms M H l own rd w hs1 hs2 hk ha' eo hc'
    (fun A'' hA'' => X A'' o c hA'' ho' (by
      obtain rfl : A'' = A' := Option.some.inj (hA''.symm.trans hseg)
      exact hc) h2)
    (by rw [eF]; exact sG) hfr (by rw [eF]; exact hb) hb₁ (by rw [eF]; exact L1) S1
    (fun f hf' => there_of (back_there hF hh (fun _ h => h) sG hb f hf') (hent G₂ tb fb r2 f hf'))
    r1 r2 (hrow ff r1) (hrow fb r2) P h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.kept_forms
