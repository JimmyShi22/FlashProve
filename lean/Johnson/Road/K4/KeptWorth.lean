-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/KeptWorth.lean: CONDITIONAL: BEHIND AN ACCEPTING DECISION OF K4's SUB-PROTOCOL THE
SENTENCE FormsT (Johnson/Desc/Plain/K04Plain.lean) COMES DOWN TO THE FORMS' WORTHS AND TO FOUR
HYPOTHESES (A hN hB hk): that both runs return, and that every form names only what is there at its
ledger, are drawn from these four and the decision. THE DEBT IS MOVED THERE, NOT PAID: A holds, as
one of its fields, that the listing "front" returns at another structure of the same skeleton; one
field of A and hB speak of the state BEHIND the decision; hN is the lookup's. One statement with its
proof. No new argument: the steps by which the proof of `forms_kept`
(Johnson/Road/K4/FormsKept.lean) derives these same facts.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: h1 and h2 are hypotheses. No example of the
hypotheses together has been through Lean. Nothing on soundness, on completeness or on any other
property. s is the state in front of the accepting decision, s' the state behind it. General in the
reading Sm of the mask row and of the reads' true entries.
  K A hN hB hk: as in `kept_forms` (Johnson/Road/K4/KeptForms.lean), whose head says what each is.
  h1: each form that the run "front" leaves is worth 0 in the world of the ledger that "front"
    leaves.
  h2: each form that the run "back" leaves, run from that ledger, is worth 0 in the world of the
    ledger that "back" leaves.

-/
import Johnson.Road.K4.FormsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith)
open OnBytes.Desc.First.K4.Slots (front_there_named back_there)
open OnBytes.Desc.First.K4.Reads (front_row0_named back_row0_named)
open OnBytes.Desc.First.K4.Total (KeptAsks runs_return_behind run_pub)
open OnBytes.Road.K4.InT (kept_open)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Plain.K04 (Sem FormsT frontRun)

/-- **FormsT behind an accepting decision, from the forms' worths**, under K A hN hB hk · h1 h2. -/
theorem kept_formsT {Wt : Type} (Sm : Sem Wt) (w : Wt) {p : Par} {s s' : S} {P₀ : Pub} {o₀ : Own}
    (K : KeptAtS p s s') (A : KeptAsks p s s' P₀ o₀)
    (hN : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F)
    (hB : readsArrayB p.hp s' = true) (hk : p.k3Runs = true)
    (h1 : ∀ o fs₁ F₁, seatS.own s' = some o → frontRun p o (seatS.fork s') = some (fs₁, F₁) →
      ∀ f ∈ fs₁.toList,
        Aff.value Reading.gl (F₁.worldOf Reading.gl (Sm.mask w) (Sm.entryT o w)) f = 0)
    (h2 : ∀ o fs₁ F₁ fs₂ F₂, seatS.own s' = some o →
      frontRun p o (seatS.fork s') = some (fs₁, F₁) → formsBack o F₁ = some (fs₂, F₂) →
      ∀ f ∈ fs₂.toList,
        Aff.value Reading.gl (F₂.worldOf Reading.gl (Sm.mask w) (Sm.entryT o w)) f = 0) :
    FormsT seatS Sm (frontRun p) formsBack s' w := by
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
  have R : ReadsArrayIs p.hp s' a' o := readsArray_gives hh ha' hB
  have hK := R.cols
  have r1 := front_row0_named hh hK N hf0
  have r2 := back_row0_named hh hK N hb
  have e2 : fb' = fb := (back_two sG S1 L1 hb hb₁).1
  rw [e2] at hb₁
  have t1 : G₁.trees = G.trees := front_trees sG hf
  have t2 : G₂'.trees = G.trees := (back_trees S1 hb₁).trans t1
  have hown : seatS.own s' = some o := by
    show (match s'.here with | .lay a => a.own | _ => none) = _
    rw [ha']
    exact eo
  have hfork : seatS.fork s' = G := by
    show (match s'.here with | .lay a => a.F | _ => {}) = _
    rw [ha']
    exact eF
  have hfr : frontRun p o (seatS.fork s') = some (ff, G₁) := by
    rw [hfork]
    have : formsFrontWith (!p.k3Runs) p.P p.g o G = frontRun p o G := by
      rw [hk]
      rfl
    rw [← this]
    exact hf
  have hent : ∀ (G' : Fork), G'.trees = G.trees → ∀ (fs : Array Aff),
      (∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
        y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < p.hp.nU.getD 2 0) →
      ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList, Fork.hasEnt G'.trees y = true :=
    fun G' hG'' fs r f hf' y hy => by
      obtain ⟨e1, e3, e4⟩ := r f hf' y hy
      have := R.ents_same (F' := G') (by rw [hG'', eF]) y.idx y.coef e4
      rw [← e1, ← e3] at this
      exact this
  exact ⟨o, ff, G₁, fb, G₂', hown, hfr, hb₁,
    fun f hf' => ⟨there_of (front_there_named hF hh (fun _ h => h) sG N hf0 f hf')
      (hent G₁ t1 ff r1 f hf'), h1 o ff G₁ hown hfr f hf'⟩,
    fun f hf' => ⟨there_of (back_there hF hh (fun j h => (L1.keep j h).1) S1 hb₁ f hf')
      (hent G₂' t2 fb r2 f hf'), h2 o ff G₁ fb G₂' hown hfr hb₁ f hf'⟩⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.kept_formsT
