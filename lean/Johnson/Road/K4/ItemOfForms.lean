-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ItemOfForms.lean: CONDITIONAL: FROM THE SENTENCE FormsT OF THE STATEMENT OF K4's LAW
(Johnson/Desc/Plain/K04Plain.lean) AND THE TABLE OF JOINTS' PUBLIC TEST formsInT
(Johnson/Desc/First/Batch/FormsIn.lean) TO THE TABLE's SENTENCE formsTQ AT K4's TWO RUNS
(Johnson/Desc/Sound/FormsQ.lean): the converses of `formsT_of_item`
(Johnson/Road/K4/FormsOfItem.lean) and of `forms_line` (Johnson/Road/K4/FormsLine.lean). Statements
and proofs. No new argument: the middle steps of these two proofs are equations (`value_stated`,
`worldOf_same`, `back_two`, `reader_front`, `reader_back`), read here the other way.

Not shown here. THAT THE FORMS ARE WORTH 0 ANYWHERE: FormsT is a hypothesis. No example of the
hypotheses together has been through Lean. Nothing on soundness, on completeness or on any other
property.
  * s is meant as the state BEHIND an accepting decision of K4's sub-protocol.
  * The other hypotheses are those of `forms_line`, less T1 and T2, which FormsT holds. The proof of
    `forms_kept` (Johnson/Road/K4/FormsKept.lean) derives them from one accepting decision.
  * P, the public test at both runs: `formsInT_own` with `inT_ofLink`
    (Johnson/Road/K4/InT/FormsInTOwn.lean) give it behind such a decision, under hypotheses of their
    own.

  `item_of_formsT`: under the hypotheses of `formsT_of_item`, less T1 and T2: where FormsT holds at
    the table's data (`semQ`), each form of the two runs is worth 0 in the forms' world at that
    run's late slots.
  `formsTQ_of`: the table's sentence at a run, of its parts: the segment's part, the reader's
    answer, the public test, and the worths.
  `line_forms`: THE JOIN: the table's sentence at both runs, at the readers of a link.

-/
import Johnson.Road.K4.FormsLine

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later hideRun_ok hideRun_later paid_later)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsBack_some blockAtC frontOf)
open OnBytes.Desc.First.K4.InT (reader_front reader_back segAt_lay)
open OnBytes.Road.K4.InT (StatesAt reader_pointwise)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (segAt? lateOf Read Readers LinkHoles readerOf statesOfLink
  readersOfLink ownRow formsInT)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated worldOwn dataQ formsTQ)
open VerifiableInference.Desc.Plain.K04 (thereAt FormsT frontRun)

variable {Wt : Type}

/-- **From FormsT to the worths in the forms' world**: the converse of `formsT_of_item`, under hs ho
hA hc X hF hS · hf hb hb₁ · L1 S1 · Tb · E1 E2. -/
theorem item_of_formsT {St : Stated} (M : S → Bound GQ → Mats GQ) (Dq : Wt → Bound GQ) {p : Par}
    {s : S} {b : LayOwn} {o : Own} {a : VerifiableInference.Desc.K9.Part} {c : ℕ × String}
    {tl : HTailF2} {n : ℕ} {F₁ Gb F₂ : Fork} {fs₁ fs₂ fs₂' : Array Aff} (w : Wt)
    (hs : s.here = .lay b) (ho : b.own = some o) (hA : a.L = b.L)
    (hc : b.L.arrayOf[o.v.iU3]? = some c) (X : StatedAt St M s tl o c n (Dq w)) (hF : a.F = b.F)
    (hS : PscRun.Sized b.F) (hf : frontRun p o b.F = some (fs₁, F₁))
    (hb : formsBack o b.F = some (fs₂, Gb)) (hb₁ : formsBack o F₁ = some (fs₂', F₂))
    (L1 : Later b.F F₁) (S1 : PscRun.Sized F₁)
    (Tb : ∀ f ∈ fs₂.toList, thereAt Gb f = true)
    (E1 : ∀ f ∈ fs₁.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (E2 : ∀ f ∈ fs₂.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (h : FormsT seatS (semQ tl M s Dq) (frontRun p) formsBack s w) :
    (∀ f ∈ fs₁.toList, f.value Reading.gl
      (worldOwn a (lateOf a.F F₁) (St.at1 s (Dq w))) = 0) ∧
    ∀ f ∈ fs₂.toList, f.value Reading.gl
      (worldOwn a (lateOf a.F Gb) (St.at1 s (Dq w))) = 0 := by
  obtain ⟨e2, hk⟩ := back_two hS S1 L1 hb hb₁
  rw [e2] at hb₁
  have hown : seatS.own s = some o := by
    show (match s.here with | .lay a => a.own | _ => none) = _
    rw [hs]
    exact ho
  have hfork : seatS.fork s = b.F := by
    show (match s.here with | .lay a => a.F | _ => {}) = _
    rw [hs]
  have SGb : PscRun.Sized Gb ∧ Later b.F Gb := by
    obtain ⟨A, _, ra, rfl⟩ := formsBack_some hb
    exact ⟨(hideRun_ok _ A _ _ _ hS ra).2.1, (hideRun_later hS ra).trans (paid_later A _)⟩
  obtain ⟨o', g₁, G₁, g₂, G₂, h1, h2, h3, h4, h5⟩ := h
  obtain rfl : o' = o := Option.some.inj (h1.symm.trans hown)
  rw [hfork, hf] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
  rw [hb₁] at h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h3)
  refine ⟨fun f hm => ?_, fun f hm => ?_⟩
  · rw [value_stated hA hc X (hF ▸ L1) (there_slots S1 (h4 f hm).1) (E1 f hm)]
    exact (h4 f hm).2
  · rw [value_stated hA hc X (hF ▸ SGb.2) (there_slots SGb.1 (Tb f hm)) (E2 f hm),
      ← worldOf_same _ _ fun x hx => ((hk x.1 (there_slots SGb.1 (Tb f hm) x hx).2).2)]
    exact (h5 f hm).2

/-- The table's sentence at a run, of its parts. -/
theorem formsTQ_of {Rd : Readers} {St : Stated} {own : List (ℕ × ℕ)} {b : ℕ} {name : String} {s : S}
    {rd : ℕ × ℕ → MsgQ} {A : VerifiableInference.Desc.K9.Part} {R : Read}
    (hA : segAt? s = some A) (hR : Rd.forms b name s = some R)
    (hP : formsInT Rd own b name s = true)
    (hv : ∀ f ∈ R.forms, f.value Reading.gl (worldOwn A R.late (St.at1 s (dataQ own A rd))) = 0) :
    formsTQ Rd St own b name s rd := by
  unfold formsInT at hP
  rw [hA, hR] at hP
  obtain ⟨hl, ha⟩ := Eq.mp (Bool.and_eq_true _ _) hP
  exact ⟨A, R, hA, hR, hl, fun f hm => ⟨List.all_eq_true.1 ha f hm, hv f hm⟩⟩

/-- **THE JOIN, THE OTHER WAY**, under hs1 hs2 hk · ha ho hc X hS · hf hb hb₁ · L1 S1 · Tb · E1 E2 ·
R1 R2 · P · h. -/
theorem line_forms {St : Stated} (M : S → Bound GQ → Mats GQ) (H : LinkHoles) (l : Link S Claim)
    (own : List (ℕ × ℕ)) (rd : Wt → ℕ × ℕ → MsgQ) (w : Wt) {p : Par} {s : S} {a : LayOwn} {o : Own}
    {tl : HTailF2} {c : ℕ × String} {n : ℕ} {F₁ Gb F₂ : Fork} {fs₁ fs₂ fs₂' : Array Aff}
    (hs1 : StatesAt (statesOfLink l) 2 p "front" s) (hs2 : StatesAt (statesOfLink l) 2 p "back" s)
    (hk : p.k3Runs = true)
    (ha : s.here = .lay a) (ho : a.own = some o) (hc : a.L.arrayOf[o.v.iU3]? = some c)
    (X : ∀ A, segAt? s = some A → StatedAt St M s tl o c n (dataQ own A (rd w)))
    (hS : PscRun.Sized a.F) (hf : frontRun p o a.F = some (fs₁, F₁))
    (hb : formsBack o a.F = some (fs₂, Gb)) (hb₁ : formsBack o F₁ = some (fs₂', F₂))
    (L1 : Later a.F F₁) (S1 : PscRun.Sized F₁)
    (Tb : ∀ f ∈ fs₂.toList, thereAt Gb f = true)
    (E1 : ∀ f ∈ fs₁.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (E2 : ∀ f ∈ fs₂.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (R1 : ∀ f ∈ fs₁.toList, f.ents.all (ownRow a.F) = true)
    (R2 : ∀ f ∈ fs₂.toList, f.ents.all (ownRow a.F) = true)
    (P : ∀ q ∈ [(2, "front"), (2, "back")], formsInT (readersOfLink H l) own q.1 q.2 s = true)
    (h : ∀ A, segAt? s = some A →
      FormsT seatS (semQ tl M s fun w => dataQ own A (rd w)) (frontRun p) formsBack s w) :
    ∀ q ∈ [(2, "front"), (2, "back")], formsTQ (readersOfLink H l) St own q.1 q.2 s (rd w) := by
  obtain ⟨A, hA, eF, eL⟩ := segAt_lay ha
  have hf' : frontOf p o a.F = some (fs₁, F₁) := by
    unfold frontOf
    rw [if_pos hk]
    exact hf
  have r1 := readers_some H l (b := 2) (name := "front") (by decide)
    ((reader_pointwise hs1).trans (reader_front rfl ha ho hf' R1))
  have r2 := readers_some H l (b := 2) (name := "back") (by decide)
    ((reader_pointwise hs2).trans (reader_back rfl ha ho hb R2))
  obtain ⟨v1, v2⟩ := item_of_formsT M (fun w => dataQ own A (rd w)) w ha ho eL hc (X A hA) eF hS hf
    hb hb₁ L1 S1 Tb E1 E2 (h A hA)
  rw [eF] at v1 v2
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact formsTQ_of hA r1 (P _ (by simp)) v1
  · obtain rfl := List.mem_singleton.1 hq
    exact formsTQ_of hA r2 (P _ (by simp)) v2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.item_of_formsT
#print axioms OnBytes.Road.K4.formsTQ_of
#print axioms OnBytes.Road.K4.line_forms
