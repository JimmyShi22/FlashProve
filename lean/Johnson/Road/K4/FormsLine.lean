-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsLine.lean: THE JOIN: FROM THE TABLE OF JOINTS' SENTENCE formsTQ AT K4's TWO
RUNS (Johnson/Desc/Sound/FormsQ.lean), AT THE READERS OF A LINK
(Johnson/Desc/First/Batch/ReadersOfLink.lean: the reader is the run itself) AND AT EVERY LETTER St
WITH StatedAt (Johnson/Road/K4/FillStated.lean), TO THE SENTENCE FormsT OF THE STATEMENT OF K4's LAW
(Johnson/Desc/Plain/K04Plain.lean).

  `readers_some`: where the generic reader answers under a name that is not the approximate range
    proof's, the link's reader gives that answer.
  `item_forms`: what formsTQ says at a run whose reader's answer is known: each of these forms is
    worth 0 in the forms' world at these late slots, at the part that segAt? finds.
  `forms_line`: THE JOIN.
No new argument: reader_front, reader_back, segAt_lay (Johnson/Road/K4/InT/ReaderAtK4.lean);
reader_pointwise (Johnson/Road/K4/InT/FormsInTOwn.lean); formsT_of_item
(Johnson/Road/K4/FormsOfItem.lean).
Limits. THE CONCLUSION IS AT semQ, WHICH HANGS ON THE VERIFIER's STATE: no filling of the law's
letter Sem: formsT_sem carries it on (FormsOfItem.lean). PREMISES of forms_line, each with its
payer:
  hs1, hs2: THE SEAT's TIE, POINTWISE (StatesAt, Johnson/Road/K4/InT/Statement.lean): at the state s
    the run that sub-protocol number 2 of the link states under the name does what blockAtC p's
    does. No equation of lists of functions: at the term that is seated each run stands under a
    wrapper that rejects where the run has written the seat. That the seated term meets it: by
    nobody yet.
  hk: the place's parameters let the lookup state its own claims.
  ha, ho: the verifier's state stands in a layers' link and holds what was heard: kept where K4's
    sub-protocol has accepted.
  hc: the reads' array has a name in the link's list: by nobody.
  X: StatedAt: at that array, in row 0, below n, St's cells are entryTrue, its mask row the data's
    (statedAt_of has it of Stated.of u where u gives uLay's cells there and the array is of the
    second sending: by nobody).
  hS: the ledger has arrays of the right sizes: the table's item on the ledger.
  hf, hb, hb₁: the three returns: the law that both listings return (Johnson/Road/K4/Total/), which
    stands under a member.
  L1, S1: "front" leaves a later ledger with arrays of the right sizes: library laws on the run.
  T1, Tb, T2: each form is there at its ledger: Johnson/Road/K4/Slots/RunsThere.lean and kin.
  E1, E2: each entry has the reads' number, row 0 and a place below n (meant: the public parameters'
    length of the reads): Johnson/Road/K4/Reads/RowZero.lean, under the lookup's promise and the
    line on the public parameters named at R1, R2.
  R1, R2: each entry names row 0 of an array with one own row: hangs on a line on the public
    parameters that nobody pays (their length of the reads is at most the array's number of
    columns).
  I: the item, at both runs.
None is called here. WHERE THE LINE IS CALLED ITS CALLER HAS THE PROMISE BEHIND AND THE ITEM IN
HAND, NO ACCEPTING RUN: so all but I must lie in that promise: laid there by nobody yet. M is a
letter. NOT HERE: that the forms are worth 0 anywhere. Met through Lean at no member. K04_law, the
law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FormsOfItem
import Johnson.Road.K4.InT.FormsInTOwn
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par seatS formsBack blockAtC frontOf)
open OnBytes.Desc.First.K4.InT (reader_front reader_back segAt_lay)
open OnBytes.Road.K4.InT (StatesAt reader_pointwise)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (segAt? lateOf Read Readers LinkHoles readerOf statesOfLink
  readersOfLink ownRow)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated second worldOwn dataQ formsTQ)
open VerifiableInference.Desc.Plain.K04 (thereAt FormsT frontRun)

/-- Where the generic reader answers, the link's reader gives that answer. -/
theorem readers_some (H : LinkHoles) (l : Link S Claim) {b : ℕ} {name : String} {s : S} {R : Read}
    (hn : (name == "K8.equations") = false) (h : readerOf (statesOfLink l) b name s = some R) :
    (readersOfLink H l).forms b name s = some R := by
  show (if (name == "K8.equations") = true then H.small s
    else match readerOf (statesOfLink l) b name s with
      | some R => some R
      | Option.none => H.silent b name s) = some R
  rw [if_neg (by rw [hn]; exact Bool.false_ne_true), h]

/-- What the sentence says at a run whose reader's answer is known. -/
theorem item_forms {Rd : Readers} {St : Stated} {own : List (ℕ × ℕ)} {b : ℕ} {name : String} {s : S}
    {rd : ℕ × ℕ → MsgQ} {A : VerifiableInference.Desc.K9.Part} {R : Read}
    (hA : segAt? s = some A) (hR : Rd.forms b name s = some R)
    (h : formsTQ Rd St own b name s rd) :
    ∀ f ∈ R.forms, f.value Reading.gl (worldOwn A R.late (St.at1 s (dataQ own A rd))) = 0 := by
  obtain ⟨A', R', hA', hR', _, hf⟩ := h
  obtain rfl : A' = A := Option.some.inj (hA'.symm.trans hA)
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  exact fun f hm => (hf f hm).2

/-- **THE JOIN**, under hs1 hs2 hk · ha ho hc X hS · hf hb hb₁ · L1 S1 · T1 Tb T2 · E1 E2 · R1 R2 ·
I. -/
theorem forms_line {Wt : Type} {St : Stated} (M : S → Bound GQ → Mats GQ) (H : LinkHoles)
    (l : Link S Claim)
    (own : List (ℕ × ℕ)) (rd : Wt → ℕ × ℕ → MsgQ) (w : Wt) {p : Par} {s : S} {a : LayOwn} {o : Own}
    {tl : HTailF2} {c : ℕ × String} {n : ℕ} {F₁ Gb F₂ : Fork} {fs₁ fs₂ fs₂' : Array Aff}
    (hs1 : StatesAt (statesOfLink l) 2 p "front" s) (hs2 : StatesAt (statesOfLink l) 2 p "back" s)
    (hk : p.k3Runs = true)
    (ha : s.here = .lay a) (ho : a.own = some o) (hc : a.L.arrayOf[o.v.iU3]? = some c)
    (X : ∀ A, segAt? s = some A → StatedAt St M s tl o c n (dataQ own A (rd w)))
    (hS : PscRun.Sized a.F) (hf : frontRun p o a.F = some (fs₁, F₁))
    (hb : formsBack o a.F = some (fs₂, Gb)) (hb₁ : formsBack o F₁ = some (fs₂', F₂))
    (L1 : Later a.F F₁) (S1 : PscRun.Sized F₁)
    (T1 : ∀ f ∈ fs₁.toList, thereAt F₁ f = true) (Tb : ∀ f ∈ fs₂.toList, thereAt Gb f = true)
    (T2 : ∀ f ∈ fs₂.toList, thereAt F₂ f = true)
    (E1 : ∀ f ∈ fs₁.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (E2 : ∀ f ∈ fs₂.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n)
    (R1 : ∀ f ∈ fs₁.toList, f.ents.all (ownRow a.F) = true)
    (R2 : ∀ f ∈ fs₂.toList, f.ents.all (ownRow a.F) = true)
    (I : ∀ q ∈ [(2, "front"), (2, "back")],
      formsTQ (readersOfLink H l) St own q.1 q.2 s (rd w)) :
    ∃ A, segAt? s = some A ∧
      FormsT seatS (semQ tl M s fun w => dataQ own A (rd w)) (frontRun p) formsBack s w := by
  obtain ⟨A, hA, eF, eL⟩ := segAt_lay ha
  have hf' : frontOf p o a.F = some (fs₁, F₁) := by
    unfold frontOf
    rw [if_pos hk]
    exact hf
  have r1 := readers_some H l (b := 2) (name := "front") (by decide)
    ((reader_pointwise hs1).trans (reader_front rfl ha ho hf' R1))
  have r2 := readers_some H l (b := 2) (name := "back") (by decide)
    ((reader_pointwise hs2).trans (reader_back rfl ha ho hb R2))
  have i1 := item_forms hA r1 (I (2, "front") (by simp))
  have i2 := item_forms hA r2 (I (2, "back") (by simp))
  refine ⟨A, hA, formsT_of_item M (fun w => dataQ own A (rd w)) w ha ho eL hc (X A hA) eF hS hf hb
    hb₁ L1 S1 T1 Tb T2 E1 E2 ?_ ?_⟩
  · rw [eF]
    exact i1
  · rw [eF]
    exact i2

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.readers_some
#print axioms OnBytes.Road.K4.item_forms
#print axioms OnBytes.Road.K4.forms_line
