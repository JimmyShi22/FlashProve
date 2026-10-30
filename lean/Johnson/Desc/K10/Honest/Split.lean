-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Split.lean: THE CLOSING OF A SEGMENT (K10): ITS DECISION's GUARDS CUT IN
TWO: WHAT READS NO ROW's SUMMAND, AND THE REST: two tests with code at the kind's own record, and
the law that the decision says yes JUST IF the rounds have the kind's number and shape and both
tests say yes. Lemmas on the verifier's own text; no honest side's frame in them; none of the
library's goals.

  `shapeAtB`, `closeShapeB`   THE GUARDS THAT READ NO ROW's SUMMAND: nothing is owed; the frame's
                   link has a shape and a group; the closing is due; the frame names a mask's
                   message; the statement has the frame's group; the ground's clauses for
                   beginning the test; the place's count of rows is the number of rows that the
                   test takes in; the layout's k and h are the request's group's, and the place's
                   k; the fold's shape and its mask fit; the ground's clauses for spending the mask
  `closeValsB`   THE REST, which reads the open rows' and the sample rows' summands, and is handed
                   THE ELEMENT THAT "BAT" DREW: the batching returns a row at that element, and
                   that row fits the fold (`Own.batch`, Johnson/Desc/Own/Batch.lean;
                   `Own.foldRowFits`, Johnson/Desc/Own/Fold.lean). MOST OF WHAT IT CAN REFUSE ON
                   IS STRUCTURE TOO, OF THE ROWS: by these two files' own heads the batching's
                   refusals hang on numbers and sizes alone, and the row's fit asks numbers, sizes
                   and marks, but for THE KIND's ONE GUARD THAT COMPARES ELEMENTS of the field: a
                   written-out variable's pair against (1, 1). It also says no where the record
                   does not name the four (`baseData`: the link's shape, the link's group, the
                   mask, the statement's group), and where "BAT" drew other than one element
  `close_yes_split`   THE LAW, BOTH WAYS
  `split_of_base`     where the test `closeBaseB` (Johnson/Desc/K10/Honest/BaseB.lean) says yes:
                   the first test says yes, and the rest's at every list of rounds in which "BAT"
                   drew one element
  `Toy.split`    the two tests say yes at a small record

Limits. Of the block's decision at the kind's own record (lifted to the first chain's state:
Johnson/Desc/K10/Honest/Keeps.lean; the step: Step.lean, AtS.lean). WHETHER `closeValsB` HANGS ON
THE ELEMENT AT ALL is not said here: under `closeBaseB` it does not (`split_of_base`); cut into a
half on makes and one test on values at the batched row: `closeVals_cut`
(Johnson/Desc/K10/Honest/AtMakes.lean). Beneath the batching stand definitions that test an
element; that NO REFUSAL of it, at the closing's call, hangs on one is no theorem here or beneath
this file; over it: `batched_eq` (AtMakes.lean): where the record names its four the batching
returns just where a function of the rows' makes, the statement's shape and the group's number
returns. AtMakes.lean STANDS OVER THIS FILE AND OVER OTHER AUTHORS' FILES: a tree may hold this
file without it: what this head says of it is then said of no file of that tree. `closeShapeB`
reads the record itself, not a typed shape (that: Johnson/Desc/K10/Honest/OnShape.lean). Shown of
no honest run. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.BaseB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- The guards that read no row's summand, at given data. -/
def shapeAtB (P : Par) (s : Rec) (D : BaseData) : Bool :=
  s.owed.isNone &&
  decide (s.frame.next = .laterOrClose) && s.frame.moment == reqMoments D.L &&
  Ground.ok (Ground.beginRunL s.st s.frame.group) &&
  P.rows == (Slice.runRows s.st D.G).size &&
  (Own.layoutOf s.st D.G).k == D.Gq.k && (Own.layoutOf s.st D.G).h == D.Gq.h &&
  P.k == D.Gq.k &&
  Own.foldShapeFits (D.S1 s) (D.F s) && Own.foldMaskFits (D.S1 s) (D.F s) D.m &&
  Ground.ok (Ground.spendAsMaskL (D.S1 s) D.m)

/-- The data that the record names, if it names them. -/
def baseData (s : Rec) : Option BaseData :=
  match s.frame.shape.link[s.frame.link]?, s.frame.groups[s.frame.link]?, s.frame.mask,
      s.st.groups[s.frame.group]? with
  | some L, some Gq, some m, some G => some ⟨L, Gq, m, G⟩
  | _, _, _, _ => none

/-- **THE GUARDS THAT READ NO ROW's SUMMAND.** -/
def closeShapeB (P : Par) (s : Rec) : Bool :=
  match baseData s with
  | some D => shapeAtB P s D
  | none => false

/-- **THE REST**: the batching returns at what "BAT" drew, and the batched row fits the fold. No
where the record does not name the four, and where "BAT" drew other than one element. -/
def closeValsB (s : Rec) (rs : List Fmt.RoundView) : Bool :=
  match baseData s, batDraw rs with
  | some D, [t] =>
    match Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩
        (E.ofTriple t) with
    | some row => Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row
    | none => false
  | _, _ => false

/-- What `baseData` yields is what the record names. -/
theorem baseData_some {s : Rec} {D : BaseData} (h : baseData s = some D) :
    s.frame.shape.link[s.frame.link]? = some D.L ∧ s.frame.groups[s.frame.link]? = some D.Gq ∧
      s.frame.mask = some D.m ∧ s.st.groups[s.frame.group]? = some D.G := by
  unfold baseData at h
  split at h
  · rename_i L Gq m G h1 h2 h3 h4
    obtain rfl := Option.some.inj h
    exact ⟨h1, h2, h3, h4⟩
  · cases h

theorem baseData_of {s : Rec} {D : BaseData} (h1 : s.frame.shape.link[s.frame.link]? = some D.L)
    (h2 : s.frame.groups[s.frame.link]? = some D.Gq) (h3 : s.frame.mask = some D.m)
    (h4 : s.st.groups[s.frame.group]? = some D.G) : baseData s = some D := by
  unfold baseData
  rw [h1, h2, h3, h4]

/-- The record behind the beginning of the test, under the ground's clauses. -/
theorem begin_at {s : Rec} {G : Group} (hb : Ground.ok (Ground.beginRunL s.st s.frame.group) = true)
    (hG : s.st.groups[s.frame.group]? = some G) :
    Ground.beginRunP (onSt s.st) s.frame.group =
      some (⟨Own.layoutOf s.st G, Slice.runRows s.st G⟩,
        { onSt s.st with st := Slice.begun s.st s.frame.group G }) := by
  unfold Ground.beginRunP
  have hb' : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true := hb
  have ht : (onSt s.st).st.groups[s.frame.group]? = some G := hG
  rw [if_pos hb', ht]
  rfl

/-- The record behind the spending of the mask, under the ground's clauses. -/
theorem spend_at {S : Statement} {m : Nat} (hb : Ground.ok (Ground.spendAsMaskL S m) = true) :
    Ground.spendAsMaskP (onSt S) m = some { onSt S with st := spent S m } := by
  unfold Ground.spendAsMaskP
  have hb' : Ground.ok (Ground.spendAsMaskL (onSt S).st m) = true := hb
  rw [if_pos hb']
  rfl

/-- **THE FACTS IN FRONT, AT AN ELEMENT, ARE THE TWO TESTS.** -/
theorem front_iff (P : Par) (s : Rec) (t : Fmt.Ext) (rs : List Fmt.RoundView) (hd : batDraw rs = [t]) :
    (∃ D, CloseFront P s (E.ofTriple t) D) ↔ closeShapeB P s = true ∧ closeValsB s rs = true := by
  constructor
  · rintro ⟨D', H⟩
    have hb : Ground.ok (Ground.beginRunL s.st s.frame.group) = true :=
      List.all_eq_true.2 H.beginRun
    obtain ⟨G, hG⟩ : ∃ G, s.st.groups[s.frame.group]? = some G := by
      have := H.beginRun _ (List.mem_cons_self ..)
      exact Option.isSome_iff_exists.1 this
    have e := (begin_at hb hG).symm.trans H.layout
    obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e)
    have hD : baseData s = some ⟨D'.L, D'.G, D'.m, G⟩ := baseData_of H.link H.group H.mask hG
    have hst : D'.d.st = Slice.begun s.st s.frame.group G := by rw [← e2]
    have hF : D'.F s = (⟨D'.L, D'.G, D'.m, G⟩ : BaseData).F s := by
      unfold CloseData.F BaseData.F
      rw [← e1]
    have hs : Ground.ok (Ground.spendAsMaskL (Slice.begun s.st s.frame.group G) D'.m) = true :=
      List.all_eq_true.2 (hst ▸ H.spendAsMask)
    have hd2 : D'.d2.st = spent (Slice.begun s.st s.frame.group G) D'.m := by
      have := (spend_at hs).symm.trans (hst ▸ H.spent)
      rw [← Option.some.inj this]
    refine ⟨?_, ?_⟩
    · unfold closeShapeB
      rw [hD]
      show shapeAtB P s ⟨D'.L, D'.G, D'.m, G⟩ = true
      unfold shapeAtB
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none,
        and_assoc]
      have r1 := H.rows
      have r2 := H.kh
      rw [← e1] at r1 r2
      have s1 := H.shape
      have s2 := H.maskfits
      rw [hst, hF] at s1 s2
      exact ⟨H.owed, H.due.1, H.due.2, hb, r1, r2.1, r2.2, H.stretch, s1, s2, hs⟩
    · unfold closeValsB
      rw [hD, hd]
      have c := H.combine
      rw [hst, ← e1] at c
      show (match Own.batch (Slice.begun s.st s.frame.group G) s.frame.group
          ⟨Own.layoutOf s.st G, Slice.runRows s.st G⟩ (E.ofTriple t) with
        | some row => Own.foldRowFits (spent (Slice.begun s.st s.frame.group G) D'.m)
            ((⟨D'.L, D'.G, D'.m, G⟩ : BaseData).F s) row
        | none => false) = true
      rw [c]
      have s3 := H.rowfits
      rw [hd2, hF] at s3
      exact s3
  · rintro ⟨h1, h2⟩
    unfold closeShapeB at h1
    cases hD : baseData s with
    | none => rw [hD] at h1; cases h1
    | some D =>
      rw [hD] at h1
      obtain ⟨k1, k2, k3, k4⟩ := baseData_some hD
      have h1' : shapeAtB P s D = true := h1
      unfold shapeAtB at h1'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none,
        and_assoc] at h1'
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h1'
      unfold closeValsB at h2
      rw [hD, hd] at h2
      cases hr : Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩
          (E.ofTriple t) with
      | none =>
        have h2' : (match Own.batch (D.S1 s) s.frame.group
            ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩ (E.ofTriple t) with
          | some row => Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row
          | none => false) = true := h2
        rw [hr] at h2'
        cases h2'
      | some row =>
        have h2' : (match Own.batch (D.S1 s) s.frame.group
            ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩ (E.ofTriple t) with
          | some row => Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row
          | none => false) = true := h2
        rw [hr] at h2'
        exact ⟨⟨D.L, D.Gq, D.m, ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩,
          { onSt s.st with st := D.S1 s }, { onSt (D.S1 s) with st := spent (D.S1 s) D.m }, row⟩,
          a1, k1, k2, ⟨a2, a3⟩, k3, all_of_ok a4, begin_at a4 k4, a5, hr, ⟨a6, a7⟩, a8, a9, a10,
          all_of_ok a11, spend_at a11, h2'⟩

/-- **THE BLOCK's DECISION SAYS YES JUST IF** there are 2 + k rounds of the kind's shape, the first
test says yes of the record, and the rest's of the record and the rounds. -/
theorem close_yes_split {Cl : Type} (P : Par) (s : Rec) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s') ↔
      rs.length = 2 + P.k ∧ ShapedAll rs ∧ closeShapeB P s = true ∧ closeValsB s rs = true := by
  rw [close_yes_iff]
  constructor
  · rintro ⟨hl, hs, t, D, hd, H⟩
    exact ⟨hl, hs, (front_iff P s t rs hd).1 ⟨D, H⟩⟩
  · rintro ⟨hl, hs, h1, h2⟩
    obtain ⟨t, hd⟩ : ∃ t, batDraw rs = [t] := by
      unfold closeValsB at h2
      split at h2
      · rename_i D t _ hd
        exact ⟨t, hd⟩
      · cases h2
    obtain ⟨D, H⟩ := (front_iff P s t rs hd).2 ⟨h1, h2⟩
    exact ⟨hl, hs, t, D, hd, H⟩

/-- **Where `closeBaseB` says yes**: the first test says yes, and the rest's at every list
of rounds in which "BAT" drew one element. -/
theorem split_of_base {P : Par} {s : Rec} (h : closeBaseB P s = true) :
    closeShapeB P s = true ∧ ∀ rs t, batDraw rs = [t] → closeValsB s rs = true := by
  obtain ⟨D, H⟩ := closeBase_of h
  have key : ∀ rs t, batDraw rs = [t] → closeShapeB P s = true ∧ closeValsB s rs = true :=
    fun rs t hd => (front_iff P s t rs hd).1 (closeFront_all H (E.ofTriple t))
  exact ⟨(key [⟨[], ⟨[(0, 0, 0)], [], [], none⟩⟩] (0, 0, 0) rfl).1, fun rs t hd => (key rs t hd).2⟩

namespace Toy

/-- The two tests say yes at the small record of Johnson/Desc/K10/Honest/FrontToy.lean. -/
theorem split : closeShapeB P s = true ∧ ∀ rs t, batDraw rs = [t] → closeValsB s rs = true :=
  split_of_base base_member

end Toy

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.front_iff
#print axioms ProofFile.Honest.K10.YesFree.close_yes_split
#print axioms ProofFile.Honest.K10.YesFree.split_of_base
#print axioms ProofFile.Honest.K10.YesFree.Toy.split
