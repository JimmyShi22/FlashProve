-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttEnds.lean: AT AN ATTENTION LINK THE TWO CELLS behind AND cleared GO ALIKE
AT TWO RECORDS THAT MEET SameRead.

* behind_att_rel: member 14 l + 10, l odd: RelX in front, RelX behind.
* cleared_att_rel: member 14 l + 14, l odd: RelX in front, EQUALITY behind: the step lays look and
  lookHeard down and reads neither.

Limits. Implications under SameRead. Nothing says that a step returns. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.AttNums
import Johnson.AtFull.Shape.Scope.AttChain
import Johnson.AtFull.Shape.Scope.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope.Ends
open Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape (ChainSh HeardAll)
open VerifiableInference.Desc.First.TailClaims.Law.Tests (lsTailG lsTailU testsGC partB behindG)
open VerifiableInference.Desc.K9 (testsWhere)
open VerifiableInference.Desc.K9.Shape (gTw)
open Johnson.Desc.First.Walk.Shape (leaveSh clearAttG clearAttB)

variable {X X₀ : Verify.Public}

/-- leaveSh at a shape whose link is open, laid out. -/
theorem leaveSh_is (c : ChainSh) {L : VerifiableInference.Desc.First.Shape.LinkSh}
    (hc : c.link = some L) :
    leaveSh c = ChainSh.mk c.marked 0 none none none c.rowsOwed c.core c.reply c.indexMasks c.pile
      c.atEnd L.check none none none c.own c.head none c.fin := by
  obtain ⟨m, h, tl, led, tb, ro, co, rp, im, pl, ae, ck, lk, lo, lh, ow, hd, at', fi⟩ := c
  obtain rfl : lk = some L := hc
  rfl

/-- At an odd link the step is a blind one, or there is no cell. -/
theorem behind_att_alike {l : Nat} (ho : l % 2 = 1) {a a' : ShA} (r : RelX X X₀ a a') :
    Alike (RelX X X₀) ((TabL.behind (LW X₀) l).1 a) ((TabL.behind (LW X₀) l).1 a') := by
  have c : (l % 2 == 0 && l != 24) = false := by
    rw [ho]
    rfl
  unfold TabL.behind
  cases (LW X₀).k8 l with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some p8 =>
    cases testsWhere (LW X₀).XZ l 0 with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some w =>
      simp only [c, if_false, Bool.false_eq_true]
      exact blind_alike (behindG_blind (gTw_strip w) p8.nU) r

/-- **behind, AT AN ATTENTION LINK.** -/
theorem behind_att_rel (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 9 + 1) ((TabL.linkRow (LW X) l).at 9) ((TabL.linkRow (LW X₀) l).at 9) := by
  intro a a' h
  have o1 : oddAt (14 * l + 9 + 1) = true := by
    rw [oddAt_place hl (by omega)]
    simp [ho]
  have o2 : oddAt (14 * l + 9 + 1 + 1) = true := by
    rw [oddAt_inside hl (by omega)]
    exact o1
  have hr : RelX X X₀ a a' := by
    unfold RelAt at h
    rw [if_pos o1] at h
    exact h
  show Alike _ ((TabL.behind (LW X) l).1 a) ((TabL.behind (LW X₀) l).1 a')
  rw [behind_same S l]
  rcases behind_att_alike (X := X) ho hr with ⟨b, b', e1, e2, r⟩ | n
  · refine Or.inl ⟨b, b', e1, e2, ?_⟩
    unfold RelAt
    rw [if_pos o2]
    exact r
  · exact Or.inr n

/-- The step at two shapes in RelX: both return one shape, or both refuse. -/
theorem clearAtt_alike (Y : Johnson.Desc.First.Walk.LinkPub) (n m : Nat) {a a' : ShA}
    (r : RelX X X₀ a a') :
    Alike (RelAt X X₀ m) (liftQ (clearAttG Y n) a) (liftQ (clearAttG Y n) a') := by
  have hb : clearAttB Y n a.1 = clearAttB Y n a'.1 := by
    unfold clearAttB
    rw [r.link, r.led, r.tl, r.here, r.marked]
  unfold liftQ clearAttG
  cases hc : clearAttB Y n a'.1 with
  | false =>
    rw [hb, hc]
    exact Or.inr ⟨rfl, rfl⟩
  | true =>
    rw [hb, hc]
    have hL : ∃ L, a'.1.link = some L := by
      unfold clearAttB at hc
      cases e : a'.1.link with
      | none =>
        rw [e] at hc
        cases hc
      | some L => exact ⟨L, rfl⟩
    obtain ⟨L, hL⟩ := hL
    have hL' : a.1.link = some L := by rw [r.link]; exact hL
    refine Or.inl ⟨_, _, rfl, rfl, relAt_of_eq ?_⟩
    show (leaveSh a.1, a.2) = (leaveSh a'.1, a'.2)
    rw [leaveSh_is a.1 hL', leaveSh_is a'.1 hL, r.marked, r.rowsOwed, r.core, r.reply, r.indexMasks,
      r.pile, r.atEnd, r.own, r.head, r.fin, r.forms]

/-- **cleared, AT AN ATTENTION LINK**: from RelX to equality. -/
theorem cleared_att_rel (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 13 + 1) ((TabL.linkRow (LW X) l).at 13)
      ((TabL.linkRow (LW X₀) l).at 13) := by
  intro a a' h
  have o1 : oddAt (14 * l + 13 + 1) = true := by
    rw [oddAt_place hl (by omega)]
    simp [ho]
  have r : RelX X X₀ a a' := by
    unfold RelAt at h
    rw [if_pos o1] at h
    exact h
  have hL : (LW X).links = (LW X₀).links := links_same S
  have c1 : (l == 24) = false := by
    have : l ≠ 24 := by omega
    simpa using this
  have c2 : (l % 2 == 1) = true := by simpa using ho
  show Alike _ ((TabL.cleared (LW X) l).1 a) ((TabL.cleared (LW X₀) l).1 a')
  unfold TabL.cleared
  rw [hL]
  cases hY : (LW X₀).links[l]? with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some Y =>
    simp only [c1, c2, if_true, Bool.false_eq_true, if_false]
    have ha := atA_map S Y.g (fun p => p.nLin) fun _ => rfl
    have hx : (LW X).XZ.A[Y.g]? = X.A[Y.g]? := rfl
    have hx₀ : (LW X₀).XZ.A[Y.g]? = X₀.A[Y.g]? := rfl
    rw [hx, hx₀]
    cases h1 : X.A[Y.g]? with
    | none =>
      cases h2 : X₀.A[Y.g]? with
      | none => exact Or.inr ⟨rfl, rfl⟩
      | some p₀ =>
        rw [h1, h2] at ha
        cases ha
    | some p =>
      cases h2 : X₀.A[Y.g]? with
      | none =>
        rw [h1, h2] at ha
        cases ha
      | some p₀ =>
        rw [h1, h2] at ha
        have e : p.nLin = p₀.nLin := Option.some.inj ha
        simp only [e]
        exact clearAtt_alike _ _ _ r

end Johnson.AtFull.Shape.Scope.Ends

#print axioms Johnson.AtFull.Shape.Scope.Ends.behind_att_rel
#print axioms Johnson.AtFull.Shape.Scope.Ends.cleared_att_rel
