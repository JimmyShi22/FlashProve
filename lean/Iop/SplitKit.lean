-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SplitKit.lean: ready-made splits for Iop/Split.lean and Iop/BatchSplit.lean.

  `RCut.ofBool h f pl`: for a round whose oracle is a string: the positions with f p = true are the
      first part; pl splits the plain part. The parts are strings over subtypes of the positions, so
      that no symbol is ever transported along an equation; that their oracles are strings is shown
      by plain terms (`RCut.ofBoolFst`, `RCut.ofBoolSnd`).
  `ACut.ofSlot`, `ACut.ofShared`: a split of a round that is sent whole by the slots, or whole in
      the shared component (`RAnn.ofSlot`, `RAnn.ofShared`: every round of the protocols of Blocks/
      is of one of these two sorts): the parts are of the same sort. The remainder is again
      annotated by `RAnn.ofSlot` or `RAnn.ofShared`, by definition, so that it can be split again.
  the conditions (`.._ok`), and `RoundSplits.endPhase`: the phase (`FPhase`, Iop/BatchFmt.lean: where a
      round is in the pattern of local and shared rounds) after an annotated list of rounds.

Limits: nothing on the protocols of an instantiation.
-/
import Iop.BatchSplit
import Iop.SplitProofs

namespace Iop

/-! ## 2. Splits of a round with a string oracle -/

/-- A type is the sum of the two parts into which a Bool-valued function divides it. -/
def sumOfBool {α : Type} (f : α → Bool) : {p // f p = true} ⊕ {p // f p = false} ≃ α where
  toFun := fun z => match z with
    | .inl p => p.1
    | .inr p => p.1
  invFun := fun p =>
    if h : f p = true then .inl ⟨p, h⟩ else .inr ⟨p, Bool.eq_false_of_not_eq_true h⟩
  left_inv := by
    rintro (⟨p, h⟩ | ⟨p, h⟩)
    · exact dif_pos h
    · exact dif_neg (by rw [h]; exact Bool.false_ne_true)
  right_inv := fun p => by
    beta_reduce
    by_cases h : f p = true
    · rw [dif_pos h]
    · rw [dif_neg h]

variable {r : Round}

/-- a string of r from its symbols on the two parts -/
def mixOfBool (f : r.Pos → Bool) (a : ∀ p : {p // f p = true}, r.Sym p.1)
    (b : ∀ p : {p // f p = false}, r.Sym p.1) : ∀ p, r.Sym p :=
  fun p => if h : f p = true then a ⟨p, h⟩ else b ⟨p, Bool.eq_false_of_not_eq_true h⟩

/-- The positions with f p = true are the first part; pl splits the plain part. -/
def RCut.ofBool (h : r.IsPoint) (f : r.Pos → Bool) {PA PB : Type} (pl : r.Plain ≃ PA × PB) :
    RCut r where
  OrcA := ∀ p : {p // f p = true}, r.Sym p.1
  OrcB := ∀ p : {p // f p = false}, r.Sym p.1
  PosA := {p // f p = true}
  PosB := {p // f p = false}
  PlainA := PA
  PlainB := PB
  orc :=
    { toFun := fun o => (fun p => r.rd o p.1, fun p => r.rd o p.1)
      invFun := fun z => h.ofSyms (mixOfBool f z.1 z.2)
      left_inv := fun o => by
        have e : mixOfBool f (fun p => r.rd o p.1) (fun p => r.rd o p.1) = r.rd o := by
          funext p
          unfold mixOfBool
          split <;> rfl
        show h.ofSyms (mixOfBool f (fun p => r.rd o p.1) (fun p => r.rd o p.1)) = o
        rw [e, h.ofSyms_rd]
      right_inv := fun z => by
        refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
        · show r.rd (h.ofSyms (mixOfBool f z.1 z.2)) p.1 = z.1 p
          rw [h.rd_ofSyms]
          exact dif_pos p.2
        · show r.rd (h.ofSyms (mixOfBool f z.1 z.2)) p.1 = z.2 p
          rw [h.rd_ofSyms]
          exact dif_neg (by rw [p.2]; exact Bool.false_ne_true) }
  pos := sumOfBool f
  plain := pl
  rdA := fun o p => o p
  rdB := fun o p => o p

theorem RCut.ofBool_ok (h : r.IsPoint) (f : r.Pos → Bool) {PA PB : Type} (pl : r.Plain ≃ PA × PB) :
    (RCut.ofBool h f pl).OK :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- The oracle of the first part is a string. -/
def RCut.ofBoolFst (h : r.IsPoint) (f : r.Pos → Bool) {PA PB : Type} (pl : r.Plain ≃ PA × PB) :
    (RCut.ofBool h f pl).fst.IsPoint where
  finPos := letI := h.finPos; inferInstanceAs (Fintype {p // f p = true})
  decPos := letI := h.decPos; inferInstanceAs (DecidableEq {p // f p = true})
  ofSyms := fun g => g
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun p => h.zero p.1

/-- The oracle of the remainder is a string. -/
def RCut.ofBoolSnd (h : r.IsPoint) (f : r.Pos → Bool) {PA PB : Type} (pl : r.Plain ≃ PA × PB) :
    (RCut.ofBool h f pl).snd.IsPoint where
  finPos := letI := h.finPos; inferInstanceAs (Fintype {p // f p = false})
  decPos := letI := h.decPos; inferInstanceAs (DecidableEq {p // f p = false})
  ofSyms := fun g => g
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun p => h.zero p.1


/-- All splits of the plan of a round satisfy `RCut.OK`. -/
def RPlan.OK : {r : Round} → RPlan r → Prop
  | _, .keep _ => True
  | _, .cut c rest => c.OK ∧ rest.OK

/-! ## 3. The number of splits -/



/-- the number of splits of the plan of a round -/
def RPlan.cuts : {r : Round} → RPlan r → ℕ
  | _, .keep _ => 0
  | _, .cut _ rest => rest.cuts + 1



/-! ## 4. Splits of rounds that are sent whole by the slots, or whole in the shared component -/

/-- a prover message is the pair of its parts -/
def RCut.msg (c : RCut r) : r.Msg ≃ c.fst.Msg × c.snd.Msg :=
  ⟨fun m => (c.left m, c.right m),
    fun z => c.join z.1 z.2,
    c.join_left_right,
    fun z => Prod.ext (c.left_join z.1 z.2) (c.right_join z.1 z.2)⟩

/-- A split of a round in which only the slots send: both parts are sent by the slots. k1 is the
kind of the round of the first part. -/
def ACut.ofSlot (k1 k : Kind) (c : RCut r) : ACut c (RAnn.ofSlot k r) where
  kind := k1
  A := RComp.ofSlot c.fst
  B := RComp.ofSlot c.snd
  m0 := (Equiv.punitProd Unit).symm
  mj := c.msg

/-- A split of a round in which only the shared component is sent: both parts are in the shared
component. -/
def ACut.ofShared (k1 k : Kind) (c : RCut r) : ACut c (RAnn.ofShared k r) where
  kind := k1
  A := RComp.ofShared c.fst
  B := RComp.ofShared c.snd
  m0 := c.msg
  mj := (Equiv.punitProd Unit).symm

theorem ACut.ofSlot_ann1 (k1 k : Kind) (c : RCut r) :
    (ACut.ofSlot k1 k c).ann1 = RAnn.ofSlot k1 c.fst := rfl
theorem ACut.ofSlot_ann2 (k1 k : Kind) (c : RCut r) :
    (ACut.ofSlot k1 k c).ann2 = RAnn.ofSlot k c.snd := rfl
theorem ACut.ofShared_ann1 (k1 k : Kind) (c : RCut r) :
    (ACut.ofShared k1 k c).ann1 = RAnn.ofShared k1 c.fst := rfl
theorem ACut.ofShared_ann2 (k1 k : Kind) (c : RCut r) :
    (ACut.ofShared k1 k c).ann2 = RAnn.ofShared k c.snd := rfl

theorem ACut.ofSlot_ok (k1 k : Kind) (c : RCut r) : (ACut.ofSlot k1 k c).OK :=
  ⟨fun _ m => (c.join_left_right m).symm, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

theorem ACut.ofShared_ok (k1 k : Kind) (c : RCut r) : (ACut.ofShared k1 k c).OK :=
  ⟨fun m _ => (c.join_left_right m).symm, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## 6. The format (Iop/BatchFmt.lean) -/

/-- the phase after an annotated list of rounds that begins in the phase ph -/
def RoundSplits.endPhase : {s : Shape} → RoundSplits s → FPhase → FPhase
  | [], _, ph => ph
  | _ :: _, (a, A), ph => RoundSplits.endPhase A (FPhase.after a.kind ph)

theorem FPhase.after_after_of_fit
    {k1 k : Kind} {ph : FPhase} {p q : Prop} (h : FPhase.fit k1 k ph p q) :
    FPhase.after k (FPhase.after k1 ph) = FPhase.after k ph := by
  cases k1 <;> cases k <;> cases ph <;> first | rfl | exact h.elim




theorem RoundSplits.endPhase_const_lo (f : ∀ r : Round, RAnn r) (hf : ∀ r, (f r).kind = .lo) :
    ∀ (r : Round) (s : Shape) (ph : FPhase), RoundSplits.endPhase (RoundSplits.const f (r :: s)) ph = ph.afterLo
  | r, [], ph => by
      show FPhase.after (f r).kind ph = ph.afterLo
      rw [hf]
      rfl
  | r, r' :: s, ph => by
      show RoundSplits.endPhase (RoundSplits.const f (r' :: s)) (FPhase.after (f r).kind ph) = ph.afterLo
      rw [hf, RoundSplits.endPhase_const_lo f hf r' s]
      cases ph <;> rfl

theorem RoundSplits.endPhase_const_sh (f : ∀ r : Round, RAnn r) (hf : ∀ r, (f r).kind = .sh) :
    ∀ s : Shape, RoundSplits.endPhase (RoundSplits.const f s) .shr = .shr
  | [] => rfl
  | r :: s => by
      show RoundSplits.endPhase (RoundSplits.const f s) (FPhase.after (f r).kind .shr) = .shr
      rw [hf]
      exact RoundSplits.endPhase_const_sh f hf s

end Iop
