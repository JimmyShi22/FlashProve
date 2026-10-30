-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CarryFramePaid.lean: the hypothesis `hE` of `carry_frame`
(CarryFrame.lean) is proved. So the item `carry m` passes over every sub-protocol of the kind
`frame` of the first chain but the 25 steps after a batching, at the invariant `lettersHead`
(FirstHead.lean), with no hypothesis on the state. Conditional lemmas on our own definitions. No
definition.

`hE` asks three facts on the state before "cleared", under the invariant there: a link is open, the
live copy of the state of the calls says "no link is under way", and there is no failure mark. The
sub-protocol just before "cleared" is K9's "the segment is shut". It writes that flag into the open
link's copy, and as the chain holds it, it tests the mark. The invariant at a border gives the
library's `Reach` there (`thr_reach`, ReachFacts.lean), and `Reach` goes one step back
(`reach_back`). The steps are those of the middle part of `calls_behind_cleared`
(Law/NoHouse/CallsBetween.lean), which has the three facts in hand and does not state them.

  1  `link_inLink`, `shut_link_behind`   a link is open after "the segment is shut"
  2  `calls_at_cleared`   the three facts at a state that is reached before "cleared"
  3  `clearedAt_full`, `clearedAt_control`, `cleared_number`   a place of the kind
     `frame` in a link, other than "laid" and the step after the batching, has the number
     `14 * l + IM.nAt l + 7`. A test on the written list of places, evaluated by the kernel, and a
     negative test
  4  `hE_head`   **`hE`**, at every clause of `keeps`
  5  `carry_frame_paid`, `carry_frame_exact_paid`   `carry_frame` and `carry_frame_exact` without
     `hE`

Hypotheses that stay.
  * `hfF`: the clause of the kind `frame` is `keepsFrame P5J.At.links P1L20.bearing`. `fHead`
    (FHead.lean) at `take := P1L20.bearing` has it by definition.
  * In `carry_frame_paid`: `hY` and `hD`, on `carryX`. `carryExact` meets both (CarryFrame.lean).

Limits.
  * The 25 steps after a batching are not treated.
  * Nothing shows that the invariant holds at any state, or that `carryExact` holds at any.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CarryFrame
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.CallsBetween
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.P5J.K09Len

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (reach_back)
open VerifiableInference.Desc.LinkJoin (hearN)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open ProofFile (Cl)

/-! ## 1 A link is open after "the segment is shut" -/

theorem link_inLink {s : S} (h : s.link?.isSome = true) : s.inLink = true := by
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
  cases here with
  | between => exact absurd h (by simp [S.link?])
  | fin a => exact absurd h (by simp [S.link?])
  | mem a => exact absurd h (by simp [S.link?])
  | lay a => rfl
  | att a => rfl
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.inLink, S.fork?, ho]
    · exact absurd h (by simp [S.link?, ho])

theorem shut_link_behind {C : Type} (p : VerifiableInference.Desc.K9.Where) (piece : Nat) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.shut (Cl := C) p piece).decide s rs gs = .ok t) :
    t.link?.isSome = true := by
  obtain ⟨L, hL, h⟩ := Meaning.K2.bindE h
  cases h
  have hl : s.link? = some L := by
    cases e : s.link? with
    | none =>
      rw [e] at hL
      cases hL
    | some L' =>
      rw [e] at hL
      exact congrArg some (Except.ok.inj hL)
  rw [Meaning.K2.link_putLink hl]
  rfl

/-! ## 2 Along the reach -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Before "link l: cleared".** -/
theorem calls_at_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 7) (z, s)) :
    s.inLink = true ∧ s.live.inLink = false ∧ s.failed = none := by
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, e1, hn, -⟩ := hall l hl
  have hn' : Lk.hear.length = IM.nAt l := hn
  obtain ⟨LkC, p, Q, eC, -, -, hcl⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk = LkC := Option.some.inj (e1.symm.trans eC)
  obtain ⟨b2, x2, c2, ex2, la2⟩ := hcl 2 KindName.K9 rfl
  have i2 := IM.close_numbers hS hR O hl e1 c2
  rw [hn'] at i2
  obtain rfl : VerifiableInference.Desc.K9.shut p (Q.piece + 1) = x2 := Option.some.inj ex2
  have R' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 4 + 2 + 1) (z, s) := R
  obtain ⟨s₂, b, -, hb, hy⟩ := reach_back R'
  obtain rfl : b2 = b := Option.some.inj (i2.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  have d' := (IM.alone_underR la2).2 _ _ _ _ d
  have e3 := shut_live (C := Unit) (rs := rs) (gs := gs) p (Q.piece + 1) d'
  have k3 := shut_link_behind (C := Unit) (rs := rs) (gs := gs) p (Q.piece + 1) d'
  have m3 : s.failed = none :=
    ((IM.yes_alone la2 (by show KindName.K9 ≠ KindName.K7; decide) s₂ s rs gs).1 d).2.1
  exact ⟨link_inLink k3, by rw [e3], m3⟩

end

/-! ## 3 The number of "cleared" -/

set_option maxRecDepth 1000000 in
/-- A test on the written list of places, evaluated by the kernel. -/
theorem clearedAt_full : ((List.range P5J.At.ps.length).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.frame) ||
      match p.link with
      | none => true
      | some l => p.piece == 0 || p.piece == hearN P5J.At.links l + 2 ||
          (decide (l < 25) && b == 14 * l + IM.nAt l + 7)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the number of "the segment is shut" the same test fails. -/
theorem clearedAt_control : ((List.range P5J.At.ps.length).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.frame) ||
      match p.link with
      | none => true
      | some l => p.piece == 0 || p.piece == hearN P5J.At.links l + 2 ||
          (decide (l < 25) && b == 14 * l + IM.nAt l + 6)) = false := by
  decide +kernel

/-- The test at a place. -/
theorem cleared_number {b : Nat} {p : Place} {l : Nat} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.frame) (hl : p.link = some l) (h0 : p.piece ≠ 0)
    (hb : p.piece ≠ hearN P5J.At.links l + 2) :
    l < 25 ∧ b = 14 * l + IM.nAt l + 7 ∧ b < P5J.At.ps.length := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 hp
  have t := List.all_eq_true.1 clearedAt_full b (List.mem_range.2 hlt)
  rw [hp, Option.all_some] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · rw [hk] at t0
    exact absurd t0 (by decide)
  · rw [hl] at t1
    have t2 : (p.piece == 0 || p.piece == hearN P5J.At.links l + 2 ||
        (decide (l < 25) && b == 14 * l + IM.nAt l + 7)) = true := t1
    rcases (Bool.or_eq_true _ _).mp t2 with t3 | t4
    · rcases (Bool.or_eq_true _ _).mp t3 with t5 | t6
      · exact absurd (eq_of_beq t5) h0
      · exact absurd (eq_of_beq t6) hb
    · obtain ⟨u1, u2⟩ := Bool.and_eq_true_iff.1 t4
      exact ⟨of_decide_eq_true u1, eq_of_beq u2, hlt⟩

namespace FirstThread
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (DoorLike)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 4 and 5 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

/-- **The hypothesis `hE` of `carry_frame`**, at every clause of `keeps`. -/
theorem hE_head (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) :
    ∀ b p l, P5J.At.ps[b]? = some p → p.kind = KindName.frame → p.link = some l →
      p.piece ≠ 0 → p.piece ≠ hearN P5J.At.links l + 2 → ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      s.inLink = true ∧ s.live.inLink = false ∧ s.failed = none := by
  intro b p l hp hk hl h0 hb k s mm E hT
  obtain ⟨hl25, eb, hlt⟩ := cleared_number hp hk hl h0 hb
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e6 : cF.blocksInOrder.length = 358 := Meaning.Carry.flat_len h.scope h.reads O
  have hle : b ≤ cF.blocksInOrder.length := by
    rw [e6, ← P5J.ps_358]
    exact Nat.le_of_lt hlt
  have R := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hle hT
  rw [eb] at R
  exact calls_at_cleared h.scope h.reads O hl25 R

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- `carry_frame` without `hE`. -/
theorem carry_frame_paid (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hY : ∀ m a (y y' : Strs) (v : WtF), carryX m a y v → carryX m a y' v)
    (hD : ∀ m (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF), DoorLike Zp m s' s →
      carryX m (z, s) y v → carryX m (z, s') y' v) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
        (Item.carry m) :=
  carry_frame h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hfF hY hD
    (hE_head h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w)

/-- **`carry_frame_exact` without `hE`**: at `carryX := carryExact Zp (P5J.At.arr Zp)` the item
passes over every sub-protocol of the kind `frame` but the steps after a batching. -/
theorem carry_frame_exact_paid (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd
        (kpBy f) w).thread b (Item.carry m) :=
  carry_frame_exact h H Q test item n₁ n₂ b₀ Vd Rd f w hfF
    (hE_head h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd (kpBy f) w)

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.link_inLink
#print axioms ProofFile.Honest.shut_link_behind
#print axioms ProofFile.Honest.calls_at_cleared
#print axioms ProofFile.Honest.clearedAt_full
#print axioms ProofFile.Honest.clearedAt_control
#print axioms ProofFile.Honest.cleared_number
#print axioms ProofFile.Honest.FirstThread.hE_head
#print axioms ProofFile.Honest.FirstThread.carry_frame_paid
#print axioms ProofFile.Honest.FirstThread.carry_frame_exact_paid
