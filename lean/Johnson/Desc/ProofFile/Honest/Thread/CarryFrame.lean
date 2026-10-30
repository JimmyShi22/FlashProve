-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CarryFrame.lean: the item `carry m` of the first chain's table
passes over the sub-protocols of the kind `frame`, all but the 25 steps after a batching, at the
invariant `lettersHead` (FirstHead.lean). Conditional lemmas on our own definitions. No definition.

Where it is used. `frame_cells` (Law/NoHouse/FrameCells.lean) takes a hypothesis `hcarry`: the
invariant's argument `carryX` passes over every sub-protocol of the kind `frame`. It spends that
hypothesis at number 0, at the chain's end, at "laid" and at "cleared" only. This file proves the
passing at these, from two hypotheses on `carryX` and one on the invariant, and shows that the text
`carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean, of other authors) meets the two.

How. At number 0, at the chain's end and at "laid" the clause `keepsFrame`
(Law/NoHouse/KeepsFrame.lean) says that the state is the same. At "cleared" it is `keepsCleared`.
The library has lemmas by which its own statement on the carried word goes back over "cleared"
(Johnson/Top/H0/Walk/FrameCarryBack.lean, FrameCarryEnds.lean). Those on the fronts
(`firstFront_like`, `doorLike_head`, `doorLike_finish`) are general in the two states. So they also
serve forwards, with the two states exchanged. What they ask of the two states then follows from
`keepsCleared`.

  1  `carryExact_doorLike`   `carryExact` passes from `s` to `s'` under the library's
     `DoorLike Zp m s' s`, by `carryExact_alike`
  2  `rest_st`, `rest_between`   what the library's `rest` leaves. The like for the book, the number
     of roots and the frame is the library's (Johnson/Top/H0/Walk/FrameCarryFence.lean)
  3  `restLike_of_cleared`, `doorLike_link`, `wayLike_of_cleared`, `doorLike_cleared`   **`DoorLike`
     from the state after "cleared" to the state before it**
  4  `ridesPastAt_carry_at`   `ridesPastAt_carry_of` (CarryRides.lean) with the invariant before the
     step among the hypotheses
  5  `frame_clause`, `carry_cell_still`, `carry_cell_cleared`, `carry_frame`   the item passes.
     `carry_frame` has the form in which the columns are gathered
  6  `carryExact_strings`, `carry_frame_exact`   at `carryX := carryExact Zp (P5J.At.arr Zp)`

Hypotheses that stay.
  * `hfF`: the clause of the kind `frame` is `keepsFrame P5J.At.links P1L20.bearing`.
  * `hE`: three facts on the state before "cleared", under the invariant there: a link is open, the
    live copy of the state of the calls says "no link is under way", and there is no failure mark.
    They are spent where the switch that spends the item stands at the head's link or at the finish:
    the first steps of the head and of the finish read that flag
    (Johnson/Top/H0/K2Caller/CarryClosed.lean). The clause `keepsCleared` does not hold them. `hE`
    is asked at the places of "cleared" only: at other places the first fact is false.

Limits.
  * It is not proved that `hE` holds at any state. Where a switch stands
    (`(ProofFile.pAtK2 Zp m).stands`) depends on the public parameters. No lemma on it is used: each of
    the three cases is treated.
  * The 25 steps after a batching are not treated. `frame_cells` admits no `carry m` there.
  * Nothing shows that the invariant holds at any state, or that `carryExact` holds at any.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameCells
import Johnson.Desc.K2.Honest.Carry.Exact
import Johnson.Top.H0.Walk.FrameCarryEnds
import Johnson.Top.H0.Walk.FrameCarryFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K2 (frontAt)
open VerifiableInference.Desc.First.K2Caller (rest doorZ rest_out)
open VerifiableInference.Desc.K2.Honest (carryExact carryExact_alike)
open VerifiableInference.Desc.LinkJoin (hearN)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Tied (StLike RestLike WayLike FrontsLike DoorLike firstFront_like
  doorLike_head doorLike_finish toOption_some rest_book rest_roots rest_frame)
open OnBytes.Model (ChainCheck)
open OnBytes.Maker (WholeD)
open _root_.Tw.K2 (firstFront)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 `carryExact` under `DoorLike` -/

/-- `carryExact` passes from `s` to `s'` where whatever `doorZ` returns at `s` it returns the like
at `s'`. -/
theorem carryExact_doorLike {P Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (m : Nat) (z : P)
    (s s' : S) (y y' : Strs) (v : Wit Cells Tok MsgT) (hD : DoorLike Zp m s' s)
    (c : carryExact Zp arr m (z, s) y v) : carryExact Zp arr m (z, s') y' v := by
  obtain ⟨t, fx, h1, h2, h3⟩ := c
  obtain ⟨t', d', F⟩ := hD t h1
  obtain ⟨fx', f', hf, -, hT, hst⟩ := F.front fx h2
  exact (carryExact_alike Zp arr m (z, s) (z, s') y y' v h1 h2 d' f' hst.sameShapes
    (fun o => by rw [F.book]) (by rw [hf]) hT).2 ⟨t, fx, h1, h2, h3⟩

/-! ## 2 What `rest` leaves -/

theorem rest_st (s : S) : (rest s).st = s.st := by
  unfold rest
  split <;> rfl

theorem rest_between {s : S} (h : s.atBetween = true) : rest s = s := by
  refine rest_out s ?_
  unfold S.inLink S.fork?
  rw [here_between h]
  rfl

/-! ## 3 `DoorLike`, forwards over "cleared" -/

/-- The library's `RestLike`, from the state after "cleared" to the state before it. -/
theorem restLike_of_cleared {tk : Bool} {s t : S} (h : keepsCleared tk s t) : RestLike t s := by
  obtain ⟨-, k1, k2, -, k4, k5, -, -, k9, k10, k11, k12, -⟩ := h
  have e := rest_between k1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e, rest_frame, k2]
  · rw [e, rest_book, k4]
  · rw [e, rest_roots, k5]
  · rw [e, rest_st]
    exact ⟨k9, k10, k11, k12⟩

/-- Where the switch stands at a link. -/
theorem doorLike_link {Zp : ProofFile.Pub} {m : Nat} (hp : (ProofFile.pAtK2 Zp m).stands = .link) {s t : S}
    (h : RestLike t s) : DoorLike Zp m t s := by
  intro t' hd
  have e : t' = rest s := by
    unfold doorZ at hd
    rw [hp] at hd
    exact (Option.some.inj hd).symm
  subst e
  refine ⟨rest t, by unfold doorZ; rw [hp], h.book, h.roots, fun fx hf => ?_⟩
  have h1 : (firstFront (rest s).st (rest s).check.frame).toOption = some fx := by
    unfold frontAt at hf
    rw [hp] at hf
    exact hf
  obtain ⟨fx', e1, hf', -, ho, hT, -, hst⟩ :=
    firstFront_like h.st (rest s).check.frame (toOption_some h1)
  refine ⟨fx', ?_, hf', ho, hT, hst⟩
  unfold frontAt
  rw [hp, h.frame, e1]
  rfl

/-- The library's `WayLike`, from the state after "cleared" to the state before it. Three facts on
the state before are asked. -/
theorem wayLike_of_cleared {tk : Bool} {s t : S} (h : keepsCleared tk s t)
    (hin : s.inLink = true) (hfl : s.live.inLink = false) (h0 : s.failed = none) :
    WayLike (rest t) (rest s) := by
  obtain ⟨k0, k1, k2, -, k4, k5, -, -, k9, k10, k11, k12, -⟩ := h
  have es : rest s = { s with check := { s.live with inLink := false }, here := .between } := by
    unfold rest
    rw [if_pos hin]
  rw [rest_between k1, es]
  refine ⟨here_between k1, rfl, fun _ => ?_, k0.trans h0.symm, k4.symm, k5.symm,
    k9, k10, k11, k12⟩
  show t.check = ({ s.live with inLink := false } : ChainCheck)
  rw [k2, ← hfl]

/-- **`DoorLike` from the state after "cleared" to the state before it**, wherever the switch
stands. Where it stands at the head's link and the state before "cleared" stands there too, with
the link open, `doorZ` returns nothing at that state, and nothing is asked. -/
theorem doorLike_cleared {Zp : ProofFile.Pub} {m : Nat} {tk : Bool} {s t : S}
    (h : keepsCleared tk s t) (hin : s.inLink = true) (hfl : s.live.inLink = false)
    (h0 : s.failed = none) : DoorLike Zp m t s := by
  have hb : ∀ a, t.here ≠ .head a := fun a e => by
    rw [here_between h.2.1] at e
    cases e
  cases hs : (ProofFile.pAtK2 Zp m).stands with
  | link => exact doorLike_link hs (restLike_of_cleared h)
  | finish => exact doorLike_finish hs (wayLike_of_cleared h hin hfl h0)
  | head =>
    by_cases hh : ∃ a, s.here = .head a
    · obtain ⟨a, ha⟩ := hh
      by_cases ho : a.opened = true
      · intro t' hd
        unfold doorZ at hd
        rw [hs] at hd
        simp [ha, ho] at hd
      · exact absurd hin (by simp [S.inLink, S.fork?, ha, ho])
    · exact doorLike_head hs hb (fun a e => hh ⟨a, e⟩) (wayLike_of_cleared h hin hfl h0)

/-! ## 4 and 5 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

section
variable (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `carry m` passes over sub-protocol `b` if `carryX m` passes from a state at which the
invariant holds, over a step that `keeps b` admits, at all strings. -/
theorem ridesPastAt_carry_at {b : Nat} (m : Nat)
    (hc : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.carry m) := by
  intro k s mm E s' ps v hA hK h0
  exact hc k s mm E s' hA hK mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

end

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The clause of `keeps` at a place of the kind `frame`. -/
theorem frame_clause (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing) {b : Nat}
    {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.frame) (s s' : TS)
    (hK : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s') :
    keepsFrame P5J.At.links P1L20.bearing p s s' := by
  have e := (kpBy_at f hk s s').1
    ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hp s s').1 hK)
  rw [hfF] at e
  exact e

/-- At number 0, at the chain's end and at "laid". `hY`: `carryX` does not read the strings. -/
theorem carry_cell_still (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hY : ∀ m a (y y' : Strs) (v : WtF), carryX m a y v → carryX m a y' v) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.frame)
    (h0 : p.link = none ∨ p.piece = 0) (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
      (Item.carry m) := by
  refine ridesPastAt_carry_of h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w m
    fun s s' hK z y y' v c => ?_
  have K := frame_clause h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hfF hp hk s s' hK
  have e : s' = s := by
    cases hl : p.link with
    | none => exact ((keepsFrame_out P5J.At.links P1L20.bearing hl s s').1 K).1
    | some l =>
      rcases h0 with h0 | h0
      · rw [hl] at h0
        cases h0
      · exact ((keepsFrame_laid P5J.At.links P1L20.bearing hl h0 s s').1 K).1
  rw [e]
  exact hY m (z, s) y y' v c

/-- At "cleared". `hD`: `carryX` passes under the library's `DoorLike`. -/
theorem carry_cell_cleared (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hD : ∀ m (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF), DoorLike Zp m s' s →
      carryX m (z, s) y v → carryX m (z, s') y' v) {b : Nat} {p : Place} {l : Nat}
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.frame) (hl : p.link = some l)
    (h0 : p.piece ≠ 0) (hb : p.piece ≠ hearN P5J.At.links l + 2) (m : Nat)
    (hE : ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b k s mm E →
      s.inLink = true ∧ s.live.inLink = false ∧ s.failed = none) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
      (Item.carry m) := by
  refine ridesPastAt_carry_at h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w m
    fun k s mm E s' hA hK z y y' v c => ?_
  have K := (keepsFrame_cleared P5J.At.links P1L20.bearing hl h0 hb s s').1
    (frame_clause h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hfF hp hk s s' hK)
  obtain ⟨e1, e2, e3⟩ := hE k s mm E hA
  exact hD m z s s' y y' v (doorLike_cleared K e1 e2 e3) c

/-- **The item passes over every sub-protocol of the kind `frame` but the steps after a
batching.** -/
theorem carry_frame (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hY : ∀ m a (y y' : Strs) (v : WtF), carryX m a y v → carryX m a y' v)
    (hD : ∀ m (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF), DoorLike Zp m s' s →
      carryX m (z, s) y v → carryX m (z, s') y' v)
    (hE : ∀ b p l, P5J.At.ps[b]? = some p → p.kind = KindName.frame → p.link = some l →
      p.piece ≠ 0 → p.piece ≠ hearN P5J.At.links l + 2 → ∀ k s mm E,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b k s mm E →
      s.inLink = true ∧ s.live.inLink = false ∧ s.failed = none) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
        (Item.carry m) := by
  intro b p hp hk hnb m
  cases hl : p.link with
  | none =>
    exact carry_cell_still h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hfF hY hp hk (Or.inl hl) m
  | some l =>
    by_cases h0 : p.piece = 0
    · exact carry_cell_still h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hfF hY hp hk (Or.inr h0) m
    · exact carry_cell_cleared h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hfF hD hp hk hl h0
        (hnb l hl) m (hE b p l hp hk hl h0 (hnb l hl))

/-! ## 6 At `carryExact` -/

/-- `carryExact` does not read the strings. -/
theorem carryExact_strings {P Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (m : Nat)
    (a : P × S) (y y' : Strs) (v : Wit Cells Tok MsgT) (c : carryExact Zp arr m a y v) :
    carryExact Zp arr m a y' v := c

/-- `carry_frame` at `carryX := carryExact Zp (P5J.At.arr Zp)`: `hfF` and `hE` stay. -/
theorem carry_frame_exact (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hE : ∀ b p l, P5J.At.ps[b]? = some p → p.kind = KindName.frame → p.link = some l →
      p.piece ≠ 0 → p.piece ≠ hearN P5J.At.links l + 2 → ∀ k s mm E,
      Thr (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd (kpBy f)
        w).thread b k s mm E →
      s.inLink = true ∧ s.live.inLink = false ∧ s.failed = none) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame →
      (∀ l, p.link = some l → p.piece ≠ hearN P5J.At.links l + 2) → ∀ m,
      RidesPastAt (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd
        (kpBy f) w).thread b (Item.carry m) :=
  carry_frame h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd f w hfF
    (fun m a y y' v c => carryExact_strings Zp (P5J.At.arr Zp) m a y y' v c)
    (fun m z s s' y y' v d c => carryExact_doorLike Zp (P5J.At.arr Zp) m z s s' y y' v d c) hE

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.carryExact_doorLike
#print axioms ProofFile.Honest.FirstThread.rest_st
#print axioms ProofFile.Honest.FirstThread.rest_between
#print axioms ProofFile.Honest.FirstThread.restLike_of_cleared
#print axioms ProofFile.Honest.FirstThread.doorLike_link
#print axioms ProofFile.Honest.FirstThread.wayLike_of_cleared
#print axioms ProofFile.Honest.FirstThread.doorLike_cleared
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_carry_at
#print axioms ProofFile.Honest.FirstThread.frame_clause
#print axioms ProofFile.Honest.FirstThread.carry_cell_still
#print axioms ProofFile.Honest.FirstThread.carry_cell_cleared
#print axioms ProofFile.Honest.FirstThread.carry_frame
#print axioms ProofFile.Honest.FirstThread.carryExact_strings
#print axioms ProofFile.Honest.FirstThread.carry_frame_exact
