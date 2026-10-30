-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FrameCells.lean: the column `hR` of `owesS_head`
(Thread/GatherHead.lean) at the 77 sub-protocols of the kind `frame` of the first chain at the full
size: every item that the table `frameOk` (RideOkFrame.lean) admits at such a place passes over the
sub-protocol there (`RidesPastAtS`, Thread/SharesS.lean). `keeps` is given kind by kind (`kpBy f`,
Thread/KeepsBy.lean), and the clause of the kind `frame` is `keepsFrame` (KeepsFrame.lean). No
definition.

  1  `frameOk_front`, `frameOk_seal`, `frameOk_laid`, `frameOk_behind`, `frameOk_cleared`   which
     items the table admits at each of the five sorts of place: 4, 6, 7, 7 and 7 kinds of item
  2  `rest9_rows`, `rest9_leftOf`, `rows_in_segment`   small facts on `S.rows` and `leftOf`
  3  `ridesPastAt_constr4`   an item `constr m q` with `q` one of the library's `P5J.parts4` passes
     over every sub-protocol
  4  `rides_still`, `rides_behind`, `rides_cleared`   the items that pass where `keeps` gives "the
     state is the same and has no failure mark", `keepsBehind`, `keepsCleared`
  5  `frame_cells`, `frame_cellsS`   **every admitted combination at a place of the kind `frame`**,
     at the table `frameOk` and at the table `rideOkF`

Each item's own lemma is by the authors of Thread/PinRides.lean, PinForward.lean, FrameRides.lean,
CarryRides.lean, RowPileRides.lean and HeadPinW.lean. The lemma for the item `wo` is
`k4_ridesPastAtS_wo_head` (K4/Law/WoRidesHead.lean), by the authors of K4's lemmas. `rows_between`
is from Thread/OpenedKeepsR.lean.
`ridesPastAt_constr4` has the statement and the proof of `ridesPastAt_constr`
(Johnson/Goal/HonestTrace/ConstrAtThread.lean, by the authors of the integer model's lemmas), which
is stated at one type of traces. Here that type is a variable.

What stays a hypothesis.
  * `hfF`: the clause of the kind `frame` is `keepsFrame P5J.At.links P1L20.bearing`.
  * `hcarry`: the invariant's argument `carryX` passes over the sub-protocol, at any strings. It is
    the hypothesis of `ridesPastAt_carry_of` (Thread/CarryRides.lean). `carryX` has no text yet.

Limits.
  * Nothing shows that the invariant holds at any state.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.RideOkFrame
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Cleared
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindLeft
import Johnson.Desc.ProofFile.Honest.Thread.HeadStaysAll
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.FrameRides
import Johnson.Desc.ProofFile.Honest.K4.Law.WoRidesHead
import Johnson.Desc.ProofFile.Honest.Thread.CarryRides
import Johnson.Desc.ProofFile.Honest.Thread.OpenedKeepsR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item Stand standOf standAt shapeAt)
open VerifiableInference.Desc.LinkJoin (hearN rest9 here9)
open VerifiableInference.Desc.Sound (MsgT mgBase)
open Johnson.Desc.First.Walk.Law (leftOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

/-! ## 1 What the table admits -/

section
variable {p : Place} {i : Item} {l : Nat}

theorem frameOk_front (hl : p.link = none) (h0 : p.piece = 0) (h : frameOk p i = true) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ ∃ m q, i = .constr m q ∧ q ∈ parts4 := by
  cases i with
  | unmarked => exact Or.inl rfl
  | pinW => exact Or.inr (Or.inl rfl)
  | pile => exact Or.inr (Or.inr (Or.inl rfl))
  | constr m q =>
    refine Or.inr (Or.inr (Or.inr ⟨m, q, rfl, ?_⟩))
    cases q <;> first
      | decide
      | (unfold frameOk at h; rw [hl] at h; simp [h0] at h)
  | _ =>
    unfold frameOk at h
    rw [hl] at h
    simp [h0] at h

theorem frameOk_seal (hl : p.link = none) (h0 : p.piece ≠ 0) (h : frameOk p i = true) :
    i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨ i = .wrow := by
  cases i with
  | unmarked => exact Or.inl rfl
  | pinW => exact Or.inr (Or.inl rfl)
  | pinI => exact Or.inr (Or.inr (Or.inl rfl))
  | pileOne => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | pinV => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | wrow => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  | _ =>
    unfold frameOk at h
    rw [hl] at h
    simp [h0] at h

theorem frameOk_laid (hl : p.link = some l) (h0 : p.piece = 0) (h : frameOk p i = true) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ m, i = .carry m) ∨
      (∃ m, i = .pinKept m) ∨ ∃ m q, i = .constr m q ∧ q ∈ parts4 := by
  cases i with
  | unmarked => exact Or.inl rfl
  | pinW => exact Or.inr (Or.inl rfl)
  | pile => exact Or.inr (Or.inr (Or.inl rfl))
  | pinI => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | carry m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))
  | pinKept m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))
  | constr m q =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, rfl, ?_⟩)))))
    cases q <;> first
      | decide
      | (unfold frameOk at h; rw [hl] at h; simp [h0] at h)
  | _ =>
    unfold frameOk at h
    rw [hl] at h
    simp [h0] at h

theorem frameOk_behind (hl : p.link = some l) (hb : p.piece = hearN P5J.At.links l + 2)
    (h : frameOk p i = true) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ m c, i = .row m c) ∨
      (∃ m, i = .wo m) ∨ ∃ m q, i = .constr m q ∧ q ∈ parts4 := by
  cases i with
  | unmarked => exact Or.inl rfl
  | pinW => exact Or.inr (Or.inl rfl)
  | pile => exact Or.inr (Or.inr (Or.inl rfl))
  | pinI => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | row m c => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, c, rfl⟩))))
  | wo m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))
  | constr m q =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, rfl, ?_⟩)))))
    cases q <;> first
      | decide
      | (unfold frameOk at h; rw [hl] at h; simp [hb] at h)
  | _ =>
    unfold frameOk at h
    rw [hl] at h
    simp [hb] at h

theorem frameOk_cleared (hl : p.link = some l) (h0 : p.piece ≠ 0)
    (hb : p.piece ≠ hearN P5J.At.links l + 2) (h : frameOk p i = true) :
    i = .unmarked ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
      (P1L20.bearing l = false ∧ (i = .pinW ∨ i = .pile ∨ i = .pinI)) ∨
      ∃ m q, i = .constr m q ∧ q ∈ parts4 := by
  cases i with
  | unmarked => exact Or.inl rfl
  | carry m => exact Or.inr (Or.inl ⟨m, rfl⟩)
  | pinKept m => exact Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))
  | pinW =>
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, Or.inl rfl⟩)))
    unfold frameOk at h
    rw [hl] at h
    simpa [h0, hb] using h
  | pile =>
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, Or.inr (Or.inl rfl)⟩)))
    unfold frameOk at h
    rw [hl] at h
    simpa [h0, hb] using h
  | pinI =>
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, Or.inr (Or.inr rfl)⟩)))
    unfold frameOk at h
    rw [hl] at h
    simpa [h0, hb] using h
  | constr m q =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, rfl, ?_⟩)))
    cases q <;> first
      | decide
      | (unfold frameOk at h; rw [hl] at h; simp [h0, hb] at h)
  | _ =>
    unfold frameOk at h
    rw [hl] at h
    simp [h0, hb] at h

end

/-! ## 2 Small facts on `S.rows` and `leftOf` -/

/-- The rows on the table are the same where `rest9` is. -/
theorem rest9_rows {L₀ : OnBytes.Model.LinkCtx} {F₀ : OnBytes.Model.Fork}
    {t₀ : OnBytes.Model.HTailF2} {s s' : S} (e : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    s'.rows = s.rows := by
  have r : ∀ u : S, (rest9 L₀ F₀ t₀ u).rows = u.rows := fun u => by
    unfold S.rows rest9
    cases u.here <;> rfl
  rw [← r s', ← r s, e]

/-- What the open segment's sub-proof has left for its row is the same where `rest9` is. -/
theorem rest9_leftOf {L₀ : OnBytes.Model.LinkCtx} {F₀ : OnBytes.Model.Fork}
    {t₀ : OnBytes.Model.HTailF2} {s s' : S} (e : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    leftOf s' = leftOf s := by
  have r : ∀ u : S, leftOf (rest9 L₀ F₀ t₀ u) = leftOf u := fun u => by
    unfold leftOf Johnson.Desc.First.Walk.leftLay VerifiableInference.Desc.First.Close.leftHead
      rest9
    cases u.here <;> rfl
  rw [← r s', ← r s, e]

/-- At a border before a place inside a segment the rows on the table are the pending rows. -/
theorem rows_in_segment {links : List VerifiableInference.Desc.First.ModelPart} {p : Place} {l : Nat}
    {s : S} (hl : p.link = some l) (h : shapeAt links (some p) s = true) :
    s.rows = s.out.pending := by
  simp only [shapeAt, Bool.and_eq_true, beq_iff_eq] at h
  have e := h.1.1
  unfold S.rows
  cases hq : s.here with
  | mem a =>
    exfalso
    unfold standOf at e
    rw [hq] at e
    unfold standAt at e
    rw [hl] at e
    dsimp only at e
    split at e
    · cases e
    · split at e <;> cases e
  | _ => rfl

/-! ## 3 to 5 At the invariant -/

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

/-- An item `constr m q`, `q` one of the four parts, passes over every sub-protocol: its statement
reads neither the state nor the strings. -/
theorem ridesPastAt_constr4 (b m : Nat) {q : P5J.TPart} (hq : q ∈ parts4) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.constr m q) := by
  intro k s mm E s' ps v _ _ h0
  simp only [parts4, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> exact h0

/-- Where `keeps` gives that the state is the same and has no failure mark. -/
theorem rides_still {b : Nat}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s' = s ∧ s'.failed = none)
    (hcarry : ∀ m s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
    {i : Item}
    (hi : i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨
      i = .wrow ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
      ∃ m q, i = .constr m q ∧ q ∈ parts4) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b i := by
  have hst : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st := fun s s' hK => by rw [(hk s s' hK).1]
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl, hq⟩
  · exact ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).2
  · exact ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b
  · exact ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' hK => by
      rw [(hk s s' hK).1]
      exact ⟨rfl, rfl, rfl⟩
  · exact ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hst
  · exact ridesPastAt_pileOne_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).1
  · exact ridesPastAt_pinV h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hst
  · exact ridesPastAt_wrow_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).1
  · exact ridesPastAt_carry_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m (hcarry m)
  · exact ridesPastAt_pinKept h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m hst
  · exact ridesPastAt_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b m hq

/-- Where the clause of `keeps` at the place gives `keepsBehind`. -/
theorem rides_behind (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {b : Nat}
    {p : Place} (hp : P5J.At.ps[b]? = some p) (hk : ∀ s s', Kp p s s' → keepsBehind s s')
    {i : Item}
    (hi : i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ m c, i = .row m c) ∨
      (∃ m, i = .wo m) ∨ ∃ m q, i = .constr m q ∧ q ∈ parts4) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i := by
  have hk' : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      keepsBehind s s' := fun s s' hK =>
    hk s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp s s').1 hK)
  have h9 : ∀ s s' : TS, keepsBehind s s' →
      rest9 { check := s.check } {} {} s' = rest9 { check := s.check } {} {} s :=
    fun _ _ K => K.2.1 _ _ _
  have hst : ∀ s s' : TS, keepsBehind s s' → s'.st = s.st :=
    fun s s' K => by
      have e := congrArg (fun z : TS => z.st) (h9 s s' K)
      exact e
  have hbk : ∀ s s' : TS, keepsBehind s s' → s'.book = s.book :=
    fun s s' K => by
      have e := congrArg (fun z : TS => z.book) (h9 s s' K)
      exact e
  rcases hi with rfl | rfl | rfl | rfl | ⟨m, c, rfl⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl, hq⟩
  · exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk' s s' hK).2.2.1)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => ⟨hst s s' (hk' s s' hK), hbk s s' (hk' s s' hK),
        rest9_rows (h9 s s' (hk' s s' hK))⟩)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => hst s s' (hk' s s' hK))
  · exact ridesPastAtS_of _ _ (ridesPastAt_row h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m c
      fun s s' hK => ⟨hst s s' (hk' s s' hK), hbk s s' (hk' s s' hK)⟩)
  · exact ProofFile.Honest.K4.k4_ridesPastAtS_wo_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said b m
      hp
      fun _ s _ _ s' _ hc => ⟨hst s s' (hk s s' hc), hbk s s' (hk s s' hc),
        keepsBehind_out (hk s s' hc),
        rest9_leftOf (h9 s s' (hk s s' hc))⟩
  · exact ridesPastAtS_of _ _
      (ridesPastAt_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b m hq)

/-- Where `keeps` gives `keepsCleared`, before a place `p` inside a segment. -/
theorem rides_cleared {b l : Nat} {p : Place} {take : Bool} (hp : P5J.At.ps[b]? = some p)
    (hl : p.link = some l)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      keepsCleared take s s')
    (hcarry : ∀ m s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v)
    {i : Item}
    (hi : i = .unmarked ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
      (take = false ∧ (i = .pinW ∨ i = .pile ∨ i = .pinI)) ∨
      ∃ m q, i = .constr m q ∧ q ∈ parts4) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b i := by
  rcases hi with rfl | ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨ht, rfl | rfl | rfl⟩ | ⟨m, q, rfl, hq⟩
  · exact ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => (hk s s' hK).1
  · exact ridesPastAt_carry_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m (hcarry m)
  · exact ridesPastAt_pinKept_cleared h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m hk
  · exact ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b
  · intro k s mm E s' ps v hA hK h0
    have K := hk s s' hK
    obtain ⟨eo, es⟩ := K.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht
    have hsh := (form_shape hA.2.2.1).2
    have hsh' : shapeAt P5J.At.links (some p) s = true := by
      rw [← hp]
      exact hsh
    have er : s'.rows = s.rows := by
      rw [rows_between K.2.1, rows_in_segment hl hsh', eo]
    exact (pile_same { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX }
      mgBase es K.2.2.2.2.1 er mm.st.input.x.pub
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v).2 h0
  · exact ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun s s' hK => ((hk s s' hK).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht).2
  · exact ridesPastAt_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w b m hq

end

variable (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **Every combination that `frameOk` admits at a place of the kind `frame`.** `hcarry`: the
argument `carryX` passes over the sub-protocol, at any strings. -/
theorem frame_cells (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v) :
    ∀ b p i, P5J.At.ps[b]? = some p → p.kind = KindName.frame → frameOk p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said b
        i := by
  intro b p i hp hkind hok
  have hKp : ∀ s s', kpBy f p s s' → keepsFrame P5J.At.links P1L20.bearing p s s' :=
    fun s s' hc => by
      have e := (kpBy_at f hkind s s').1 hc
      rw [hfF] at e
      exact e
  have hK : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      keepsFrame P5J.At.links P1L20.bearing p s s' := fun s s' hk =>
    hKp s s' ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hp s s').1 hk)
  cases hl : p.link with
  | none =>
    have hS : ∀ s s',
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
        s' = s ∧ s'.failed = none :=
      fun s s' hk => (keepsFrame_out P5J.At.links P1L20.bearing hl s s').1 (hK s s' hk)
    have go : (i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨
        i = .wrow ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
        ∃ m q, i = .constr m q ∧ q ∈ parts4) →
        RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
          Said b i := fun hi => ridesPastAtS_of _ _
      (rides_still h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hS (hcarry b p hp hkind) hi)
    by_cases h0 : p.piece = 0
    · rcases frameOk_front hl h0 hok with e | e | e | e
      · exact go (Or.inl e)
      · exact go (Or.inr (Or.inl e))
      · exact go (Or.inr (Or.inr (Or.inl e)))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))))))
    · rcases frameOk_seal hl h0 hok with e | e | e | e | e | e
      · exact go (Or.inl e)
      · exact go (Or.inr (Or.inl e))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))
  | some l =>
    by_cases h0 : p.piece = 0
    · have hS : ∀ s s',
          (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
          s' = s ∧ s'.failed = none :=
        fun s s' hk => (keepsFrame_laid P5J.At.links P1L20.bearing hl h0 s s').1 (hK s s' hk)
      have go : (i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ i = .pileOne ∨ i = .pinV ∨
          i = .wrow ∨ (∃ m, i = .carry m) ∨ (∃ m, i = .pinKept m) ∨
          ∃ m q, i = .constr m q ∧ q ∈ parts4) →
          RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
            Said b i := fun hi => ridesPastAtS_of _ _
        (rides_still h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hS (hcarry b p hp hkind) hi)
      rcases frameOk_laid hl h0 hok with e | e | e | e | e | e | e
      · exact go (Or.inl e)
      · exact go (Or.inr (Or.inl e))
      · exact go (Or.inr (Or.inr (Or.inl e)))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))))
      · exact go (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e)))))))))
    · by_cases hb : p.piece = hearN P5J.At.links l + 2
      · exact rides_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w Said hp
          (fun s s' hc =>
            (keepsFrame_behind P5J.At.links P1L20.bearing hl hb s s').1 (hKp s s' hc))
          (frameOk_behind hl hb hok)
      · exact ridesPastAtS_of _ _ (rides_cleared h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
          (take := P1L20.bearing l) hp hl
          (fun s s' hk =>
            (keepsFrame_cleared P5J.At.links P1L20.bearing hl h0 hb s s').1 (hK s s' hk))
          (hcarry b p hp hkind) (frameOk_cleared hl h0 hb hok))

/-- The same in the form that `head_hR_of_cellsF` (RideOkFrame.lean) asks at a place of the kind
`frame`. -/
theorem frame_cellsS (hfF : f KindName.frame = keepsFrame P5J.At.links P1L20.bearing)
    (hcarry : ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.frame → ∀ m s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF), carryX m (z, s) y v → carryX m (z, s') y' v) :
    ∀ b p i, P5J.At.ps[b]? = some p → p.kind = KindName.frame → rideOkF p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said b
        i :=
  fun b p i hp hkind hok =>
    frame_cells h H Q test carryX item n₁ n₂ b₀ Vd Rd f w Said hfF hcarry b p i hp hkind
      ((rideOkF_frame hkind i).symm.trans hok)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.frameOk_front
#print axioms ProofFile.Honest.FirstThread.frameOk_seal
#print axioms ProofFile.Honest.FirstThread.frameOk_laid
#print axioms ProofFile.Honest.FirstThread.frameOk_behind
#print axioms ProofFile.Honest.FirstThread.frameOk_cleared
#print axioms ProofFile.Honest.FirstThread.rest9_rows
#print axioms ProofFile.Honest.FirstThread.rest9_leftOf
#print axioms ProofFile.Honest.FirstThread.rows_in_segment
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_constr4
#print axioms ProofFile.Honest.FirstThread.rides_still
#print axioms ProofFile.Honest.FirstThread.rides_behind
#print axioms ProofFile.Honest.FirstThread.rides_cleared
#print axioms ProofFile.Honest.FirstThread.frame_cells
#print axioms ProofFile.Honest.FirstThread.frame_cellsS
