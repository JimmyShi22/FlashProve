-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PinForward.lean: the four kinds of pin among the open items of
the first chain's invariant pass over a sub-protocol whose step may add to the statement, as long as
a first sample row that the statement holds before the step is still there after it. PinRides.lean
and RowPileRides.lean show the same under the stronger hypothesis that the step leaves the whole
statement as it was. That hypothesis is false for a sub-protocol that sends new oracle messages
(kind K1) and for one that closes a segment (kind K10). No definition.

Why the weaker hypothesis is enough. A pin states that the verifier's statement holds a sample for
certain messages and that the witness's messages have that sample's answers (`ansJT`,
Honest/Thread/Ans.lean). It begins with "the statement holds a sample", so it is true only where the
first sample row of the message is there (`rowAt₀`), and what it states further depends on that row
alone. Nothing has to be known about messages whose row is not there yet. The library's
`K1.smpNamed_old` (Johnson/Desc/K1/Law/SmpNamedEarlierMessages.lean) shows that the sample is equal at both
states, and for that it needs a bound on the message's number. Here only one direction is shown, and
no bound is needed.

  1  `rowAt₀_rows`, `rowAt₀_same`, `rowAt₀_old`, `rowAt₀_smpStay`   the hypothesis "a first
     sample row that is there stays", from three relations of the library on two statements: every
     message has the same sample rows; the older messages stay (`K1.OldMsgs`); the messages that
     are marked as sampled stay (`K1.SmpStay`), if before the step a message without the mark has
     no sample row (`OnBytes.Means.NoneYet`)
  2  `smpAt_noRow`, `smpNamed_noRow`, `smpNamed_older`   the library's reader of samples:
     without the row it holds nothing; a sample that it holds before the step it holds after it
  3  `ansJT_older`, `ansJT_rows_older`   the pin's statement passes from the one state to the other
  4  `ridesPastAt_pin_older`, `ridesPastAt_pinI_older`, `ridesPastAt_pinKept_older`,
     `ridesPastAt_pinV_older`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the
     four items at `lettersHead`, at every sub-protocol number `b`
  5  `exchangeAtS_pin_older`, `exchangeAtS_pinI_older`   a pin that the sub-protocol's row has to
     show again after the step

The hypothesis of 4 and 5 may use the invariant before the step (`Thr`), so that a fact such as
`NoneYet` can be taken from there.

Limits.
  * Parts 4 and 5: full size only, and only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * The hypothesis on `keeps b` has to be shown for each kind from its own clause. This file shows
    it for no kind.
  * One direction only, from the state before the step to the state after it.
  * Nothing here shows that a pin holds at any state of a run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.K1.Law.GoodSendStays
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.Means.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed smpNamed_stays smpNamed_at
  smpNamed_none numAt)
open VerifiableInference.Desc.First (S)
open Johnson.Pack (sigOf)

/-! ## 1 "A first sample row that is there stays", from three relations of the library -/

/-- The first sample row, read through the message's array of sample rows. -/
theorem rowAt₀_rows (St : OnBytes.Statement) (o : ℕ) :
    rowAt₀ St o =
      ((St.oracles[o]?).map fun x : OnBytes.Oracle => x.sampleRows).bind fun rs => rs[0]? := by
  unfold rowAt₀
  cases St.oracles[o]? <;> rfl

/-- Where message `o` has the same sample rows in two statements, its first sample row is the
same. -/
theorem rowAt₀_same {A B : OnBytes.Statement} {o : ℕ}
    (h : (B.oracles[o]?).map (fun x : OnBytes.Oracle => x.sampleRows) =
      (A.oracles[o]?).map fun x : OnBytes.Oracle => x.sampleRows) :
    rowAt₀ B o = rowAt₀ A o := by
  rw [rowAt₀_rows, rowAt₀_rows, h]

/-- Where the older messages stay, a first sample row that is there stays. -/
theorem rowAt₀_old {A B : OnBytes.Statement} (h : VerifiableInference.Desc.K1.OldMsgs A B) {o : ℕ}
    {r : OnBytes.Row} (hr : rowAt₀ A o = some r) : rowAt₀ B o = some r := by
  obtain ⟨x, hx, -⟩ := Option.bind_eq_some_iff.1 hr
  obtain ⟨ho, -⟩ := Array.getElem?_eq_some_iff.1 hx
  exact (rowAt₀_same (VerifiableInference.Desc.K1.rows_old h o ho)).trans hr

/-- Where the messages that are marked as sampled stay, and a message without the mark has no sample
row before the step, a first sample row that is there stays. -/
theorem rowAt₀_smpStay {A B : OnBytes.Statement} (h : VerifiableInference.Desc.K1.SmpStay A B)
    (hN : OnBytes.Means.NoneYet A) {o : ℕ} {r : OnBytes.Row} (hr : rowAt₀ A o = some r) :
    rowAt₀ B o = some r := by
  obtain ⟨x, hx, hxr⟩ := Option.bind_eq_some_iff.1 hr
  have hxr' : x.sampleRows[0]? = some r := hxr
  have hs : x.sampled = true := by
    cases hb : x.sampled with
    | true => rfl
    | false =>
      obtain ⟨h0, -⟩ := Array.getElem?_eq_some_iff.1 hxr'
      rw [hN o x hx hb] at h0
      exact absurd h0 (Nat.lt_irrefl 0)
  obtain ⟨x', hx', -, -, e⟩ := h.2 o x hx hs
  unfold rowAt₀
  rw [hx']
  show x'.sampleRows[0]? = some r
  rw [e]
  exact hxr'

/-! ## 2 The library's reader of samples -/

variable (cs : OnBytes.Codes) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- Without a first sample row the kind's reading at a message's number holds nothing. -/
theorem smpAt_noRow (sh : OnBytes.OracleShape) (e : ℕ) (St : OnBytes.Statement) (o : ℕ)
    (hr : rowAt₀ St o = none) : VerifiableInference.Desc.K1.smpAt cs sh e St o = none := by
  have hf : VerifiableInference.Desc.K1.formsAt cs sh St o = none := by
    rw [formsAt_row, hr, Option.map_none]
  unfold VerifiableInference.Desc.K1.smpAt
  exact dif_neg fun ⟨_, hρ⟩ => by
    rw [hf] at hρ
    cases hρ

/-- Without a first sample row at the member's number the reader of samples holds nothing. -/
theorem smpNamed_noRow {P : Type} (seats : List (ℕ × ℕ)) (a : P × S)
    (sd : VerifiableInference.Desc.Sound.Sending) (i : Fin sd.l.length)
    (hr : rowAt₀ a.2.st (numAt seats ⟨sd, i⟩) = none) :
    smpNamed cs seats a sd i = none := by
  by_cases hq : sd.seat i ∈ seats
  · exact (smpNamed_at cs seats a sd i hq).trans (smpAt_noRow cs _ _ _ _ hr)
  · exact smpNamed_none cs seats a sd i hq

/-- **A sample that the reader holds at the one state it holds at the other**, if the first sample
row at the member's number stays. -/
theorem smpNamed_older {P : Type} (seats : List (ℕ × ℕ)) (a b : P × S)
    (sd : VerifiableInference.Desc.Sound.Sending) (i : Fin sd.l.length)
    (h : ∀ r, rowAt₀ a.2.st (numAt seats ⟨sd, i⟩) = some r →
      rowAt₀ b.2.st (numAt seats ⟨sd, i⟩) = some r)
    {z : ((sigOf cs sd.l).om i).Smp} (hz : smpNamed cs seats a sd i = some z) :
    smpNamed cs seats b sd i = some z := by
  cases hr : rowAt₀ a.2.st (numAt seats ⟨sd, i⟩) with
  | none =>
    rw [smpNamed_noRow cs seats a sd i hr] at hz
    cases hz
  | some r =>
    have e : rowAt₀ b.2.st (numAt seats ⟨sd, i⟩) = rowAt₀ a.2.st (numAt seats ⟨sd, i⟩) :=
      (h r hr).trans hr.symm
    exact (smpNamed_stays cs seats a b sd i (by rw [formsAt_row, formsAt_row, e])
      (by rw [ansAt_row, ansAt_row, e])).trans hz

/-! ## 3 The pin's statement -/

/-- The pin's statement passes from `a` to `a'` if every sample that the reader holds at `a`, of a
member that sits at the seat, it holds at `a'`. -/
theorem ansJT_older
    {smp : A → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {j t : ℕ} {a a' : A} {y y' : Strs} {w : Wit Cells Tok MsgT}
    (h : ∀ x ∈ ms, SitsAt x j t → ∀ z, smp a x.1 x.2 = some z → smp a' x.1 x.2 = some z)
    (h0 : ansJT cs arr smp ms j t a y w) : ansJT cs arr smp ms j t a' y' w := by
  obtain ⟨h1, h2⟩ := h0
  refine ⟨h1, fun x hx hs => ?_⟩
  obtain ⟨z, hz, hv⟩ := h2 x hx hs
  exact ⟨z, h x hx hs z hz, hv⟩

/-- **The pin's statement passes from `s` to `s'`** if, at the number of every member that sits at
the seat, a first sample row that the statement of `s` holds is held by the statement of `s'`. -/
theorem ansJT_rows_older {P : Type} {seats : List (ℕ × ℕ)} {ms : List Mem} {j t : ℕ} {p p' : P}
    {s s' : S} {y y' : Strs} {w : Wit Cells Tok MsgT}
    (h : ∀ x ∈ ms, SitsAt x j t → ∀ r, rowAt₀ s.st (numAt seats x) = some r →
      rowAt₀ s'.st (numAt seats x) = some r)
    (h0 : ansJT cs arr (smpNamed cs seats) ms j t (p, s) y w) :
    ansJT cs arr (smpNamed cs seats) ms j t (p', s') y' w := by
  refine ansJT_older cs arr (fun x hx hs z hz => ?_) h0
  obtain ⟨sd, i⟩ := x
  exact smpNamed_older cs seats (p, s) (p', s') sd i (h ⟨sd, i⟩ hx hs) hz

end ProofFile.Honest

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-! ## 4 At the invariant: the four kinds of pin -/

/-- The item `pin m t` passes over sub-protocol `b` if a first sample row that is there before the
step is there after it. -/
theorem ridesPastAt_pin_older {b : Nat} (m t : Nat)
    (hst : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.pin m t) := by
  intro k s mm E s' ps v hA hK h0 z hz
  exact ansJT_rows_older (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => hst k s mm E s' hA hK _) (h0 z hz)

/-- The item `pinI` passes over sub-protocol `b` under the same hypothesis. -/
theorem ridesPastAt_pinI_older {b : Nat}
    (hst : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinI := by
  intro k s mm E s' ps v hA hK h0
  exact ansJT_rows_older (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => hst k s mm E s' hA hK _) h0

/-- The item `pinKept m` passes over sub-protocol `b` under the same hypothesis. -/
theorem ridesPastAt_pinKept_older {b : Nat} (m : Nat)
    (hst : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.pinKept m) := by
  intro k s mm E s' ps v hA hK h0 z hz
  exact ansJT_rows_older (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => hst k s mm E s' hA hK _) (h0 z hz)

/-- The item `pinV` passes over sub-protocol `b` under the same hypothesis. -/
theorem ridesPastAt_pinV_older {b : Nat}
    (hst : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinV := by
  intro k s mm E s' ps v hA hK h0
  exact ansJT_rows_older (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => hst k s mm E s' hA hK _) h0

/-! ## 5 A pin that the row has to show again -/

/-- The item `pin m t`, where the row of sub-protocol `b` has to show it again after the step. -/
theorem exchangeAtS_pin_older {b : Nat} (m t : Nat)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hst : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q)
    (hi : Item.pin m t ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b
      (Item.pin m t) :=
  exchangeAtS_again _ _ hi hB
    (ridesPastAtS_of _ _
      (ridesPastAt_pin_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m t hst))

/-- The item `pinI`, where the row of sub-protocol `b` has to show it again after the step. -/
theorem exchangeAtS_pinI_older {b : Nat}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hst : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      ∀ o q, rowAt₀ s.st o = some q → rowAt₀ s'.st o = some q)
    (hi : Item.pinI ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b Item.pinI :=
  exchangeAtS_again _ _ hi hB
    (ridesPastAtS_of _ _ (ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hst))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.rowAt₀_rows
#print axioms ProofFile.Honest.rowAt₀_same
#print axioms ProofFile.Honest.rowAt₀_old
#print axioms ProofFile.Honest.rowAt₀_smpStay
#print axioms ProofFile.Honest.smpAt_noRow
#print axioms ProofFile.Honest.smpNamed_noRow
#print axioms ProofFile.Honest.smpNamed_older
#print axioms ProofFile.Honest.ansJT_older
#print axioms ProofFile.Honest.ansJT_rows_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pin_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinI_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinKept_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinV_older
#print axioms ProofFile.Honest.FirstThread.exchangeAtS_pin_older
#print axioms ProofFile.Honest.FirstThread.exchangeAtS_pinI_older
