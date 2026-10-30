-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RowPileRides.lean: the hypothesis `RidesPastAt` (Shares.lean)
for four kinds of item at the first chain's invariant at the full size (`lettersHead`,
FirstHead.lean), at every sub-protocol number `b`, from what the condition `keeps b` leaves of the
verifier's state. PinRides.lean does the same for `pin`, `pinI` and `unmarked`. No definition.

  1  `row_same`, `pile_same`   at the library's meaning `mgAll`: the statement of `row m c` reads
     the fields `st` and `book` of the state only; the statement of `pile` reads these and `S.rows`
  2  `ridesPastAt_row`, `ridesPastAt_pile`   the two items pass over `b` if `keeps b` leaves these
  3  `ridesPastAt_pinKept`, `ridesPastAt_pinV`   they pass over `b` if `keeps b` leaves `st`

Sources. The proofs of `row_same` and `pile_same` are those of the library's `row_back` and
`pile_back` (Johnson/Top/H0/MergeLaw/RidesRows.lean), which are stated for the accepting step of one
sub-protocol, the merge. Here the equations that those proofs take from that step are hypotheses.
The proofs of 3 are those of PinRides.lean.

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The hypotheses on `keeps b` have to be shown for each kind from its own clause. This file shows
    them for no kind.
  * Nothing here shows that an item's statement holds at any state of a run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Top.H0.MergeLaw.RidesRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item RowClass Meaning classRows)
open VerifiableInference.Desc.First.MergeLaw (classRows_same)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_row mgAll_pile CellsQ)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `row m c` is the same at two states with the same `st` and `book`. -/
theorem row_same (h1 : s'.st = s.st) (h2 : s'.book = s.book) (m : Nat) (c : RowClass) (z : P)
    (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).row m c (z, s') y' w ↔ (mgAll 𝔇 Mg).row m c (z, s) y w := by
  rw [mgAll_row]
  show OnBytes.Means.AllSay _ s'.st (classRows 𝔇.N m c s')
      (VerifiableInference.Desc.Sound.wordsFirst 𝔇.arr s'.st s'.book w) ↔
    OnBytes.Means.AllSay _ s.st (classRows 𝔇.N m c s)
      (VerifiableInference.Desc.Sound.wordsFirst 𝔇.arr s.st s.book w)
  rw [classRows_same 𝔇.N m c h1 h2, h1, h2]

/-- The statement of `pile` is the same at two states with the same `st`, `book` and `S.rows`. -/
theorem pile_same (h1 : s'.st = s.st) (h2 : s'.book = s.book) (hr : s'.rows = s.rows) (z : P)
    (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) :
    (mgAll 𝔇 Mg).pile (z, s') y' w ↔ (mgAll 𝔇 Mg).pile (z, s) y w := by
  have hw : VerifiableInference.Desc.K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s') w =
      VerifiableInference.Desc.K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s) w := by
    unfold VerifiableInference.Desc.K13.Law.rwBook
    show (⟨_, VerifiableInference.Desc.K13.Law.maskCut s'.st
        (VerifiableInference.Desc.Sound.wordsFirst 𝔇.arr s'.st s'.book w)⟩ :
        VerifiableInference.Desc.K13.Law.Wit _ _ _) =
      ⟨_, VerifiableInference.Desc.K13.Law.maskCut s.st
        (VerifiableInference.Desc.Sound.wordsFirst 𝔇.arr s.st s.book w)⟩
    rw [h1, h2]
  rw [mgAll_pile]
  show (∀ r ∈ s'.rows, VerifiableInference.Desc.K13.Law.Holds _
      (VerifiableInference.Desc.K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s') w) r) ↔
    ∀ r ∈ s.rows, VerifiableInference.Desc.K13.Law.Holds _
      (VerifiableInference.Desc.K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s) w) r
  rw [hr, hw]

end

/-! ## 2 At the invariant: `row` and `pile` -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `row m c` passes over sub-protocol `b` if `keeps b` leaves `st` and `book`. -/
theorem ridesPastAt_row {b : Nat} (m : Nat) (c : RowClass)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st ∧ s'.book = s.book) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.row m c) := by
  intro k s mm E s' ps v _ hK h0
  obtain ⟨h1, h2⟩ := hk s s' hK
  exact (row_same { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    h1 h2 m c mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v).2 h0

/-- The item `pile` passes over sub-protocol `b` if `keeps b` leaves `st`, `book` and `S.rows`. -/
theorem ridesPastAt_pile {b : Nat}
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile := by
  intro k s mm E s' ps v _ hK h0
  obtain ⟨h1, h2, h3⟩ := hk s s' hK
  exact (pile_same { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    h1 h2 h3 mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v).2 h0

/-! ## 3 At the invariant: `pinKept` and `pinV` -/

/-- The item `pinKept m` passes over sub-protocol `b` if `keeps b` leaves `st`. -/
theorem ridesPastAt_pinKept {b : Nat} (m : Nat)
    (hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.pinKept m) := by
  intro k s mm E s' ps v _ hK h0 z hz
  exact ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => by rw [hst s s' hK]) (h0 z hz)

/-- The item `pinV` passes over sub-protocol `b` if `keeps b` leaves `st`. -/
theorem ridesPastAt_pinV {b : Nat}
    (hst : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.st = s.st) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pinV := by
  intro k s mm E s' ps v _ hK h0
  exact ansJT_rows (P5J.At.cs Zp) (P5J.At.arr Zp) (seats := P5J.At.seats Zp)
    (y := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    (y' := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    (fun _ _ _ => by rw [hst s s' hK]) h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.row_same
#print axioms ProofFile.Honest.FirstThread.pile_same
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_row
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinKept
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pinV
