-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsK9.lean: at two of the three sub-protocols of the kind K9
in each segment of the first chain at the full size, the batching and the one that ends the
segment's closing, the condition `keeps` leaves the statement, the book of trees and the rows on the
table as they were. So the items `pile`, `pinI`, `pin` and `row` pass over these 50 sub-protocols.
That is a part of the column `hR` of the gathering (`owesS_head_form`, GatherHeadForm.lean). No
definition.

  1  `rows_readsRest9`   the rows on the table do not read what K9's three sub-protocols write
     (`ReadsRest9`, Johnson/Desc/First/Link/Law/Rest9.lean)
  2  `bat_quiet`   two states that are alike but for what these write have the same three things
  3  `head_rides_bat`, `head_rides_shut`   the four sorts of item pass over the batching and over
     the sub-protocol that ends the closing, in every segment

Called: `rest9_quiet`, `shut_quiet` (ArmsQuiet.lean), `rides_of_quiet` (CellsQuiet.lean),
`head_keeps_bat`, `head_keeps_shut` (what `keeps` says at these numbers).

Limits.
  * Not treated: K9's third sub-protocol, "the one equation", which changes the statement.
    PileCellsEqK7.lean and RowCellEq.lean treat it.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsQuiet
import Johnson.Desc.ProofFile.Honest.Thread.PinKeptCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (rest9 ReadsRest9)
open ProofFile.Honest.K9 (k9KeepsAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- The rows on the table do not read what K9's three sub-protocols write. -/
theorem rows_readsRest9 {L₀ : _} {F₀ : _} {t₀ : _} : ReadsRest9 L₀ F₀ t₀ S.rows := fun s => by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

/-- Two states that are alike but for what K9's three sub-protocols write. -/
theorem bat_quiet {s s' : S} (k : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.rows = s.rows :=
  rest9_quiet (ReadsRest9.alike _ _ _ rows_readsRest9 (k { check := s.check } {} {}))
    (k { check := s.check } {} {})

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **Over a segment's batching.** -/
theorem head_rides_bat (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 2) Item.pile ∧
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 2) Item.pinI ∧
      (∀ m t, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 2) (Item.pin m t)) ∧
      ∀ m c, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 2) (Item.row m c) :=
  rides_of_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w fun s s' hK =>
    bat_quiet (head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK)

/-- **Over the sub-protocol that ends a segment's closing.** -/
theorem head_rides_shut (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 6) Item.pile ∧
      RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 6) Item.pinI ∧
      (∀ m t, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 6) (Item.pin m t)) ∧
      ∀ m c, RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
        (14 * l + IM.nAt l + 6) (Item.row m c) :=
  rides_of_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w fun s s' hK =>
    shut_quiet (head_keeps_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rows_readsRest9
#print axioms ProofFile.Honest.FirstThread.bat_quiet
#print axioms ProofFile.Honest.FirstThread.head_rides_bat
#print axioms ProofFile.Honest.FirstThread.head_rides_shut
