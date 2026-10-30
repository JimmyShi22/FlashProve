-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SeedAtFive.lean: "seed" AT LINK 0 AT THE FIVE-LIST (loFive: the first
  written list's entries that have a main row; seat := the seats at these places, seatsMain): the
  form in which onS_of_rowAsks takes it at l = 0. From seed_at_K10 at the six-list
  (Johnson/P2LawR/SeedAtK10.lean) and one closed fact.


THE NAMES.
fiveInSixB, five_in_six_all: a closed fact at the written seats, by Lean's kernel: every place of
  the five-list is a place of the six-list with the same entry and the same seat.
five_in_six: what it says, a place at a time. seed_move: the invariant reads of a place its entry
  and its seat alone: at letters.
seed_at_five: **the head · the promise at ixK10 0 · reached there · no mark · a place i of loFive ·
  K1.Tie at its shape ⊢ ∃ ρ y, K1.SeedIs (At.cs Zp) (loFive.get i).1 a.1.2.st (Sound.numAt (At.seats
  Zp) ⟨⟨loFive, the five seats⟩, i⟩) ρ y.**

Limits. As seed_at_K10's. THAT fiveInSixB CAN SAY FALSE IS SHOWN BY NO LINE HERE: negative lines are
  left to other files. A raised limit stands in this file (maxRecDepth 100000). Nothing on
  soundness.
-/
import Johnson.P2LawR.SeedAtK10
import Johnson.Desc.First.Close.Law.FiveAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.P2Notices
open OnBytes OnBytes.Slice
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Close (seatK10 seatsOfLink seatsMain loSix loFive)
open VerifiableInference.Desc.Sound
open LPFK10 (ixK10)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The test at the written seats: every place of the five-list is a place of the six-list with the
same entry and the same seat. -/
def fiveInSixB : Bool :=
  (List.finRange loFive.length).all fun i =>
    (List.finRange loSix.length).any fun j =>
      decide (loFive.get i = loSix.get j) &&
        decide ((seatsMain loSix (seatsOfLink P5T.psFull 0)).getD i.val (0, 0) =
          seatK10 loSix P5T.psFull 0 j)

/-- **It accepts**: by Lean's kernel. -/
theorem five_in_six_all : fiveInSixB = true := by decide +kernel

/-- What it says, a place at a time. -/
theorem five_in_six (i : Fin loFive.length) : ∃ j : Fin loSix.length, loFive.get i = loSix.get j ∧
    (seatsMain loSix (seatsOfLink P5T.psFull 0)).getD i.val (0, 0) =
      seatK10 loSix P5T.psFull 0 j := by
  have k := List.all_eq_true.1 five_in_six_all i (List.mem_finRange i)
  obtain ⟨j, -, hj⟩ := List.any_eq_true.1 k
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hj
  exact ⟨j, of_decide_eq_true q1, of_decide_eq_true q2⟩

/-- The invariant reads of a place its entry and its seat alone: at letters. -/
theorem seed_move {cs : Codes} {st : Statement} {seats : List (ℕ × ℕ)}
    {lo lo' : List (OracleShape × ℕ)} {seat : Fin lo.length → ℕ × ℕ}
    {seat' : Fin lo'.length → ℕ × ℕ} {i : Fin lo.length} {j : Fin lo'.length}
    (g1 : lo.get i = lo'.get j) (g2 : seat i = seat' j)
    (s : K1.Tie cs (lo'.get j).1 →
      ∃ ρ y, K1.SeedIs cs (lo'.get j).1 st (Sound.numAt seats ⟨⟨lo', seat'⟩, j⟩) ρ y)
    (hT : K1.Tie cs (lo.get i).1) :
    ∃ ρ y, K1.SeedIs cs (lo.get i).1 st (Sound.numAt seats ⟨⟨lo, seat⟩, i⟩) ρ y := by
  show ∃ ρ y, K1.SeedIs cs (lo.get i).1 st (seats.idxOf (seat i)) ρ y
  rw [g1] at hT ⊢
  rw [g2]
  exact s hT

/-- **"seed" AT LINK 0 AT THE FIVE-LIST.** -/
theorem seed_at_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {a : (ProofFile.InstPub × TS) ×
      (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (ha : onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 0) a)
    (hr : h.toAtMg.rch (ixK10 0) a) (hm : ¬ a.1.2.failed ≠ none) (i : Fin loFive.length)
    (hT : K1.Tie (At.cs Zp) (loFive.get i).1) :
    ∃ ρ y, K1.SeedIs (At.cs Zp) (loFive.get i).1 a.1.2.st
      (Sound.numAt (At.seats Zp)
        ⟨⟨loFive, fun i => (seatsMain loSix (seatsOfLink (At.pseats Zp) 0)).getD i.val (0, 0)⟩,
          i⟩) ρ y :=
  (five_in_six i).elim fun j hj =>
    seed_move (seat' := seatK10 loSix (At.pseats Zp) 0) hj.1
      (by
        have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
        rw [e1]
        exact hj.2)
      (fun t => seed_at_K10 h (l := 0) (by decide) ha hr hm j t) hT

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.five_in_six_all
#print axioms VerifiableInference.Desc.P2Notices.five_in_six
#print axioms VerifiableInference.Desc.P2Notices.seed_move
#print axioms VerifiableInference.Desc.P2Notices.seed_at_five
