-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PubPAtK9.lean: lemmas about the borders after the three
sub-protocols of the kind K9 in each of the 25 segments of the first chain (the batching and the two
that follow it), at the full size. They show that no public item `left m` or `leftOn m` is open at
these 75 borders. With PubPAtHead.lean it follows that the fourth part of the invariant's clause
`Form` there (what the open public items say beside their Boolean tests) holds at every state. No
definition.

It imports PubPAtHead.lean, which reduces that part of the form at any border to the statements
of the open items `left m` and `leftOn m`, and the library's list of places (IMR/WrittenList.lean)
for the number `IM.nAt l` of a segment's sub-protocols before its batching.

  1  `no_left_after_k9`   the closed test at the 75 borders (kernel evaluation)
  2  `left_is_open_somewhere`, `sets_after_k9_not_empty`   two controls (kernel evaluations)
  3  `head_pubP_after_k9`   the fourth part of the form at these borders

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the format's second hash function.
  * The first control shows that the test can reject a set of the same list, not that it can reject
    at one of the 75 borders.
  * Nothing is proved about the other three parts of the form, and no property of the protocol
    is claimed.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PubPAtHead
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (flatPlacesOf pubSets)
open VerifiableInference.Desc.K1 (leftish saidSetB)
open VerifiableInference.Desc.Sound (MsgT linksFull moreAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- At the border after each of the three sub-protocols of the kind K9 of each segment, no open
public item is `left m` or `leftOn m`. The three borders of segment `l` are
`14 * l + IM.nAt l + j` for `j` = 3, 5 and 7. -/
theorem no_left_after_k9 :
    ((List.range 25).all fun l => [3, 5, 7].all fun j =>
      saidSetB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + IM.nAt l + j)
        fun q => !leftish q) = true := by
  decide +kernel

/-- Control: some open public set of the same list holds an item `left m` or `leftOn m`, so the test
on a set can reject. -/
theorem left_is_open_somewhere :
    ((pubSets moreAll linksFull (flatPlacesOf linksFull true)).any fun Q =>
      Q.any leftish) = true := by
  decide +kernel

/-- Control: the open public set after the batching of some segment is not empty, so the first
evaluation does not run over empty sets alone. -/
theorem sets_after_k9_not_empty :
    ((List.range 25).any fun l =>
      !((pubSets moreAll linksFull
        (flatPlacesOf linksFull true))[14 * l + IM.nAt l + 3]?.getD []).isEmpty) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- At the border `14 * l + IM.nAt l + j`, for `l` below 25 and `j` one of 3, 5 and 7, every open
public item's statement holds at every state `a`. -/
theorem head_pubP_after_k9 {l j : Nat} (hl : l < 25) (hj : j ∈ [3, 5, 7])
    (a : ProofFile.InstPub × TS) :
    ∀ q ∈ P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps (14 * l + IM.nAt l + j),
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pubP q a := by
  have hs : saidSetB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + IM.nAt l + j)
      (fun q => !leftish q) = true :=
    List.all_eq_true.1 (List.all_eq_true.1 no_left_after_k9 l (List.mem_range.2 hl)) j hj
  have hno : ∀ q ∈ P1K2.pubAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps (14 * l + IM.nAt l + j),
      leftish q = false := by
    intro q hq
    have e := head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    unfold P1K2.pubAt at hq
    rw [e] at hq
    have h1 : (!leftish q) = true := List.all_eq_true.1 hs q hq
    cases hh : leftish q with
    | false => rfl
    | true => rw [hh] at h1; cases h1
  refine head_pubP_of_left h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ a ?_ ?_
  · intro m hm
    exact Bool.noConfusion (show true = false from hno _ hm)
  · intro m hm
    exact Bool.noConfusion (show true = false from hno _ hm)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.no_left_after_k9
#print axioms ProofFile.Honest.FirstThread.left_is_open_somewhere
#print axioms ProofFile.Honest.FirstThread.sets_after_k9_not_empty
#print axioms ProofFile.Honest.FirstThread.head_pubP_after_k9
