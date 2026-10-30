-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudSends.lean: kind K14: THE BOUND ON THE POSITIONS READ OF A
SENDING's TREES, FROM THE LIBRARY's COUNT OF THE DECLARED ROUNDS; AND THAT ONE BOUND SERVES THE LAWS
ON BOTH SENDINGS' PARTS. Counting lemmas on public numbers. Statements with their proofs; no
definition.

  budAt_of_counts **where, for each message of a sending with the public numbers P whose first tree
                  has the number n₀ in the chain ch, the library's count at its tree, in a batch of
                  one request, is at most the r of its main rows' code and of its mask rows' code:
                  budAt P (Johnson/SendSim/At/Sim.lean) holds of the positions that the frame lays
                  for the sending's trees at every due list of challenges**: by asks_inBatch
                  (Honest/K14/BudCount.lean) and budAt_of_readsAt
                  (Johnson/SendSim/Seat/ReadsCountAt.lean)
  spBud_of_budAt  **budAt at "send o_omega"'s public numbers gives spBud**
                  (Honest/K14/FreshDefs.lean), the bound in fresh_at_omega
                  (Honest/K14/FreshField.lean): its clause at the message number 1, o_sp, which has
                  a mask row. So a filling whose letter bud at that row is budAt pays that premise
  spBud_of_count  spBud from the count at o_sp's tree alone

What is assumed. spBud_of_budAt: the shape splits; o_sp has one mask row (a field of SpShape).
What is not claimed. That the counts are within r at any description. A RUN OF ONE REQUEST: nothing
on the union over a batch. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BudCount
import Johnson.Desc.ProofFile.Honest.K14.FreshShows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription)
open OnBytes.SendSim.At (budAt asked)
open OnBytes.SendSim.Seat (ReadsWithinAt budAt_of_readsAt asked_asksFrom)
open AtPublicFiles.TreeReads (declOpens treeNo)
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- **From the library's count at each of the sending's trees to the bound on the positions that are
read.** -/
theorem budAt_of_counts {F : FileDescription Xi} {file : String} {D : OnBytes.Maker.WholeD}
    (h : F.data file = .ok D) (ch : Nat) (P : VerifiableInference.Desc.K1.Par) (n₀ : Nat)
    (hc : ∀ k τ, k < P.sent.size →
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ →
      ((shapeAt P k).mainRows ≠ 0 → (declOpens F).inBatch 1 (treeNo F ch (n₀ + τ)) ≤
        (P.codes.base.getD (shapeAt P k).code default).r) ∧
      ((shapeAt P k).maskRows ≠ 0 → (declOpens F).inBatch 1 (treeNo F ch (n₀ + τ)) ≤
        (P.codes.mask.getD (shapeAt P k).maskCode default).r))
    (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    budAt P (asksFrom (treeAsks F ρ ch) rs n₀) := by
  refine budAt_of_readsAt (fun ρ' hρ' k τ hk hτ => ?_) ρ hρ rs
  have ha := asks_inBatch h ρ' hρ' ch (n₀ + τ)
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans ha ((hc k τ hk hτ).1 hm))
  · exact le_trans (List.toFinset_card_le _) (by
      rw [List.length_map]
      exact le_trans ha ((hc k τ hk hτ).2 hm))

/-- **budAt at "send o_omega"'s public numbers gives spBud.** -/
theorem spBud_of_budAt (A : SendPub) (n : Nat) (hs : A.P.S.sharedSplitNeeded = true)
    (H : Desc.K14.Honest.SpShape A.P.codes A.P.S n) (asks : List (List (List Nat)))
    (h : budAt (jobOmega A).Q asks) : spBud A asks := by
  unfold spBud spAsked
  cases ht : ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
      (jobOmega A).Q.sent).getD {}).tree[1]? with
  | none => exact Nat.zero_le _
  | some t =>
    have h1 : 1 < (jobOmega A).Q.sent.size := by
      rw [omega_sent A hs]
      exact Nat.one_lt_two
    have hsh : shapeAt (jobOmega A).Q 1 = A.P.S.sharedSplit := omega_shape1 A hs
    have h2 := (h 1 t h1 ht).2 (by rw [hsh, H.oneRow]; decide)
    rw [hsh] at h2
    exact h2

/-- spBud from the count at o_sp's tree alone. -/
theorem spBud_of_count {F : FileDescription Xi} {file : String} {D : OnBytes.Maker.WholeD}
    (h : F.data file = .ok D) (A : SendPub) (n₀ : Nat)
    (hc : ∀ t, ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
        (jobOmega A).Q.sent).getD {}).tree[1]? = some t →
      (declOpens F).inBatch 1 (treeNo F 1 (n₀ + t)) ≤ (spMaskCode A).r)
    (ρ : Draws) (hρ : ρ.due F = true) (rs : List Nat) :
    spBud A (asksFrom (treeAsks F ρ 1) rs n₀) := by
  unfold spBud spAsked
  cases ht : ((VerifiableInference.Desc.Own.treesMade (jobOmega A).Q.codes
      (jobOmega A).Q.sent).getD {}).tree[1]? with
  | none => exact Nat.zero_le _
  | some t =>
    show (((asked (asksFrom (treeAsks F ρ 1) rs n₀) t).map
      (· % 2 ^ (spMaskCode A).logN)).toFinset).card ≤ (spMaskCode A).r
    rcases asked_asksFrom (treeAsks F ρ 1) rs n₀ t with e | e
    · rw [e]
      exact le_trans (List.toFinset_card_le _) (by
        rw [List.length_map]
        exact le_trans (asks_inBatch h ρ hρ 1 (n₀ + t)) (hc t ht))
    · rw [e]
      exact Nat.zero_le _

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.budAt_of_counts
#print axioms ProofFile.Honest.K14.spBud_of_budAt
#print axioms ProofFile.Honest.K14.spBud_of_count
