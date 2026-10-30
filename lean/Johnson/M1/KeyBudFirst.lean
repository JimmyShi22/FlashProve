-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the second part's bound at the first chain.
/-
Johnson/M1/KeyBudFirst.lean: aloneInFirstChain, asks_in_first_chain, bound_rest_first_chain of K12/Sim2/StandL.lean, word for word, in this namespace: general
in the file. They are copied because that file stands on the proof file's own facts.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudRestAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.KeyFirst
open VerifiableInference.Desc (FileDescription Block Place Chain)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)

variable {Xi : Type}

/-- aloneB (ReadsInBlock.lean) at the first chain: no round of the file outside the sub-protocol
between pre and t of the first list opens the first chain's tree number k. -/
def aloneInFirstChain {Xi : Type} (F : FileDescription Xi) (pre t : List (Block F.S₁ F.Cl)) (k : ℕ) : Bool :=
  (openedOf 0 (pre.flatMap (·.rounds)) ++ openedOf 0 (t.flatMap (·.rounds)) ++
    openedOf 1 F.roundsDeclaredByBlocks.2.1 ++ openedOf 2 F.roundsDeclaredByBlocks.2.2).all (·.1 != (0, k))

/-- asks_in_block (ReadsInBlock.lean) at the first chain. -/
theorem asks_in_first_chain {Xi : Type} {F : FileDescription Xi} (pre t : List (Block F.S₁ F.Cl))
    (b : Block F.S₁ F.Cl) (hcut : F.first.blocksInOrder = pre ++ b :: t) (ρ : Draws)
    (hρ : ρ.due F = true) (k : ℕ) (ha : aloneInFirstChain F pre t k = true) :
    ∀ x ∈ treeAsks F ρ 0 k, x ∈ ((readsOf 0 0 (fun _ _ => none) (fun _ => none) b.rounds
      ((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length)).filter fun q =>
        q.src == some (0, k)).map (·.pos) := by
  intro x hx
  unfold treeAsks at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hq, hs⟩ := List.mem_filter.1 hq
  have hs' : q.src = some (0, k) := beq_iff_eq.1 hs
  have off : ∀ e ∈ openedOf 0 (pre.flatMap (·.rounds)) ++ openedOf 0 (t.flatMap (·.rounds)) ++
      openedOf 1 F.roundsDeclaredByBlocks.2.1 ++ openedOf 2 F.roundsDeclaredByBlocks.2.2, e.1 ≠ (0, k) := fun e he =>
    bne_iff_ne.1 (List.all_eq_true.1 ha e he)
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true := hρ.1.1.1
  have hlen := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at hlen
  unfold allBare bareReads at hq
  rcases List.mem_append.1 hq with hq | hq
  · rcases List.mem_append.1 hq with hq | hq
    · have hq' : q ∈ readsOf 0 0 (fun _ _ => none) (fun _ => none)
          (pre.flatMap (·.rounds) ++ (b.rounds ++ t.flatMap (·.rounds)))
          (ρ.first.take (pre.flatMap (·.rounds)).length ++
            ((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length ++
              (ρ.first.drop (pre.flatMap (·.rounds)).length).drop b.rounds.length)) := by
        rw [List.take_append_drop, List.take_append_drop, ← List.flatMap_cons,
          ← List.flatMap_append, ← hcut]
        exact hq
      rw [readsOf_append 0 0 _ _ _ _ _ _ (by rw [List.length_take]; omega),
        readsOf_append 0 0 _ _ _ _ _ _ (by rw [List.length_take, List.length_drop]; omega)] at hq'
      rcases List.mem_append.1 hq' with h | h
      · exact absurd hs' (reads_off 0 0 _ _ _ _ (0, k) (fun e he => off e
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))) q h)
      · rcases List.mem_append.1 h with h | h
        · exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨h, hs⟩, rfl⟩
        · exact absurd hs' (reads_off 0 0 _ _ _ _ (0, k) (fun e he => off e
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he)))) q h)
    · exact absurd hs' (reads_off 1 0 _ _ _ _ (0, k) (fun e he => off e
        (List.mem_append_left _ (List.mem_append_right _ he))) q hq)
  · exact absurd hs' (reads_off 2 F.lastChainFirstTreeNumber _ _ _ _ (0, k) (fun e he => off e
                    (List.mem_append_right _ he)) q hq)

/-- bud_rest_file (Sim/BudRestAtRun.lean) at the first chain. -/
theorem bound_rest_first_chain {V W Y Pb : Type} {F : FileDescription Xi} (J : TestJob W Y) (Js : SimJob Pb)
    (pre t : List (Block F.S₁ F.Cl)) (b : Block F.S₁ F.Cl)
    (hcut : F.first.blocksInOrder = pre ++ b :: t) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ)
    (O : OpensFit J b.rounds depths src₀ sent) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf 0 (src₀ k) = (0, n) → n < sent)
    (hlen : b.rounds.length = J.laid.length)
    (hen : firstLen J.p.nums.stages ≤ J.laid.length) (ρ : Draws) (hρ : ρ.due F = true)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneInFirstChain F pre t (sent + sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1
      ((ρ.first.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
        (restMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 0) ((restMember (V := V) J Js).rounds.map (·.2.length))
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  have hρ' := hρ
  unfold Draws.due at hρ'
  simp only [Bool.and_eq_true] at hρ'
  have h2 : drawsFit (F.first.blocksInOrder.flatMap (·.rounds)) ρ.first = true := hρ'.1.1.1
  have htot := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at htot
  have hrl : (restMember (V := V) J Js).rounds.length =
      b.rounds.length - firstLen J.p.nums.stages := by
    show (J.laid.drop (firstLen J.p.nums.stages)).length = _
    rw [List.length_drop, hlen]
  have hds : (ρ.first.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length =
      (((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).drop
        (firstLen J.p.nums.stages)) := by
    rw [List.drop_take, List.drop_drop, hrl]
  have h1 : (((ρ.first.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take, List.length_take, List.length_drop]
    omega
  rw [hds]
  refine bud_sub _ _ _ _ _ _ (bud_own_rest (V := V) J Js b.rounds depths src₀ sent 0 0 O s next
    rest hst hk hT hold (fun _ _ => none) (fun _ => none) _ _ h1) fun i hi q hq => ?_
  rw [List.take_append_drop]
  have hil : i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hroots : ∀ i, i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length →
      ((restMember (V := V) J Js).rounds.map (·.2.length)).getD i 0 =
        if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0 :=
    fun i hi => roots_fit J hT _ i hi
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ _ hroots i (Nat.le_of_lt hil)] at hq ⊢
  exact asks_in_first_chain pre t b hcut ρ hρ _ (ha i hsome) q hq

end ProofFile.Honest.K12.KeyFirst

#print axioms ProofFile.Honest.K12.KeyFirst.bound_rest_first_chain
