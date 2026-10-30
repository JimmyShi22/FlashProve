-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OffAtJoin.lean: HOW MANY OF ITS MEMBER's OWN CHALLENGES A TREE's TABLE READS, AT THE JOINED LOTS OF TREES (joinTl,
Honest/Thread/Join.lean). Two statements with their proofs.

  switchShareAt_off_zero   at a number of K2's share a tree's table reads none of them
  off_at_join              the bound that ofLots_hfix (Honest/Thread/ScriptLots.lean) asks, at the joined lots, from the bound on the
                           other senders' lots outside a share of which it is known

At the joined lots each member is K1's, whose lot reads none by the text of k1TreeLots, or the other senders'.

Limits. Conditional: off_at_join takes that each member that declares a tree has a number in the lists, that the share stands in
the other senders' record, and both bounds. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.K2.JoinShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block)
open ProofFile.Honest.FirstThread

section Share
variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- At a number of K2's share a tree's table reads none of its member's own challenges. -/
theorem switchShareAt_off_zero (bs : List (Block P5J.TS ProofFile.Cl)) (front : ℕ) (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (Dq : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : ℕ → TreeLot Bk (Local W₀ Rc Xi Tr)) {b : ℕ}
    (hb : b ∈ (K2.switchShareAt Bk bs front Zq G Dq readers rest).tn) (j : ℕ) :
    ((K2.switchShareAt Bk bs front Zq G Dq readers rest).tl b).off j = 0 := by
  unfold K2.switchShareAt K2.switchShare at hb ⊢
  dsimp only at hb ⊢
  obtain ⟨p, hp, e⟩ := List.mem_map.1 hb
  have e' : borderNo bs p.place = b := e
  split
  · rfl
  · rename_i hf
    exact absurd (beq_iff_eq.2 e') (List.find?_eq_none.1 hf p hp)

end Share

section Join
variable {Bk : ProverCoinCounts} {Wl Xj Xo : Type}

/-- **The bound on the joined tree lots**, from the same bound on the other senders' lots outside the share A₀. -/
theorem off_at_join {bs : List (Block P5J.TS ProofFile.Cl)} {wit : Wl → K1.PlaceIn Xj} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn Xj) Xo)} {O A₀ : Others Bk Wl}
    (owned : ∀ b blk, bs[b]? = some blk → (blk.oracles.flatMap id).length ≠ 0 →
      b ∈ jobs.map (·.1) ++ O.tn)
    (hin : K2.Law.ShareIn A₀ O) (hz : ∀ b ∈ A₀.tn, ∀ j, (A₀.tl b).off j = 0)
    (hrest : ∀ b ∈ O.tn, b ∉ A₀.tn → ∀ blk, bs[b]? = some blk →
      ∀ j, j < (blk.oracles.flatMap id).length → (O.tl b).off j ≤ blk.rounds.length) :
    ∀ b blk, bs[b]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (joinTl wit own₀ jobs O b).off j ≤ blk.rounds.length := by
  intro b blk hb j hj
  unfold joinTl K1.k1TreeLots
  cases hl : jobs.lookup b with
  | some J => exact Nat.zero_le _
  | none =>
    have hO : b ∈ O.tn := by
      rcases List.mem_append.1 (owned b blk hb (by omega)) with hm | hm
      · exfalso
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
        rw [List.lookup_eq_none_iff] at hl
        have := hl q hq
        simp at this
      · exact hm
    show (O.tl b).off j ≤ blk.rounds.length
    by_cases hs : b ∈ A₀.tn
    · rw [hin.tl b hs, hz b hs j]
      exact Nat.zero_le _
    · exact hrest b hO hs blk hb j hj

end Join

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.switchShareAt_off_zero
#print axioms ProofFile.Honest.K5.off_at_join
