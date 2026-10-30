-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberRun.lean: member_fold (Johnson/IMR/MemberFold.lean) REPACKED FOR THE
ROWS' EXAMPLES: one small structure for a run, and its member from the two tests.

  RunAt Z c p R C st   a run of the first chain's fold: every entry of c.blocksInOrder passes its own test on
                   the plan (plan) · c.blocksInOrder has 358 entries (len) · st 0 is the first state at p
                   (start) · the fold over the whole list, from that state, at the list of rounds R
                   and the columns C, returns st 358 with nothing left over (whole) · at every k ≤
                   358 the fold over the first k entries, at the same, returns st k (fold) · st k is
                   reached at border k, in the narrower sense (narrow) and in the wider (wide) · no
                   st k bears a mark (noMark).
  at_gate          from the goals' scope test at the public files and the proof file's decision
                   behind its gate: the goals' reader returns, onlineDescription's value at P's files is
                   opened, and there is a run at the instance's own public part and at the first
                   view's own list of rounds (with the seal's empty round behind) and columns.

LETTERS of at_gate: P, z, v₁, v₂, v₃: free; pp by its equation; F, Z, Bs, base, c, A, B pinned by
Open (Open.unique); st pinned at every k ≤ 358 by the field fold, free beyond. Two fields follow
from others and stand for the caller's ease: start (from fold at 0) and wide (from narrow, by
reach_raw). WHAT IS NOT SAID. All that Johnson/IMR/MemberFold.lean does not say. RunAt drops of
member_fold:
that F.run accepts, the folds over the wrapped list, the steps, okBy, S.fin, S.finAsked, "live" and
"laid": whoever wants these calls member_fold. No soundness.

-/
import Johnson.IMR.MemberFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **A run of the first chain's fold**, with its state at every border. -/
structure RunAt (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn)
    (st : ℕ → S) : Prop where
  plan : ∀ b ∈ c.blocksInOrder, b.planOk = true
  len : c.blocksInOrder.length = 358
  start : st 0 = ProofFile.startS Z p
  whole : foldBlocks 0 c.blocksInOrder (ProofFile.startS Z p) R C = .ok (st 358, [], [])
  fold : ∀ k ≤ 358, ∃ r q, foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (st k, r, q)
  narrow : ∀ k ≤ 358, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (p, st k)
  wide : ∀ k ≤ 358, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, st k)
  noMark : ∀ k ≤ 358, (st k).failed = none

/-- **An opening and a run, from the two tests on verify()'s own road.** -/
theorem at_gate {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
      (st : ℕ → S),
      VerifierAndGoals.readFiles P = .ok pp ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      RunAt Z c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, st, hR, O, -, hp, hlen, -, h0, hw, hf, -, hall, -⟩ :=
    member_fold hS hg
  exact ⟨pp, F, Z, Bs, base, c, A, B, st, hR, O, hp, hlen, h0, hw,
    fun k hk => by obtain ⟨r, q, g, -⟩ := hf k hk; exact ⟨r, q, g⟩,
    fun k hk => (hall k hk).1, fun k hk => (hall k hk).2.1, fun k hk => (hall k hk).2.2⟩

#print axioms at_gate

end IM
