-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberPub.lean: THE MEMBERS OF "REACHED" ON EACH OF THE THREE
CHAINS, IN THE VERY LETTERS OF THE THREE FAMILIES WITH A CONDITION ON THE PUBLIC PART (RchPub,
RchPub₂, RchPub₃: Johnson/Top/H0/Walk/ReachPub.lean), which are taken as the one "reached"
on each chain for all fields. IM's clauses are their right sides "by shape":
here Lean holds it.

  rchPub_of_run    general in the description and in the condition Pp: where F.run accepts at x, v₁,
                   v₂, v₃ and Pp holds of F.pub x: three lists of states st₁, st₂, st₃ with: RchPub
                   F Pp k ((F.pub x, st₁ k), y) at every border k of the first chain; RchPub₂ F Pp
                   k (((F.pub x, ‹the first chain's last state›), st₂ k), y) at every border of the
                   shared chain; RchPub₃ F Pp k (((F.pub x, ‹the two last states›), st₃ k), y) at
                   every border of the second chain: at every type Str and every y : Str.
  member_pub       from the goals' scope test at the public files and the proof file's decision
                   behind its gate: an opening, the run st of Johnson/IMR/MemberRun.lean (so: no st
                     k bears
                   a mark), st₂, st₃, and the three memberships at the description written out at
                   the opening's letters (IM.fileOf), at Pp := fun p => ∃ z, p = (instanceAsPlainRecord z).pub,
                   WITH THE FIRST CHAIN's STATES NAMED: st k, and its last: st 358.

HOW. IM.three_of_run | IM.member_three (Johnson/IMR/MemberThree.lean) give Reach on each chain;
RchPub and
RchPub₂ are these by unfolding; RchPub₃ speaks through ReachR: ONE call of reachR_of_const
(Johnson/Top/H0/Walk/ReachStart.lean).
WHAT IS NOT SAID. That the two tests say yes anywhere. "No mark", or anything else, of the shared or
the second chain's states. All that Johnson/IMR/MemberThree.lean and Johnson/IMR/MemberFold.lean do
not say. Spent
through IM.gate_of_verify (verify()'s accept alone) these are members "at an accepting run at these
public files", NOT "at the honest run". No soundness.
-/
import Johnson.IMR.MemberThree
import Johnson.Top.H0.Walk.ReachPub
import Johnson.Top.H0.Walk.ReachStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach RchPub RchPub₂ RchPub₃ reachR_of_const)

/-- **Where a description's run accepts: members of the three families**, at every border of each
chain. -/
theorem rchPub_of_run {Xi : Type} {F : FileDescription Xi} {x : Xi} {v₁ v₂ v₃ : Fmt.View}
    (h : F.run x v₁ v₂ v₃ = true) (Pp : F.XiPub → Prop) (hP : Pp (F.pub x)) :
    ∃ (st₁ : ℕ → F.S₁) (st₂ : ℕ → F.S₂) (st₃ : ℕ → F.S₃),
      (∀ k ≤ F.first.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub F Pp k ((F.pub x, st₁ k), y)) ∧
      (∀ k ≤ F.shared.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₂ F Pp k (((F.pub x, st₁ F.first.blocksInOrder.length), st₂ k), y)) ∧
      ∀ k ≤ F.second.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₃ F Pp k
          (((F.pub x, st₁ F.first.blocksInOrder.length, st₂ F.shared.blocksInOrder.length), st₃ k), y) := by
  obtain ⟨st₁, st₂, st₃, -, -, h₃, a, b, c, -⟩ := three_of_run h
  have E₁ := (a F.first.blocksInOrder.length (Nat.le_refl _)).1
  have E₂ := (b F.shared.blocksInOrder.length (Nat.le_refl _)).1
  exact ⟨st₁, st₂, st₃, fun k hk _ _ => ⟨(a k hk).1, hP⟩,
    fun k hk _ _ => ⟨⟨(b k hk).1, E₁⟩, hP⟩,
    fun k hk _ _ => ⟨⟨reachR_of_const (c k hk).1 h₃, E₂, E₁⟩, hP⟩⟩

/-- **The members of "reached" on each chain, from the two tests on verify()'s own road**, with the
first chain's states named: the run's. -/
theorem member_pub {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (st : ℕ → S)
      (st₂ : ℕ → (fileOf Z A B c).S₂) (st₃ : ℕ → (fileOf Z A B c).S₃),
      VerifierAndGoals.readFiles P = .ok pp ∧
      Open OnBytes.secondHashFunction P.pol P.lay P.KL (fileOf Z A B c) Z Bs base c A B ∧
      RunAt Z c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st ∧
      (∀ k ≤ 358, ∀ (Str : Type) (y : Str),
        RchPub (fileOf Z A B c) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          (((LPFD.Full.instanceAsPlainRecord z).pub, st k), y)) ∧
      (∀ k ≤ (fileOf Z A B c).shared.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₂ (fileOf Z A B c) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358), st₂ k), y)) ∧
      ∀ k ≤ (fileOf Z A B c).second.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₃ (fileOf Z A B c) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358, st₂ (fileOf Z A B c).shared.blocksInOrder.length), st₃ k),
            y) := by
  obtain ⟨pp, Z, Bs, base, c, A, B, st, st₂, st₃, hR, O, Rn, -, h₃, b, d, -⟩ :=
    member_three hS hg
  have E₁ : Reach 0 ((fileOf Z A B c).first.blocksInOrder.map Sound.below) (fileOf Z A B c).start₁
      (fileOf Z A B c).first.blocksInOrder.length ((LPFD.Full.instanceAsPlainRecord z).pub, st 358) := by
    have e : (fileOf Z A B c).first.blocksInOrder.length = 358 := Rn.len
    rw [e]
    exact Rn.narrow 358 (Nat.le_refl _)
  have E₂ := (b (fileOf Z A B c).shared.blocksInOrder.length (Nat.le_refl _)).1
  exact ⟨pp, Z, Bs, base, c, A, B, st, st₂, st₃, hR, O, Rn,
    fun k hk _ _ => ⟨Rn.narrow k hk, z, rfl⟩,
    fun k hk _ _ => ⟨⟨(b k hk).1, E₁⟩, z, rfl⟩,
    fun k hk _ _ => ⟨⟨reachR_of_const (d k hk).1 h₃, E₂, E₁⟩, z, rfl⟩⟩

#print axioms rchPub_of_run
#print axioms member_pub

end IM
