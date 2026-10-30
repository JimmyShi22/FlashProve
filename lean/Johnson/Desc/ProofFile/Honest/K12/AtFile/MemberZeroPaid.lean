-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/MemberZeroPaid.lean: `MemberPaid` at member 0 of a shared thread whose
list is alike to the written one, at the letter that keeps the field.

  `trees_zero`   behind member 0 no tree is new: `TreesNext`
  `paid_zero`    `MemberPaid` at 0: `five_zero` (MemberZero.lean), `paid_of_five` (K12/AtFile/SharedWalk.lean)

Limits. The premises on letters are `five_zero`'s, all at a stand but hsp. NOT IN FRONT OF A LAW OVER COINS.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.MemberZero
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedWalk
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Alike₂)
open Desc.K14 (St frontBlock)
open Desc.K14.Honest (Like)
open P2Law.ProofPlan (WP)

/-- No tree stands in front of member 1. -/
theorem trees_one : ((sharedR.take 1).map (·.2)).sum = 0 := by decide +kernel

variable {Bk : ProverCoinCounts} {Cl W₀ Rc X₀ P₁ Wt : Type}
  (L : ProofFile.Honest.SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt)

/-- **Behind member 0 no tree is new.** -/
theorem trees_zero (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.thread.bs) : TreesNext L.thread Said 0 := by
  have e : sharedR = L.thread.bs.map roundsTrees := rounds_alike hl
  have ht : treesTo L.thread.bs 1 = 0 := by
    rw [trees_rounds, ← e]
    exact trees_one
  refine treesNext_of_fresh_nil _ ?_
  have hh : L.thread.hand 1 = [] := by
    show [] ++ (List.range (treesTo L.thread.bs 1)).map Fmt.TreeSource.own = []
    rw [ht]
    rfl
  unfold Thread.fresh
  rw [hh]
  rfl

/-- **`MemberPaid` at member 0.** -/
theorem paid_zero {n : ℕ} (F : WalkFacts L.thread n) (hn : 0 < n)
    (hsp : L.split = true) (c : OnBytes.Model.Verify.Chains) {b₀ : Block St Cl}
    (hb₀ : L.thread.bs[0]? = some b₀) (hl₀ : Like b₀ (frontBlock c))
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.thread.bs)
    (hform : ∀ k s m E, ThrS L.thread (SaidField L.thread BaseNil) 0 k s m E → L.shape 1 s = true)
    (hrides : ∀ k s m E, ThrS L.thread (SaidField L.thread BaseNil) 0 k s m E →
      L.thread.rides 1 m.st.input s)
    (hkeep : ∀ k s m E, ThrS L.thread (SaidField L.thread BaseNil) 0 k s m E → L.thread.keeps 0 s s)
    (hE : ∀ k s m E s', ThrS L.thread (SaidField L.thread BaseNil) 0 k s m E →
      L.thread.keeps 0 s s' → s' = s)
    (hC : ∀ w s y y' v, (L.Mg w).pinT s y v → (L.Mg w).pinT s y' v) :
    MemberPaid L.thread (SaidField L.thread BaseNil) 0 := by
  obtain ⟨hP, hA, hB, hX, hR⟩ := five_zero L (SaidField L.thread BaseNil) hsp c hb₀ hl₀ hform hrides
    hkeep hE hC (fun _ _ _ => none)
  exact paid_of_five F hn (trees_zero L _ hl) hP hA hB hX hR

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.trees_one
#print axioms ProofFile.Honest.K12.AtFile.trees_zero
#print axioms ProofFile.Honest.K12.AtFile.paid_zero
