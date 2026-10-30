-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyKeeps.lean: THE PAYERS OF THE CLAUSES OF E2E/KeyKeepsEq.lean: what the step of a sub-protocol
of the key file leaves of the verifier's state, AT FOURTEEN OF THE SIXTEEN SUB-PROTOCOLS THAT BELONG
TO NO KIND: each from the sub-protocol's own accepting step. By calls of the library's laws on these
decisions. NOTHING IS SHOWN OF ANY PROVER.

  `end_same`: GENERAL in the state: a yes of a chain's last sub-protocol
      (Johnson/Desc/ChainEnd.lean) hands the state on as it was: the library's `chainEnd_same`, said
      of the decision's text
  **`keeps_paid₁`**: at the first chain's ten: AT FREE LETTERS: at the library's `firstChain` of any
      public values: from the sub-protocol's accepting step (`StepYes`,
      Johnson/Top/H0/Walk/Reach.lean), where the plan has just two lookups and the shape has a
      message with W
  **`keeps_paid₂`**, **`keeps_paid₃`**: at the description's own shared chain's front and end; at
      its last chain's test on the taken trees' sources and its end. They end in "the state is as it
      was"; an end's number is said as the list's length less one

By `dec_laid0` and its like, `dec_seal`, `yes_caller0`, `yes_caller1`, `yes_rngRows`
(Johnson/RunOne/KeyTenAt.lean), `lay_ok`, `after_ok`, `clear_ok`, `seal_ok`
(Johnson/RunOne/KeyTen.lean), `stepYes_decide` (Johnson/Top/H0/Walk/ReachInv.lean), `flat_last`
(E2E/KeyThreads.lean). `front₂_same`, `chainEnd_same`, `sources_same`
(Johnson/RunOne/KeyKeepsAt23.lean).

Limits.
- THE TWO LAYERS (numbers 5 and 11 of the first chain) HAVE NO PAYER HERE: E2E/KeyKeepsLayer.lean.
- NO STATEMENT HERE ENDS IN A THREAD's OWN LETTER: that join, with the number of the shared chain's
  end, which wants a third public premise: E2E/KeyKeepsAt.lean.
- EQUATIONS ALONE. That an item which is open across such a sub-protocol says behind it what it said
  in front: E2E/KeyRides.lean, for the first chain.
- The two premises on the public values are not shown here.

-/
import E2E.KeyThreads
import E2E.KeyKeepsEq
import Johnson.RunOne.KeyTenAt
import Johnson.RunOne.KeyKeepsAt23
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (FirstState Claim Lookup lookupsOf firstChain)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (St₂ St₃ front₂ front₂_same chainEnd_same sources_same)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

/-! ## The payers -/

/-- A yes of a chain's last sub-protocol hands the state on as it was. -/
theorem end_same {S : Type} (asks : S → VerifiableInference.Desc.ChainEnd.Clauses) (s s' : S)
    (h : ((VerifiableInference.Desc.ChainEnd.refuse (asks s)).map fun _ => s) = .ok s') :
    s' = s :=
  chainEnd_same (Cl := Unit) 0 0 false [] asks s [] [] s' h

section First
variable (one : OnBytes.Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (set : OnBytes.Params.Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)
  (other : Nat → FirstState → FirstState → Prop)

/-- **The first chain's ten.** -/
theorem keeps_paid₁ (hl : lookupsOf one = [x₀, x₁]) (bw : Block FirstState Claim)
    (hw : VerifiableInference.Desc.Key.sendW one VerifiableInference.Desc.Key.pieces
      (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.batchRound D))
      (VerifiableInference.Desc.Key.groupsTold told
        (VerifiableInference.Desc.Key.rootsBefore D (VerifiableInference.Desc.Key.lastSendRound D))
        (VerifiableInference.Desc.Key.rootsAt D (VerifiableInference.Desc.Key.lastSendRound D))) =
      some bw) (ft : Nat) :
    ∀ b ∈ [2, 3, 6, 7, 8, 9, 12, 13, 14, 18], ∀ blk,
      (firstChain one D told set N).blocksInOrder[b]? = some blk → ∀ s s', StepYes ft blk s s' →
      eq₁ one other b s s' := by
  intro b hb blk hblk s s' hy
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [dec_laid0 one D told set N x₀ x₁ hl blk hblk] at e
    exact lay_ok one set 0 x₀ s s' e
  · exact yes_caller0 one D told set N x₀ x₁ hl blk hblk s rs gs s' e
  · rw [dec_behind0 one D told set N x₀ x₁ hl blk hblk] at e
    exact after_ok one set 0 x₀ s s' e
  · rw [dec_cleared0 one D told set N x₀ x₁ hl blk hblk] at e
    exact clear_ok one set 0 x₀ s s' e
  · rw [dec_laid1 one D told set N x₀ x₁ hl blk hblk] at e
    exact lay_ok one set 1 x₁ s s' e
  · exact yes_caller1 one D told set N x₀ x₁ hl blk hblk s rs gs s' e
  · rw [dec_behind1 one D told set N x₀ x₁ hl blk hblk] at e
    exact after_ok one set 1 x₁ s s' e
  · rw [dec_cleared1 one D told set N x₀ x₁ hl blk hblk] at e
    exact clear_ok one set 1 x₁ s s' e
  · exact yes_rngRows one D told set N x₀ x₁ hl blk hblk s rs gs s' e
  · obtain ⟨asks, ha⟩ := dec_seal one D told set N x₀ x₁ hl bw hw blk hblk
    rw [ha] at e
    exact seal_ok asks s s' e

end First

section Later
open AtPublicFiles.AtFiles (keyFileDescription flat_last)
variable (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)

/-- **The shared chain's front and end.** The end's number is said as the list's length less one. -/
theorem keeps_paid₂ (ft : Nat) :
    (∀ blk, (keyFileDescription Xs N P).shared.blocksInOrder[0]? = some blk → ∀ s s', StepYes ft blk s s' → s' = s) ∧
      ∀ blk, (keyFileDescription Xs N P).shared.blocksInOrder[(keyFileDescription Xs N P).shared.blocksInOrder.length - 1]? = some blk →
        ∀ s s', StepYes ft blk s s' → s' = s := by
  constructor
  · intro blk hblk s s' hy
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    have hb : ∃ b₀, (keyFileDescription Xs N P).shared.blocksInOrder[0]? = some b₀ ∧
        ∀ s rs gs, b₀.decide s rs gs = (front₂ Xs).decide s rs gs := ⟨_, rfl, fun _ _ _ => rfl⟩
    obtain ⟨b₀, e₀, hd⟩ := hb
    rw [e₀] at hblk
    cases hblk
    rw [hd] at e
    exact front₂_same Xs s rs gs s' e
  · intro blk hblk s s' hy
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    obtain ⟨b', e', -, -, -, hd⟩ := flat_last (keyFileDescription Xs N P).shared
    rw [e'] at hblk
    cases hblk
    rw [hd] at e
    exact end_same (S := St₂) (fun d => VerifiableInference.Desc.ChainEnd.untestedL d.st) s s' e

/-- **The last chain's test on the taken trees' sources, and its end.** -/
theorem keeps_paid₃ (ft : Nat) :
    (∀ blk, (keyFileDescription Xs N P).second.blocksInOrder[1]? = some blk → ∀ s s', StepYes ft blk s s' → s' = s) ∧
      ∀ blk, (keyFileDescription Xs N P).second.blocksInOrder[(keyFileDescription Xs N P).second.blocksInOrder.length - 1]? = some blk →
        ∀ s s', StepYes ft blk s s' → s' = s := by
  constructor
  · intro blk hblk s s' hy
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    have hb : ∃ b₀, (keyFileDescription Xs N P).second.blocksInOrder[1]? = some b₀ ∧
        ∀ s rs gs, b₀.decide s rs gs = (VerifiableInference.Desc.Third.takenSources
          (VerifiableInference.Desc.Key.ownTest P)).decide s rs gs := ⟨_, rfl, fun _ _ _ => rfl⟩
    obtain ⟨b₀, e₀, hd⟩ := hb
    rw [e₀] at hblk
    cases hblk
    rw [hd] at e
    exact sources_same (VerifiableInference.Desc.Key.ownTest P) s rs gs s' e
  · intro blk hblk s s' hy
    obtain ⟨rs, gs, e⟩ := stepYes_decide hy
    obtain ⟨b', e', -, -, -, hd⟩ := flat_last (keyFileDescription Xs N P).second
    rw [e'] at hblk
    cases hblk
    rw [hd] at e
    exact end_same (S := St₃) (fun d => VerifiableInference.Desc.ChainEnd.untestedL d.st) s s' e

end Later

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.end_same
#print axioms AtPublicFiles.KeyThread.keeps_paid₁
#print axioms AtPublicFiles.KeyThread.keeps_paid₂
#print axioms AtPublicFiles.KeyThread.keeps_paid₃
