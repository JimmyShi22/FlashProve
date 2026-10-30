-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASideHist.lean: THE KEY FILE's FIRST CHAIN: THE STATE's SIDE OF THE TABLES' PROMISE FROM THE HISTORY: at every verifier's state that the first chain reaches (Reached along the held blocks) ASide one at_ k holds (RunOne/KeyASide.lean: the book-keeping shape₁ … k · Placed at the open pins · InOrder · MaskWith 1 2), BY FOLDING THE STEPS AT THE BLOCKS' YESES (Top/Fire/Code/ReachedInv.lean).
OBJECT: ASide along a history · USER: KeyASideAtFk.lean (aSide_upto and the twelve steps) · LETTERS: one · at_ · D told set N (the chain's) · the start st₀.
  aStep0 | aStep1   PROVED: at a block that decides and declares as the sending (Public10 | Public11; at_ 0 = (0, 0) · at_ 1 = (1, 0))
  aStep2 · 3 · 6 · 7 · 8 · 9 · 12 · 13 · 14 · 18   PROVED: at (firstChain one D told set N).blocksInOrder[k], where the plan's lookups are a list of two
  Mine one at_ l    the twelve, gathered: at a list l of blocks
  aSide_upto        PROVED: from the start, up to a border K, under the steps below K
  aSide_from        PROVED: from a border j on, where ASide j holds at every state reached at j
SEVEN STEPS ARE NOT HERE AND ENTER AS PREMISES WHERE A BORDER BEHIND THEM IS WANTED: 4 | 10 (K3's blocks) · 5 | 11 (the layers) · 15 (the ranges' test): other files' · 16 | 17 (astep16 | astep17: Top/Fire/Code/RowASteps.lean). WITHOUT ANY OF THEM: BORDERS 0 … 4. astep16 and astep17 are declared in that file, Johnson/Top/Fire/Code/RowASteps.lean, which is in this library, and the library's build takes it in (lakefile.toml).
AN IMPLICATION: EMPTY WHERE NOTHING IS REACHED. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.ReachedInv
import Johnson.RunOne.KeyASide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup Xi)
open Johnson.RunOne.KeyRows1

section
variable (one : OneTime) (at_ : Where)

theorem aStep0 (N : Pieces) (groups : List (List Nat)) (Pb : Public10 one N groups) (hat : at_ 0 = (0, 0)) (b : Block FirstState Claim)
    (hd : b.decide = (sendIndexMasks one N groups : Block FirstState Claim).decide) (hr : b.rounds = K1.rounds (parIdx one N groups)) :
    StepInv b (ASide one at_ 0) (ASide one at_ 1) := by
  intro s s' rs gs hf hy hA
  rw [hr] at hf
  have hlen := roundsFit_length _ _ hf
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  rw [hd] at hy
  obtain ⟨a0, -, c0, d0⟩ := front0 one s hA.1
  have hf' : roundsFit (K1.rounds (parIdx one N groups)) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf
  exact aSide_send0 one at_ hat s s' (sent0_of one N groups Pb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 c0 d0 hA.2.2.1) hA

theorem aStep1 (N : Pieces) (groups : List (List Nat)) (Pb : Public11 one N groups) (hst : 1 ≤ one.ranges.stages.length) (hat : at_ 1 = (1, 0)) (b : Block FirstState Claim)
    (hd : b.decide = (sendOwnMessage one N groups : Block FirstState Claim).decide) (hr : b.rounds = K1.rounds (parMsg' one N groups)) :
    StepInv b (ASide one at_ 1) (ASide one at_ 2) := by
  intro s s' rs gs hf hy hA
  rw [hr] at hf
  have hlen := roundsFit_length _ _ hf
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  rw [hd] at hy
  obtain ⟨a0, b0, c0, d0, e0, -⟩ := front1 one s hA.1
  have hf' : roundsFit (K1.rounds (parMsg' one N groups)) ([r₁, r₂].map noDigest) = true := by rw [roundsFit_noDigest']; exact hf
  exact aSide_send1 one at_ hst hat s s' (laid1_of one N groups Pb s s' (noDigest r₁) (noDigest r₂) gs hf' hy a0 b0 c0 d0 e0 hA.2.2.1) hA

variable (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)

theorem aStep2 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[2]? = some b) : StepInv b (ASide one at_ 2) (ASide one at_ 3) := by
  intro s s' rs gs _ hy hA
  obtain rfl := lay_ok one set 0 x₀ s s' ((dec_laid0 one D told set N x₀ x₁ hl b h s _ gs).symm.trans hy)
  exact aSide_step one at_ 2 s' s' (by decide) (by omega) (sh_2_3 one s') rfl id hA

theorem aStep8 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[8]? = some b) : StepInv b (ASide one at_ 8) (ASide one at_ 9) := by
  intro s s' rs gs _ hy hA
  obtain rfl := lay_ok one set 1 x₁ s s' ((dec_laid1 one D told set N x₀ x₁ hl b h s _ gs).symm.trans hy)
  exact aSide_step one at_ 8 s' s' (by decide) (by omega) (sh_8_9 one s') rfl id hA

theorem aStep6 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[6]? = some b) : StepInv b (ASide one at_ 6) (ASide one at_ 7) := by
  intro s s' rs gs _ hy hA
  obtain rfl := after_ok one set 0 x₀ s s' ((dec_behind0 one D told set N x₀ x₁ hl b h s _ gs).symm.trans hy)
  exact aSide_step one at_ 6 s' s' (by decide) (by omega) (sh_6_7 one s') rfl id hA

theorem aStep12 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[12]? = some b) : StepInv b (ASide one at_ 12) (ASide one at_ 13) := by
  intro s s' rs gs _ hy hA
  obtain rfl := after_ok one set 1 x₁ s s' ((dec_behind1 one D told set N x₀ x₁ hl b h s _ gs).symm.trans hy)
  exact aSide_step one at_ 12 s' s' (by decide) (by omega) (sh_12_13 one s') rfl id hA

theorem aStep7 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[7]? = some b) : StepInv b (ASide one at_ 7) (ASide one at_ 8) := by
  intro s s' rs gs _ hy hA
  obtain rfl := clear_ok one set 0 x₀ s s' ((dec_cleared0 one D told set N x₀ x₁ hl b h s _ gs).symm.trans hy)
  exact aSide_step one at_ 7 s (clr s) (by decide) (by omega) (sh_7_8 one s) rfl id hA

theorem aStep13 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[13]? = some b) : StepInv b (ASide one at_ 13) (ASide one at_ 14) := by
  intro s s' rs gs _ hy hA
  obtain rfl := clear_ok one set 1 x₁ s s' ((dec_cleared1 one D told set N x₀ x₁ hl b h s _ gs).symm.trans hy)
  exact aSide_step one at_ 13 s (clr s) (by decide) (by omega) (sh_13_14 one s) rfl id hA

theorem aStep3 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[3]? = some b) : StepInv b (ASide one at_ 3) (ASide one at_ 4) := by
  intro s s' rs gs _ hy hA
  obtain ⟨d', Fk, hm, rfl, H, Hf⟩ := yes_caller0 one D told set N x₀ x₁ hl b h s _ gs s' hy
  exact aSide_call0 one at_ s d' Fk hm H Hf hA

theorem aStep9 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[9]? = some b) : StepInv b (ASide one at_ 9) (ASide one at_ 10) := by
  intro s s' rs gs _ hy hA
  obtain ⟨d', Fk, hm, rfl, H, Hf⟩ := yes_caller1 one D told set N x₀ x₁ hl b h s _ gs s' hy
  exact aSide_call1 one at_ s d' Fk hm H Hf hA

theorem aStep14 (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[14]? = some b) : StepInv b (ASide one at_ 14) (ASide one at_ 15) := by
  intro s s' rs gs _ hy hA
  obtain ⟨d', rfl, H, h2⟩ := yes_rngRows one D told set N x₀ x₁ hl b h s _ gs s' hy
  exact aSide_rows one at_ s d' H h2 hA

theorem aStep18 (hl : lookupsOf one = [x₀, x₁]) (bw : Block FirstState Claim)
    (hw : sendW one pieces (rootsBefore D (batchRound D)) (groupsTold told (rootsBefore D (lastSendRound D)) (rootsAt D (lastSendRound D))) = some bw)
    (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[18]? = some b) : StepInv b (ASide one at_ 18) (ASide one at_ 19) := by
  intro s s' rs gs _ hy hA
  obtain ⟨asks, ha⟩ := dec_seal one D told set N x₀ x₁ hl bw hw b h
  rw [ha] at hy
  obtain rfl : s = s' := by
    cases hq : ChainEnd.refuse (asks s) with
    | error e => rw [hq] at hy; cases hy
    | ok u => rw [hq] at hy; exact Except.ok.inj hy
  exact aSide_step one at_ 18 s s (by decide) (by omega) (sh_18_19 one s) rfl id hA

end

section
variable {P : Type} (one : OneTime) (at_ : Where) (ft : ℕ) (l : List (Block FirstState Claim)) (st₀ : P × FirstState → Prop)

/-- **From the start, up to the border K.** -/
theorem aSide_upto (K : ℕ) (h0 : ∀ a, st₀ a → ASide one at_ 0 a.2)
    (hs : ∀ k, k < K → ∀ b, l[k]? = some b → StepInv b (ASide one at_ k) (ASide one at_ (k + 1)))
    (k : ℕ) (a : P × FirstState) (hk : k ≤ K) (h : Reached ft (l.map held) st₀ k a) : ASide one at_ k a.2 :=
  reached_held_inv ft l st₀ (ASide one at_) K h0 hs k a hk h

/-- **From a border j on.** -/
theorem aSide_from (j K : ℕ) (hj : ∀ a, Reached ft (l.map held) st₀ j a → ASide one at_ j a.2)
    (hs : ∀ k, j ≤ k → k < K → ∀ b, l[k]? = some b → StepInv b (ASide one at_ k) (ASide one at_ (k + 1)))
    (n : ℕ) (a : P × FirstState) (hk : j + n ≤ K) (h : Reached ft (l.map held) st₀ (j + n) a) : ASide one at_ (j + n) a.2 :=
  reached_held_from ft l st₀ (ASide one at_) j K hj hs n a hk h

end

end LPFD

#print axioms LPFD.aStep0
#print axioms LPFD.aStep1
#print axioms LPFD.aStep2
#print axioms LPFD.aStep3
#print axioms LPFD.aStep6
#print axioms LPFD.aStep7
#print axioms LPFD.aStep8
#print axioms LPFD.aStep9
#print axioms LPFD.aStep12
#print axioms LPFD.aStep13
#print axioms LPFD.aStep14
#print axioms LPFD.aStep18
#print axioms LPFD.aSide_upto
#print axioms LPFD.aSide_from
