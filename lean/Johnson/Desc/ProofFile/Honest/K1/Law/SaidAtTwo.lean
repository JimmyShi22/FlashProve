-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SaidAtTwo.lean: the kind K1's opening and its sending of W
(numbers 2 and 356 of the first chain's flat list): what every public item that is open at the
border behind (3; 357) says beside its test (the meaning's field pubP) holds at EVERY state, at a
meaning whose pubP is the composed one and whose extra rows are moreAll. No step is asked.

What this file proves. No definition. Five theorems.
  - Three facts on the written lists, by evaluation in Lean's kernel, with no premise. said_three,
    said_W: at border 3, and at border 357, no "left" and no "leftOn" is open, and every other open
    public item is of hasRow's sort or one to which the table gives no sentence (p1Item, saysNone).
    said_some_not: the same test says no at some border below 358: so it can fail; at which border,
    and by which of its arms, is not said.
  - pubP_three, pubP_W: so, at a meaning Mg with Mg.pubP = (fillK3 X3 D3 (fillP1 d1 rw1 A cr
    mgBase)).pubP (hP) and Mg.more = moreAll (hm), at every a : Pp × S: Mg.pubP q a for every q in
    P1K2.pubAt Mg linksFull (flatPlacesOf linksFull true) at border 3; at border 357.
No thread, no prover and no file's bytes occur.

How it fits. pubP_later_all (Johnson/Desc/ProofFile/Honest/K1/Law/DoorFactsAtAll.lean) has the same
end behind each of the fifty later sendings, under the same hP and hm; there a "leftOn" can be open
and must ride over the step. At these two borders none is open: so neither a step, nor the head, nor
anything at the state in front is asked. The proof is pubP_later_all's, less its arm on leftOn.

Kin in the library. mgAll_pubP_said (Johnson/Desc/Sound/MgBase.lean): at the composed meaning
mgAll 𝔇 mgBase itself, at an item q to which saysNone gives "no sentence is meant", the sentence
of q holds at every state. mgAll_pubP_else (the same file): under the premise whoSays q = saysNone
q, which left, leftOn and hasRow do not meet, the sentence is the table's own word.
What comes here: that at these two borders no left and no
leftOn is open (two closed facts, at moreAll, linksFull and flatPlacesOf linksFull true), hasRow's
sentence, and the form with hP and hm as premises on a meaning Mg, which is pubP_later_all's.

Limits. hP and hm are premises on the meaning: not proved here. The sentences that hold here are the
empty ones: the items that are open at these two borders say nothing beside their tests. At the full
size's written lists alone. The three closed facts are evaluations in Lean's kernel (decide
+kernel). Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.DoorFactsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Strs)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf pubSets saysNone PubData pubAll)
open VerifiableInference.Desc.First.FillP1 (p1Item fillP1 PileWit)
open VerifiableInference.Desc.First.Look (fillK3)
open VerifiableInference.Desc.Sound (linksFull moreAll mgBase)

/-! ## 1 Three closed tests on the table, by evaluation in Lean's kernel -/

/-- **Behind number 2**: no "left" and no "leftOn" is open; every other open item is of hasRow's
sort or one to which the table gives no sentence. -/
theorem said_three :
    (((pubSets moreAll linksFull (flatPlacesOf linksFull true))[2 + 1]?.getD []).all fun q =>
      match q with
      | .left _ => false
      | .leftOn _ => false
      | _ => p1Item q || (saysNone q).isSome) = true := by
  decide +kernel

/-- **Behind number 356**: the same. -/
theorem said_W :
    (((pubSets moreAll linksFull (flatPlacesOf linksFull true))[356 + 1]?.getD []).all fun q =>
      match q with
      | .left _ => false
      | .leftOn _ => false
      | _ => p1Item q || (saysNone q).isSome) = true := by
  decide +kernel

/-- **The test can fail**: at some border below 358 it says no. -/
theorem said_some_not : ((List.range 358).all fun k =>
    (((pubSets moreAll linksFull (flatPlacesOf linksFull true))[k]?.getD []).all fun q =>
      match q with
      | .left _ => false
      | .leftOn _ => false
      | _ => p1Item q || (saysNone q).isSome)) = false := by
  decide +kernel

/-! ## 2 The sentences behind -/

variable {Pp W : Type}

/-- **What every public item that is open at border 3 says beside its test holds at every
state.** -/
theorem pubP_three {nR kC : ℕ} (X3 : OnBytes.Model.Verify.Public) (D3 : First.Look.Sent)
    (d1 : First.FillP1.PubData) (rw1 : Pp × S → W → PileWit nR kC)
    (A : ℕ → Pp × S → W → ℕ → ℕ → ℕ → Cb.Gl.E) (cr : ℕ → Pp × S → Strs → W → Prop)
    (Mg : Meaning Pp W) (hP : Mg.pubP = (fillK3 X3 D3 (fillP1 d1 rw1 A cr mgBase)).pubP)
    (hm : Mg.more = moreAll) (a : Pp × S) :
    ∀ q ∈ P1K2.pubAt Mg linksFull (flatPlacesOf linksFull true) (2 + 1), Mg.pubP q a := by
  intro q hq
  have hq' : q ∈ (pubSets moreAll linksFull (flatPlacesOf linksFull true))[2 + 1]?.getD [] := by
    unfold P1K2.pubAt at hq
    rw [hm] at hq
    exact hq
  have ht := List.all_eq_true.1 said_three q hq'
  rw [hP]
  cases q with
  | left m => exact absurd ht (by simp)
  | leftOn m => exact absurd ht (by simp)
  | hasRow m => exact trivial
  | _ => exact ht

/-- **The same at border 357.** -/
theorem pubP_W {nR kC : ℕ} (X3 : OnBytes.Model.Verify.Public) (D3 : First.Look.Sent)
    (d1 : First.FillP1.PubData) (rw1 : Pp × S → W → PileWit nR kC)
    (A : ℕ → Pp × S → W → ℕ → ℕ → ℕ → Cb.Gl.E) (cr : ℕ → Pp × S → Strs → W → Prop)
    (Mg : Meaning Pp W) (hP : Mg.pubP = (fillK3 X3 D3 (fillP1 d1 rw1 A cr mgBase)).pubP)
    (hm : Mg.more = moreAll) (a : Pp × S) :
    ∀ q ∈ P1K2.pubAt Mg linksFull (flatPlacesOf linksFull true) (356 + 1), Mg.pubP q a := by
  intro q hq
  have hq' : q ∈ (pubSets moreAll linksFull (flatPlacesOf linksFull true))[356 + 1]?.getD [] := by
    unfold P1K2.pubAt at hq
    rw [hm] at hq
    exact hq
  have ht := List.all_eq_true.1 said_W q hq'
  rw [hP]
  cases q with
  | left m => exact absurd ht (by simp)
  | leftOn m => exact absurd ht (by simp)
  | hasRow m => exact trivial
  | _ => exact ht

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.said_three
#print axioms ProofFile.Honest.K1.said_W
#print axioms ProofFile.Honest.K1.said_some_not
#print axioms ProofFile.Honest.K1.pubP_three
#print axioms ProofFile.Honest.K1.pubP_W
