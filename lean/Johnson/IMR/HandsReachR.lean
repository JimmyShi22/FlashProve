-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HandsReachR.lean: KIND-FREE: IT IMPORTS Johnson/IMR/HandsReach.lean ALONE: THE TOOL
handsR_of_counts | handsR_of_same OF THAT FILE FOR A SHARE THAT ALREADY ENDS IN HandsR AT THE FENCE
«REACHED» (or at a fence that «reached» implies) UNDER THE PLAN's TWO COUNTS: they fall there too.
(handsR_of_counts takes a share that ends in Hands:
it does not take close0_R | behind_R [not in this library], which end in HandsR Fk.)
  handsR_of_countsR · handsR_of_sameR   (hT → hM → HandsR (RF …) …) ⟹ HandsR (RF …) …, under «bookAt at every reached state» and how many trees and oracle messages an accepting step adds.
What is not claimed. HandsR at any sub-protocol. bookAt at any state. No soundness.
-/
import Johnson.IMR.HandsReach

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers bookAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

variable {P : Type}

theorem handsR_of_countsR {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b) {dT dM : Nat}
    (adds : ∀ s s', Yes ft b s s' → s'.book.trees.size = s.book.trees.size + dT ∧
      s'.st.oracles.size = s.st.oracles.size + dM)
    (H : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + dT →
      N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + dM →
      HandsR (RF ft bs start z) N links ps E ft k b) :
    HandsR (RF ft bs start z) N links ps E ft k b := by
  have key : ∀ s s', RF ft bs start z k s → Yes ft b s s' →
      HandsR (RF ft bs start z) N links ps E ft k b :=
    fun s s' hf hy =>
      have c := counts_of_reach hB hb hf hy (adds s s' hy).1 (adds s s' hy).2
      H c.1 c.2
  exact ⟨fun s s' hf hy => (key s s' hf hy).mark s s' hf hy,
    fun s s' hf hy => (key s s' hf hy).shape s s' hf hy,
    fun s s' hf hy => (key s s' hf hy).rows s s' hf hy,
    fun s s' hf hy => (key s s' hf hy).members s s' hf hy,
    fun s s' hf hy => (key s s' hf hy).book s s' hf hy,
    fun s s' hf hy => (key s s' hf hy).more s s' hf hy⟩

theorem handsR_of_sameR {N : Numbers} {links : List ModelPart} {ps : List Place} {E : Nat → S → Bool}
    {ft : Nat} {bs : List (Block S Cl)} {start : P → S} {z : P}
    (hB : ∀ k s, Reach ft bs start k (z, s) → bookAt N ps[k]? s = true) {k : Nat}
    {b : Block S Cl} (hb : bs[k]? = some b)
    (same : ∀ s s', Yes ft b s s' → s'.book.trees.size = s.book.trees.size ∧
      s'.st.oracles.size = s.st.oracles.size)
    (H : N.treesAt ps[k + 1]? = N.treesAt ps[k]? → N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? →
      HandsR (RF ft bs start z) N links ps E ft k b) :
    HandsR (RF ft bs start z) N links ps E ft k b :=
  handsR_of_countsR (dT := 0) (dM := 0) hB hb same H

end IM

#print axioms IM.handsR_of_countsR
#print axioms IM.handsR_of_sameR
