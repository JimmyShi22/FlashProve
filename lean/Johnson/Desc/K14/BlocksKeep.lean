-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/BlocksKeep.lean: the blocks of the linear claim's shared rounds (the two sendings
are the kind K1's own block, seated by Block.inside) and the shared chain's front block keep EVERY
relation R on statements that the ground's plain functions keep
(GroundKeeps R): among them the four together: "a statement only grows", "no new mark", "Linked
stays", "behind its mark a group is as it was". Theorems.

  why_ok             a block's yes is its page's function's yes.
  sendAt_keeps       a sending at this chain's state: K1's own block keeps R; enter hands the
                     statement in as it is; leave hands it out as it is, and what the page notes
                     behind the sending keeps R.
  blocks_keep · blocksOr_keep · frontBlock_keeps
  own_blocks_keep_four   the front block and the eight blocks keep the four together.
What is not claimed. Nothing on the two proximity tests' blocks, on the chain's end, or on the chain
as a whole (a proximity test's block lays a mark: it does NOT keep "no new mark"). Nothing on the
small record beside the statement. No soundness of a verifier.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K14.KeepsFour
import Johnson.Desc.K1.Keeps
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Keeps VerifiableInference.Desc.Ground

variable {R : Statement → Statement → Prop}

theorem why_ok {l : Ground.Clauses} {x : Option St} {d : St} (h : why l x = .ok d) :
    x = some d := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- The reading of the statement at the shared chain's record. -/
abbrev stOf : St → Statement := fun d => d.st

/-- A sending at this chain's state. -/
theorem sendAt_keeps (H : GroundKeeps R) (P : P14) (n : String) (Q : K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → R d.st d'.st) :
    Decides (By R stOf) (sendAt P n Q inFront groups behind) := by
  intro s rs gs s' h
  unfold sendAt at h
  dsimp only [Block.inside] at h
  obtain ⟨t, h0, h1⟩ := ebind_ok h
  obtain ⟨t', h2, h3⟩ := ebind_ok h1
  cases h0
  have hq := K1.Rel.sendOwn_keeps (Cl := Unit) H Q _ _ _ _ h2
  exact H.trans hq (hb _ _ _ (named_ok h3))

theorem blocks_keep (H : GroundKeeps R) (P : P14) (l : List (Block St Unit))
    (h : blocks P = some l) : ∀ b ∈ l, Decides (By R stOf) b := by
  unfold blocks at h
  dsimp only at h
  obtain ⟨w, _, h⟩ := obind_ok h
  cases h
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun d rs _ d' hd => linPoint_keeps H _ d d' rs (why_ok hd)
  · exact sendAt_keeps H _ _ _ _ _ _ fun d ids d' k => behindU_keeps H _ d d' ids k
  · exact fun d rs _ d' hd => laysRec_keeps H _ d d' rs (why_ok hd)
  · exact fun d rs gs d' hd => loc_keeps H _ d d' rs gs (why_ok hd)
  · exact sendAt_keeps H _ _ _ _ _ _ fun d ids d' k => behindOmega_keeps H _ d d' ids k
  · exact fun d rs _ d' hd => joins_keeps H _ d d' rs (why_ok hd)
  · exact fun d rs _ d' hd => linZeta_keeps H d d' rs (why_ok hd)
  · exact fun d rs _ d' hd => split_keeps H _ d d' rs (why_ok hd)

theorem blocksOr_keep (H : GroundKeeps R) (P : P14) :
    ∀ b ∈ blocksOr P, Decides (By R stOf) b := by
  unfold blocksOr
  cases h : blocks P with
  | some l => exact blocks_keep H P l h
  | none =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · intro d _ _ d' hd
      cases hd
      exact H.refl _
    · cases hb

theorem frontBlock_keeps (H : GroundKeeps R) (c : Model.Verify.Chains) :
    Decides (By R stOf) (frontBlock c) := by
  intro d _ _ d' hd
  cases hd
  exact H.refl _

/-- **The front block and the eight blocks keep all four.** -/
theorem own_blocks_keep_four (c : Model.Verify.Chains) (P : P14) :
    ∀ b ∈ frontBlock c :: blocksOr P, Decides (By Four stOf) b := by
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact frontBlock_keeps groundKeeps_four c
  · exact blocksOr_keep groundKeeps_four P b hb

end Desc.K14
