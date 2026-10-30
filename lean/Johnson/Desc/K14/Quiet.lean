-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Quiet.lean: THE LINEAR CLAIM's SHARED ROUNDS: the page's eight functions, the eight
blocks, the shared chain's front block: each keeps EVERY relation R on statements that the ground's
eight plain functions keep which ask nothing of their caller (Johnson/Desc/GroundQuiet.lean) and
that the admitting of a sample keeps where the rows are on the message (Johnson/Desc/K1/Quiet.lean:
the two sendings are kind K1's own block). Theorems.

  linPoint · behindU · laysRec · loc · behindOmega · joins · linZeta · split: each name with _rel
  behind it: THE PROOFS ARE THOSE OF Johnson/Desc/K14/Keeps.lean TO THE SIGN: they call the eight
  functions alone.
  sendAt_steps         a sending at this chain's record: its step keeps R, where its test on the
                       plan passes.
  blocks_steps · blocksOr_steps · frontBlock_steps   the eight blocks; the front block.
What is not claimed. Nothing on the two tests' blocks or on the last block: these are arguments of
the chain.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K14.Keeps
import Johnson.Desc.K1.Quiet
import Johnson.Desc.StepKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain VerifiableInference.Desc VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Keeps

variable {R : Statement → Statement → Prop}

/-- The shared point: the two groups are opened. -/
theorem linPoint_rel (H : GroundQuiet R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : linPoint p d rs = some d') :
    R d.st d'.st := by
  unfold linPoint at h
  split at h
  · obtain ⟨_, _, h⟩ := obind_ok h
    obtain ⟨⟨gU, d₁⟩, h1, h⟩ := obind_ok h
    dsimp only at h
    split at h
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h
      exact H.trans (H.newGroup d d₁ _ _ gU h1) (H.newGroup d₁ y.2 _ _ y.1 h2)
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h2
      cases h
      exact H.newGroup d d₁ _ _ gU h1
  · cases h

/-- Behind the folded row's sending: the statement is left as it is. -/
theorem behindU_rel (H : GroundQuiet R) (p : Par) (d d' : St) (ids : Array Nat)
    (h : behindU p d ids = some d') : R d.st d'.st := by
  unfold behindU at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     exact H.refl _)

/-- The folded row joins its group; the record's rows are laid. -/
theorem laysRec_rel (H : GroundQuiet R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : laysRec p d rs = some d') :
    R d.st d'.st := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  obtain ⟨rows, _, h⟩ := obind_ok h
  exact H.trans (H.join _ _ _ _ _ h1) (H.addRows _ _ _ _ h)

/-- The rows at the locations drawn are laid. -/
theorem loc_rel (H : GroundQuiet R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : loc p d rs gs = some d') : R d.st d'.st := by
  unfold loc at h
  split at h
  · dsimp only at h
    obtain ⟨rows, _, h⟩ := obind_ok h
    exact H.addRows _ _ _ _ h
  · cases h

/-- Behind Omega's sending: the statement is left as it is. -/
theorem behindOmega_rel (H : GroundQuiet R) (p : Par) (d d' : St) (ids : Array Nat)
    (h : behindOmega p d ids = some d') : R d.st d'.st := by
  unfold behindOmega at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     exact H.refl _)

/-- Omega and the split's message join their groups. -/
theorem joins_rel (H : GroundQuiet R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : joins p d rs = some d') :
    R d.st d'.st := by
  unfold joins at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  split at h
  · obtain ⟨d₂, h2, h⟩ := obind_ok h
    exact H.trans (H.trans (H.join _ _ _ _ _ h1) (H.join _ _ _ _ _ h2)) (H.join _ _ _ _ _ h)
  · cases h
    exact H.join _ _ _ _ _ h1

/-- The second point: the statement is left as it is. -/
theorem linZeta_rel (H : GroundQuiet R) (d d' : St) (rs : List Fmt.RoundView)
    (h : linZeta d rs = some d') :
    R d.st d'.st := by
  unfold linZeta at h
  split at h
  · cases h; exact H.refl _
  · cases h

/-- The split: an entry of a mask is taken; two rows are laid. -/
theorem split_rel (H : GroundQuiet R) (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : split p d rs = some d') :
    R d.st d'.st := by
  unfold split at h
  dsimp only at h
  obtain ⟨row, _, h⟩ := obind_ok h
  split at h
  · exact H.addRow _ _ _ _ h
  · split at h
    · obtain ⟨mu, _, h⟩ := obind_ok h
      obtain ⟨G, _, h⟩ := obind_ok h
      obtain ⟨_, _, h⟩ := obind_ok h
      obtain ⟨⟨kappa, d₁⟩, h1, h⟩ := obind_ok h
      dsimp only at h
      obtain ⟨d₂, h2, h⟩ := obind_ok h
      exact H.trans (H.trans (H.takeMask _ _ _ _ h1) (H.addRow _ _ _ _ h2)) (H.addRow _ _ _ _ h)
    · obtain ⟨mu, hm, h⟩ := obind_ok h
      cases hm
  · cases h

/-- A block's yes is its page's function's yes. -/
theorem why_some {l : Ground.Clauses} {x : Option St} {d : St} (h : why l x = .ok d) :
    x = some d := by
  cases x with
  | none => cases h
  | some y => cases h; rfl

/-- R, read at the shared chain's record. -/
def RelAt (R : Statement → Statement → Prop) (a b : St) : Prop := R a.st b.st

/-- **A sending at this chain's record**: its step keeps R where its test on the plan passes. -/
theorem sendAt_steps (H : GroundQuiet R) (hA : K1.AdmitOn R) (P : P14) (n : String) (Q : K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → R d.st d'.st) :
    Steps (RelAt R) (sendAt P n Q inFront groups behind) := by
  intro hp ft s rs cols s' k hs
  obtain ⟨hfit, gs, h⟩ := step_fit ft _ s s' rs cols k hs
  have hB : K1.planOkOwn Q = true := by
    unfold sendAt at hp
    simp only [Block.inside, Bool.and_eq_true] at hp
    exact hp.1.1.1.1
  unfold sendAt at h
  dsimp only [Block.inside] at h
  obtain ⟨t, h0, h1⟩ := ebind_ok h
  obtain ⟨t', h2, h3⟩ := ebind_ok h1
  cases h0
  have hq := K1.sendOwn_rel (Cl := Unit) H hA Q hB _ _ rs _ hfit h2
  exact H.trans hq (hb _ _ _ (named_ok h3))

/-- The eight blocks. -/
theorem blocks_steps (H : GroundQuiet R) (hA : K1.AdmitOn R) (P : P14) (l : List (Block St Unit))
    (h : blocks P = some l) : ∀ b ∈ l, Steps (RelAt R) b := by
  unfold blocks at h
  dsimp only at h
  obtain ⟨w, _, h⟩ := obind_ok h
  cases h
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact steps_of_decides fun d rs _ d' hd => linPoint_rel H _ d d' rs (why_some hd)
  · exact sendAt_steps H hA _ _ _ _ _ _ fun d ids d' k => behindU_rel H _ d d' ids k
  · exact steps_of_decides fun d rs _ d' hd => laysRec_rel H _ d d' rs (why_some hd)
  · exact steps_of_decides fun d rs gs d' hd => loc_rel H _ d d' rs gs (why_some hd)
  · exact sendAt_steps H hA _ _ _ _ _ _ fun d ids d' k => behindOmega_rel H _ d d' ids k
  · exact steps_of_decides fun d rs _ d' hd => joins_rel H _ d d' rs (why_some hd)
  · exact steps_of_decides fun d rs _ d' hd => linZeta_rel H d d' rs (why_some hd)
  · exact steps_of_decides fun d rs _ d' hd => split_rel H _ d d' rs (why_some hd)

/-- The eight blocks, or the one that fails its test on the plan. -/
theorem blocksOr_steps (H : GroundQuiet R) (hA : K1.AdmitOn R) (P : P14) :
    ∀ b ∈ blocksOr P, Steps (RelAt R) b := by
  unfold blocksOr
  cases h : blocks P with
  | some l => exact blocks_steps H hA P l h
  | none =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · refine steps_of_decides fun d _ _ d' hd => ?_
      cases hd
      exact H.refl _
    · cases hb

/-- The shared chain's front block. -/
theorem frontBlock_steps (H : GroundQuiet R) (c : Model.Verify.Chains) :
    Steps (RelAt R) (frontBlock c) := by
  refine steps_of_decides fun d _ _ d' hd => ?_
  cases hd
  exact H.refl _

end Desc.K14
