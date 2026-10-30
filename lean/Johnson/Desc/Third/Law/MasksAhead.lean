-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/MasksAhead.lean: EVERY PLAN THAT THE PLANNER MAKES SENDS THE MASKS AHEAD, UP
TO THE VERIFIER's OWN CHAINS: masksAhead_of_linSized
(Johnson/Desc/Last/ShapeMask.lean: what linSized returns has masksAhead = true) carried up through
proofSized, sized, configure and Model.Verify.chainsOf; and so at the parameters of the last chain's
first block as its seat reads them (p₁₄Z). Theorems; no definition.
masksAhead_of_linSized is CALLED: it is not typed here.


WHY. The one typed filling of the book-keeping of the last chain's promise (shapeAt,
Johnson/Desc/Last/ShapeAt.lean) has the clause "the mask has come"; the chain's start asks
mask.isSome == S.masksAhead. At a shape whose masks are not sent ahead that promise is empty at
every border. ShapeMask.lean leaves open that the seated p is p₁₄Z at an x out of linSized: here
that is had wherever the chains are chainsOf's.

OBJECT   proofSized · sized · configure (OnBytes/Params/Configure.lean) · Model.Verify.chainsOf
         (OnBytes/Model/VerifyChains.lean): the texts.
USER     whoever shows a member of the last chain's promise at fillZ
         (Johnson/Desc/Last/ShapeRowZero.lean); p₁₄Z_masksAhead is called in
         Johnson/Desc/Last/ShapeDoorAhead.lean.
LETTERS  none but the texts' own.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean): it shuts one way in which
         the promise at border 0 could be empty; it pays no field.

  proofSized_masksAhead · sized_masksAhead · configure_masksAhead
  chainsOf_masksAhead  **at the verifier's own chains.**
  p₁₄Z_masksAhead      at the last chain's first block's parameters, read off these chains.
  mask_at_chains       there the start's record has a mask's number: by mask_of_start.
What is not claimed. That a description is seated at chains that chainsOf returns: the seat's
matter. That the start says yes anywhere. A shape read from parameter bytes bears a flag of its own
(OnBytes/Params/Items.lean): nothing is said of it. No member. No soundness.

-/
import OnBytes.Params.ConfigureLaws
import OnBytes.Model.VerifyChains
import Johnson.Desc.Last.ShapeMask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- The sizes of a proof's chains send the masks ahead. -/
theorem proofSized_masksAhead {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) : z.batch.shape.masksAhead = true := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, _, h⟩ := opt_bind h
  obtain ⟨stages, _, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  replace h := opt_guard h
  obtain ⟨⟨batch, c2⟩, hb, h⟩ := opt_bind h
  cases h
  exact VerifiableInference.Desc.Last.masksAhead_of_linSized hb

/-- So does what sized returns. -/
theorem sized_masksAhead {l : Lines} {x : Shapes} {z : Sized} (h : sized l x = .ok z) :
    z.proof.batch.shape.masksAhead = true := by
  unfold sized at h
  extract_lets at h
  replace h := exc_guard h
  obtain ⟨proof, hp, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨key, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨⟨link, codes⟩, hl, h⟩ := exc_bind h
  replace h := exc_guard h
  replace h := exc_guard h
  cases h
  exact proofSized_masksAhead (orRefuse_ok hp)

/-- So does what configure returns. -/
theorem configure_masksAhead {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    made.sized.proof.batch.shape.masksAhead = true := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, he, h⟩ := exc_bind h
  have hm : made.sized = z := by
    split at h
    · obtain ⟨_, _, h⟩ := exc_bind h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      replace h := exc_guard h
      cases h
      rfl
    · cases h
  rw [hm]
  exact sized_masksAhead hz

end OnBytes.Params

namespace OnBytes.Model.Verify
open OnBytes.Params

/-- **At the verifier's own chains.** -/
theorem chainsOf_masksAhead {X : Public} {layoutFile : Option ByteArray} {cfg : ByteArray}
    {c : Chains} (h : chainsOf X layoutFile cfg = .ok c) :
    c.made.sized.proof.batch.shape.masksAhead = true := by
  unfold chainsOf at h
  obtain ⟨⟨links, shapes⟩, _, h⟩ := exc_bind h
  obtain ⟨z, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  split at h
  · cases h
    exact configure_masksAhead hm
  · cases h

/-- At the last chain's first block's parameters, read off these chains. -/
theorem p₁₄Z_masksAhead {X : Public} {layoutFile : Option ByteArray} {cfg : ByteArray}
    {c : Chains} (h : chainsOf X layoutFile cfg = .ok c) :
    (VerifiableInference.Desc.Third.p₁₄Z c.made.sized.proof.set c.made.sized.proof.codes
      c.made.sized.proof.batch).S.masksAhead = true :=
  chainsOf_masksAhead h

/-- **So at these chains the record that the last chain's start returns has a mask's number**: the
clause "the mask has come" of the promise's book-keeping at border 0 asks nothing beyond the start's
yes. -/
theorem mask_at_chains {X : Public} {layoutFile : Option ByteArray} {cfg : ByteArray}
    {c : Chains} (h : chainsOf X layoutFile cfg = .ok c)
    (f : VerifiableInference.Desc.Third.FirstEnd₃) (o : VerifiableInference.Desc.Third.SharedOut)
    (s₀ : VerifiableInference.Desc.Third.S₃)
    (h₀ : VerifiableInference.Desc.Third.start₃E
      (VerifiableInference.Desc.Third.p₁₄Z c.made.sized.proof.set c.made.sized.proof.codes
        c.made.sized.proof.batch).codes
      (VerifiableInference.Desc.Third.p₁₄Z c.made.sized.proof.set c.made.sized.proof.codes
        c.made.sized.proof.batch).S f.st f.book f.roots f.w f.own f.mask f.pending o = .ok s₀) :
    s₀.loc.mask.isSome = true :=
  (VerifiableInference.Desc.Last.mask_of_start _ _ _ _ _ _ _ _ _ _ _ h₀).trans (p₁₄Z_masksAhead h)

end OnBytes.Model.Verify
