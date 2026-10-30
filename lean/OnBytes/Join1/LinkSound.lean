-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Join1/LinkSound.lean: from the link's item on knowledge soundness (`Hiop.LinkKnowR`,
Hiop/RecSubs.lean) to round-by-round soundness of the link's protocol, as it stands and behind the
two transformers (samplers of challenges, proof of work) at their idle settings. General, over
letters.

Main names:
  `LinkLang C`: the language: the first word gives no index with its record; or the further word has
    a collision at its record's seed; or both give the same index.
  `link_sound_of_know`: from the item to soundness for that language, with the same errors. (The
    step of `Hiop.rec_sndL_ofK`, Cb/Thin/Cond/TargetSoundOnly.lean, said for a link that stands in
    no record of sub-protocols.)
  `passed W Q`, `passedErr W Q ε`: a protocol, and a list of errors, behind the two transformers at
    the samplers that change nothing and at no added bit of work.
  `passed_sound`, `passed_below`: soundness passes; a bound on every error passes unchanged.
  `link_passed`: the two together, from the item and a bound on its list.

Limits: nothing on an honest prover. No error is evaluated. "No added bit of work" speaks of the
transformer alone: test bits that stand inside a round's own verifier messages are part of Q, and a
bound on Q's errors that counts them counts them behind the transformers too. `ConfigurationWithOutOfDomainSample.D` gives no
index in three cases: a collision at the record's seed, no decoding with the record, a decoded
message that holds no index.
Terms: lean/GLOSSARY.md.

-/
import Hiop.RecSubs
import Ior.ToProtoProofs
import Iop.GrindProofs
import OnBytes.Join1.SamplersId

set_option autoImplicit false

namespace OnBytes.Join1
open Iop Prob Hiop
open scoped ENNReal

/-- **The language of a link's soundness**: the first word gives no index with its record
(`ConfigurationWithOutOfDomainSample.D`: a collision at the record's seed, no decoding, or a decoded message that holds no
index); or the further word has a collision at its record's seed; or both give the same index. -/
def LinkLang (C : ConfigurationWithOutOfDomainSample) (rr : C.Rec × C.Rec) (y : (twoExternalStrings C.n C.Sg).Str) : Prop :=
  C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1

/-- **From the link's item on knowledge soundness to round-by-round soundness of its protocol**, for
that language, with the same errors. -/
theorem link_sound_of_know (C : ConfigurationWithOutOfDomainSample) (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone)
    (ε : Err Q.shape) (h : LinkKnowR Q ε) : Q.toInteractiveOracleProof.Sound (LinkLang C) ε := by
  classical
  have sL := Iop.sound_toProto (C.Rec × C.Rec) Unit (twoExternalStrings C.n C.Sg) Q C.onEq C.ReqR
    (fun _ _ _ => ()) ε h
  refine fun rr y hy => sL rr y fun h => hy ?_
  rcases h with h | ⟨_, hw⟩
  · by_cases h1 : (C.D y.1 rr.1).isSome
    · by_cases h2 : C.coll y.2 rr.2.1
      · exact Or.inr (Or.inl h2)
      · exact absurd ⟨h1, h2⟩ h
    · left
      cases hd : C.D y.1 rr.1 with
      | none => rfl
      | some i => rw [hd] at h1; exact absurd rfl h1
  · exact Or.inr (Or.inr hw)

section
variable {X : Type} {E : ExtSpec} (W : Type) [Inhabited W] (Q : InteractiveOracleProof X E)

/-- **A protocol passed through the two transformers at their idle settings**: challenges drawn by
the samplers that change nothing; no bit of proof of work ADDED in any round. Test bits inside Q's
own verifier messages are not touched. -/
def passed : InteractiveOracleProof X E := (Q.pull (Samplers.idS Q.shape)).grind W (GBits.zero _)

/-- The list of errors behind the two transformers. -/
def passedErr (ε : Err Q.shape) : Err (passed W Q).shape :=
  Err.grind (W := W) (GBits.zero _) (Err.pull (Samplers.idS Q.shape) ε)

/-- Soundness passes. This is said under the hypotheses that stand in the statement itself, which
this comment does not list; it is no claim that they hold. -/
theorem passed_sound {L : X → E.Str → Prop} {ε : Err Q.shape} (h : Q.Sound L ε) :
    (passed W Q).Sound L (passedErr W Q ε) :=
  (h.pull (idS_fib Q.shape)).grind _

/-- A bound on every error of the list passes unchanged. -/
theorem passed_below {ε : Err Q.shape} {c : ℝ≥0∞} (h : Err.Below ε c) :
    Err.Below (passedErr W Q ε) c := by
  have h1 : Err.Below (Err.pull (Samplers.idS Q.shape) ε) (1 * c) :=
    Err.Below.pull (idS_good_one Q.shape) h
  rw [one_mul] at h1
  exact (Err.below_grind_iff _ _ c).2 (Err.BelowG.of_below _ h1)

end

/-- **The link's share of soundness at the passed protocol**: from the item and a bound on its list:
a list of errors below the bound, with which the passed protocol is sound for the link's language.
-/
theorem link_passed (W : Type) [Inhabited W] (C : ConfigurationWithOutOfDomainSample)
    (Q : IOR (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg) Unit extNone) (ε : Err Q.shape) (c : ℝ≥0∞)
    (h : LinkKnowR Q ε) (hb : Err.Below ε c) :
    ∃ ε' : Err (passed W Q.toInteractiveOracleProof).shape, Err.Below ε' c ∧
      (passed W Q.toInteractiveOracleProof).Sound (LinkLang C) ε' :=
  ⟨passedErr W Q.toInteractiveOracleProof ε, passed_below W Q.toInteractiveOracleProof hb,
    passed_sound W Q.toInteractiveOracleProof (link_sound_of_know C Q ε h)⟩

end OnBytes.Join1

#print axioms OnBytes.Join1.link_sound_of_know
#print axioms OnBytes.Join1.passed_sound
#print axioms OnBytes.Join1.passed_below
#print axioms OnBytes.Join1.link_passed
