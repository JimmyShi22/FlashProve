-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/QuietGood.lean: A BLOCK WITHOUT A WRITTEN ROUND COSTS NO ERROR: what its
goodness is.

The setting. Some blocks of a chain have no round of a transcript: a seal (its one round is put back
behind the chain's own rounds and holds nothing), a block that lays or clears a mark. As a piece
(Johnson/Desc/Sound/ChainRule.lean) such a block has the empty stretch: its reduction has no round
and its list of errors is empty. The rule of composition still asks that it be good.

What is said. `quietGoodIn_iff`, `quietKnow_iff`: for a piece with the empty stretch, `Piece.GoodIn`
and the third part of `BK.Good` ARE plain implications on statements, with nothing counted: from
every statement with the front condition, where the block says yes, the statement behind keeps the
promise, and a witness behind gives, by the extractor, a witness in front.
`quietGood`: the whole of `BK.Good` from the implication.

Trials. An equivalence is met by a silly block just where the implication is: `quiet_trial_yes`: a
block that says yes to all and changes nothing is good only if the relation behind implies the
relation in front at every statement; `quiet_trial_no`: a block that refuses all is good between any
two relations: as it must be: a verifier that never accepts is sound; what bars it is completeness,
which no statement here speaks of.

Limits. Nothing on any block of the protocol. The oracles behind such a piece are `p.ior.imp y ()`:
that these are y itself (each tree listed once) is not shown here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodInProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Iop.Reduction (orOff)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- A block with the empty stretch. back: the rounds that are put behind. -/
abbrev quietPiece (b : Block S Cl) (base : ℕ) (back : List Fmt.RoundView)
    (e : S × F.E.Str → Iop.Tr (uLT C []) → W → W) : Piece C F S Cl W :=
  ⟨b, base, [], back, e, ()⟩

variable (b : Block S Cl) (base : ℕ) (back : List Fmt.RoundView)
  (e : S × F.E.Str → Iop.Tr (uLT C []) → W → W)

/-- **`GoodIn` of a block with the empty stretch is a plain implication.** -/
theorem quietGoodIn_iff (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) :
    (quietPiece b base back e).GoodIn on on' R R' ↔
      ∀ a, on a → ∀ a', (quietPiece b base back e).ior.red.out a () = some a' →
        on' a' ∧ ∀ w, R' a' w → R a (e a () w) :=
  Iff.rfl

/-- **So is the clause of knowledge soundness that `EachGood` asks.** -/
theorem quietKnow_iff (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) :
    (quietPiece b base back e).ior.red.KnowInto on on' R R' e () ↔
      ∀ a, on a → ∀ a' w, (quietPiece b base back e).ior.red.out a () = some a' →
        (R' a' w ∨ ¬ on' a') → R a (e a () w) :=
  Iff.rfl

/-- **The whole of `BK.Good`**, from the implication. -/
theorem quietGood (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (h : ∀ a, on a → ∀ a' w, (quietPiece b base back e).ior.red.out a () = some a' →
      (R' a' w ∨ ¬ on' a') → R a (e a () w)) :
    ((quietPiece b base back e).bk on on' R R').Good :=
  ⟨⟨pointsT C []⟩, stageIOR_isLocal C (quietPiece b base back e).stage
    (quietPiece b base back e).run, (quietKnow_iff b base back e on on' R R').2 h⟩

/-- A block that refuses all is good between any two relations. -/
theorem quiet_trial_no (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (hno : ∀ a, (quietPiece b base back e).ior.red.out a () = none) :
    ((quietPiece b base back e).bk on on' R R').Good :=
  quietGood b base back e on on' R R' fun a _ a' _ h => by
    rw [hno a] at h
    cases h

/-- A block that says yes to all and hands every statement on as it is, is good just where
the relation behind (with the statements outside the promise) implies the relation in front. -/
theorem quiet_trial_yes (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (hyes : ∀ a, (quietPiece b base back e).ior.red.out a () = some a) :
    (quietPiece b base back e).ior.red.KnowInto on on' R R' e () ↔
      ∀ a, on a → ∀ w, (R' a w ∨ ¬ on' a) → R a (e a () w) := by
  rw [quietKnow_iff]
  constructor
  · intro h a ha w hw
    exact h a ha a w (hyes a) hw
  · intro h a ha a' w ho hw
    rw [hyes a] at ho
    obtain rfl := Option.some.inj ho
    exact h a ha w hw

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.quietGoodIn_iff
#print axioms VerifiableInference.Desc.Sound.quietKnow_iff
#print axioms VerifiableInference.Desc.Sound.quietGood
#print axioms VerifiableInference.Desc.Sound.quiet_trial_no
#print axioms VerifiableInference.Desc.Sound.quiet_trial_yes
