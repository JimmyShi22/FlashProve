-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ShapeRides.lean: THE RECORD's SHARE OF «THE TABLE's PROMISE RIDES»
(`RecRides`, QuietRides.lean): A RULE FOR THE TEST ON THE RECORD's SHAPE, AND THE SHARE PAID AT THE
SHUTTING. Theorems at the first chain's record.

What is said.
  `shape_step`, `stand_putLink`, `link_putLink`, `NextIn` LIE IN THE LIGHT FILE
    RbDef.lean. Here: `rec_shut`: **`RecRides` at a yes of a block each of whose
    yeses is the shutting's**, from the promise's test on the shape in front, `NextIn`, and the
    plan's two counts.

Limits. The places and the plan's counts are premises: tests on the written list and on the plan's
numbers. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.QuietRides
import Johnson.Desc.First.Link.Law.RbDef
import Johnson.Desc.First.Link.Law.ShutTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Where shut closed)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Numbers shapeAt standOf standAt mayWait)
open _root_.Run.PQ (CK)

variable {W : Type} {C : CK} {F : Frame}

/-- **THE RECORD's SHARE AT THE SHUTTING.** -/
theorem rec_shut (Nm : Numbers) (links : List ModelPart) (pl : List Place) (k : ℕ) (p p' : Place)
    (hp : pl[k]? = some p) (hp' : pl[k + 1]? = some p') (hn : NextIn links p p')
    (hnw : mayWait links p = false)
    (ht : Nm.treesAt pl[k + 1]? = Nm.treesAt pl[k]?) (hm : Nm.msgsAt pl[k + 1]? = Nm.msgsAt pl[k]?)
    (pw : Where) (piece : ℕ) (b₅ : Block S Claim)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Claim) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Claim W) (hps : ps.b = below b₅) (a b : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT C ps.ds)) (hout : ps.ior.red.out a τ = some b)
    (hs : shapeAt links pl[k]? a.1 = true) : RecRides Nm links pl k a b := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hps hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨L, hL, hb⟩ := shut_inv pw piece _ _ _ _ _ j (hb₅ _ _ _ _ _ hstep)
  obtain ⟨e1, e2, e3, e4⟩ := stand_putLink a.1 (closed L L.check.frame)
  rw [hp] at hs
  have hs' : (standOf a.1 == standAt links p && (a.1.noneWaits || mayWait links p) &&
      a.1.link?.all fun L => p.link == some L.link) = true := hs
  have hw : a.1.noneWaits = true := by
    have h2 := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hs').1).2
    rw [hnw, Bool.or_false] at h2
    exact h2
  refine ⟨by rw [hb]; exact failed_putLink _ _, by rw [hb]; exact e3, by rw [hb]; exact e4, ?_, ht,
    hm⟩
  rw [hp', hb]
  refine shape_step links p p' a.1 _ hs e1 hn.stand hn.link (Or.inl ?_) ?_
  · unfold S.noneWaits at hw ⊢
    rw [e2]
    exact hw
  · rw [link_putLink a.1 L _ hL, hL]
    rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rec_shut
