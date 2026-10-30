-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Switch/RideIn.lean: an oracle without a sample that is sent for a later block (a rider), as a
block of its own of one round; and the rule for a block before which a rider is sent.

Why. In the programs the fresh mask of a fold goes out with an earlier prover message: the message
of the sending with which the fold's group begins (OnBytes/Iop/Fold.lean, `foldMaskNotice`: "no
sample"). The blocks between only hand it on (`IOR.keepE`, Ior/Frame.lean; Cb/Pv/Rider.lean). Here
is the block that puts it among the oracles: the prover sends a native word of a code, the verifier
answers with a message of one value, nothing is claimed and nothing is read. Its round is then
merged with the next prover message by a plan (Cb/Pv/Switch/Recut.lean; case (J1) of Iop/Join.lean).
Definitions and proofs.

Main names:
  `rider Cw X Ei`: the block: one round; the new implicit instance is the old one and the word.
  `rider_good`: for every joint A: point queries, locality, the clause on outputs, and
    round-by-round knowledge soundness from A to `A.keepE Cw.nat`, the identity extracting, at the
    error 0.
  `goodK₀_seq`: two reductions in a row: the four clauses of `IOR.GoodK₀` (Cb/Thin/Kinds/Rules.lean)
    are kept. `goodK₀_keepE`: they are kept beside a further oracle. `goodK₀_recut`: they are kept
    by a plan of splits and merges that meets its conditions.
  `rideIn Cw R`: the rider's round, then R beside the rider. `rideIn_good`.
Limits: nothing is said of the word that is sent: the joint behind asks nothing of it. Nothing on an
honest prover. Behind a merge by (J1) the rider is the FIRST component of the merged message; where
in a prover message of the programs it stands, and in which leaves, is a matter of the layout, of
which nothing is said here.

-/
import Cb.Pv.Switch.Recut
import Cb.Pv.Rider
import Cb.Thin.Kinds.Rules
import Cb.Ld.LdRelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv
open Iop Prob IOR

section Rules
variable {K X₁ X₂ X₃ W₁ W₂ W₃ : Type} {E₁ E₂ E₃ : ExtSpec}

/-- Two reductions in a row. d: the extractor's value where the first verifier rejects. -/
theorem goodK₀_seq (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃) (A : Rels K X₁ E₁ W₁)
    (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
    (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (ε₁ : Err R₁.shape) (ε₂ : Err R₂.shape) (d : W₁)
    (g₁ : IOR.GoodK₀ R₁ A B e₁ ε₁) (g₂ : IOR.GoodK₀ R₂ B C e₂ ε₂) :
    IOR.GoodK₀ (R₁.seq R₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (Err.app ε₁ ε₂) where
  point := g₁.point.elim fun p₁ => g₂.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
  isLocal := g₁.isLocal.seq g₂.isLocal
  onOut := by
    intro a τ c ha hc
    obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
    exact g₂.onOut b _ c (g₁.onOut a _ b ha hb) hc'
  know := know_seq _ _ _ _ _ _ R₁ R₂ _ _ _ _ _ _ _ _ e₁ e₂ ε₁ ε₂ d g₁.know g₂.know g₁.onOut

/-- Beside a further oracle. -/
theorem goodK₀_keepE (F : ExtSpec) (R : IOR X₁ E₁ X₂ E₂) (A : Rels K X₁ E₁ W₁) (B : Rels K X₂ E₂ W₂)
    (e : X₁ × E₁.Str → Tr R.shape → W₂ → W₁) (ε : Err R.shape) (g : IOR.GoodK₀ R A B e ε) :
    IOR.GoodK₀ (R.keepE F) (A.keepE F) (B.keepE F) (fun a τ w => e (a.1, a.2.1) τ w) ε where
  point := g.point
  isLocal := g.isLocal.keepE F
  onOut := onOut_keepE F R A B g.onOut
  know := know_keepE F R A B e ε g.know

/-- By a plan of splits and merges. -/
theorem goodK₀_recut (R : IOR X₁ E₁ X₂ E₂) (P : XPlan R.shape) (hP : P.OK) (Kt : P.Kits)
    (A : Rels K X₁ E₁ W₁) (B : Rels K X₂ E₂ W₂) (e : X₁ × E₁.Str → Tr R.shape → W₂ → W₁)
    (ε : Err R.shape) (g : IOR.GoodK₀ R A B e ε) :
    IOR.GoodK₀ (R.recut P) A B (fun a τ w => e a (Tr.old P τ) w) (Err.recut P ε) where
  point := recut_point R P Kt g.point
  isLocal := recut_isLocal R P g.isLocal hP
  onOut := fun a τ b ha hb => g.onOut a (Tr.old P τ) b ha hb
  know := recut_know R P _ _ _ e ε g.know

end Rules

variable {E Pw : Type} [Zero E] (Cw : LdCode E Pw)

/-- A rider is sent: one round; the word joins the oracles; nothing is claimed, nothing is read. -/
def rider (X : Type) (Ei : ExtSpec) : IOR X Ei X (Ei.prod Cw.nat) where
  shape := [Cw.sendRound Unit Unit ()]
  blinded _ := true
  extReads _ := ∅
  reads _ := ∅
  out x _ _ := some x
  imp y τ := (y, τ.1.1)
  srcE _ q := match q with
    | .inl p => {p}
    | .inr _ => ∅
  srcO _ q := match q with
    | .inl _ => ∅
    | .inr p => {Sum.inl p}
  tie _ _ := ∅

theorem rider_isLocal (X : Type) (Ei : ExtSpec) : (rider Cw X Ei).IsLocal where
  out := fun _ _ _ _ _ _ _ _ _ => rfl
  imp := by
    intro y y' τ τ' q _ _ hE hO
    rcases q with p | p
    · exact congrArg Sum.inl (hE p (Finset.mem_singleton.2 rfl))
    · have h := hO (Sum.inl p) (Finset.mem_singleton.2 rfl)
      exact congrArg (fun z => Sum.inr (⟨p, z⟩ : Σ p, Cw.NS p → E)) h

/-- The rider's block between A and "A, and a further oracle of which nothing is asked". -/
theorem rider_good {K X W : Type} {Ei : ExtSpec} (A : Rels K X Ei W) :
    IOR.GoodK₀ (rider Cw X Ei) A (A.keepE Cw.nat) (fun _ _ w => w) (0, ()) where
  point := ⟨(Cw.sendPoint Unit Unit (), ())⟩
  isLocal := rider_isLocal Cw X Ei
  onOut := by
    intro a τ b ha hb
    obtain rfl := Option.some.inj hb
    exact ha
  know := by
    intro a _
    refine Doomed.of_forall _ _ ?_
    intro τ b w hb hw
    obtain rfl := Option.some.inj hb
    exact hw

/-- The rider's round, then R beside the rider. -/
noncomputable def rideIn {X Xo : Type} {Ei Eo : ExtSpec} (R : IOR X Ei Xo Eo) : IOR X Ei Xo
  (Eo.prod Cw.nat) :=
  (rider Cw X Ei).seq (R.keepE Cw.nat)

theorem rideIn_good {K X Xo W Wo : Type} {Ei Eo : ExtSpec} (R : IOR X Ei Xo Eo) (A : Rels K X Ei W)
    (B : Rels K Xo Eo Wo) (e : X × Ei.Str → Tr R.shape → Wo → W) (ε : Err R.shape) (d : W)
    (g : IOR.GoodK₀ R A B e ε) :
    IOR.GoodK₀ (rideIn Cw R) A (B.keepE Cw.nat)
      (IOR.extSeq (rider Cw X Ei) (R.keepE Cw.nat) (fun _ _ w => w)
        (fun a τ w => e (a.1, a.2.1) τ w) d)
      (Err.app (s := (rider Cw X Ei).shape) (0, ()) ε) :=
  goodK₀_seq _ _ A (A.keepE Cw.nat) (B.keepE Cw.nat) _ _ _ _ d (rider_good Cw A)
    (goodK₀_keepE Cw.nat R A B e ε g)

#print axioms goodK₀_seq
#print axioms goodK₀_keepE
#print axioms goodK₀_recut
#print axioms rider_good
#print axioms rideIn_good

end Cb.Pv
