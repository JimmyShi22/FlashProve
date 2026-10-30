-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ChainZ.lean: the end of a chain whose witnesses carry a further part.

The honest side that drops the further part at the end (`Honest.dropZ`), and what is left of the
bundle (`Good`) of Ior/Chain.lean then (`Spec.end_of_good`, proved here).
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Why: `Good R H A B ext P` asks that the honest prover hands the core of the witness on unchanged
(`keeps`), of every IOR, the last of a chain too. So the core of the input witness is a function of
the output witness, and one cover has to hold the hidden withheld sets of all input witnesses that
end in one output witness. An IOR whose hidden event reads something that its output witness no
longer holds is therefore `Good` only with pHid ≥ the probability of the union of these events
(Ior/ChainTest.lean: a block with events of probability 1/2 that is `Good` for no numbers with pHid
< 1).
The cure: what later events read (in the protocol: the cells) rides along as a further part z of the
witness up to the last joint of the chain (`Honest.carry`, `Spec.good_frame` of Ior/Frame.lean: z
joins the core; the extractor fills it on the way back). At the very end the honest prover drops z.
What results is no longer `Good` (nothing follows, so nothing needs the core; in this sense:
`Spec.end_of_good` does not conclude `Good`), but, under the hypotheses of its statement
(`Spec.end_of_good`), it has these properties that a parameter list asks for: locality,
completeness, the two probabilities, knowledge soundness with the extractor "put a fixed z0 beside
the witness, then the chain's extractor", and honest-verifier exact zero knowledge with the same
simulator and budget (the simulator: in the proof of `end_of_good`; `Spec.end_of_good` names none).

Main names:
  `Spec.end_of_good`: from `Good R H A B ext P`, on R with `H.dropZ`: see its statement. What is
    asked besides: the last joint B implies the wanted relation Ro on the first part of the witness;
    a witness in the wanted relaxation RoR, with the fixed z0 beside it, is in `B.relR` (so at the
    last joint the relaxation must admit z0 beside every such witness).

Limits: this file says nothing on numbers of queries.
Terms: lean/GLOSSARY.md.
-/
import Ior.FrameProofs
import Ior.ChainProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo Wz : Type}

/-- The honest side whose last witness forgets the further part. -/
def Honest.dropZ {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi (Wo × Wz)) : R.Honest Wi Wo where
  Coin := H.Coin
  strat w x c := Strat.map (fun o => (o.1, o.2.1)) (H.strat w x c)
  Bad := H.Bad
  Hid := H.Hid

theorem Honest.dropZ_run {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi (Wo × Wz)) (w : Wi) (x : Xi)
    (c : H.Coin) (ρ : Rho R.shape) :
    (H.dropZ.strat w x c).run ρ =
      (((H.strat w x c).run ρ).1, (((H.strat w x c).run ρ).2.1, ((H.strat w x c).run ρ).2.2.1)) :=
  Strat.run_map _ _ _

/-- The run shows the same. -/
theorem Honest.dropZ_output {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi (Wo × Wz)) (w : Wi) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    H.dropZ.output w x ρ T = H.output w x ρ T := by
  by_cases h : ρ ∈ H.withheld w x
  · rw [H.output_of_mem T h]
    exact H.dropZ.output_of_mem T h
  · rw [H.output_of_not_mem T h]
    refine (H.dropZ.output_of_not_mem T h).trans ?_
    refine congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => ?_)
    rw [Honest.dropZ_run]

end IOR

namespace Spec
open IOR

/-- What the end of a chain has, when the further part of the witness is dropped. -/
def end_of_good : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi (Wo × Wz)) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo (Wo × Wz))
      (ext : Ei.Str → Orcs R.shape → Wo × Wz → Wi) (P : Nums K R) (Ro : Xo → Eo.Str → Wo → Prop)
      (RoR : Xo × Eo.Str → Wo → Prop) (z0 : Wz),
    Good R H A B ext P → (∀ x y w, B.rel x y w → Ro x y w.1) → (∀ b w, RoR b w → B.relR b (w, z0)) →
    Nonempty R.shape.IsPoint ∧
    R.IsLocal ∧
    H.dropZ.Acc A.rel Ro ∧
    prRho H.dropZ.Bad ≤ P.pBad ∧
    (∀ w x, prRho (H.dropZ.Hid w x) ≤ P.pHid) ∧
    R.red.Know A.on A.relR RoR (fun a τ w => ext a.2 τ.read (w, z0)) P.err ∧
    H.dropZ.Exact A.rel P.bud

end Spec

open IOR

theorem end_of_good : Spec.end_of_good := by
  intro K Xi Xo Ei Eo R Wi Wo Wz H A B ext P Ro RoR z0 hG hrel hrelR
  refine ⟨hG.point, hG.isLocal, ?_, hG.prBad,
    fun w x => le_trans (pr_mono _ (hG.cover w x)) (hG.prCov _), ?_, ?_⟩
  · intro x y w c ρ hR hρ
    have h := hG.acc x y w c ρ hR hρ
    rw [Honest.dropZ_run]
    exact ⟨h.1, hrel _ _ _ h.2⟩
  · exact fun a ha =>
      Doomed.mono _ _ (fun τ hτ b w hb hw => hτ b (w, z0) hb (hrelR b w hw)) (hG.know a ha)
  · obtain ⟨Sm, hS⟩ := hG.exact
    exact ⟨Sm, fun x y w hR ρ hρ T hT => (H.dropZ_output w x ρ T).trans (hS x y w hR ρ hρ T hT)⟩

end Iop
