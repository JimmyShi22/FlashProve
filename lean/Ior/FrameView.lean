-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FrameView.lean: an interactive oracle reduction (IOR) with the same rounds and another new
implicit instance: other oracles in its output statement.

The definition `IOR.reimp`, its honest side, and one rule for the bundle of Ior/Chain.lean
(`Spec.good_reimp`); the proof is in Ior/FrameViewProofs.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. For statement see the head of Ior/Frame.lean.

`R.reimp f imp' srcE' srcO'` has the shape, the verifier's positions, the blinding and the ties of
R. Its new implicit instance imp' may read the whole transcript, verifier messages too (a fold of an
oracle by challenges), which a step after R (`IOR.post`, a map on implicit instances) cannot; srcE',
srcO' say from which symbols a symbol of it is computed.

Main names:
  `Spec.good_reimp`: if R leads from A to B (`Good R H A B ext P`, Ior/Chain.lean), then `R.reimp`
    leads from A to B', with the errors of R plus those of a second game on the same rounds, if
  (1) imp' is local with respect to srcE', srcO';
  (2) on honest runs that are not withheld the new output statement with the new witness is in
      `B'.rel`;
  (3) the second game: on every statement with `A.on` the prover has lost, with errors ε', towards Q
      a τ (say: "no challenge was bad for the proximity of a line");
  (4) backward: at a transcript with Q a τ at which R's verifier outputs xo, a witness w' of the new
      output statement in `B'.relR` extracts by ext' to a witness of the input; for this one may use
      that at this transcript every witness of R's own output statement in `B.relR` extracts by ext
      to a witness of the input;
  (5) the condition on statements and the core are handed on.
  Probabilities, budget, cover and simulator are those of R (the simulator: in the proof of
    `Honest.Exact.reimp`, Ior/FrameViewProofs.lean; `Spec.good_reimp` names none): what a run shows
    depends neither on the new implicit instance nor on its sources.

Limits: the new extractor ext' still has the type "reads oracles only". This file says nothing on
numbers of queries.
Terms: lean/GLOSSARY.md.
-/
import Ior.Frame

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec} {Wi Wo Wo' : Type}

/-- The rounds of R, another new implicit instance. -/
def reimp (R : IOR Xi Ei Xo Eo) (f : Xo → Xo') (imp' : Ei.Str → Tr R.shape → Eo'.Str)
    (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
    (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)) : IOR Xi Ei Xo' Eo' where
  shape := R.shape
  blinded := R.blinded
  extReads := R.extReads
  reads := R.reads
  out x y τ := (R.out x y τ).map f
  imp := imp'
  srcE := srcE'
  srcO := srcO'
  tie := R.tie

/-- Its honest side: the messages of H; it ends with (f xo, g w xo wo). -/
def Honest.reimp {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (f : Xo → Xo')
    (imp' : Ei.Str → Tr R.shape → Eo'.Str) (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
    (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)) (g : Wi → Xo → Wo → Wo') :
    (R.reimp f imp' srcE' srcO').Honest Wi Wo' where
  Coin := H.Coin
  strat w x c := Strat.map (fun o => (f o.1, g w o.1 o.2)) (H.strat w x c)
  Bad := H.Bad
  Hid := H.Hid

/-- Its numbers: those of R, with the errors of the second game added. -/
def Nums.reimp {R : IOR Xi Ei Xo Eo} (P : Nums K R) (ε' : Err R.shape) (f : Xo → Xo')
    (imp' : Ei.Str → Tr R.shape → Eo'.Str) (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
    (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)) :
    Nums K (R.reimp f imp' srcE' srcO') :=
  ⟨Err.add P.err ε', P.pBad, P.pHid, P.bud, P.cov⟩

end IOR

namespace Spec
open IOR

/-- The rule for another new implicit instance. After `Good R H A B ext P` the hypotheses are (1) to
(5) of the head, in that order; (5) is the last two. -/
def good_reimp : Prop :=
  ∀ (K Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (B' : Rels K Xo' Eo' Wo')
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (ext' : Ei.Str → Orcs R.shape → Wo' → Wi)
      (P : Nums K R) (ε' : Err R.shape) (Q : Xi × Ei.Str → Tr R.shape → Prop) (f : Xo → Xo')
      (imp' : Ei.Str → Tr R.shape → Eo'.Str) (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
      (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)) (g : Wi → Xo → Wo → Wo'),
    Good R H A B ext P →
    (∀ y y' (τ τ' : Tr R.shape) q, τ.rho = τ'.rho → τ.plains = τ'.plains →
      (∀ p ∈ srcE' τ.rho q, Ei.rd y p = Ei.rd y' p) → (∀ p ∈ srcO' τ.rho q, τ.read p = τ'.read p) →
      Eo'.rd (imp' y τ) q = Eo'.rd (imp' y' τ') q) →
    (∀ x y w c ρ, A.rel x y w → ρ ∉ H.withheld w x →
      B.rel ((H.strat w x c).run ρ).2.1
        (R.imp y ((H.strat w x c).run ρ).1) ((H.strat w x c).run ρ).2.2 →
      B'.rel (f ((H.strat w x c).run ρ).2.1) (imp' y ((H.strat w x c).run ρ).1)
        (g w ((H.strat w x c).run ρ).2.1 ((H.strat w x c).run ρ).2.2)) →
    (∀ a, A.on a → Doomed R.shape ε' (Q a)) →
    (∀ a τ xo w', A.on a → Q a τ → R.out a.1 a.2 τ = some xo → B'.relR (f xo, imp' a.2 τ) w' →
      (∀ w, B.relR (xo, R.imp a.2 τ) w → A.relR a (ext a.2 τ.read w)) →
      A.relR a (ext' a.2 τ.read w')) →
    (∀ a τ xo, A.on a → R.out a.1 a.2 τ = some xo → B'.on (f xo, imp' a.2 τ)) →
    (∀ w x c ρ, B'.core (g w ((H.strat w x c).run ρ).2.1 ((H.strat w x c).run ρ).2.2) = A.core w) →
    Good (R.reimp f imp' srcE' srcO') (H.reimp f imp' srcE' srcO' g)
      A B' ext' (P.reimp ε' f imp' srcE' srcO')

end Spec
end Iop
