-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigLift.lean: a rule for knowledge soundness: a reduction that is knowledge sound for claims
about each fixed tuple of messages is knowledge sound, with words and samples copied, for statements
about the oracles that decode to them.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdSigLiftProofs.lean. The joints are those of Cb/Ld/LdSig.lean: `S.over A` is the base joint
A, claimed of the messages of the oracle messages of the signature S.

Why: between a sending and a test a protocol reduces claims on the messages of its oracle messages
to other claims on the same messages (a sumcheck, a zerocheck, a batching, a lookup): the verifier
reads no oracle message, and words and samples are only copied. Such a block is best written once,
with no code in it: as a reduction R between base joints A, B, in which the tuple m of messages is a
part of the witness.
Why `GoodAt`: at a base joint the messages are named later than the verifier's messages. So for the
blocks whose challenge enters the new claim (a batching, a zerocheck, a sumcheck, a lookup)
round-by-round knowledge soundness between base joints fails at the wanted errors: at every value of
the challenge some tuple meets the new claim without meeting the old one. [An argument in words; no
theorem here.] What holds there is knowledge soundness for each fixed tuple. Over a signature S the
tuple is fixed before the block begins: it is the decoding of the statement (`S.decs`), and words
and samples are copied.

Main names:
  `GoodAt R H A B ext P`: the bundle `GoodB` (Ior/Masked.lean: all of GoodT but zero knowledge) with
    two changes. `same`: the honest prover ends with the messages with which it began. `know`: that
    of `GoodB`, for every m, at the witnesses (m, ·), with the extractor `ext m`. The verifier
    cannot read m, by type: m stands in no statement.
  `S.liftH H`: the honest side over S: it runs H on the messages of its witness, and hands the pairs
    (message, randomness) on.
  `Spec.sigLift_goodB`: `GoodAt R H A B ext P` gives
    `GoodB (R.keep S.Smp S.ext) (S.liftH H) (S.over A) (S.over B)`, same numbers; the extractor
    keeps the pairs and applies ext at their messages.
  `Spec.sigLift_exact`: honest-verifier zero knowledge in the exact form is carried along, same
    budget (`Honest.Exact`, Ior/Honest.lean).
  `Spec.sigLift_goodT`: the two together.
  `Spec.sigLift_know`: the step on knowledge soundness, on reductions alone.

Limits: "collision-free" is not used in these rules: the decoder is a function of the statement on
all statements. The condition is carried (it stands in the field "on" of S.over ..); it is used
where candidates of a test come in.
This file says nothing on blocks that read or send oracle messages. It says nothing on masked
blocks' own item (Ior/Masked.lean): a masked block that has GoodAt goes through sigLift_goodB. It
says nothing on a protocol.

As a lemma the rule stands in this library's Lean text: a write-up of ours, which is not in
this repository, argues it block by block (the state of such a block is "the witness is the
decoding, and the tracked claim holds of it"; extraction is the identity on the carried part).  The
nearest lemma of this protocol's technical report (lean/CREDITS.md), on the carried part, follows
(BCFW25).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSig
import Ior.KnowCollRulesFrame

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-- R, with the honest side H, leads from A to B for each fixed tuple of messages. -/
structure GoodAt {K M Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (H : R.Honest (M × Wi) (M × Wo)) (A : IOR.Rels K Xi Ei (M × Wi)) (B : IOR.Rels K Xo Eo (M × Wo))
    (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : IOR.Nums K R) : Prop where
  point   : Nonempty R.shape.IsPoint
  isLocal : R.IsLocal
  acc     : H.Acc A.rel B.rel
  onOut   : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b
  keeps   : ∀ w x c ρ, B.core ((H.strat w x c).run ρ).2.2 = A.core w
  prBad   : prRho H.Bad ≤ P.pBad
  cover   : ∀ w x, H.Hid w x ⊆ P.cov (A.core w)
  prCov   : ∀ k, prRho (P.cov k) ≤ P.pHid
  same    : ∀ w x c ρ, ((H.strat w x c).run ρ).2.2.1 = w.1
  know    : ∀ m,
    R.red.Know A.on (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp)) (ext m) P.err

/-- The honest side over a signature. -/
def Sig.liftH {E : Type} (S : Sig E) {St St' Wp Wp' : Type} {E₀ E₀' : ExtSpec}
    {R : IOR St E₀ St' E₀'} (H : R.Honest (S.Msg × Wp) (S.Msg × Wp')) :
    (R.keep S.Smp S.ext).Honest (S.Wit × Wp) (S.Wit × Wp') :=
  (H.keep S.Smp S.ext).mapW (fun w => (S.msgs w.1, w.2)) fun w o => (w.1, o.2)

namespace Spec
open IOR

section
variable (E : Type) [Field E]

/-- Knowledge soundness for each fixed tuple gives knowledge soundness over the signature, on the
statements with the condition of `S.over A`. -/
def sigLift_know : Prop :=
  ∀ (S : Sig E) (Kc St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec) (R : IOR St E₀ St' E₀')
      (A : Rels Kc St E₀ (S.Msg × Wp)) (B : Rels Kc St' E₀' (S.Msg × Wp'))
      (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (ε : Err R.shape),
    (∀ m, R.red.Know A.on (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp)) (ext m) ε) →
    (R.keep S.Smp S.ext).red.Know (S.over A).on (S.over A).relR (S.over B).relR
      (fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) ε

/-- The lifting rule. -/
def sigLift_goodB : Prop :=
  ∀ (S : Sig E) (Kc St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec) (R : IOR St E₀ St' E₀')
      (H : R.Honest (S.Msg × Wp) (S.Msg × Wp')) (A : Rels Kc St E₀ (S.Msg × Wp))
      (B : Rels Kc St' E₀' (S.Msg × Wp'))
      (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (P : Nums Kc R),
    GoodAt R H A B ext P →
    GoodB (R.keep S.Smp S.ext) (S.liftH H) (S.over A) (S.over B)
      (fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) (P.keep S.Smp S.ext)

/-- Honest-verifier zero knowledge in the exact form is carried along (`Honest.Exact`,
Ior/Honest.lean). -/
def sigLift_exact : Prop :=
  ∀ (S : Sig E) (Kc St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec) (R : IOR St E₀ St' E₀')
      (H : R.Honest (S.Msg × Wp) (S.Msg × Wp')) (A : Rels Kc St E₀ (S.Msg × Wp))
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop),
    H.Exact A.rel bud → (S.liftH H).Exact (S.over A).rel bud

def sigLift_goodT : Prop :=
  ∀ (S : Sig E) (Kc St St' Wp Wp' : Type) (E₀ E₀' : ExtSpec) (R : IOR St E₀ St' E₀')
      (H : R.Honest (S.Msg × Wp) (S.Msg × Wp')) (A : Rels Kc St E₀ (S.Msg × Wp))
      (B : Rels Kc St' E₀' (S.Msg × Wp'))
      (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (P : Nums Kc R),
    GoodAt R H A B ext P → H.Exact A.rel P.bud →
    GoodT (R.keep S.Smp S.ext) (S.liftH H) (S.over A) (S.over B)
      (fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)) (P.keep S.Smp S.ext)

end

/-- `GoodB` with an extractor that keeps the messages gives `GoodAt`, if the honest prover ends with
the messages with which it began. -/
def goodAt_of_goodB : Prop :=
  ∀ (K M Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo)
      (H : R.Honest (M × Wi) (M × Wo)) (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo))
      (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodB R H A B (fun a τ w => (w.1, ext w.1 a τ w.2)) P →
    (∀ w x c ρ, ((H.strat w x c).run ρ).2.2.1 = w.1) → GoodAt R H A B ext P

end Spec
end Cb
