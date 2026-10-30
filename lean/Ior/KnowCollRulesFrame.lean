-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesFrame.lean: interactive oracle reductions (IORs) that act on a part of a larger
statement, for extractors that may read the whole statement and the whole transcript; a part that is
carried beside a reduction.

Definitions and statements; the proofs are in Ior/KnowCollRulesFrameProofs.lean. No protocol, no
code occurs here.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. A statement has an explicit part, held by the verifier,
and an implicit part: oracles that it queries.

Ior/Frame.lean has the constructions (`keepX`, `keepE`, `keep`, `pre`, `post`, `pure`, `carry`) and
their rules for the bundle `Good`, whose extractor reads the implicit part, the oracles and a
witness of the output statement only. Here the same rules for the bundles with a wide extractor:
`GoodB` (Ior/Masked.lean: all of `GoodT` but zero knowledge) and `GoodT` (Ior/KnowCollGood.lean:
`GoodB` and the field exact). Every rule but `Spec.goodT_pure` is stated for `GoodB`; what it does
to the field exact is stated apart (`Spec.exact_mapW` to `Spec.exact_post`); the rule for `GoodT` is
the two together. So a block without the field exact (a masked block) goes through the same rules.

Main names (what is new beside the wider type):
  `H.mapW fi fo`: the same IOR, the witness re-typed: the honest prover is given w', runs H on fi
    w', and ends with fo w' (H's last witness). `H.carry` is the case fi = the first part, fo = "put
    the second part back".
  `Spec.goodB_mapW`: the general change of joints on one IOR: from (A, B) to (A', B') on other
    witness types, if the new relations are transported: forward along honest runs that are not
    withheld, backward along the extractors on accepted transcripts. (not all hypotheses are named
    here: see its statement) Consequence at the same numbers, the frame rule and the further part of
    a witness are cases [no theorem here].
  `A.beside S`: witness (w, wz); the core is that of S (A has none: its core type is Unit).
  `Spec.goodB_beside`, `Spec.goodT_beside`: if R leads from A to B, then `R.keep Z F`, whose honest
    prover hands wz on, leads from `A.beside S` to `B.beside S`, for every joint S: same errors,
    same probabilities, same budget; the extractor is R's on the part and copies wz. Nothing is
    asked of S: its relaxation may decode, with a sample or without. An oracle may stand in both
    parts (put there by a step before, `Spec.goodB_pre`).

Limits: declared differences to a write-up of ours (lean/CREDITS.md).
 (a) Its lemma on oracles that the relations do not name asks that the simulator runs its
     distinguisher once; our exact form has no distinguisher (a set of further positions
     instead), so the clause has no counterpart.
 (b) The acting part of "beside" has the core type Unit (no hidden withheld set that reads a
     witness; exactly: `GoodB.cover`, Ior/Masked.lean: `H.Hid w x ⊆ P.cov (A.core w)`, with
     `A.core w : Unit`); the carried joint is any joint.
 (c) The first half of the written item, parallel composition, is not here: the rules for batches
     stand for it (Ior/BatchSeq.lean: `KnowB`, whose extractors are wide already;
     Ior/KnowWideOnline.lean).
This file does not say that two candidates for one oracle that stands in both parts hold the same
message: that is the matter of the step that joins or splits the parts. It says nothing on numbers
of queries or running times.
The rule "beside" follows this protocol's technical report (lean/CREDITS.md), which follows
(BCFW25).
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Ior.Masked
import Ior.Frame

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K K' X X' Xi Xi' Xo Xo' Z : Type}
  {E E' Ei Ei' Eo Eo' F : ExtSpec} {W W' Wi Wi' Wo Wo' Wz : Type}

/-- The same IOR, the witness re-typed. -/
def Honest.mapW {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') :
    R.Honest Wi' Wo' where
  Coin := H.Coin
  strat w x c := Strat.map (fun o => (o.1, fo w o.2)) (H.strat (fi w) x c)
  Bad := H.Bad
  Hid w x := H.Hid (fi w) x

/-- A step without rounds leads from A to B; the extractor may read the whole statement at which the
step starts. -/
structure StepT (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W')
    (back : X × E.Str → W' → W) (A : Rels K X E W) (B : Rels K X' E' W') : Prop where
  isLocal : g.IsLocal
  acc     : ∀ x y w,
    A.rel x y w → f x = some (m (x, w)).1 ∧ B.rel (m (x, w)).1 (g.map y) (m (x, w)).2
  onOut   : ∀ x y x', A.on (x, y) → f x = some x' → B.on (x', g.map y)
  keeps   : ∀ x w, B.core (m (x, w)).2 = A.core w
  know    : ∀ x y x' w',
    A.on (x, y) → f x = some x' → B.relR (x', g.map y) w' → A.relR (x, y) (back (x, y) w')

/-- A on one part of the statement, S on the other. -/
def Rels.beside (A : Rels Unit X E W) (S : Rels K Z F Wz) : Rels K (X × Z) (E.prod F) (W × Wz) where
  rel x y w := A.rel x.1 y.1 w.1 ∧ S.rel x.2 y.2 w.2
  relR a w := A.relR (a.1.1, a.2.1) w.1 ∧ S.relR (a.1.2, a.2.2) w.2
  on a := A.on (a.1.1, a.2.1) ∧ S.on (a.1.2, a.2.2)
  core w := S.core w.2

/-- The numbers of R beside a carried part: those of R. -/
def Nums.beside {R : IOR Xi Ei Xo Eo} (P : Nums Unit R) (K Z : Type) (F : ExtSpec) :
    Nums K (R.keep Z F) :=
  ⟨P.err, P.pBad, P.pHid, P.bud, fun _ => P.cov ()⟩

end IOR

namespace Spec
open IOR

/-! ### The same IOR, other joints -/

/-- What a run shows does not change when the witness is re-typed (`Honest.mapW_output`,
Ior/KnowCollRulesFrameProofs.lean; the statement: `Honest.ExactWith`, Ior/Honest.lean, under the
hypotheses below). -/
def exact_mapW : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo Wo' : Type)
      (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo')
      (Ri : Xi → Ei.Str → Wi → Prop) (Ri' : Xi → Ei.Str → Wi' → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Honest.Sim R),
    (∀ x y w, Ri' x y w → Ri x y (fi w)) → H.ExactWith Ri bud S → (H.mapW fi fo).ExactWith Ri' bud S

/-- The general change of joints. bo: from a witness of the new output joint to one of the old. -/
def goodB_mapW : Prop :=
  ∀ (K K' Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo Wo' : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (A' : Rels K' Xi Ei Wi')
      (B' : Rels K' Xo Eo Wo') (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ext' : Xi × Ei.Str → Tr R.shape → Wo' → Wi') (P : Nums K R) (cov' : K' → Set (Rho R.shape))
      (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') (bo : Wo' → Wo),
    GoodB R H A B ext P → (∀ x y w, A'.rel x y w → A.rel x y (fi w)) →
    (∀ x y w c ρ, A'.rel x y w → ρ ∉ H.withheld (fi w) x →
      B.rel ((H.strat (fi w) x c).run ρ).2.1
        (R.imp y ((H.strat (fi w) x c).run ρ).1) ((H.strat (fi w) x c).run ρ).2.2 →
      B'.rel ((H.strat (fi w) x c).run ρ).2.1 (R.imp y ((H.strat (fi w) x c).run ρ).1)
        (fo w ((H.strat (fi w) x c).run ρ).2.2)) →
    (∀ a, A'.on a → A.on a) → (∀ a τ b, A'.on a → R.red.out a τ = some b → B.on b → B'.on b) →
    (∀ w x c ρ, B'.core (fo w ((H.strat (fi w) x c).run ρ).2.2) = A'.core w) →
    (∀ w x, H.Hid (fi w) x ⊆ cov' (A'.core w)) → (∀ k, prRho (cov' k) ≤ P.pHid) →
    (∀ a τ b w, A'.on a → R.red.out a τ = some b → B'.relR b w → B.relR b (bo w)) →
    (∀ a τ b w, A'.on a → R.red.out a τ = some b → B'.relR b w →
      A.relR a (ext a τ (bo w)) → A'.relR a (ext' a τ w)) →
    GoodB R (H.mapW fi fo) A' B' ext' (P.recore cov')

/-- The frame rule, no type changes. -/
def goodB_and : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R) (S : Xi → Ei.Str → Wi → Prop)
      (SR : Xi × Ei.Str → Wi → Prop) (T : Xi × Ei.Str → Prop) (S' : Xo → Eo.Str → Wo → Prop)
      (SR' : Xo × Eo.Str → Wo → Prop) (T' : Xo × Eo.Str → Prop),
    GoodB R H A B ext P →
    (∀ x y w c ρ, A.rel x y w → S x y w → ρ ∉ H.withheld w x →
      B.rel ((H.strat w x c).run ρ).2.1
        (R.imp y ((H.strat w x c).run ρ).1) ((H.strat w x c).run ρ).2.2 →
      S' ((H.strat w x c).run ρ).2.1 (R.imp y ((H.strat w x c).run ρ).1)
        ((H.strat w x c).run ρ).2.2) →
    (∀ a τ b w, A.on a → T a → R.red.out a τ = some b → B.relR b w → A.relR a (ext a τ w) →
      SR' b w → SR a (ext a τ w)) →
    (∀ a τ b, A.on a → T a → R.red.out a τ = some b → T' b) →
    GoodB R H (A.and S SR T) (B.and S' SR' T') ext P

/-- Under the hypotheses below, a smaller honest relation keeps the field exact. -/
def exact_conseq : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri Ri' : Xi → Ei.Str → Wi → Prop)
      (bud bud' : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Honest.Sim R),
    (∀ x y w, Ri' x y w → Ri x y w) → (∀ ρ T, bud' ρ T → bud ρ T) →
    H.ExactWith Ri bud S → H.ExactWith Ri' bud' S

/-- A further part of the witness: handed on unchanged by the honest prover; the extractor may do to
it what it likes (the relations of the joints do not read it; it joins the core). -/
def goodB_carry : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (upd : Xi × Ei.Str → Tr R.shape → Wo → Wz → Wz),
    GoodB R H A B ext P →
    GoodB R (H.carry Wz) (A.lift Wz) (B.lift Wz)
      (fun a τ w => (ext a τ w.1, upd a τ w.1 w.2)) (P.carry Wz)

def exact_carry : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Honest.Sim R),
    H.ExactWith Ri bud S → (H.carry Wz).ExactWith (fun x y w => Ri x y w.1) bud S

/-- The frame rule, with a further part z of the witness. -/
def goodB_frame : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (upd : Xi × Ei.Str → Tr R.shape → Wo → Wz → Wz)
      (S : Xi → Ei.Str → Wi → Wz → Prop) (SR : Xi × Ei.Str → Wi → Wz → Prop)
      (T : Xi × Ei.Str → Prop) (S' : Xo → Eo.Str → Wo → Wz → Prop)
      (SR' : Xo × Eo.Str → Wo → Wz → Prop) (T' : Xo × Eo.Str → Prop),
    GoodB R H A B ext P →
    (∀ x y w z c ρ, A.rel x y w → S x y w z → ρ ∉ H.withheld w x →
      B.rel ((H.strat w x c).run ρ).2.1
        (R.imp y ((H.strat w x c).run ρ).1) ((H.strat w x c).run ρ).2.2 →
      S' ((H.strat w x c).run ρ).2.1 (R.imp y ((H.strat w x c).run ρ).1)
        ((H.strat w x c).run ρ).2.2 z) →
    (∀ a τ b w z, A.on a → T a → R.red.out a τ = some b → B.relR b w → A.relR a (ext a τ w) →
      SR' b w z → SR a (ext a τ w) (upd a τ w z)) →
    (∀ a τ b, A.on a → T a → R.red.out a τ = some b → T' b) →
    GoodB R (H.carry Wz) ((A.lift Wz).and (fun x y w => S x y w.1 w.2) (fun a w => SR a w.1 w.2) T)
      ((B.lift Wz).and (fun x y w => S' x y w.1 w.2) (fun b w => SR' b w.1 w.2) T')
      (fun a τ w => (ext a τ w.1, upd a τ w.1 w.2)) (P.carry Wz)

/-- Another core and another cover. -/
def goodB_recore : Prop :=
  ∀ (K K' Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (κi : Wi → K') (κo : Wo → K') (cov : K' → Set (Rho R.shape)),
    GoodB R H A B ext P → (∀ w x c ρ, κo ((H.strat w x c).run ρ).2.2 = κi w) →
    (∀ w x, H.Hid w x ⊆ cov (κi w)) → (∀ k, prRho (cov k) ≤ P.pHid) →
    GoodB R H (A.recore κi) (B.recore κo) ext (P.recore cov)

/-! ### Copied components -/

/-- A further explicit part that is only copied. -/
def goodB_keepX : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodB R H A B ext P →
    GoodB (R.keepX Z) (H.keepX Z) (A.keepX Z) (B.keepX Z)
      (fun a τ w => ext (a.1.1, a.2) τ w) (P.keepX Z)

def exact_keepX : Prop :=
  ∀ (Xi Xo Z : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop),
    H.Exact Ri bud → (H.keepX Z).Exact (fun a y w => Ri a.1 y w) bud

/-- Oracles that the relations do not name: further oracles that are only copied. -/
def goodB_keepE : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodB R H A B ext P →
    GoodB (R.keepE F) (H.keepE F) (A.keepE F) (B.keepE F)
      (fun a τ w => ext (a.1, a.2.1) τ w) (P.keepE F)

def exact_keepE : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop),
    H.Exact Ri bud → (H.keepE F).Exact (fun x y w => Ri x y.1 w) bud

/-- The frame rule for copied components: if R is `GoodB` from A to B, predicates that read the
copied components and the further part of the witness alone are carried along; nothing is asked. -/
def goodB_keep_frame : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R)
      (S SR : Z → F.Str → Wz → Prop) (T : Z → F.Str → Prop),
    GoodB R H A B ext P →
    GoodB (R.keep Z F) ((H.keep Z F).carry Wz)
      (((A.keep Z F).lift Wz).and
        (fun a y w => S a.2 y.2 w.2) (fun a w => SR a.1.2 a.2.2 w.2) (fun a => T a.1.2 a.2.2))
      (((B.keep Z F).lift Wz).and
        (fun a y w => S a.2 y.2 w.2) (fun a w => SR a.1.2 a.2.2 w.2) (fun a => T a.1.2 a.2.2))
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) ((P.keep Z F).carry Wz)

/-- Any reduction, with any relaxations, beside a carried part. (its joints have the core type Unit:
Limits (b) in the head) -/
def goodB_beside : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums Unit R) (S : Rels K Z F Wz),
    GoodB R H A B ext P →
    GoodB (R.keep Z F) ((H.keep Z F).carry Wz) (A.beside S) (B.beside S)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) (P.beside K Z F)

def exact_beside : Prop :=
  ∀ (Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop),
    H.Exact Ri bud → ((H.keep Z F).carry Wz).Exact (fun a y w => Ri a.1 y.1 w.1) bud

def goodT_beside : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (A : Rels Unit Xi Ei Wi) (B : Rels Unit Xo Eo Wo)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums Unit R) (S : Rels K Z F Wz),
    GoodT R H A B ext P →
    GoodT (R.keep Z F) ((H.keep Z F).carry Wz) (A.beside S) (B.beside S)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) (P.beside K Z F)

/-! ### Steps without rounds -/

def goodB_pre : Prop :=
  ∀ (K Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (A' : Rels K Xi' Ei' Wi') (A : Rels K Xi Ei Wi)
      (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ext' : Xi' × Ei'.Str → Tr R.shape → Wo → Wi') (P : Nums K R) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) (back : Xi' × Ei'.Str → Wi → Wi'),
    StepT f g m back A' A → GoodB R H A B ext P →
    (∀ a x₁ τ w, f a.1 = some x₁ → ext' a τ w = back a (ext (x₁, g.map a.2) τ w)) →
    GoodB (R.pre f g) (H.pre f g m) A' B ext' (P.pre f g)

def exact_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop) (Ri' : Xi' → Ei'.Str → Wi' → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi),
    g.IsLocal →
    (∀ x y w, Ri' x y w → f x = some (m (x, w)).1 ∧ Ri (m (x, w)).1 (g.map y) (m (x, w)).2) →
    H.Exact Ri bud → (H.pre f g m).Exact Ri' bud

def goodB_post : Prop :=
  ∀ (K Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (B' : Rels K Xo' Eo' Wo') (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (ext' : Xi × Ei.Str → Tr R.shape → Wo' → Wi) (P : Nums K R) (f : Xo → Option Xo')
      (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo') (back : Xo × Eo.Str → Wo' → Wo),
    GoodB R H A B ext P → StepT f g m back B B' →
    (∀ a τ b w, R.red.out a τ = some b → ext' a τ w = ext a τ (back b w)) →
    GoodB (R.post f g) (H.post f g m) A B' ext' (P.post f g)

def exact_post : Prop :=
  ∀ (Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (f : Xo → Option Xo')
      (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo'),
    H.Exact Ri bud → (H.post f g m).Exact Ri bud

/-- Under the hypothesis below (`StepT f g m back A B`): a step without rounds, alone: it has the
whole bundle. -/
def goodT_pure : Prop :=
  ∀ (K X X' : Type) (E E' : ExtSpec) (W W' : Type) (A : Rels K X E W) (B : Rels K X' E' W')
      (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W') (back : X × E.Str → W' → W),
    StepT f g m back A B →
    GoodT (IOR.pure f g) (Honest.pure f g m) A B (fun a _ w => back a w) (Nums.pure K f g)

end Spec
end Iop
