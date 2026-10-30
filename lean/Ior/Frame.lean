-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Frame.lean: interactive oracle reductions (IORs) that act on a part of a larger statement, and
the frame rule.

Definitions and statements; the proofs are in Ior/FrameProofsBasic.lean and Ior/FrameProofs.lean.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. A statement has an explicit part, held by the verifier,
and an implicit part: oracles that it queries.
The constructions of this file add no rounds. All but `IOR.pure` take an IOR R and have the shape of
R itself, by definition, so that lists of errors, budgets and sets of ρ carry over unchanged.
"R leads from A to B" is `Good R H A B ext P` (Ior/Chain.lean); A, B are joints, P the numbers
(`Nums`).
Notions of other files (`Good`, `Rels`, `Nums`: Ior/Chain.lean):
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge. A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for
one kind of statement and of witness: the honest relation; a second relation, called relaxed, of
which round-by-round knowledge soundness speaks; the set of statements of which that soundness
speaks; and a map from a witness to its core. `A.core` is a map from the witnesses at a joint to a
type K; the clause `keeps` of `Good` asks that, for every w, x, coins c and ρ, `B.core` of the
witness with which the honest prover ends equals `A.core w`. `P.cov k` is a set of verifier
randomness for each value k of the core; `Good` asks that, for every w and x, in the relation or
not, `H.Hid w x` lies in `P.cov (A.core w)` (`cover`), and that every `P.cov k` has probability at
most `P.pHid` (`prCov`). `Good.exact`: `Honest.Exact`, Ior/Honest.lean. In the statements `good_…`
of this file `Good` is the conclusion, and in all of them but `good_pure` also a premise.

Main names:
  `R.keepX Z`, `R.keepE F`, `R.keep Z F`: a further explicit part z : Z, further oracles of the kind
    F, or both, are handed on unchanged (a query to a copied oracle is one query to the old one;
    nothing is tied to it).
  `R.pre f g`, `R.post f g`: a step without rounds before R, or after R: the explicit part is mapped
    by f (none = reject), the implicit part by g.
  `H.carry Wz`: the witness has a further part.
  `IOR.pure f g`: no rounds at all: re-bracketing, renaming, consequences.
  "R on a part of a statement, the rest (which may overlap with the part) handed on" is
    `((R.keep Z F).pre f g).post f' g'`.
  `ExtMap E E'`: a map on implicit instances; the identity, composition, the two projections and
    pairing give every re-bracketing of nested products.
  `Step f g m back A B`: what a step without rounds must satisfy to lead from the joint A to the
    joint B of a chain (`Rels`, Ior/Chain.lean).
  `Spec.good_and`: the frame rule, no type changes: if R leads from A to B, then R leads from "A and
    S" to "B and S'", where S, S' are predicates on (statement, witness): one pair beside the honest
    relations (S, S'), one pair beside the relaxations (SR, SR'), one pair of conditions on
    statements (T, T'). Asked is only that they are transported: S forward along honest runs that
    are not withheld; SR backward along the extractor and T forward, on accepted transcripts; for
    the transport of S and SR the relations of R itself may be assumed on both sides.
  `Spec.good_frame`: the same with a further part of the witness, which the honest prover hands on
    unchanged and joins the core; the extractor may change it (`upd`), say by moving a message out
    of the output witness into it.
  The frame rule, in three forms (`Spec.good_and`, `Spec.good_frame`, `Spec.good_keep_frame`): same
    errors, same probabilities, same budget, same simulator throughout (the simulator: in the proofs
    of `good_and` and `good_frame` (Ior/FrameProofsBasic.lean); for `good_keep_frame`: in the proofs
    of `good_keepX` (Ior/FrameProofsBasic.lean) and `Honest.Exact.keepE` (Ior/FrameProofs.lean); the
    three statements name none).
  For reductions, without the bundle: `Spec.know_frame`.
  `Spec.know_of_soundW`: from soundness to knowledge with a further part: witnesses (s, p) at both
    ends, where s is determined by the statement and p (decoding) and p stands in no oracle yet (the
    reading meant; by type p : `WP`, any type).

Limits: this file says nothing on numbers of queries (it sets which positions are read: `extReads`,
`reads`, `srcE`, `srcO`, `ExtMap.src`; it counts none) or running times. A step's extractor "back"
may read the implicit instance at which it stands; after R (`post`) this keeps the form "reads
oracles only" if R's new implicit instance is a function of the old one and the oracles sent
(`ImpBy`).
Terms: lean/GLOSSARY.md.
-/
import Ior.Chain
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Finset.Image
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Maps on implicit instances -/

/-- A map on implicit instances, with the positions from which a symbol of the image is computed. -/
structure ExtMap (E E' : ExtSpec) where
  map : E.Str → E'.Str
  src : E'.Pos → Finset E.Pos

namespace ExtMap
variable {E E' E'' E₁ E₂ : ExtSpec}

/-- A symbol of the image depends on the argument only at the positions declared. -/
def IsLocal (g : ExtMap E E') : Prop :=
  ∀ y y' q, (∀ p ∈ g.src q, E.rd y p = E.rd y' p) → E'.rd (g.map y) q = E'.rd (g.map y') q

protected def id (E : ExtSpec) : ExtMap E E := ⟨fun y => y, fun q => {q}⟩

open Classical in
/-- First g, then g'. -/
def comp (g' : ExtMap E' E'') (g : ExtMap E E') : ExtMap E E'' :=
  ⟨fun y => g'.map (g.map y), fun q => (g'.src q).biUnion g.src⟩

protected def fst (E₁ E₂ : ExtSpec) : ExtMap (E₁.prod E₂) E₁ := ⟨fun y => y.1, fun q => {Sum.inl q}⟩

protected def snd (E₁ E₂ : ExtSpec) : ExtMap (E₁.prod E₂) E₂ := ⟨fun y => y.2, fun q => {Sum.inr q}⟩

def pair (g₁ : ExtMap E E₁) (g₂ : ExtMap E E₂) : ExtMap E (E₁.prod E₂) :=
  ⟨fun y => (g₁.map y, g₂.map y), fun q => match q with
    | .inl q => g₁.src q
    | .inr q => g₂.src q⟩

/-- To no oracle at all. -/
def toNone (E : ExtSpec) : ExtMap E extNone := ⟨fun _ => (), fun _ => ∅⟩

end ExtMap

namespace IOR
variable {K K' X X' Xi Xi' Xo Xo' Z : Type}
  {E E' Ei Ei' Eo Eo' F : ExtSpec} {W W' Wi Wi' Wo Wo' Wz : Type}

/-! ## 2. The constructions: the data -/

/-- A further explicit part is handed on unchanged. -/
def keepX (R : IOR Xi Ei Xo Eo) (Z : Type) : IOR (Xi × Z) Ei (Xo × Z) Eo where
  shape := R.shape
  blinded := R.blinded
  extReads := R.extReads
  reads := R.reads
  out a y τ := (R.out a.1 y τ).map fun xo => (xo, a.2)
  imp := R.imp
  srcE := R.srcE
  srcO := R.srcO
  tie := R.tie

/-- Further oracles are handed on unchanged. -/
def keepE (R : IOR Xi Ei Xo Eo) (F : ExtSpec) : IOR Xi (Ei.prod F) Xo (Eo.prod F) where
  shape := R.shape
  blinded := R.blinded
  extReads ρ := (R.extReads ρ).map Function.Embedding.inl
  reads := R.reads
  out x y τ := R.out x y.1 τ
  imp y τ := (R.imp y.1 τ, y.2)
  srcE ρ q := match q with
    | .inl q => (R.srcE ρ q).map Function.Embedding.inl
    | .inr p => {Sum.inr p}
  srcO ρ q := match q with
    | .inl q => R.srcO ρ q
    | .inr _ => ∅
  tie ρ p := (R.tie ρ p).map Function.Embedding.inl

/-- Both. -/
@[reducible] def keep (R : IOR Xi Ei Xo Eo) (Z : Type) (F : ExtSpec) :
    IOR (Xi × Z) (Ei.prod F) (Xo × Z) (Eo.prod F) :=
  (R.keepX Z).keepE F

open Classical in
/-- A step without rounds, then R. -/
def pre (R : IOR Xi Ei Xo Eo) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) :
    IOR Xi' Ei' Xo Eo where
  shape := R.shape
  blinded := R.blinded
  extReads ρ := (R.extReads ρ).biUnion g.src
  reads := R.reads
  out x y τ := (f x).bind fun x₁ => R.out x₁ (g.map y) τ
  imp y τ := R.imp (g.map y) τ
  srcE ρ q := (R.srcE ρ q).biUnion g.src
  srcO := R.srcO
  tie ρ p := (R.tie ρ p).biUnion g.src

open Classical in
/-- R, then a step without rounds. -/
def post (R : IOR Xi Ei Xo Eo) (f : Xo → Option Xo') (g : ExtMap Eo Eo') :
    IOR Xi Ei Xo' Eo' where
  shape := R.shape
  blinded := R.blinded
  extReads := R.extReads
  reads := R.reads
  out x y τ := (R.out x y τ).bind f
  imp y τ := g.map (R.imp y τ)
  srcE ρ q := (g.src q).biUnion (R.srcE ρ)
  srcO ρ q := (g.src q).biUnion (R.srcO ρ)
  tie := R.tie

/-- A step without rounds, alone. -/
protected def pure (f : Xi → Option Xo) (g : ExtMap Ei Eo) : IOR Xi Ei Xo Eo where
  shape := []
  blinded _ := true
  extReads _ := ∅
  reads _ := ∅
  out x _ _ := f x
  imp y _ := g.map y
  srcE _ q := g.src q
  srcO _ _ := ∅
  tie _ _ := ∅

namespace Honest
variable {R : IOR Xi Ei Xo Eo}

/-- The witness has a further part, which is handed on unchanged. -/
def carry (H : R.Honest Wi Wo) (Wz : Type) : R.Honest (Wi × Wz) (Wo × Wz) where
  Coin := H.Coin
  strat w x c := Strat.map (fun o => (o.1, (o.2, w.2))) (H.strat w.1 x c)
  Bad := H.Bad
  Hid w x := H.Hid w.1 x

def keepX (H : R.Honest Wi Wo) (Z : Type) : (R.keepX Z).Honest Wi Wo where
  Coin := H.Coin
  strat w a c := Strat.map (fun o => ((o.1, a.2), o.2)) (H.strat w a.1 c)
  Bad := H.Bad
  Hid w a := H.Hid w a.1

def keepE (H : R.Honest Wi Wo) (F : ExtSpec) : (R.keepE F).Honest Wi Wo where
  Coin := H.Coin
  strat := H.strat
  Bad := H.Bad
  Hid := H.Hid

@[reducible] def keep (H : R.Honest Wi Wo) (Z : Type) (F : ExtSpec) : (R.keep Z F).Honest Wi Wo :=
  (H.keepX Z).keepE F

/-- m: what the honest prover does to (explicit part, witness) in the step. -/
def pre (H : R.Honest Wi Wo) (f : Xi' → Option Xi)
    (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) : (R.pre f g).Honest Wi' Wo where
  Coin := H.Coin
  strat w x c := H.strat (m (x, w)).2 (m (x, w)).1 c
  Bad := H.Bad
  Hid w x := H.Hid (m (x, w)).2 (m (x, w)).1

def post (H : R.Honest Wi Wo) (f : Xo → Option Xo')
    (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo') : (R.post f g).Honest Wi Wo' where
  Coin := H.Coin
  strat w x c := Strat.map m (H.strat w x c)
  Bad := H.Bad
  Hid := H.Hid

protected def pure (f : Xi → Option Xo) (g : ExtMap Ei Eo) (m : Xi × Wi → Xo × Wo) :
    (IOR.pure f g).Honest Wi Wo where
  Coin := Unit
  strat w x _ := m (x, w)
  Bad := ∅
  Hid _ _ := ∅

end Honest

/-! ## 3. Joints and numbers (`Rels`, `Nums`: Ior/Chain.lean) -/

/-- The joint A, read on the first component of the explicit part. -/
def Rels.keepX (A : Rels K X E W) (Z : Type) : Rels K (X × Z) E W where
  rel a y w := A.rel a.1 y w
  relR a w := A.relR (a.1.1, a.2) w
  on a := A.on (a.1.1, a.2)
  core := A.core

/-- The joint A, read on the first component of the implicit part. -/
def Rels.keepE (A : Rels K X E W) (F : ExtSpec) : Rels K X (E.prod F) W where
  rel x y w := A.rel x y.1 w
  relR a w := A.relR (a.1, a.2.1) w
  on a := A.on (a.1, a.2.1)
  core := A.core

@[reducible] def Rels.keep (A : Rels K X E W) (Z : Type) (F : ExtSpec) :
    Rels K (X × Z) (E.prod F) W :=
  (A.keepX Z).keepE F

/-- The joint A, read on the first part of a witness; the further part joins the core. -/
def Rels.lift (A : Rels K X E W) (Wz : Type) : Rels (K × Wz) X E (W × Wz) where
  rel x y w := A.rel x y w.1
  relR a w := A.relR a w.1
  on := A.on
  core w := (A.core w.1, w.2)

/-- The joint "A and S": S beside the honest relation, SR beside the relaxation, T beside the
condition on statements. -/
def Rels.and (A : Rels K X E W) (S : X → E.Str → W → Prop)
    (SR : X × E.Str → W → Prop) (T : X × E.Str → Prop) : Rels K X E W where
  rel x y w := A.rel x y w ∧ S x y w
  relR a w := A.relR a w ∧ SR a w
  on a := A.on a ∧ T a
  core := A.core

/-- Another core. -/
def Rels.recore (A : Rels K X E W) (κ : W → K') : Rels K' X E W := ⟨A.rel, A.relR, A.on, κ⟩

namespace Nums
variable {R : IOR Xi Ei Xo Eo}

def carry (P : Nums K R) (Wz : Type) : Nums (K × Wz) R :=
  ⟨P.err, P.pBad, P.pHid, P.bud, fun k => P.cov k.1⟩
def keepX (P : Nums K R) (Z : Type) : Nums K (R.keepX Z) := ⟨P.err, P.pBad, P.pHid, P.bud, P.cov⟩
def keepE (P : Nums K R) (F : ExtSpec) : Nums K (R.keepE F) := ⟨P.err, P.pBad, P.pHid, P.bud, P.cov⟩
@[reducible] def keep (P : Nums K R) (Z : Type) (F : ExtSpec) : Nums K (R.keep Z F) :=
  (P.keepX Z).keepE F
def pre (P : Nums K R) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) : Nums K (R.pre f g) :=
  ⟨P.err, P.pBad, P.pHid, P.bud, P.cov⟩
def post (P : Nums K R) (f : Xo → Option Xo') (g : ExtMap Eo Eo') : Nums K (R.post f g) :=
  ⟨P.err, P.pBad, P.pHid, P.bud, P.cov⟩
def recore (P : Nums K R) (cov : K' → Set (Rho R.shape)) : Nums K' R :=
  ⟨P.err, P.pBad, P.pHid, P.bud, cov⟩
/-- Of a step without rounds: no error, nothing withheld, every budget. -/
protected def pure (K : Type) (f : Xi → Option Xo) (g : ExtMap Ei Eo) : Nums K (IOR.pure f g) :=
  ⟨(), 0, 0, fun _ _ => True, fun _ => ∅⟩

end Nums

/-- A step without rounds leads from A to B. f, g: what the verifier does; m: what the honest prover
does; back: the extractor (it may read the implicit instance at which the step starts). -/
structure Step (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W') (back : E.Str → W' → W)
    (A : Rels K X E W) (B : Rels K X' E' W') : Prop where
  isLocal : g.IsLocal
  acc     : ∀ x y w, A.rel x y w → f x = some (m (x, w)).1 ∧ B.rel (m (x, w)).1 (g.map y) (m (x, w)).2
  onOut   : ∀ x y x', A.on (x, y) → f x = some x' → B.on (x', g.map y)
  keeps   : ∀ x w, B.core (m (x, w)).2 = A.core w
  know    : ∀ x y x' w', A.on (x, y) → f x = some x' → B.relR (x', g.map y) w' → A.relR (x, y) (back y w')

end IOR

namespace Spec
open IOR

/-- Under the hypotheses below, the standard maps on implicit instances are local. -/
def extMap_isLocal : Prop :=
  (∀ E : ExtSpec, (ExtMap.id E).IsLocal) ∧
  (∀ E₁ E₂ : ExtSpec, (ExtMap.fst E₁ E₂).IsLocal ∧ (ExtMap.snd E₁ E₂).IsLocal) ∧
  (∀ E : ExtSpec, (ExtMap.toNone E).IsLocal) ∧
  (∀ (E E' E'' : ExtSpec) (g' : ExtMap E' E'') (g : ExtMap E E'),
    g'.IsLocal → g.IsLocal → (g'.comp g).IsLocal) ∧
  (∀ (E E₁ E₂ : ExtSpec) (g₁ : ExtMap E E₁) (g₂ : ExtMap E E₂),
    g₁.IsLocal → g₂.IsLocal → (g₁.pair g₂).IsLocal)

/-- The frame rule for reductions (no bundle): under the hypotheses below, a predicate on
(statement, witness, further part) is carried along; the extractor may change the further part. For
the transport the two relations may be assumed. -/
def know_frame : Prop :=
  ∀ (A B WA WB Wz : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA → Prop)
      (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA) (ε : Err K.shape)
      (Φ : A → WA → Wz → Prop) (Φ' : B → WB → Wz → Prop) (upd : A → Tr K.shape → WB → Wz → Wz),
    K.Know on RA RB ext ε →
    (∀ a τ b w c, on a → K.out a τ = some b → RB b w → RA a (ext a τ w) →
      Φ' b w c → Φ a (ext a τ w) (upd a τ w c)) →
    K.Know on (fun a (w : WA × Wz) => RA a w.1 ∧ Φ a w.1 w.2)
      (fun b (w : WB × Wz) => RB b w.1 ∧ Φ' b w.1 w.2)
      (fun a τ w => (ext a τ w.1, upd a τ w.1 w.2)) ε

/-- From soundness to knowledge soundness, with a further part p of the witness that no oracle holds
(the reading meant; by type p : `WP`, any type). LA a p, LB b p: "the statement is true with the
further part p". d a p: the rest of the witness, read off the input statement. The main hypothesis
is soundness for all p jointly: the prover has lost towards "whenever the output is true with p, the
input is true with p". (Knowledge soundness with the identity as extractor; from sets of bad values
that do not depend on p: `Know.of_badFam`.) (not all hypotheses are named here: see the statement
below) -/
def know_of_soundW : Prop :=
  ∀ (A B WA WB WP : Type) (K : Reduction A B) (on : A → Prop) (RA : A → WA × WP → Prop)
      (RB : B → WB × WP → Prop) (LA : A → WP → Prop) (LB : B → WP → Prop)
      (d : A → WP → WA) (ε : Err K.shape),
    K.Know on LA LB (fun _ _ p => p) ε → (∀ a p, on a → LA a p → RA a (d a p, p)) →
    (∀ b w, RB b w → LB b w.2) → K.Know on RA RB (fun a _ w => (d a w.2, w.2)) ε

/-- The frame rule, no type changes. S forward along honest runs that are not withheld; SR backward
along the extractor and T forward, on accepted transcripts. -/
def good_and : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R) (S : Xi → Ei.Str → Wi → Prop)
      (SR : Xi × Ei.Str → Wi → Prop) (T : Xi × Ei.Str → Prop) (S' : Xo → Eo.Str → Wo → Prop)
      (SR' : Xo × Eo.Str → Wo → Prop) (T' : Xo × Eo.Str → Prop),
    Good R H A B ext P →
    (∀ x y w c ρ, A.rel x y w → S x y w → ρ ∉ H.withheld w x →
      B.rel ((H.strat w x c).run ρ).2.1
        (R.imp y ((H.strat w x c).run ρ).1) ((H.strat w x c).run ρ).2.2 →
      S' ((H.strat w x c).run ρ).2.1 (R.imp y ((H.strat w x c).run ρ).1)
        ((H.strat w x c).run ρ).2.2) →
    (∀ a τ b w, A.on a → T a → R.red.out a τ = some b → B.relR b w → A.relR a (ext a.2 τ.read w) →
      SR' b w → SR a (ext a.2 τ.read w)) →
    (∀ a τ b, A.on a → T a → R.red.out a τ = some b → T' b) →
    Good R H (A.and S SR T) (B.and S' SR' T') ext P

/-- If R leads from A to B: a further part of the witness, handed on unchanged by the honest prover;
the extractor may do to it what it likes (the relations of the joints do not read it; it joins the
core). -/
def good_carry : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Ei.Str → Orcs R.shape → Wo → Wi)
      (P : Nums K R) (upd : Ei.Str → Orcs R.shape → Wo → Wz → Wz),
    Good R H A B ext P →
    Good R (H.carry Wz) (A.lift Wz) (B.lift Wz)
      (fun y o w => (ext y o w.1, upd y o w.1 w.2)) (P.carry Wz)

/-- The frame rule, with a further part z of the witness. -/
def good_frame : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Ei.Str → Orcs R.shape → Wo → Wi)
      (P : Nums K R) (upd : Ei.Str → Orcs R.shape → Wo → Wz → Wz)
      (S : Xi → Ei.Str → Wi → Wz → Prop) (SR : Xi × Ei.Str → Wi → Wz → Prop)
      (T : Xi × Ei.Str → Prop) (S' : Xo → Eo.Str → Wo → Wz → Prop)
      (SR' : Xo × Eo.Str → Wo → Wz → Prop) (T' : Xo × Eo.Str → Prop),
    Good R H A B ext P →
    (∀ x y w z c ρ, A.rel x y w → S x y w z → ρ ∉ H.withheld w x →
      B.rel ((H.strat w x c).run ρ).2.1
        (R.imp y ((H.strat w x c).run ρ).1) ((H.strat w x c).run ρ).2.2 →
      S' ((H.strat w x c).run ρ).2.1 (R.imp y ((H.strat w x c).run ρ).1)
        ((H.strat w x c).run ρ).2.2 z) →
    (∀ a τ b w z, A.on a → T a → R.red.out a τ = some b → B.relR b w → A.relR a (ext a.2 τ.read w) →
      SR' b w z → SR a (ext a.2 τ.read w) (upd a.2 τ.read w z)) →
    (∀ a τ b, A.on a → T a → R.red.out a τ = some b → T' b) →
    Good R (H.carry Wz) ((A.lift Wz).and (fun x y w => S x y w.1 w.2) (fun a w => SR a w.1 w.2) T)
      ((B.lift Wz).and (fun x y w => S' x y w.1 w.2) (fun b w => SR' b w.1 w.2) T')
      (fun y o w => (ext y o w.1, upd y o w.1 w.2)) (P.carry Wz)

/-- A further explicit part that is only copied. -/
def good_keepX : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R),
    Good R H A B ext P → Good (R.keepX Z) (H.keepX Z) (A.keepX Z) (B.keepX Z) ext (P.keepX Z)

/-- Further oracles that are only copied. -/
def good_keepE : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R),
    Good R H A B ext P →
    Good (R.keepE F) (H.keepE F) (A.keepE F) (B.keepE F) (fun y o w => ext y.1 o w) (P.keepE F)

/-- What is copied is copied: the facts with which transports over `keepX` and `keepE` are
proved. -/
def keep_copies : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo),
    (∀ (Z : Type) (a : (Xi × Z) × Ei.Str) τ b, (R.keepX Z).red.out a τ = some b →
      b.1.2 = a.1.2 ∧ R.red.out (a.1.1, a.2) τ = some (b.1.1, b.2)) ∧
    (∀ (F : ExtSpec) (a : Xi × (Ei.prod F).Str) τ b, (R.keepE F).red.out a τ = some b →
      b.2.2 = a.2.2 ∧ R.red.out (a.1, a.2.1) τ = some (b.1, b.2.1)) ∧
    (∀ (Z Wi Wo : Type) (H : R.Honest Wi Wo) (w : Wi) (a : Xi × Z) c ρ,
      (((H.keepX Z).strat w a c).run ρ) =
        (((H.strat w a.1 c).run ρ).1,
          ((((H.strat w a.1 c).run ρ).2.1, a.2), ((H.strat w a.1 c).run ρ).2.2))) ∧
    (∀ (Wi Wo Wz : Type) (H : R.Honest Wi Wo) (w : Wi × Wz) (x : Xi) c ρ,
      (((H.carry Wz).strat w x c).run ρ) =
        (((H.strat w.1 x c).run ρ).1,
          (((H.strat w.1 x c).run ρ).2.1, (((H.strat w.1 x c).run ρ).2.2, w.2))))

/-- The frame rule for copied components: if R leads from A to B, predicates that read the copied
components and the further part of the witness alone are carried along; nothing is asked. -/
def good_keep_frame : Prop :=
  ∀ (K Xi Xo Z : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R)
      (S SR : Z → F.Str → Wz → Prop) (T : Z → F.Str → Prop),
    Good R H A B ext P →
    Good (R.keep Z F) ((H.keep Z F).carry Wz)
      (((A.keep Z F).lift Wz).and
        (fun a y w => S a.2 y.2 w.2) (fun a w => SR a.1.2 a.2.2 w.2) (fun a => T a.1.2 a.2.2))
      (((B.keep Z F).lift Wz).and
        (fun a y w => S a.2 y.2 w.2) (fun a w => SR a.1.2 a.2.2 w.2) (fun a => T a.1.2 a.2.2))
      (fun y o w => (ext y.1 o w.1, w.2)) ((P.keep Z F).carry Wz)

/-- A step without rounds before R. -/
def good_pre : Prop :=
  ∀ (K Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (A' : Rels K Xi' Ei' Wi') (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) (back : Ei'.Str → Wi → Wi'),
    Step f g m back A' A → Good R H A B ext P →
    Good (R.pre f g) (H.pre f g m) A' B (fun y o w => back y (ext (g.map y) o w)) (P.pre f g)

/-- A step without rounds after R. -/
def good_post : Prop :=
  ∀ (K Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (B' : Rels K Xo' Eo' Wo') (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R)
      (f : Xo → Option Xo') (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo')
      (back : Eo.Str → Wo' → Wo) (io : Ei.Str → Orcs R.shape → Eo.Str),
    Good R H A B ext P → Step f g m back B B' → R.ImpBy io →
    Good (R.post f g) (H.post f g m) A B' (fun y o w => ext y o (back (io y o) w)) (P.post f g)

/-- A step without rounds, alone. -/
def good_pure : Prop :=
  ∀ (K X X' : Type) (E E' : ExtSpec) (W W' : Type) (A : Rels K X E W) (B : Rels K X' E' W')
      (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W') (back : E.Str → W' → W),
    Step f g m back A B →
    Good (IOR.pure f g) (Honest.pure f g m) A B (fun y _ w => back y w) (Nums.pure K f g)

/-- Another core and another cover. -/
def good_recore : Prop :=
  ∀ (K K' Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Ei.Str → Orcs R.shape → Wo → Wi)
      (P : Nums K R) (κi : Wi → K') (κo : Wo → K') (cov : K' → Set (Rho R.shape)),
    Good R H A B ext P → (∀ w x c ρ, κo ((H.strat w x c).run ρ).2.2 = κi w) →
    (∀ w x, H.Hid w x ⊆ cov (κi w)) → (∀ k, prRho (cov k) ≤ P.pHid) →
    Good R H (A.recore κi) (B.recore κo) ext (P.recore cov)

/-- Under `R.ImpBy io`: how the new implicit instance is given (`ImpBy`, Ior/Chain.lean), for
`keepX`, `keepE`, `pre`, `post`. -/
def impBy_frame : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (io : Ei.Str → Orcs R.shape → Eo.Str),
    R.ImpBy io →
    (∀ Z : Type, (R.keepX Z).ImpBy io) ∧
    (∀ F : ExtSpec, (R.keepE F).ImpBy fun y o => (io y.1 o, y.2)) ∧
    (∀ (Xi' : Type) (Ei' : ExtSpec) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei),
      (R.pre f g).ImpBy fun y o => io (g.map y) o) ∧
    (∀ (Xo' : Type) (Eo' : ExtSpec) (f : Xo → Option Xo') (g : ExtMap Eo Eo'),
      (R.post f g).ImpBy fun y o => g.map (io y o))

end Spec
end Iop
