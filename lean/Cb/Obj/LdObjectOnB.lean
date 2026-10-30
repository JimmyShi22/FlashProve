-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnB.lean: the test for linear constraints (an IOPP) for at most N instances, for any
term: its parameter list, under the hypotheses of `Spec.ldOBT_object`.

Definitions, one statement and its proof.
`O : LdOL F E` is the test's data (Cb/Obj/LdObjectLin.lean), `O.Cf.conf` the configuration
(Cb/Obj/LdObjectConf.lean).

Main names:
  `O.LinBT N`: any term: a reduction R on the list's types to the trivial statement, an annotation,
    the honest side of a chain of batch links (`HonestV`, Ior/LinkV.lean) whose shared witness at
    the start is the prover encoded index, its numbers; a condition on0 on the index and a backward
    extractor.
  `T.OK`: what is used of it.
    The honest half: the hypotheses of `Hiop.rec_linB_list` (formats of R and its annotation;
    `bud0`, `prBad`; complete and exactly honest-verifier zero knowledge for sets of slots from a
    relation RiV of its own (`acc`, `exact`); the constraint relation gives RiV).
    The other half: on0 holds wherever the index decodes and has no collision (`O.Fits`), and one
    `KnowB` of R from the test's first joint `O.P.j0 on0` (its condition `on`, its relaxed relation
    `relR`), for vectors of statements with one (index, record).
    And what the verifier reads is within a bound qi that is closed under subsets (for the line on
    the preamble's budget: `Spec.ldOR_fit`, Cb/Obj/LdObjectReq.lean).
  `Spec.ldOBT_object`: `HasDist O.Cf.C₀.G O.Cf.C₀.d`, `O.Cf.eM < O.Cf.C₀.d`, `T.OK` ⇒
    `LinBListR` and `LinBKnowR` (Hiop/RecSubs.lean) of `T.Q`.

Limits: no term is given.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinB
import Hiop.RecLinkV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdOL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (O : LdOL F E)

/-- Any term for the test at N instances: the data. -/
structure LinBT (N : ℕ) where
  R   : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone
  A   : RoundSplits R.shape
  Wi  : Type
  W0' : Type
  Wo  : Type
  H   : R.HonestV A O.Cf.conf.PIdx Wi W0' Wo
  mkW : O.Cf.conf.PIdx → O.left.WAux → Wi
  RiV : O.left.Xl × O.Cf.conf.Rec → O.left.El.Str → O.Cf.conf.PIdx × Wi → Prop
  RoV : Unit → extNone.Str → W0' × Wo → Prop
  P   : LinBNums R.shape N
  on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop
  ext : (O.left.Xl × O.Cf.conf.Rec) × O.left.El.Str → Tr R.shape → Unit → O.P.W0
  qi  : Finset O.left.El.Pos → Prop

namespace LinBT
variable {O} {N : ℕ} (T : O.LinBT N)

/-- The batch protocol and its honest side, in the list's types. -/
def Q : BIOP (O.left.Xl × O.Cf.conf.Rec) O.left.El := ⟨T.R, T.A⟩
def hQ : T.Q.Honest O.Cf.conf.PIdx O.left.WAux := T.H.toB T.mkW

open Classical in
structure OK : Prop where
  point    : Nonempty T.R.shape.IsPoint
  isLocal  : T.R.IsLocal
  coherent : T.A.Coherent
  tied     : T.R.Tied
  idxShared : ∀ ρ ρ', Rho.sh T.A ρ = Rho.sh T.A ρ' →
    (T.R.extReads ρ).filter (fun p => p.isLeft) = (T.R.extReads ρ').filter (fun p => p.isLeft)
  idxReads : ∀ ρ, ((T.R.extReads ρ).filter fun p => p.isLeft).card ≤ T.P.q
  acc      : T.H.AccV T.RiV T.RoV
  exact    : T.H.ExactV N T.RiV T.P.bud
  bud0     : ∀ J ρs, T.P.bud J ρs fun _ => ∅
  prBad    : prRho T.H.withheld ≤ T.P.pBad
  bridge   : ∀ x y w, O.left.Rlin x y w → T.RiV x y (w.1, T.mkW w.1 w.2)
  fits     : O.Fits T.on0
  know     : T.R.KnowB T.A N (SameKey fun a => (a.2.1, a.1.2)) (O.P.j0 T.on0).on (O.P.j0 T.on0).relR
    (fun _ (_ : Unit) => True) T.ext T.P.err
  reads    : ∀ ρ, T.qi (T.R.given ρ ∅) ∧ T.R.extReads ρ ⊆ T.R.given ρ ∅
  mono     : ∀ U V, V ⊆ U → T.qi U → T.qi V

end LinBT
end LdOL

def Spec.ldOBT_object (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] : Prop :=
  ∀ (O : LdOL F E) (N : ℕ) (T : O.LinBT N) (d0 : O.left.AMsg), HasDist O.Cf.C₀.G O.Cf.C₀.d →
    O.Cf.eM < O.Cf.C₀.d → T.OK → LinBListR O.left T.Q T.hQ N T.P ∧ LinBKnowR O.left T.Q N d0 T.P.err



-- Limit: no theorem of this library states the hypothesis `T.OK` at a concrete instance.

theorem ldOBT_object (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] :
    Spec.ldOBT_object F E := fun O N T d0 hd he h =>
  ⟨rec_linB_list O.Cf.conf O.left T.R T.A T.Wi T.W0' T.Wo T.H T.mkW T.RiV T.RoV N T.P h.point
      h.isLocal h.coherent h.tied h.idxShared h.idxReads h.acc h.exact h.bud0 h.prBad h.bridge,
    ldOB_know F E O T.on0 T.Q N T.ext T.P.err d0 hd he h.fits h.know⟩

end Cb
