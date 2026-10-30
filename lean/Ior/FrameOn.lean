-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FrameOn.lean: an interactive oracle reduction (IOR) that acts on a part of a larger statement,
in one step: the definition `IOR.on`, its honest side, and one rule for the bundle of Ior/Chain.lean
(`Spec.good_on`, proved here).

An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. For statement see the head of Ior/Frame.lean.

`R.on Z F fi gi fo go` has the shape of R, by definition. First a step without rounds takes the
larger statement apart (fi, gi): into a statement of R, a further explicit part z : Z and further
oracles of the kind F. The parts may overlap: an oracle may be both in R's statement and among the
oracles handed on. Then R runs; z and the further oracles are copied. Then a step without rounds
(fo, go) puts R's output statement and what was copied together.

Main names:
  `Spec.good_on`: if R leads from A to B (`Good R H A B ext P`, Ior/Chain.lean), `R.ImpBy io` holds,
    the first step leads from A' to "A on the part, and S on what is copied", and the last step
    leads from "B on the part, and S on what is copied" to B', then `R.on` leads from A' to B'. S
    (beside the honest relations), SR (beside the relaxations) and T (a condition on statements)
    read the copied components and a further part Wz of the witness, which the honest prover
    hands on and which joins the core. Errors, probabilities and budget are those of R.

Limits: this file says nothing on numbers of queries. The rule is a composition of
`good_keep_frame`, `good_pre` and `good_post`; whoever needs predicates that read more than the
copied components uses those rules and `good_frame` one by one.
Terms: lean/GLOSSARY.md.
-/
import Ior.FrameProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K X X' Xi Xo : Type} {E E' Ei Eo : ExtSpec} {W W' Wi Wo : Type}

/-- R on a part of a larger statement. -/
def on (R : IOR Xi Ei Xo Eo) (Z : Type) (F : ExtSpec) (fi : X → Option (Xi × Z))
    (gi : ExtMap E (Ei.prod F)) (fo : Xo × Z → Option X') (go : ExtMap (Eo.prod F) E') :
    IOR X E X' E' :=
  ((R.keep Z F).pre fi gi).post fo go

/-- Its honest side: mi, mo are what the honest prover does to (explicit part, witness) in the two
steps; Wz is the part of the witness that is handed on. -/
def Honest.on {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (Z : Type)
    (F : ExtSpec) (Wz : Type) (fi : X → Option (Xi × Z)) (gi : ExtMap E (Ei.prod F))
    (fo : Xo × Z → Option X') (go : ExtMap (Eo.prod F) E')
    (mi : X × W → (Xi × Z) × (Wi × Wz)) (mo : (Xo × Z) × (Wo × Wz) → X' × W') :
    (R.on Z F fi gi fo go).Honest W W' :=
  ((((H.keep Z F).carry Wz).pre fi gi mi).post fo go mo)

/-- Its numbers: those of R. -/
def Nums.on {R : IOR Xi Ei Xo Eo} (P : Nums K R) (Z : Type) (F : ExtSpec)
    (Wz : Type) (fi : X → Option (Xi × Z)) (gi : ExtMap E (Ei.prod F))
    (fo : Xo × Z → Option X') (go : ExtMap (Eo.prod F) E') :
    Nums (K × Wz) (R.on Z F fi gi fo go) :=
  ((((P.keep Z F).carry Wz).pre fi gi).post fo go)

/-- Its extractor: back through the last step, R's extractor on the part (the further part of the
witness is copied), back through the first step. -/
def extOn {s : Shape} {F : ExtSpec} {Wz : Type} (ext : Ei.Str → Orcs s → Wo → Wi)
    (io : Ei.Str → Orcs s → Eo.Str) (gi : ExtMap E (Ei.prod F)) (backi : E.Str → Wi × Wz → W)
    (backo : (Eo.prod F).Str → W' → Wo × Wz) : E.Str → Orcs s → W' → W :=
  fun y o w =>
    backi y (ext (gi.map y).1 o (backo (io (gi.map y).1 o, (gi.map y).2) w).1,
        (backo (io (gi.map y).1 o, (gi.map y).2) w).2)

/-- The joint "A on the part, and S, SR, T on what is copied". -/
@[reducible] def Rels.part (A : Rels K Xi Ei Wi) (Z : Type) (F : ExtSpec) (Wz : Type)
    (S SR : Z → F.Str → Wz → Prop) (T : Z → F.Str → Prop) :
    Rels (K × Wz) (Xi × Z) (Ei.prod F) (Wi × Wz) :=
  ((A.keep Z F).lift Wz).and
    (fun a y w => S a.2 y.2 w.2) (fun a w => SR a.1.2 a.2.2 w.2) (fun a => T a.1.2 a.2.2)

end IOR

namespace Spec
open IOR

/-- The rule for an IOR that acts on a part of a larger statement. -/
def good_on : Prop :=
  ∀ (K X X' Xi Xo Z : Type) (E E' Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (W W' Wi Wo Wz : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (A' : Rels (K × Wz) X E W)
      (B' : Rels (K × Wz) X' E' W') (ext : Ei.Str → Orcs R.shape → Wo → Wi)
      (io : Ei.Str → Orcs R.shape → Eo.Str) (P : Nums K R) (S SR : Z → F.Str → Wz → Prop)
      (T : Z → F.Str → Prop) (fi : X → Option (Xi × Z)) (gi : ExtMap E (Ei.prod F))
      (fo : Xo × Z → Option X') (go : ExtMap (Eo.prod F) E') (mi : X × W → (Xi × Z) × (Wi × Wz))
      (mo : (Xo × Z) × (Wo × Wz) → X' × W') (backi : E.Str → Wi × Wz → W)
      (backo : (Eo.prod F).Str → W' → Wo × Wz),
    Good R H A B ext P → R.ImpBy io → Step fi gi mi backi A' (A.part Z F Wz S SR T) →
    Step fo go mo backo (B.part Z F Wz S SR T) B' →
    Good (R.on Z F fi gi fo go) (H.on Z F Wz fi gi fo go mi mo) A' B'
      (extOn ext io gi backi backo) (P.on Z F Wz fi gi fo go)

end Spec

open IOR

theorem good_on : Spec.good_on := by
  intro K X X' Xi Xo Z E E' Ei Eo F R W W' Wi Wo Wz H A B A' B' ext io P S SR T fi gi fo go mi mo
    backi backo hG hio hi ho
  have h1 := good_keep_frame K Xi Xo Z Ei Eo F R Wi Wo Wz H A B ext P S SR T hG
  have h2 := good_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fi gi mi backi hi h1
  have i1 : (R.keep Z F).ImpBy fun y o => (io y.1 o, y.2) :=
    (impBy_frame _ _ _ _ (R.keepX Z) io ((impBy_frame _ _ _ _ R io hio).1 Z)).2.1 F
  have i2 : ((R.keep Z F).pre fi gi).ImpBy fun y o => (io (gi.map y).1 o, (gi.map y).2) :=
    (impBy_frame _ _ _ _ (R.keep Z F) _ i1).2.2.1 _ _ fi gi
  exact good_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fo go mo backo _ h2 ho i2

end Iop
