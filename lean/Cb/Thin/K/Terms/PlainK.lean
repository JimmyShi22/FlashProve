-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K/Terms/PlainK.lean: the part of the library's conditions on the object which the road to
index binding reads, as a record, and what it gives.

Definitions, statements and proofs. The object is `LdObj` (Cb/Obj/LdObject.lean); the records on
its terms are those of Cb/Thin/K/Terms/Terms.lean.
Main names:
  `LdObj.KnowOK`: of the configuration: the distance, and the radius of decoding below it; of the
    five terms: their records.
  `ldObj_hypK`: the five items on knowledge soundness (`SubsR.HypK`).
  `ldObj_sides`, `ldObj_points`: the two facts on the request's preamble, locality, coherence; the
    five point structures.
  `ldCf_sub`: a fact on the configuration.

Limits: the link's three (its item `LinkKnowR`, its locality, its point structure) are fields, that
is hypotheses: they are made elsewhere. No object is shown here to have that record. No statement
of this file names a bundle, a list of the honest side or an honest prover.


-/
import Cb.Obj.LdObjectProofs
import Cb.Thin.K.Terms.Terms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- What the road reads of the configuration and of the five terms. -/
structure LdObj.KnowOK {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    (Obj : LdObj F E) : Prop where
  /-- the code of the encoded index has its distance -/
  dist      : HasDist Obj.Cf.C₀.G Obj.Cf.C₀.d
  /-- the radius of decoding is below the distance -/
  rad       : Obj.Cf.eM < Obj.Cf.C₀.d
  /-- weights-formedness -/
  wf        : Obj.wf.KnowOK
  /-- the test at one instance -/
  lin       : Obj.lin.KnowOK
  /-- the link's item on knowledge soundness: taken as it stands in the list -/
  linkKnow  : LinkKnowR (C := Obj.Cf.conf) (Obj.K.link Obj.link) (Obj.K.nums Obj.link).err
  /-- the link is local -/
  linkLocal : (Obj.K.link Obj.link).IsLocal
  /-- the link's shape has a point structure -/
  linkPoint : Nonempty (Obj.K.link Obj.link).shape.IsPoint
  /-- a request -/
  req       : Obj.req.KnowOK Obj.z0
  /-- the test at N instances -/
  linB      : Obj.linB.LinBK

/-- The half on knowledge soundness of `ldObj_hyp` (Cb/Obj/LdObjectProofs.lean). -/
theorem ldObj_hypK (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Obj : LdObj F E)
    (h : Obj.KnowOK) : Obj.subs.HypK Obj.nums :=
  ⟨ldOW_know F E Obj.off.ol Obj.Kw Obj.wf h.wf,
    ldOT_know F E Obj.off.ol Obj.lin Obj.dOff h.dist h.rad h.lin,
    h.linkKnow,
    ldOR_know F E Obj.on.ol Obj.Kr Obj.req Obj.z0 Obj.r0 h.req,
    ldOBT_know F E Obj.on.ol Obj.N Obj.linB Obj.dOn h.dist h.rad h.linB⟩

/-- The two facts on the request's preamble, the sub-protocols' locality and coherence, in this
order. -/
theorem ldObj_sides (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Obj : LdObj F E)
    (h : Obj.KnowOK) :
    (∀ x y τ b, Obj.subs.req.out x y τ = some b → b.2 = x.2) ∧
      (∀ y τ, (Obj.subs.req.imp y τ).1 = y) ∧ Obj.subs.wf.IsLocal ∧ Obj.subs.linOff.IsLocal ∧
      Obj.subs.link.IsLocal ∧ Obj.subs.req.IsLocal ∧ Obj.subs.linOn.ior.IsLocal ∧
      Obj.subs.linOn.ann.Coherent :=
  ⟨ldOR_passes F E Obj.on.ol Obj.Kr Obj.req Obj.z0 h.req,
    ldOR_copy F E Obj.on.ol Obj.Kr Obj.req Obj.z0 h.req,
    ldOW_local F E Obj.off.ol Obj.Kw Obj.wf h.wf, h.lin.isLocal, h.linkLocal,
    ldOR_local F E Obj.on.ol Obj.Kr Obj.req Obj.z0 h.req, h.linB.isLocal, h.linB.coherent⟩

/-- The five shapes have point structures. -/
theorem ldObj_points (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Obj : LdObj F E)
    (h : Obj.KnowOK) :
    Nonempty Obj.subs.wf.shape.IsPoint ∧ Nonempty Obj.subs.linOff.shape.IsPoint ∧
      Nonempty Obj.subs.link.shape.IsPoint ∧ Nonempty Obj.subs.req.shape.IsPoint ∧
      Nonempty Obj.subs.linOn.ior.shape.IsPoint :=
  ⟨h.wf.point, h.lin.point, h.linkPoint, h.req.point, h.linB.point⟩

/-- The clause `sub` of `ldCf_props` (Cb/Obj/LdObjectConfProofs.lean) by itself: the configuration
takes the model's two relations over. -/
theorem ldCf_sub (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)
    (h : ∀ i x w, Cf.Ryes i x w → Cf.Rno i x w) :
    ∀ i x w, Cf.conf.Ryes i x w → Cf.conf.Rno i x w :=
  h

end Cb

