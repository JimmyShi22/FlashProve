-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefJFin.lean: book-keeping for the data of a holographic IOP's hypotheses: the
one record of data for the object at the reference request with the session below the Johnson
radius.

One definition, data only, but for the proofs inside its fields' types (see "Limits"); no statement.
The object's data: the head of Cb/Obj/LdObjectData.lean. The reference request and a request's end
R: the head of Cb/Obj/LdObjectDataRef.lean.
A radius e is below the Johnson radius, at length n and distance d, if n (n - d) < (n - e)^2
(`InJohnson n d e`, Cb/Gen/JohnsonList.lean).

Main names:
  `LdFinJ F E`: the object, and the reference request with one first sending; the object is
    `Z : LdObjZM F E` (Cb/Obj/LdObjectDataMix.lean: four towers within a third, three
    below the Johnson radius).

Why it is here: the records of conditions on these data (Cb/Obj/LdObjectDataRefJ.lean: `Z.HypRefJ`;
Cb/Gl/GlFinJ.lean: `Gl.FinJ`) are stated in Cb/.

Limits: nothing is claimed: no field of `LdFinJ` itself is a proposition (records under its fields
have proofs among their fields, among them `LdCf.hp`, `LdObjD.ne`, `LdLinPl.hU` .., `LdLinPlT.hc₁`,
`hc₂`, `LdLkP.Cl.all`).
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefJ

set_option autoImplicit false

namespace Cb
open Iop Hiop

/-- The data: the object with its seven towers and distances, and the reference request with one
first sending. -/
structure LdFinJ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  Z     : LdObjZM F E
  Kc    : Type
  R     : LdORE F E Kc
  core  : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc
  first : LdSendD (LdStage.start E Kc (R.O.jReq core))
  c     : LdStage E Kc
  Ls    : LdRefL E Kc R.ix first.tgt c
  T     : LdRefT R c
  qφ    : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop
  q     : Finset R.z.J.E.Pos → Prop
  κ     : ENNReal

end Cb
