-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpFin.lean: assembly of the holographic IOP from its sub-protocols: the data at the
plan of this protocol's technical report (lean/CREDITS.md) for the linear test.

One definition: data only (proofs among the data, among them: those of the plans' and tests' own
records under `Z.R`). Records of conditions on these data: `Z.HypRefPJ`
(Cb/Obj/LdObjectPpData.lean); at the fields `Gl.F`, `Gl.E`: `Gl.FinalPp` (Cb/Gl/GlFinalPp.lean).

The analogue of Cb/Obj/LdObjectDataRefJFin.lean (`LdFinJ`).

Main names:
  `LdFinPp F E`: the object on data at that plan with its nine towers and distances
    (Cb/Obj/LdObjectPpData.lean: `LdObjZp`), and the reference request with one first sending.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPpData

set_option autoImplicit false

namespace Cb
open Iop Hiop

/-- The data. -/
structure LdFinPp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  Z     : LdObjZp F E
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
