-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/GatedEndsText.lean: the verifier's routines for the product layers of the gated
products are written with the forms of Johnson/Road/Rows/GatedEnds.lean.

Main theorems, each by rfl: claimsEnds_eq (the two end claims are slot + endForm), claimsGated_eq
(with which arguments claimsEnds is called), hearGated_eq (the first layer starts from the slot of
the first never-sent vector's value, the second from start2). So a statement on endForm or start2
speaks of the forms that the routines claim or start from.

What is not claimed: the equations say how the text reads, not what a run of it leaves. The program
does not import this file.


-/
import Johnson.Road.Rows.GatedEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (Aff Level SubM hiTab layerObject levelIn orderRange)
open OnBytes.Model.Layer (Env Pub Heard HeardStack form note downFrom claimsEnds claimsGated
  hearGated)

/-- claimsEnds, with endForm. -/
theorem claimsEnds_eq (v : Env) (o : Level) (e : Array E) (t rows blocks stride : ℕ)
    (lamOf : ℕ → ℕ) (first : ℕ) :
    claimsEnds v o e t rows blocks stride lamOf first = (do
      let ts ← form (v.y.T_ "s")
      let tu ← form (v.y.T_ "u")
      SubM.lin (Aff.slot o.sL + (← form (endForm v t ts e rows blocks stride lamOf first)))
      SubM.lin (Aff.slot o.sR + (← form (endForm v t tu e rows blocks stride lamOf first)))) :=
  rfl

/-- claimsGated: the layers' claims, and the arguments of claimsEnds. -/
theorem claimsGated_eq (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level) :
    claimsGated P v hd hd2 = (do
      layerObject hd
      let e ← form (hiTab hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption
      claimsEnds v hd e (← form (v.tabAt "af@Z_a")) P.y.Lam (P.y.h.f / P.y.S2)
        (P.y.Pf / P.y.S2) id 0
      match hd2 with
      | none => pure ()
      | some o =>
        layerObject o
        let e ← form (hiTab o.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption
        claimsEnds v o e (← form (v.tabAt "af@Z_b")) P.y.LamM (P.y.h.fe / P.y.S2)
          (P.y.h.fe / P.y.S2) (fun lm => 2 * lm + 1) (P.y.h.fe / P.y.S2)) := rfl

/-- hearGated: the two layers' points and start forms. -/
theorem hearGated_eq (P : Pub) (H : Heard) (K : HeardStack) :
    hearGated P H K = (do
      let hd ← levelIn P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1)
        (orderRange P.rd.muH)
      note "hd.r[0]" (hd.r.getD 0 zeroE)
      if !P.y.h.p3 then pure (hd, none)
      else
        let tT ← form H.tT
        let rhoM ← if P.y.h.ll > 1 then SubM.point .join (P.y.h.ll - 1) else pure #[]
        let hd2 ← levelIn P.rd.muH2 (rhoM ++ downFrom K.rs P.y.lfe ++ tT.r)
          (start2 P.y.LamM K.sH1 rhoM) (orderRange P.rd.muH2)
        note "hd2.r[0]" (hd2.r.getD 0 zeroE)
        pure (hd, some hd2)) := rfl

end OnBytes.Road.Rows
