-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/GatedClaims.lean: which claims the verifier's routine claimsGated adds.

Johnson/Road/FormsKeysClaims.lean says of a routine of a sub-proof's check which list of forms it
adds to the one equation (AddsL). This file gives that list for claimsEnds and for claimsGated
(OnBytes/Model/Layer.lean), with the sums of claimsEnds written as endForm of
Johnson/Road/Rows/GatedEnds.lean.

Main definitions: endsL, gatedL. Main theorems: adds_claimsEnds, adds_claimsGated.

What is not claimed. The theorems have the form "whenever the routine returns". That a form of the
list is worth 0 is not said here. The program does not import this file.


-/
import Johnson.Road.FormsKeysClaims
import Johnson.Road.Rows.GatedEndsText

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (Aff Level hiTab)
open OnBytes.Model.Layer (Env Pub claimsEnds claimsGated)

/-- The two claims of claimsEnds. -/
def endsL (v : Env) (o : Level) (e : Array E) (t rows blocks stride : ℕ) (lamOf : ℕ → ℕ)
    (first : ℕ) : Option (List Aff) :=
  (v.y.T_ "s").bind fun ts => (v.y.T_ "u").bind fun tu =>
    (endForm v t ts e rows blocks stride lamOf first).bind fun aS =>
      appL (some [Aff.slot o.sL + aS])
        ((endForm v t tu e rows blocks stride lamOf first).bind fun aU =>
          some [Aff.slot o.sR + aU])

/-- claimsEnds adds them. -/
theorem adds_claimsEnds (v : Env) (o : Level) (e : Array E) (t rows blocks stride : ℕ)
    (lamOf : ℕ → ℕ) (first : ℕ) :
    AddsL (claimsEnds v o e t rows blocks stride lamOf first)
      (endsL v o e t rows blocks stride lamOf first) := by
  rw [claimsEnds_eq]
  exact addsV_form _ fun ts => addsV_form _ fun tu => addsV_form _ fun aS =>
    addsV_bind (addsL_lin _) fun _ _ => addsV_form _ fun aU => addsL_lin _

/-- The claims of claimsGated for the second product layer, if there is one. -/
def gatedL2 (P : Pub) (v : Env) : Option Level → Option (List Aff)
  | none => some []
  | some o => appL (some [o.row])
      ((hiTab o.r P.y.h.la (P.y.h.ll - 1 + P.y.lfe - P.y.ls)).toOption.bind fun e =>
        (v.tabAt "af@Z_b").bind fun t =>
          endsL v o e t P.y.LamM (P.y.h.fe / P.y.S2) (P.y.h.fe / P.y.S2) (fun lm => 2 * lm + 1)
            (P.y.h.fe / P.y.S2))

/-- The claims of claimsGated. -/
def gatedL (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level) : Option (List Aff) :=
  appL (some [hd.row])
    ((hiTab hd.r P.y.h.la (P.y.h.ll + P.y.lPf - P.y.ls)).toOption.bind fun e =>
      (v.tabAt "af@Z_a").bind fun t =>
        appL (endsL v hd e t P.y.Lam (P.y.h.f / P.y.S2) (P.y.Pf / P.y.S2) id 0) (gatedL2 P v hd2))

/-- claimsGated adds them. -/
theorem adds_claimsGated (P : Pub) (v : Env) (hd : Level) (hd2 : Option Level) :
    AddsL (claimsGated P v hd hd2) (gatedL P v hd hd2) := by
  rw [claimsGated_eq]
  refine addsV_bind (addsL_lin _) fun _ _ => addsV_form _ fun e => addsV_form _ fun t =>
    addsV_bind (adds_claimsEnds _ _ _ _ _ _ _ _ _) fun _ _ => ?_
  cases hd2 with
  | none => exact addsV_pure _ trivial
  | some o =>
    exact addsV_bind (addsL_lin _) fun _ _ => addsV_form _ fun e2 => addsV_form _ fun t2 =>
      adds_claimsEnds _ _ _ _ _ _ _ _ _

end OnBytes.Road.Rows
