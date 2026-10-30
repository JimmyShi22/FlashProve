-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAtDigits.lean

The premises "PremF" of Johnson/HonestTrace/LookDefs.lean at the lookup on the digits of a
sub-proof's smallness test.

Main theorem: "premF_Z": under Fo.ZPlan.FromPieces tl, DigitsIn tl zz and LaidBZ tl zz bz
(Johnson/HonestTrace/CountsDigits.lean), for every reading ν of the places Fo.Pl that reads 0 at
.zero and virtZ tl bz r c at every place .cell r c with r below 2^5 and c below NC 2^(kT + 5 - 5),
every θ and al, and every C whose lists have the lengths of the plan: PremF holds at the shape
tl.f9, lm = 5 and the key vectors kvZ tl zz. There are two calls, so nothing is asked of θ.

Limits. It joins premF_of_law (Johnson/HonestTrace/LookAt.lean) with the theorems of
Johnson/HonestTrace/CountsDigits.lean and adds nothing to them; their limits hold here. DigitsIn is
assumed. The cells .cell r c are those of the matrix with one row a plane, not BZ's own rows and
columns: virtZ says which entry of BZ each is.

Not claimed: that a prover sends these values or commits to these arrays; that a verifier accepts.

-/
import Johnson.HonestTrace.CountsDigits
import Johnson.HonestTrace.LookAt

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open OnBytes.Model
open Fo.ZPlan (FromPieces)

section
variable {K : Type} [Field K] [DecidableEq K]

/-- Under FromPieces tl, DigitsIn tl zz and LaidBZ tl zz bz: if ν reads 0 at Fo.Pl.zero and
virtZ tl bz r c at every place .cell r c with r below 2^5 and c below NC 2^(kT + 5 - 5), and C.Fits
holds at tl.f9's v and d, then PremF holds at tl.f9, lm = 5, the key vectors kvZ tl zz, θ, al, ν and
C. -/
theorem premF_Z {tl : HTailF2} (hF : FromPieces tl) {zz bz : ℕ → ℕ → K} (hd : DigitsIn tl zz)
    (hb : LaidBZ tl zz bz) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ 5, ∀ c < tl.f9.NC * 2 ^ (tl.f9.kT + 5 - 5), ν (.cell r c) = virtZ tl bz r c)
    (h0 : ν .zero = 0) (θ al : K) (C : Chal K) (hC : C.Fits tl.f9.v tl.f9.d 5) :
    PremF tl.f9 5 jLK (kvZ tl zz) θ al ν C :=
  premF_of_law tl.f9 (kvZ tl zz) (padZ tl) (nums_Z hF).1 (inTable_Z hF hd) (kvZ_padRow hF zz)
    (pubFits_Z hF) (le_refl 5) (Nat.le_add_left 5 _) jLK ν
    (fun r hr c hc => (hν r hr c hc).trans (virtZ_plane hF hb r hr c hc)) h0 θ al
    (fun h => by
      unfold FoNums.several at h
      rw [(nums_Z hF).2.1] at h
      exact absurd h (by decide)) C hC

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.premF_Z
