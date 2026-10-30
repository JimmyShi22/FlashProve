-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookAtDigitsClaims.lean

The list of claims of a lookup, at the rounds "rsF" of Johnson/HonestTrace/LookDefs.lean, at the
lookup on the digits of a sub-proof's smallness test.

Main theorems: "claimsZero_digits": under Fo.ZPlan.FromPieces tl, DigitsIn tl zz and LaidBZ tl zz bz
(Johnson/HonestTrace/CountsDigits.lean), for every reading ν of the places Fo.Pl that reads 0 at
.zero and virtZ tl bz r c at every place .cell r c with r below 2^5 and c below NC 2^(kT + 5 - 5),
every θ and al, and every C whose lists have the lengths of the plan: "ClaimsZero"
(Johnson/HonestTrace/LookAtClaims.lean) holds at tl.f9, lm = 5 and the key vectors kvZ tl zz: every
member of Fo.claimsOf at these rounds is 0.
"claimsZero_digits_G", "claimsZero_digits_A", "claimsZero_digits_H": where Verify.publicOf returns
X, the same at hp.tl for a member hp of X.G, at a.seam.tl for a member a of X.A, and at X.H.tl,
without the premise FromPieces (public_G_from, public_A_from, public_H_from,
OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean).

Limits. It joins claims_hon (Johnson/HonestTrace/LookClaimsHon.lean) with premF_Z
(Johnson/HonestTrace/LookAtDigits.lean) and adds nothing to them; their limits hold here. DigitsIn
is assumed. Fo.claimsOf is the library's list at lm = 5, on the matrix with one row a plane. The
smallness test of OnBytes/Model/Tail.lean writes its claims on BZ and ZZ by routines of its own;
that these are the members of this list is not shown in this file.

Not claimed: that a prover sends these values or commits to these arrays; that a verifier accepts.

-/
import Johnson.HonestTrace.LookAtClaims
import Johnson.HonestTrace.LookAtDigits

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open OnBytes.Model
open Fo.ZPlan (FromPieces)

section
variable {K : Type} [Field K] [DecidableEq K]

/-- Under FromPieces tl, DigitsIn tl zz and LaidBZ tl zz bz: if ν reads 0 at Fo.Pl.zero and
virtZ tl bz r c at every place .cell r c with r below 2^5 and c below NC 2^(kT + 5 - 5), and C.Fits
holds at tl.f9's v and d, then ClaimsZero holds at tl.f9, lm = 5, the key vectors kvZ tl zz, θ, al,
ν and C. -/
theorem claimsZero_digits {tl : HTailF2} (hF : FromPieces tl) {zz bz : ℕ → ℕ → K}
    (hd : DigitsIn tl zz) (hb : LaidBZ tl zz bz) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ 5, ∀ c < tl.f9.NC * 2 ^ (tl.f9.kT + 5 - 5), ν (.cell r c) = virtZ tl bz r c)
    (h0 : ν .zero = 0) (θ al : K) (C : Chal K) (hC : C.Fits tl.f9.v tl.f9.d 5) :
    ClaimsZero tl.f9 5 jLK (kvZ tl zz) θ al ν C :=
  claims_hon tl.f9 5 jLK (kvZ tl zz) θ al ν C (premF_Z hF hd hb jLK ν hν h0 θ al C hC)

variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- If Verify.publicOf returns X and hp is member g of X.G: under DigitsIn hp.tl zz and
LaidBZ hp.tl zz bz, if ν reads 0 at Fo.Pl.zero and virtZ hp.tl bz r c at every place .cell r c with
r below 2^5 and c below NC 2^(kT + 5 - 5), and C.Fits holds at hp.tl.f9's v and d, then ClaimsZero
holds at hp.tl.f9, lm = 5, the key vectors kvZ hp.tl zz, θ, al, ν and C. -/
theorem claimsZero_digits_G (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) {zz bz : ℕ → ℕ → K} (hd : DigitsIn hp.tl zz)
    (hb : LaidBZ hp.tl zz bz) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ 5, ∀ c < hp.tl.f9.NC * 2 ^ (hp.tl.f9.kT + 5 - 5),
      ν (.cell r c) = virtZ hp.tl bz r c)
    (h0 : ν .zero = 0) (θ al : K) (C : Chal K) (hC : C.Fits hp.tl.f9.v hp.tl.f9.d 5) :
    ClaimsZero hp.tl.f9 5 jLK (kvZ hp.tl zz) θ al ν C :=
  claimsZero_digits (Fo.ZPlan.public_G_from h g hp hg) hd hb jLK ν hν h0 θ al C hC

/-- If Verify.publicOf returns X and a is member g of X.A: under DigitsIn a.seam.tl zz and
LaidBZ a.seam.tl zz bz, if ν reads 0 at Fo.Pl.zero and virtZ a.seam.tl bz r c at every place
.cell r c with r below 2^5 and c below NC 2^(kT + 5 - 5), and C.Fits holds at a.seam.tl.f9's v and
d, then ClaimsZero holds at a.seam.tl.f9, lm = 5, the key vectors kvZ a.seam.tl zz, θ, al, ν and
C. -/
theorem claimsZero_digits_A (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ)
    (a : Attention.Plan) (hg : X.A[g]? = some a) {zz bz : ℕ → ℕ → K}
    (hd : DigitsIn a.seam.tl zz) (hb : LaidBZ a.seam.tl zz bz) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ 5, ∀ c < a.seam.tl.f9.NC * 2 ^ (a.seam.tl.f9.kT + 5 - 5),
      ν (.cell r c) = virtZ a.seam.tl bz r c)
    (h0 : ν .zero = 0) (θ al : K) (C : Chal K) (hC : C.Fits a.seam.tl.f9.v a.seam.tl.f9.d 5) :
    ClaimsZero a.seam.tl.f9 5 jLK (kvZ a.seam.tl zz) θ al ν C :=
  claimsZero_digits (Fo.ZPlan.public_A_from h g a hg) hd hb jLK ν hν h0 θ al C hC

/-- If Verify.publicOf returns X: under DigitsIn X.H.tl zz and LaidBZ X.H.tl zz bz, if ν reads 0 at
Fo.Pl.zero and virtZ X.H.tl bz r c at every place .cell r c with r below 2^5 and c below
NC 2^(kT + 5 - 5), and C.Fits holds at X.H.tl.f9's v and d, then ClaimsZero holds at X.H.tl.f9,
lm = 5, the key vectors kvZ X.H.tl zz, θ, al, ν and C. -/
theorem claimsZero_digits_H (h : Verify.publicOf pol KL layout = .ok X) {zz bz : ℕ → ℕ → K}
    (hd : DigitsIn X.H.tl zz) (hb : LaidBZ X.H.tl zz bz) (jLK : ℕ) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ 5, ∀ c < X.H.tl.f9.NC * 2 ^ (X.H.tl.f9.kT + 5 - 5),
      ν (.cell r c) = virtZ X.H.tl bz r c)
    (h0 : ν .zero = 0) (θ al : K) (C : Chal K) (hC : C.Fits X.H.tl.f9.v X.H.tl.f9.d 5) :
    ClaimsZero X.H.tl.f9 5 jLK (kvZ X.H.tl zz) θ al ν C :=
  claimsZero_digits (Fo.ZPlan.public_H_from h) hd hb jLK ν hν h0 θ al C hC

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.claimsZero_digits
#print axioms OnBytes.HonestTrace.Look.claimsZero_digits_G
#print axioms OnBytes.HonestTrace.Look.claimsZero_digits_A
#print axioms OnBytes.HonestTrace.Look.claimsZero_digits_H
