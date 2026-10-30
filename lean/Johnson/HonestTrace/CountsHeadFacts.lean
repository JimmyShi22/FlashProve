-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsHeadFacts.lean

The lookup of the calls of the output head's sub-proof: three equations on its keys and on the
matrix bH, in which no challenge occurs but θ, the element that keeps the calls apart, and the point
of comparison al. Keys and bits are read at one reading cell.

Notation: as in Johnson/HonestTrace/CountsHead.lean; lmbH is P.h.lmbH; Z, a_pad, P_1 and G_0 are the
terms zRoot, aPad, pChain at 1 and gRoot at 0 of Johnson/HonestTrace/CountsProducts.lean.

Main theorem: "factsH". Let Head.layout P.h tau return P.L; for every call c below NC let every
place below 2^(n_c) of H.kvH P cell c hold the value of a row below 2^(k_c) of the call's table; let
FillerIsPad P cell and LaidBH P cell hold (Johnson/HonestTrace/CountsHead.lean); let ν read cell
(.cell (P.h.NHf + 2) r c) at every place .cell r c with r below 2^lmbH and c below NC 2^(kT + 5 -
lmbH). Then, for all θ and al:
1. Z = a_pad (P_1^2 G_0), in the terms zRoot, aPad, pChain, gRoot of
   Johnson/HonestTrace/CountsProducts.lean, at the keys H.kvH P cell and the bits H.bitsH P.h P.L.fs
   cell;
2. every x = ν (.cell r c) at such r and c has x (x - 1) = 0;
3. Cb.Fo.Pin.countK P.L.fs lmbH (Cb.Fo.Pin.pinColK lmbH ν) = 0
   (OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean).

Limits. The premises are assumed, not proved. Of the claims of the byte format's page
docs/format/11-1-machinery.md, equation 3 is LP2: the counts add up to the number of keys that are
not padding. It is an equation in K. Equations 1 and 2 are what the format's "tie step 0" and its
test of the bits are about; they are not the claims LK0, LK(31 + v + dL) and LP1, which read further
challenges and the mask row; this file says nothing of these or of any other claim.

Not claimed: that H.kvH and H.bitsH are what a verifier reads; that a prover sends these values;
that a verifier accepts; completeness of the protocol.

-/
import Johnson.HonestTrace.CountsHead
import Johnson.HonestTrace.CountsProducts

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open OnBytes.Ends.H (NameH PubH)

section
variable {K : Type} [Field K] [DecidableEq K]

/-- If Head.layout P.h tau returns P.L, for every call c below NC every place below 2^(n_c) of
H.kvH P cell c holds the value of a row below 2^(k_c) of tabOf, FillerIsPad P cell and
LaidBH P cell hold, and ν reads cell (.cell (P.h.NHf + 2) r c) at every place .cell r c with r below
2^lmbH and c below NC 2^(kT + 5 - lmbH), then for all θ and al: Z = a_pad (P_1^2 G_0) at the keys
H.kvH P cell and the bits H.bitsH P.h P.L.fs cell; every x = ν (.cell r c) at such r and c has
x (x - 1) = 0; and countK P.L.fs lmbH (pinColK lmbH ν) = 0. -/
theorem factsH {tau : Array F} (P : PubH) (hy : Head.layout P.h tau = .ok P.L)
    (cell : NameH → K)
    (hin : ∀ c < P.L.fs.NC, Cb.Lkp.InTable (FoNums.nOf P.L.fs c) (FoNums.kOf P.L.fs c)
      (Ends.H.kvH P cell c) (tabOf K P.L.fs c))
    (hfill : FillerIsPad P cell) (hb : LaidBH P cell) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ P.h.lmbH, ∀ c < P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH),
      ν (.cell r c) = cell (.cell (P.h.NHf + 2) r c)) (θ al : K) :
    zRoot P.L.fs (Ends.H.kvH P cell) θ al =
        aPad P.L.fs θ al *
          (pChain P.L.fs (fun u j => Ends.H.bitsH P.h P.L.fs cell (u * 32 + j)) θ al 1 ^ 2 *
            gRoot P.L.fs (fun u j => Ends.H.bitsH P.h P.L.fs cell (u * 32 + j)) θ al 0) ∧
      (∀ r < 2 ^ P.h.lmbH, ∀ c < P.L.fs.NC * 2 ^ (P.L.fs.kT + 5 - P.h.lmbH),
        ν (.cell r c) * (ν (.cell r c) - 1) = 0) ∧
      Cb.Fo.Pin.countK P.L.fs P.h.lmbH (Cb.Fo.Pin.pinColK P.h.lmbH ν) = 0 :=
  facts_plane (lawH P hy cell hin hfill hb θ al) _ _ _ (ok_H hy).1 (fitsH P hy cell hin hfill)
    (ok_H hy).2.1 (ok_H hy).2.2 ν fun r hr c hc => (hν r hr c hc).trans (hb r hr c hc)

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.factsH
