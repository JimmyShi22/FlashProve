-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsLayersFacts.lean

The lookup of the calls of a layers' sub-proof: three equations on its keys and on the matrix b, in
which no challenge occurs but θ, the element that keeps the calls apart, and the point of comparison
al. Keys and bits are read at one reading cell.

Notation: as in Johnson/HonestTrace/CountsLayers.lean; lmb is P.y.h.lmb; Z, a_pad, P_1 and G_0 are
the terms zRoot, aPad, pChain at 1 and gRoot at 0 of Johnson/HonestTrace/CountsProducts.lean.

Main theorem: "factsG". Let Layer.layout h pc return P.y and Road.Switches h hold; for every call c
below NC let every place below 2^(n_c) of G.kvG P g cell c hold the value of a row below 2^(k_c) of
the call's table; let LaidB P g cell hold (Johnson/HonestTrace/CountsLayers.lean); let ν read cell
(.cell (G.iB P.y) r c) at every place .cell r c with r below 2^lmb and c below NC 2^(kT + 5 - lmb).
Then, for all θ and al:
1. Z = a_pad (P_1^2 G_0), in the terms zRoot, aPad, pChain, gRoot of
   Johnson/HonestTrace/CountsProducts.lean, at the keys G.kvG P g cell and the bits G.bitsG P.y
   cell;
2. every x = ν (.cell r c) at such r and c has x (x - 1) = 0;
3. Cb.Fo.Pin.countK P.y.fo lmb (Cb.Fo.Pin.pinColK lmb ν) = 0
   (OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean).

Limits. The premises are assumed, not proved; keysSkipB (Johnson/HonestTrace/CountsLayersSkip.lean)
with withBG_laid and inTable_withBG (CountsLayers.lean) gives, under six premises on public numbers,
that withBG P g cell meets LaidB, and that the premise on the keys passes from cell to it. Of the
claims of the byte format's page docs/format/11-1-machinery.md, equation 3 is LP2: the counts add up
to the number of keys that are not padding. It is an equation in K. Equations 1 and 2 are what the
format's "tie step 0" and its test of the bits are about; they are not the claims LK0, LK(31 + v +
dL) and LP1, which read further challenges and the mask row; this file says nothing of these or of
any other claim.

Not claimed: that G.kvG and G.bitsG are what a verifier reads; that a prover sends these values;
that a verifier accepts; completeness of the protocol.

-/
import Johnson.HonestTrace.CountsLayers
import Johnson.HonestTrace.CountsProducts

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Layer (layout)
open OnBytes.Road (Switches)

section
variable {K : Type} [Field K] [DecidableEq K]

/-- If Layer.layout h pc returns P.y, Switches h holds, for every call c below NC every place below
2^(n_c) of G.kvG P g cell c holds the value of a row below 2^(k_c) of tabOf, LaidB P g cell holds,
and ν reads cell (.cell (G.iB P.y) r c) at every place .cell r c with r below 2^lmb and c below
NC 2^(kT + 5 - lmb), then for all θ and al: Z = a_pad (P_1^2 G_0) at the keys G.kvG P g cell and the
bits G.bitsG P.y cell; every x = ν (.cell r c) at such r and c has x (x - 1) = 0; and
countK P.y.fo lmb (pinColK lmb ν) = 0. -/
theorem factsG {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c))
    (hb : LaidB P g cell) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ P.y.h.lmb, ∀ c < P.y.fo.NC * 2 ^ (P.y.fo.kT + 5 - P.y.h.lmb),
      ν (.cell r c) = cell (.cell (G.iB P.y) r c)) (θ al : K) :
    zRoot P.y.fo (G.kvG P g cell) θ al =
        aPad P.y.fo θ al *
          (pChain P.y.fo (fun u j => G.bitsG P.y cell (u * 32 + j)) θ al 1 ^ 2 *
            gRoot P.y.fo (fun u j => G.bitsG P.y cell (u * 32 + j)) θ al 0) ∧
      (∀ r < 2 ^ P.y.h.lmb, ∀ c < P.y.fo.NC * 2 ^ (P.y.fo.kT + 5 - P.y.h.lmb),
        ν (.cell r c) * (ν (.cell r c) - 1) = 0) ∧
      Cb.Fo.Pin.countK P.y.fo P.y.h.lmb (Cb.Fo.Pin.pinColK P.y.h.lmb ν) = 0 := by
  obtain ⟨hok, h5, hlm⟩ := ok_of_layout hy
  exact facts_plane (lawG P hy S g cell hin hb θ al) _ _ _ hok (fitsG P hy S g cell hin) h5 hlm ν
    fun r hr c hc => (hν r hr c hc).trans (hb r hr c hc)

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.factsG
