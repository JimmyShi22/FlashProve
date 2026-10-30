-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsAttentionFacts.lean

The lookup of the calls of an attention sub-proof: three equations on its keys and on the matrix bA,
in which no challenge occurs but θ, the element that keeps the calls apart, and the point of
comparison al. Keys and bits are read at one reading cell.

Notation: as in Johnson/HonestTrace/CountsAttention.lean; lmb is S.cf.lmb; Z, a_pad, P_1 and G_0 are
the terms zRoot, aPad, pChain at 1 and gRoot at 0 of Johnson/HonestTrace/CountsProducts.lean.

Main theorem: "factsA". Let Attention.shapeHid lid cf return (S, fs); for every call c below NC let
every place below 2^(n_c) of A.kvA S fs cell c hold the value of a row below 2^(k_c) of the call's
table; let LaidBA S fs cell hold (Johnson/HonestTrace/CountsAttention.lean); let ν read cell
⟨S.cf.NAs + 2, r, c⟩ at every place .cell r c with r below 2^lmb and c below NC 2^(kT + 5 - lmb).
Then, for all θ and al:
1. Z = a_pad (P_1^2 G_0), in the terms zRoot, aPad, pChain, gRoot of
   Johnson/HonestTrace/CountsProducts.lean, at the keys A.kvA S fs cell and the bits A.bitsA S fs
   cell;
2. every x = ν (.cell r c) at such r and c has x (x - 1) = 0;
3. Cb.Fo.Pin.countK fs lmb (Cb.Fo.Pin.pinColK lmb ν) = 0 (OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean).

Limits. The premises are assumed, not proved; withBA_laid and inTable_withBA (CountsAttention.lean)
give a reading that meets LaidBA and keeps the premise on the keys. Of the claims of the byte
format's page docs/format/11-1-machinery.md, equation 3 is LP2: the counts add up to the number of
keys that are not padding. It is an equation in K. Equations 1 and 2 are what the format's "tie step
0" and its test of the bits are about; they are not the claims LK0, LK(31 + v + dL) and LP1, which
read further challenges and the mask row; this file says nothing of these or of any other claim.

Not claimed: that A.kvA and A.bitsA are what a verifier reads; that a prover sends these values;
that a verifier accepts; completeness of the protocol.

-/
import Johnson.HonestTrace.CountsAttention
import Johnson.HonestTrace.CountsProducts

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open OnBytes.Ends (NameA)

section
variable {K : Type} [Field K] [DecidableEq K]

/-- If Attention.shapeHid lid cf returns (S, fs), for every call c below NC every place below
2^(n_c) of A.kvA S fs cell c holds the value of a row below 2^(k_c) of tabOf, LaidBA S fs cell
holds, and ν reads cell ⟨S.cf.NAs + 2, r, c⟩ at every place .cell r c with r below 2^lmb and c below
NC 2^(kT + 5 - lmb), then for all θ and al: Z = a_pad (P_1^2 G_0) at the keys A.kvA S fs cell and
the bits A.bitsA S fs cell; every x = ν (.cell r c) at such r and c has x (x - 1) = 0; and
countK fs lmb (pinColK lmb ν) = 0. -/
theorem factsA {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, Cb.Lkp.InTable (FoNums.nOf fs c) (FoNums.kOf fs c)
      (Ends.A.kvA S fs cell c) (tabOf K fs c))
    (hb : LaidBA S fs cell) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ S.cf.lmb, ∀ c < fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb),
      ν (.cell r c) = cell ⟨S.cf.NAs + 2, r, c⟩) (θ al : K) :
    zRoot fs (Ends.A.kvA S fs cell) θ al =
        aPad fs θ al *
          (pChain fs (fun u j => Ends.A.bitsA S fs cell (u * 32 + j)) θ al 1 ^ 2 *
            gRoot fs (fun u j => Ends.A.bitsA S fs cell (u * 32 + j)) θ al 0) ∧
      (∀ r < 2 ^ S.cf.lmb, ∀ c < fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb),
        ν (.cell r c) * (ν (.cell r c) - 1) = 0) ∧
      Cb.Fo.Pin.countK fs S.cf.lmb (Cb.Fo.Pin.pinColK S.cf.lmb ν) = 0 :=
  facts_plane (lawA hs cell hin hb θ al) _ _ _ (ok_A hs) (fitsA hs cell hin) (lmb_A hs).1
    (lmb_A hs).2 ν fun r hr c hc => (hν r hr c hc).trans (hb r hr c hc)

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.factsA
