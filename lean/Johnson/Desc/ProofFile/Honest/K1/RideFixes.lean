-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/RideFixes.lean: THE SHARED "SENDING" (the kind K1): A RIDING TABLE
FIXES ITS VALUES, AT EVERY ⟨h + n, h⟩, n = 0 AMONG THEM: Ride.lay (Honest/K1/Coins.lean). PUBLIC IN
FORM: c is any list of values by number. One theorem; no definition. NO NEW ARGUMENT: CALLS.

  - lay_fixes: AT EVERY h AND n: if Ride.lay c and Ride.lay c' agree at the rows below 2 ^ h and
    the places below h + 2 n + 1, then c i = c' i for every i < 2 (h + n) + 1 (= Ride.count).

The road. THE SEAL: ld_pack_inj (Cb/Ld/LdSumPackProofs.lean: "The table determines the
coefficients"); toE_freshRow_at, coefU_at, coefU_cst (Johnson/Prover/Link/FoldPairs.lean): at a
vertex's row and a column's place a row of the format's table is the sumcheck library's packing pkC;
hidePlace_lt (OnBytes/Slice/SimFold.lean); rowNo_lt (OnBytes/Slice/Cells.lean). ANOTHER HOUSE's, A
ROW OF laws.12: ixOf, toE_w, toE_w0 (Johnson/SendSim/At/RideLay.lean): which number hideOfCoins
gives to a coefficient.

KIN, TOLD. That Ride.lay is additive, and what stands at each place, at every R: lay_add, lay_eq
(RideLay.lean): NOT RESTATED HERE. That Ride.lay is the library's packedN inside the table:
lay_is_packed (Honest/K12/AtProof/FreshAtL.lean, another house's).

Limits. IT SAYS AN IMPLICATION BETWEEN EQUATIONS ON Ride.lay, AND NOTHING ELSE. On a definition: not
on rowsR: that wants the room (at W's sending: Law/RoomAtW.lean). Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.SendSim.At.RideLay
import Johnson.Prover.Link.FoldPairs
import Cb.Ld.LdSumPackProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc Cb
open OnBytes.SendSim.At (ixOf toE_w toE_w0)
open Johnson.Prover.Link (toE_freshRow_at coefU coefU_at coefU_cst)

/-- **THE TABLE FIXES THE VALUES**, at every h and n. -/
theorem lay_fixes (h n : ℕ) (c c' : ℕ → GE)
    (H : ∀ b, b < 2 ^ h → ∀ j, j < h + 2 * n + 1 →
      (⟨h + n, h⟩ : Ride).lay c b j = (⟨h + n, h⟩ : Ride).lay c' b j) :
    ∀ i, i < 2 * (h + n) + 1 → c i = c' i := by
  have e : pkC h n 1 (coefU (h + n) (hideOfCoins (h + n) c)) =
      pkC h n 1 (coefU (h + n) (hideOfCoins (h + n) c')) := by
    funext a
    obtain ⟨β, col⟩ := a
    rw [← toE_freshRow_at, ← toE_freshRow_at]
    exact H _ (rowNo_lt β) _ (hidePlace_lt h n col)
  have e2 := ld_pack_inj GE h n 1 e
  have A : ∀ (l : Fin (h + n)) (p : Fin 2),
      c (ixOf (h + n) (l.val + 1) (p.val + 1)) = c' (ixOf (h + n) (l.val + 1) (p.val + 1)) := by
    intro l p
    have g := congrFun e2 (hIx GE 2 (h + n) l p)
    rw [coefU_at, coefU_at, toE_w, toE_w] at g
    exact g
  have A0 : c (2 * (h + n - 1)) = c' (2 * (h + n - 1)) := by
    have g := congrFun e2 (hCst GE 2 (h + n))
    rw [coefU_cst, coefU_cst, toE_w0, toE_w0] at g
    exact g
  intro i hi
  by_cases h1 : i = 2 * (h + n - 1)
  · rw [h1]
    exact A0
  by_cases h2 : i < 2 * (h + n - 1)
  · have g := A ⟨i / 2, by omega⟩ ⟨i % 2, by omega⟩
    have w : ixOf (h + n) (i / 2 + 1) (i % 2 + 1) = i := by
      unfold ixOf
      rw [if_pos (by omega)]
      omega
    rw [w] at g
    exact g
  · have g := A ⟨h + n - 1, by omega⟩ ⟨i - 2 * (h + n - 1) - 1, by omega⟩
    have w : ixOf (h + n) (h + n - 1 + 1) (i - 2 * (h + n - 1) - 1 + 1) = i := by
      unfold ixOf
      rw [if_neg (by omega)]
      omega
    rw [w] at g
    exact g

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lay_fixes
