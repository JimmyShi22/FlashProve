-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/NormsTabs.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side, the norms' stretch
(Johnson/Desc/K4/Honest/Norms.lean): the makers' tables and loops, entry by entry, read into the
field. Statements and proofs.

  `NormsPlan`      public numbers and facts on the plan.
  `sqTab_read`     an entry of the squares' table is the library's sqV.
  `product_sum`, `rowProducts_sum`   a row product is a sum over the tokens of a product of two
                   entries of the rows' tables.
  `prodsOf_pairs`  the library's seven products, by the verifier's list of pairs.

Not shown here. That the hypotheses hold anywhere: no example is known. NormsPlan's seven fields
follow from the plan's public facts K4Plan (normsPlan_of_plan, NormsPlanOf.lean, whose head says
where K4Plan holds). Nothing says that the cells are those of an inference.
No property is claimed.
-/
import Johnson.Road.K4.C.Feats
import Johnson.Road.K4.C.NormsKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten matIx)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First (P6.rowProducts)

/-- **Public numbers and facts on the plan.** This defines a hypothesis; the definition claims
nothing. -/
structure NormsPlan (Q : K4Pub) (D : Dim) : Prop where
  T : Q.P.y.T = 2 ^ D.lT
  NI : Q.P.y.NI = D.nNu
  Pd : Q.P.y.Pd = 2 ^ Q.P.y.lPd
  lsPd : Q.P.y.ls ≤ Q.P.y.lPd
  muV : Q.P.rd.muV = Q.P.rd.lNI + Q.P.y.lPd - Q.P.y.ls + Q.P.y.ls + D.lT
  mats : MatsLaid Q
  streams : StreamsIn Q.P.y

variable {W : World Cb.Gl.E} {v : Env} {t : Cell → Cb.Gl.E} [scl : Scl] {D : Dim}
  {low u : ℕ → Cb.Gl.E} {Q : K4Pub} {w : K4In} {Mm : Mats Cb.Gl.E}

/-- **An entry of the squares' table**, read into the field, is the library's. -/
theorem sqTab_read (F : Fits Reading.gl W v D (cellsAt v.y Mm) t low u) (hy : Q.P.y = v.y)
    (C : CellsAre Q w Mm) (N : NormsPlan Q D) (gp : Array E) {x : ℕ}
    (hx : x < 2 ^ Q.P.rd.muV) :
    Reading.gl.val ((squaresTab Q w gp).getD x zeroE) =
      Road.K4.sqV v.y.NI (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) v.y.lPd v.y.xb.nl D.lT
        (fun l => Reading.gl.val (gp.getD l zeroE)) (fun ν l j p => bS D t ν l j p) x := by
  have hd : Q.P.y.h.d = D.d := by rw [hy]; exact F.d
  have hxl : Q.P.y.h.xl = 5 := by rw [hy]; exact F.xl
  have hdd : Q.P.y.h.d / Q.P.y.S2 * 2 ^ Q.P.y.ls = D.d := by
    obtain ⟨n, hn⟩ := F.bd
    rw [hd, hy, F.S2, hn, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have hnl : Q.P.y.xb.nl = 5 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, T0, _⟩ := F.stream
    rw [hy]
    exact T0.1
  rw [← hy, hdd, N.NI, hnl]
  unfold Road.K4.sqV
  dsimp only [squaresTab]
  rw [range_map_getD' _ _ _ hx, N.T, N.Pd, hd, N.NI, hxl]
  by_cases h : x / 2 ^ D.lT / 2 ^ Q.P.y.lPd < D.nNu ∧ x / 2 ^ D.lT % 2 ^ Q.P.y.lPd < D.d
  · have hb : (decide (x / 2 ^ D.lT % 2 ^ Q.P.y.lPd < D.d) &&
        decide (x / 2 ^ D.lT / 2 ^ Q.P.y.lPd < D.nNu)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨h.2, h.1⟩
    rw [if_pos h, if_pos hb, gl_foldl_maddS, Reading.gl.zero, zero_add, list_range_sum]
    refine sum_congr rfl fun l hl => ?_
    rw [limb_read F hy C N.mats N.streams N.T N.NI h.1 (mem_range.mp hl) h.2
      (Nat.mod_lt _ (Nat.two_pow_pos _)), mul_comm]
  · have hb : ¬ (decide (x / 2 ^ D.lT % 2 ^ Q.P.y.lPd < D.d) &&
        decide (x / 2 ^ D.lT / 2 ^ Q.P.y.lPd < D.nNu)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact fun k => h ⟨k.2, k.1⟩
    rw [if_neg h, if_neg hb]
    exact Reading.gl.zero

omit scl in
/-- One row product's loop over the tokens. -/
theorem product_sum (e ta tb : Array E) (N : ℕ) :
    Reading.gl.val ((List.range N).foldl
      (fun s t => maddE s (e.getD t zeroE) (mulE (ta.getD t zeroE) (tb.getD t zeroE))) zeroE) =
      ∑ t ∈ range N, Reading.gl.val (e.getD t zeroE) *
        (Reading.gl.val (ta.getD t zeroE) * Reading.gl.val (tb.getD t zeroE)) := by
  rw [gl_foldl_maddE, Reading.gl.zero, zero_add, list_range_sum]
  exact sum_congr rfl fun t _ => by rw [Reading.gl.mul]

omit scl in
/-- **A row product is a sum over the tokens.** ms: the rows' tables. -/
theorem rowProducts_sum (Q : K4Pub) (w : K4In) (p : Pts) {ms : Array Tab}
    (hms : rowMaps Q w p = some ms) {i r : ℕ} (hi : i < Q.P.y.NI) (hr : r < 7) :
    Reading.gl.val ((rowProducts Q w p).getD (7 * i + r) zeroE) =
      ∑ t ∈ range Q.P.y.T, Reading.gl.val ((eqTab p.PV).getD t zeroE) *
        (Reading.gl.val
            ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).1) #[]).getD t zeroE) *
          Reading.gl.val
            ((ms.getD (4 * i + (P6.rowProducts.getD r (0, 0)).2) #[]).getD t zeroE)) := by
  unfold rowProducts
  rw [hms]
  dsimp only
  rw [flat_getD _ 7 (fun _ => by rw [List.length_map]; rfl) zeroE (List.range Q.P.y.NI) i r
      (by rw [List.length_range]; exact hi) hr, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  have hg : P6.rowProducts[r]? = some (P6.rowProducts.getD r (0, 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by show r < 7; exact hr)]
    rfl
  rw [hg]
  exact product_sum _ _ _ _

omit scl in
/-- The library's seven products of four numbers, by the verifier's list of pairs. f: the four
numbers by their places. -/
theorem prodsOf_pairs {K : Type} [CommRing K] (f : ℕ → K) {r : ℕ} (hr : r < 7) :
    Inst.Model.Ledger.prodsOf (f 0) (f 1) (f 2) (f 3) r =
      f (P6.rowProducts.getD r (0, 0)).1 *
        f (P6.rowProducts.getD r (0, 0)).2 := by
  interval_cases r
  · exact pow_two _
  · rfl
  · exact pow_two _
  · rfl
  · rfl
  · rfl
  · rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sqTab_read
#print axioms OnBytes.Road.K4.C.product_sum
#print axioms OnBytes.Road.K4.C.rowProducts_sum
#print axioms OnBytes.Road.K4.C.prodsOf_pairs
