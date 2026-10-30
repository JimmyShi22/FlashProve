-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/TablesLaw.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE: THE
FOUR SUMS' TWO ENDS, READ IN THE FIELD.
WHAT IT IS NOT. No prover, no round, no mask, no ledger, no verifier. Nothing on whether the
verifier accepts, on soundness, on completeness or on what a proof hides. Equations alone, most of
them between the reading rd of the values of Tables.lean, which are the program's words, and terms
in the field K of Johnson/Desc/Kinds/Law/; six are not equations in K (sq_vars, pr_vars, nm_vars,
lg_vars: between numbers; known_getD: between forms; weights_point: between lists), and some
equations in K name no value of Tables.lean (total_terms, total_product, end_reads, on any PairSum,
among them).
What lies hidden under a slot, each round's polynomial, and the form that a masked sumcheck leaves
are not spoken of.
NOTHING ON CANONICAL WRITING, in any statement: who goes back from K to the program's words owes
that both sides are written canonically (okE). Tables.lean and Pairs.lean have neither Mathlib nor a
file of the Law folder in the closure of their imports (by a program over the import lines): this
file has both.
WHAT IT IS. At all sizes.
  1  Each map of the four sums, read at an index, is a table of the Law folder at the index's bits:
     AtS (NormSquares.lean), AtR (NormProducts.lean), AtN, BtN (Normed.lean), AtP, UtP
     (Lemma2b.lean). No condition.
  2  The sixteen hidden scalars read as sumWAt and prodRAt of dataOf c at the point pV
     (OnBytes/Desc/First/NormBridge/BridgeCore.lean). CONDITIONAL: pV has lt coordinates.
  3  THE FIRST END. The start form of the sums of squares on the nine scalars, and the three
     claimed sums, read as sigS, sigR, sigN, sigP. CONDITIONAL: pV, or zt, has lt coordinates.
     The four sums' totals read as the same four. No condition.
  4  THE SECOND END. Each end value reads as its table's multilinear extension (mle) at the
     challenges. CONDITIONAL: as many challenges as variables. For the squares and the products also
     as Blocks.ext at ptK: CONDITIONAL on that and on one thing more: pV has lt coordinates.
  5  The four sums' numbers of variables.
WHAT IS CALLED. Of Pairs' law (PairLaw.lean): total_reads with partK_nil; ends_reads with laid_all.
Of Tables.lean: lgSum_eq. Of the Law folder: rd's laws, cv_const, cv_coe (Base.lean), rd_fieldE,
rd_prodE, rd_R (NormProof.lean), rd_sum_point, ext_congr_pt (NormPoint.lean), nat_tupK
(NormJoint.lean), mle_eq_sum, idxOf_bl, tot_pairs (Mle.lean), mle_eq_ext, sigS's text
(NormSquares.lean), sigR_eq, sumTerms_tsP (NormProducts.lean), sigN_eq (Normed.lean), sigP_eq
(Lemma2b.lean), start_at_truth (NormEnds.lean), le_two_pow_clog2 (Tables.lean of that folder),
sumZ_eq (Ints.lean). Of Blocks/Ext.lean: Blocks.ext_congr.

-/
import Mathlib
import Johnson.Desc.K6.Honest.Tables
import Johnson.Desc.K6.Honest.PairLaw
import Johnson.Desc.Kinds.Law.NormEnds
import Johnson.Desc.Kinds.Law.Lemma2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Honest

open OnBytes (E)
open OnBytes.Model (Reading)
open OnBytes.Desc.First (P6.rowProducts)
open OnBytes.Desc.First.P1 (mle tot sumTerms)
open Norm (lt d lPd T)
open Law (K rd idxOf dataOf ptK fieldK AtS AtR AtP UtP sigS sigR sigP)
open Law.Came (AtN BtN sigN)

variable [Sizes] [Policy] [Request] [Token]

/-! ## 5 The sums' numbers of variables -/

theorem sq_vars (c : Law.NCells) (pV : Point) (gam : E) :
    (sqSum c pV gam).z.length = lPd + pV.size := by
  show ((#[] : Point) ++ halves lPd ++ pV).toList.length = _
  unfold halves
  simp

theorem pr_vars (c : Law.NCells) (pV : Point) (om : E) : (prSum c pV om).z.length = pV.size := by
  show pV.toList.length = _
  simp

theorem nm_vars [FinalNorm.In] (c : Law.NCells) : (nmSum c).z.length = (FinalNorm.zt).size := by
  show (FinalNorm.zt).toList.length = _
  simp

theorem lg_vars [FinalNorm.In] [In] (c : Law.Cells) :
    (lgSum c).z.length = (FinalNorm.zt).size + lPd := by
  show (FinalNorm.zt ++ halves lPd).toList.length = _
  unfold halves
  simp

/-! ## 1 The maps, read in the field, are the tables of the Law folder, index by index -/

/-- The map of the sums of squares at every index. -/
theorem sqMap_at (c : Law.NCells) (gam : E) (i : Nat) :
    rd (sqMap c gam i) = (dataOf c).sqTab lPd (rd gam) i := by
  have hd : d ≤ 2 ^ lPd := Law.le_two_pow_clog2 d
  unfold sqMap D6.Bridge.Data.sqTab D6.Bridge.Data.batch
  have e1 : (dataOf c).lt = lt := rfl
  have e2 : (dataOf c).d = d := rfl
  have e3 : (dataOf c).NI = 1 := rfl
  have hT : (T : Nat) = 2 ^ lt := rfl
  rw [e1, e2, e3, hT]
  by_cases h : i / 2 ^ lt < d
  · have h2 : i / 2 ^ lt < 2 ^ lPd := Nat.lt_of_lt_of_le h hd
    rw [if_pos h, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h2, if_pos ⟨Nat.zero_lt_one, h⟩,
      Law.rd_sumTo]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Law.rd_mul, Law.rd_pow, Law.rd_ofInt]
    rfl
  · rw [if_neg h, if_neg, Law.rd_zero]
    rintro ⟨h1, h2⟩
    have h3 : i / 2 ^ lt / 2 ^ lPd = 0 := Nat.lt_one_iff.mp h1
    have h4 := Nat.div_add_mod (i / 2 ^ lt) (2 ^ lPd)
    rw [h3, Nat.mul_zero, Nat.zero_add] at h4
    rw [h4] at h2
    exact h h2

theorem sqMap_reads (c : Law.NCells) (gam : E) (b : List Bool) :
    rd (sqMap c gam (idxOf b)) = AtS c gam b := sqMap_at c gam (idxOf b)

/-- A field of the row at every position and number. -/
theorem fieldE_at (c : Law.NCells) (t q : Nat) : rd (Law.fieldE c t q) = fieldK c q t := by
  -- four classes that the called lemma carries and does not read
  letI : FinalNorm.In := (Law.cornerN 0 0).normIn
  letI : Norm.Heard := Law.normHeardAt c #[]
  letI : FinalNorm.Heard := Law.finalHeardAt c
  letI : FinalNorm.Reads := Law.normReadsAtCells c
  obtain ⟨ha, hb, hl, hh⟩ := Law.rd_fieldE c t
  match q with
  | 0 => exact ha
  | 1 => exact hb
  | 2 => exact hl
  | _ + 3 => exact hh

theorem fieldMap_reads (c : Law.NCells) (q : Nat) (b : List Bool) :
    rd (Law.fieldE c (idxOf b) q) = AtR c q b := fieldE_at c (idxOf b) q

theorem recMap_reads [FinalNorm.In] (c : Law.NCells) (b : List Bool) :
    rd (recMap c (idxOf b)) = AtN c b := by
  letI : Norm.Heard := Law.normHeardAt c #[]
  letI : FinalNorm.Heard := Law.finalHeardAt c
  letI : FinalNorm.Reads := Law.normReadsAtCells c
  exact Law.rd_R c (idxOf b)

theorem streamMap_reads [FinalNorm.In] (c : Law.NCells) (b : List Bool) :
    rd (streamMap c (idxOf b)) = BtN c b := by
  show rd (sumTo d fun x => FinalNorm.ew .remLow x * Law.ofInt (Law.str c (idxOf b) x)) =
    (Finset.range d).sum fun x => Law.Came.UN .remLow x * ((Law.str c (idxOf b) x : Int) : K)
  rw [Law.rd_sumTo]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Law.rd_mul, Law.rd_ofInt]
  rfl

theorem actMap_reads [FinalNorm.In] [In] (c : Law.Cells) (b : List Bool) :
    rd (actMap c (idxOf b)) = AtP c b := by
  show rd (if idxOf b % 2 ^ lPd < d then
      Law.ofInt (Law.act c (idxOf b / 2 ^ lPd) (idxOf b % 2 ^ lPd)) else 0) =
    if idxOf b % 2 ^ lPd < d then Law.fA c (idxOf b / 2 ^ lPd) (idxOf b % 2 ^ lPd) else 0
  by_cases h : idxOf b % 2 ^ lPd < d
  · rw [if_pos h, if_pos h]
    exact Law.rd_ofInt _
  · rw [if_neg h, if_neg h]
    exact Law.rd_zero

theorem uhMap_reads [FinalNorm.In] [In] (c : Law.Cells) (b : List Bool) :
    rd (uhMap c (idxOf b)) = UtP c b := by
  show rd (if idxOf b % 2 ^ lPd < d then
      Law.UH c (idxOf b % 2 ^ lPd) (idxOf b / 2 ^ lPd) else 0) =
    if idxOf b % 2 ^ lPd < d then Law.fU c (idxOf b / 2 ^ lPd) (idxOf b % 2 ^ lPd) else 0
  by_cases h : idxOf b % 2 ^ lPd < d
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    exact Law.rd_zero

/-! ## 2 The sixteen hidden scalars -/

/-- The sum of limb products number s at position t, cast, is the bridge's. -/
theorem sumW_at (c : Law.NCells) (s t : Nat) :
    ((Law.wsqZ c t s : Int) : K) = (dataOf c).sumW 0 s t := by
  show _ = Inst.Model.Ledger.Wsum d (fun l j => ((Law.limbZ c t l j : Int) : K)) s
  unfold Inst.Model.Ledger.Wsum Law.wsqZ
  rw [Law.sumZ_eq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Law.sumZ_eq]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Law.sumZ_eq]
  push_cast
  rfl

theorem wScalars_reads (c : Law.NCells) (pV : Point) (hz : pV.size = lt) (s : Nat) (hs : s < 9) :
    rd ((wScalars c pV).getD s 0) = (dataOf c).sumWAt (ptK pV) 0 s := by
  have e : (wScalars c pV).getD s 0 = sumTo T fun t => eq pV t * Law.ofInt (Law.wsqZ c t s) := by
    unfold wScalars
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]
    rfl
  rw [e, Law.rd_sum_point pV hz]
  show _ = Blocks.ext lt ((dataOf c).sumW 0 s) (ptK pV)
  refine Blocks.ext_congr (fun t _ => ?_) _
  rw [Law.rd_ofInt]
  exact sumW_at c s t

theorem pScalars_reads (c : Law.NCells) (pV : Point) (hz : pV.size = lt) (n : Nat) (hn : n < 7) :
    rd ((pScalars c pV).getD n 0) = (dataOf c).prodRAt (ptK pV) 0 n := by
  letI : FinalNorm.In := (Law.cornerN 0 0).normIn
  letI : Norm.Heard := Law.normHeardAt c #[]
  letI : FinalNorm.Heard := Law.finalHeardAt c
  letI : FinalNorm.Reads := Law.normReadsAtCells c
  have e : (pScalars c pV).getD n 0 = sumTo T fun t => eq pV t * Law.prodE c t n := by
    unfold pScalars
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
    rfl
  rw [e, Law.rd_sum_point pV hz]
  show _ = Blocks.ext lt (fun t => Inst.Model.Ledger.prods (Law.dK c t) n) (ptK pV)
  exact Blocks.ext_congr (fun t _ => Law.rd_prodE c t hn) _

/-- The same two at the point as a tuple, as the rounds' truth has it (NormTrue.lean: NormTruth). -/
theorem sumWAt_tuple (c : Law.NCells) (pV : Point) (s : Nat) :
    (dataOf c).sumWAt (Blocks.nat (Law.tupK pV)) 0 s = (dataOf c).sumWAt (ptK pV) 0 s :=
  Law.ext_congr_pt lt _ fun _ ht => Law.nat_tupK pV ht

@[inherit_doc sumWAt_tuple]
theorem prodRAt_tuple (c : Law.NCells) (pV : Point) (n : Nat) :
    (dataOf c).prodRAt (Blocks.nat (Law.tupK pV)) 0 n = (dataOf c).prodRAt (ptK pV) 0 n :=
  Law.ext_congr_pt lt _ fun _ ht => Law.nat_tupK pV ht

/-! ## 3 The first end -/

/-- Entry s of a list of values laid as hidden scalars: its variable is the constant form. -/
theorem known_getD (l : List E) (s : Nat) (h : s < l.length) :
    ((l.map known).toArray.getD s {}).var = ((l.getD s 0 : E) : Form) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem sqStart_reads (c : Law.NCells) (pV : Point) (gam : E) (hz : pV.size = lt) :
    rd (Norm.squaresStart ((wScalars c pV).map known).toArray gam #[]).const = sigS c pV gam := by
  rw [← Law.cv_const]
  refine Law.start_at_truth c pV hz gam _ Law.W0 fun s hs => ?_
  have hl : s < (wScalars c pV).length := by
    unfold wScalars
    simpa using hs
  rw [known_getD _ s hl, sumWAt_tuple, ← wScalars_reads c pV hz s hs]
  exact Law.cv_coe _

theorem prLead_batch (c : Law.NCells) (pV : Point) (om : E) (hz : pV.size = lt) :
    rd (prLead c pV om) =
      (Finset.range 7).sum fun n => rd om ^ n * (dataOf c).prodRAt (ptK pV) 0 n := by
  show rd (sumTo 7 fun n => om ^ n * (pScalars c pV).getD n 0) = _
  rw [Law.rd_sumTo]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Law.rd_mul, Law.rd_pow, pScalars_reads c pV hz n (Finset.mem_range.mp hn)]

theorem prLead_reads (c : Law.NCells) (pV : Point) (om : E) (hz : pV.size = lt) :
    rd (prLead c pV om) = sigR c pV om :=
  (prLead_batch c pV om hz).trans (Law.sigR_eq c pV om hz).symm

theorem nmLead_reads [FinalNorm.In] (c : Law.NCells) (hzt : (FinalNorm.zt).size = lt) :
    rd (nmLead c) = sigN c := (Law.Came.sigN_eq c hzt).symm

theorem lgLead_reads [FinalNorm.In] [In] (c : Law.Cells) (hzt : (FinalNorm.zt).size = lt) :
    rd (lgLead c) = sigP c := by
  have h2 : rd (2 : E) = 2 := by rw [Law.rd_ofNat]; norm_num
  show rd (OnBytes.invE (2 ^ lPd) * Law.trueSum c) = _
  rw [Law.rd_mul, Law.rd_inv, Law.rd_pow, h2, Law.sigP_eq c hzt]

/-- The weights under which a sumcheck at the point z sums its variables. -/
theorem weights_point (z : Point) :
    Part.MaskedSum.weightsOf Reading.gl (Law.Came.vsG z) =
      (z.toList.map rd).map fun x => (1 - x, x) := by
  unfold Part.MaskedSum.weightsOf Law.Came.vsG
  simp only [List.map_map]
  rfl

/-- **A sum's total**, where each map reads as a table: the table's sum of terms under the weights
of the points. -/
theorem total_terms (s : PairSum) (A : Nat → List Bool → K)
    (hA : ∀ j b, rd (s.map j (idxOf b)) = A j b) :
    rd s.total = tot ((s.z.map rd).map fun x => (1 - x, x)) fun b =>
      sumTerms (s.pairs.map fun p => (rd p.1, p.2.1, p.2.2)) fun j => A j b := by
  rw [total_reads, partK_nil, Law.tot_pairs, Law.mle_eq_sum, List.length_map]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  unfold PairSum.onK sumTerms
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  show rd p.1 * (rd (s.map p.2.1 i) * rd (s.map p.2.2 i)) = rd p.1 * (A p.2.1 _ * A p.2.2 _)
  rw [← hA, ← hA, Law.idxOf_bl, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]

/-- The same for one product of the first two maps. -/
theorem total_product (s : PairSum) (hp : s.pairs = [(1, 0, 1)]) (A B : List Bool → K)
    (h0 : ∀ b, rd (s.map 0 (idxOf b)) = A b) (h1 : ∀ b, rd (s.map 1 (idxOf b)) = B b) :
    rd s.total = tot ((s.z.map rd).map fun x => (1 - x, x)) fun b => A b * B b := by
  rw [total_terms s (fun j b => rd (s.map j (idxOf b))) fun _ _ => rfl, hp]
  refine congrArg _ (funext fun b => ?_)
  simp [sumTerms, Law.rd_one, h0, h1]

theorem sqTotal_reads (c : Law.NCells) (pV : Point) (gam : E) :
    rd (sqSum c pV gam).total = sigS c pV gam := by
  show _ = tot (Part.MaskedSum.weightsOf Reading.gl (Law.Came.vsG (Law.zS pV))) fun b =>
    AtS c gam b * AtS c gam b
  rw [weights_point]
  exact total_product _ rfl _ _ (sqMap_reads c gam) (sqMap_reads c gam)

theorem prTotal_reads (c : Law.NCells) (pV : Point) (om : E) :
    rd (prSum c pV om).total = sigR c pV om := by
  show _ = tot (Part.MaskedSum.weightsOf Reading.gl (Law.Came.vsG pV)) fun b =>
    sumTerms (Law.tsP (rd om)) fun q => AtR c q b
  rw [weights_point, total_terms (prSum c pV om) (fun j b => rd ((prSum c pV om).map j (idxOf b)))
    fun _ _ => rfl]
  have hts : ((prSum c pV om).pairs.map fun p => (rd p.1, p.2.1, p.2.2)) = Law.tsP (rd om) := by
    show ((P6.rowProducts.zipIdx.map fun x => (om ^ x.2, x.1.1, x.1.2)).map
      fun p => (rd p.1, p.2.1, p.2.2)) = _
    unfold Law.tsP
    rw [List.map_map]
    refine List.map_congr_left fun x _ => ?_
    show (rd (om ^ x.2), x.1.1, x.1.2) = _
    rw [Law.rd_pow]
  rw [hts]
  refine congrArg _ (funext fun b => ?_)
  rw [Law.sumTerms_tsP, Law.sumTerms_tsP]
  have h : ∀ q, q < 4 → rd ((prSum c pV om).map q (idxOf b)) = AtR c q b := by
    intro q hq
    have e : (prSum c pV om).map q = fun t => Law.fieldE c t q := by
      show ((List.range 4).map fun j t => Law.fieldE c t j).getD q (fun _ => 0) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
      rfl
    rw [e]
    exact fieldMap_reads c q b
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem nmTotal_reads [FinalNorm.In] (c : Law.NCells) : rd (nmSum c).total = sigN c := by
  show _ = tot (Part.MaskedSum.weightsOf Reading.gl (Law.Came.vsG FinalNorm.zt)) fun b =>
    AtN c b * BtN c b
  rw [weights_point]
  exact total_product _ rfl _ _ (recMap_reads c) (streamMap_reads c)

theorem lgTotal_reads [FinalNorm.In] [In] (c : Law.Cells) : rd (lgSum c).total = sigP c := by
  show _ = tot (Part.MaskedSum.weightsOf Reading.gl (Law.Came.vsG Law.zP)) fun b =>
    AtP c b * UtP c b
  rw [weights_point, lgSum_eq]
  exact total_product _ rfl _ _ (actMap_reads c) (uhMap_reads c)

/-! ## 4 The second end -/

/-- **An end value**, where its map reads as a table: the table's extension at the challenges. -/
theorem end_reads (s : PairSum) (rs : List E) (h : rs.length = s.z.length) (j : Nat)
    (A : List Bool → K) (hA : ∀ b, rd (s.map j (idxOf b)) = A b) :
    rd ((s.ends rs).getD j 0) = mle rs.length A (rs.map rd) := by
  have e := Law.mle_eq_sum (rs.map rd) A
  rw [List.length_map] at e
  rw [ends_reads s rs j h, laid_all, e, List.length_map]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← hA, Law.idxOf_bl, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]

theorem sqEnds_reads (c : Law.NCells) (pV : Point) (gam : E) (rs : List E)
    (h : rs.length = (sqSum c pV gam).z.length) (j : Nat) (hj : j < 2) :
    rd (((sqSum c pV gam).ends rs).getD j 0) = mle rs.length (AtS c gam) (rs.map rd) := by
  refine end_reads _ rs h j _ fun b => ?_
  match j, hj with
  | 0, _ => exact sqMap_reads c gam b
  | 1, _ => exact sqMap_reads c gam b

theorem sqEnds_ext (c : Law.NCells) (pV : Point) (gam : E) (rs : List E) (hz : pV.size = lt)
    (h : rs.length = lPd + lt) (j : Nat) (hj : j < 2) :
    rd (((sqSum c pV gam).ends rs).getD j 0) =
      Blocks.ext (lPd + lt) ((dataOf c).sqTab lPd (rd gam)) (ptK rs.toArray) := by
  rw [sqEnds_reads c pV gam rs (by rw [sq_vars, hz, h]) j hj]
  have e := Law.mle_eq_ext (rs.map rd) ((dataOf c).sqTab lPd (rd gam))
  rw [List.length_map, h] at e
  rw [h]
  exact e

theorem prEnds_reads (c : Law.NCells) (pV : Point) (om : E) (rs : List E)
    (h : rs.length = (prSum c pV om).z.length) (q : Nat) (hq : q < 4) :
    rd (((prSum c pV om).ends rs).getD q 0) = mle rs.length (AtR c q) (rs.map rd) := by
  refine end_reads _ rs h q _ fun b => ?_
  have e : (prSum c pV om).map q = fun t => Law.fieldE c t q := by
    show ((List.range 4).map fun j t => Law.fieldE c t j).getD q (fun _ => 0) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
    rfl
  rw [e]
  exact fieldMap_reads c q b

theorem prEnds_ext (c : Law.NCells) (pV : Point) (om : E) (rs : List E) (hz : pV.size = lt)
    (h : rs.length = lt) (q : Nat) (hq : q < 4) :
    rd (((prSum c pV om).ends rs).getD q 0) = Blocks.ext lt (fieldK c q) (ptK rs.toArray) := by
  rw [prEnds_reads c pV om rs (by rw [pr_vars, hz, h]) q hq]
  have e := Law.mle_eq_ext (rs.map rd) (fieldK c q)
  rw [List.length_map, h] at e
  rw [h]
  exact e

theorem nmEnds_reads [FinalNorm.In] (c : Law.NCells) (rs : List E)
    (h : rs.length = (nmSum c).z.length) :
    rd (((nmSum c).ends rs).getD 0 0) = mle rs.length (AtN c) (rs.map rd) ∧
      rd (((nmSum c).ends rs).getD 1 0) = mle rs.length (BtN c) (rs.map rd) :=
  ⟨end_reads _ rs h 0 _ (recMap_reads c), end_reads _ rs h 1 _ (streamMap_reads c)⟩

theorem lgEnds_reads [FinalNorm.In] [In] (c : Law.Cells) (rs : List E)
    (h : rs.length = (lgSum c).z.length) :
    rd (((lgSum c).ends rs).getD 0 0) = mle rs.length (AtP c) (rs.map rd) ∧
      rd (((lgSum c).ends rs).getD 1 0) = mle rs.length (UtP c) (rs.map rd) := by
  rw [lgSum_eq] at h ⊢
  exact ⟨end_reads _ rs h 0 _ (actMap_reads c), end_reads _ rs h 1 _ (uhMap_reads c)⟩

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sq_vars
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.pr_vars
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.nm_vars
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lg_vars
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqMap_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqMap_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.fieldE_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.fieldMap_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.recMap_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.streamMap_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.actMap_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.uhMap_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sumW_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.wScalars_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.pScalars_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sumWAt_tuple
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prodRAt_tuple
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.known_getD
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqStart_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prLead_batch
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prLead_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.nmLead_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lgLead_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.weights_point
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.total_terms
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.total_product
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqTotal_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prTotal_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.nmTotal_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lgTotal_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.end_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqEnds_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqEnds_ext
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prEnds_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prEnds_ext
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.nmEnds_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lgEnds_reads
