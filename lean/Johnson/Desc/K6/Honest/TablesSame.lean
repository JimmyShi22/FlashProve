-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/TablesSame.lean: THE OUTPUT HEAD'S OWN ROUNDS, THE HONEST PROVER'S SIDE: THE
VALUES OF Tables.lean READ NO CELL BEYOND THE RANGES: at two structures of cells that agree on what
the head's relation names (Johnson/Desc/Kinds/Law/CellsAlike.lean: SameCells) they read alike, and
"what lies hidden is Tables.lean's values" (TruthOfTables.lean: HidesTables) holds at the one if it
holds at the other.
WHAT IT IS NOT. Equations between READINGS IN THE FIELD K, or between elements where that is had for
nothing (two, limbZ_same and wsqZ_same, between integers): NOT between the four sums as terms: the
maps of three of them are functions of all indices that read the position unguarded, and may differ
beyond the table. Nothing on what is SENT: no prover, no round, no coin. CONDITIONAL: on SameCells
(that two readings of cells agree inside the ranges is the caller's to show); every statement on end
values on as many challenges as variables; from the logits' lemmas on, on the request's own test and
on y < V; the top on all of these, as five sizes. Of SameCells' five clauses four are spent; no
value here reads the wide matrix.
Nothing on whether the verifier accepts, on soundness, on completeness or on what a proof hides.
Mathlib and Johnson/Desc/Kinds/Law/ are in the closure of its imports.
WHY. A law on the verifier's side reads the cells off a witness, cut to 0 outside four ranges; the
prover's cells are not cut. The two are not equal as functions; they agree inside the ranges.
  end_sum, ends_same   at as many challenges as variables an end value of a sum, read, is a sum
                       over the table's indices alone; so two sums whose maps read alike below 2 ^ n
                       have end values that read alike.
  limbZ_same, wsqZ_same, fieldE_same, prodE_same, rd_rec, recMap_same, streamMap_same, UH_same
                       the cells' functions.
  wScalars_same, pScalars_at, pScalars_same, sqSum_same, prLead_same, nmLead_same, lgLead_same
                       scalars, claimed sums, and the one sum that is the same term.
  prEnds_same, nmEnds_same, lgEnds_same   the three other sums' end values.
  HidesTables.same     THE TOP.
CALLED: TablesLaw.lean (end_reads, fieldE_at, pr_vars, nm_vars, lg_vars), Tables.lean (lgSum_eq); of
the library: mle_idx, digZ_same, recZ_same, str_same, act_same, win_lt, b256M_same, rd_R,
sumTo_congr, sumZ_eq, rd_sumTo, rd_mul.

-/
import Mathlib
import Johnson.Desc.K6.Honest.TruthOfTables
import Johnson.Desc.Kinds.Law.CellsAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Honest

open OnBytes (E)
open OnBytes.Model (Fork)
open Norm (lt d lPd T)
open Law (K rd wt idxOf SameCells ofInt UH trueSum)
open Law.Came (sumTo_congr)

variable [Sizes] [Policy] [Request] [Token]

/-! ## 1 An end value reads the table's indices alone -/

/-- An end value of a sum, read, at as many challenges as variables: a sum over the indices below
2 ^ n. -/
theorem end_sum (s : PairSum) (rs : List E) (h : rs.length = s.z.length) (j : Nat) :
    rd ((s.ends rs).getD j 0) =
      (Finset.range (2 ^ rs.length)).sum fun i => wt (rs.map rd) i * rd (s.map j i) := by
  rw [end_reads s rs h j (fun b => rd (s.map j (idxOf b))) fun _ => rfl]
  have e := Law.mle_idx (rs.map rd) fun i => rd (s.map j i)
  rw [List.length_map] at e
  exact e

/-- Two sums whose maps number j read alike below 2 ^ n have end values number j that read alike. -/
theorem ends_same (s s' : PairSum) (rs : List E) (h : rs.length = s.z.length)
    (h' : rs.length = s'.z.length) (j : Nat)
    (hm : ∀ i, i < 2 ^ rs.length → rd (s.map j i) = rd (s'.map j i)) :
    rd ((s.ends rs).getD j 0) = rd ((s'.ends rs).getD j 0) := by
  rw [end_sum s rs h j, end_sum s' rs h' j]
  exact Finset.sum_congr rfl fun i hi => by rw [hm i (Finset.mem_range.1 hi)]

/-! ## 2 The cells' functions -/

variable {c c' : Law.NCells}

theorem limbZ_same (h : SameCells c c') {t l k : Nat} (ht : t < T) (hl : l < 5) (hk : k < d) :
    Law.limbZ c t l k = Law.limbZ c' t l k := by
  unfold Law.limbZ
  have hb : l * d + k < 5 * d := by
    have : l * d ≤ 4 * d := Nat.mul_le_mul_right _ (by omega)
    omega
  exact h.stream _ t hb ht

theorem wsqZ_same (h : SameCells c c') {t : Nat} (ht : t < T) (s : Nat) :
    Law.wsqZ c t s = Law.wsqZ c' t s := by
  unfold Law.wsqZ
  rw [Law.sumZ_eq, Law.sumZ_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Law.sumZ_eq, Law.sumZ_eq]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Law.sumZ_eq, Law.sumZ_eq]
  refine Finset.sum_congr rfl fun l' hl' => ?_
  rw [limbZ_same h ht (Finset.mem_range.1 hl) (Finset.mem_range.1 hk),
    limbZ_same h ht (Finset.mem_range.1 hl') (Finset.mem_range.1 hk)]

/-- A field of the row at a position of the table, read. -/
theorem fieldE_same (h : SameCells c c') {t : Nat} (ht : t < T) (q : Nat) :
    rd (Law.fieldE c t q) = rd (Law.fieldE c' t q) := by
  rw [fieldE_at, fieldE_at]
  have hD : ∀ n < 120, Law.dK c t n = Law.dK c' t n := fun n hn => by
    unfold Law.dK
    rw [Law.Came.digZ_same h ht hn]
  rcases q with _ | _ | _ | q
  · show Inst.Model.Ledger.sa (Law.dK c t) = Inst.Model.Ledger.sa (Law.dK c' t)
    unfold Inst.Model.Ledger.sa
    rw [hD 58 (by norm_num), hD 59 (by norm_num), hD 60 (by norm_num), hD 61 (by norm_num)]
  · show Inst.Model.Ledger.sb (Law.dK c t) = Inst.Model.Ledger.sb (Law.dK c' t)
    unfold Inst.Model.Ledger.sb
    rw [hD 62 (by norm_num), hD 63 (by norm_num)]
  · show Inst.Model.Ledger.Rlo (Law.dK c t) = Inst.Model.Ledger.Rlo (Law.dK c' t)
    unfold Inst.Model.Ledger.Rlo
    rw [_root_.Policy.b256M_same hD (by norm_num)]
  · show Inst.Model.Ledger.Rhi (Law.dK c t) = Inst.Model.Ledger.Rhi (Law.dK c' t)
    unfold Inst.Model.Ledger.Rhi
    rw [_root_.Policy.b256M_same hD (by norm_num)]

theorem prodE_same (h : SameCells c c') {t : Nat} (ht : t < T) (n : Nat) :
    rd (Law.prodE c t n) = rd (Law.prodE c' t n) := by
  unfold Law.prodE
  rw [Law.rd_mul, Law.rd_mul, fieldE_same h ht, fieldE_same h ht]

/-! ## 3 Scalars, claimed sums, and the sum on the squares -/

theorem wScalars_same (h : SameCells c c') (pV : Point) : wScalars c pV = wScalars c' pV := by
  unfold wScalars
  exact List.map_congr_left fun s _ => sumTo_congr T fun t ht => by rw [wsqZ_same h ht s]

theorem pScalars_at (c : Law.NCells) (pV : Point) {n : Nat} (hn : n < 7) :
    (pScalars c pV).getD n 0 = ∑ t < T, eq pV t * Law.prodE c t n := by
  unfold pScalars
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
  rfl

theorem pScalars_same (h : SameCells c c') (pV : Point) {n : Nat} (hn : n < 7) :
    rd ((pScalars c pV).getD n 0) = rd ((pScalars c' pV).getD n 0) := by
  rw [pScalars_at c pV hn, pScalars_at c' pV hn, Law.rd_sumTo, Law.rd_sumTo]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Law.rd_mul, Law.rd_mul, prodE_same h (Finset.mem_range.1 ht)]

theorem sqSum_same (h : SameCells c c') (pV : Point) (gam : E) :
    sqSum c pV gam = sqSum c' pV gam := by
  have e : sqMap c gam = sqMap c' gam := by
    funext i
    unfold sqMap
    by_cases hi : i / T < d
    · rw [if_pos hi, if_pos hi]
      exact sumTo_congr 5 fun l hl => by
        rw [limbZ_same h (Nat.mod_lt _ (Nat.two_pow_pos lt)) hl hi]
    · rw [if_neg hi, if_neg hi]
  unfold sqSum
  rw [e]

theorem prLead_same (h : SameCells c c') (pV : Point) (om : E) :
    rd (prLead c pV om) = rd (prLead c' pV om) := by
  show rd (∑ n < 7, om ^ n * (pScalars c pV).getD n 0) =
    rd (∑ n < 7, om ^ n * (pScalars c' pV).getD n 0)
  rw [Law.rd_sumTo, Law.rd_sumTo]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Law.rd_mul, Law.rd_mul, pScalars_same h pV (Finset.mem_range.1 hn)]

/-- The products' end values, at as many challenges as positions have bits. -/
theorem prEnds_same (h : SameCells c c') (pV : Point) (om : E) (rs : List E)
    (hz : pV.size = lt) (hr : rs.length = lt) {q : Nat} (hq : q < 4) :
    rd (((prSum c pV om).ends rs).getD q 0) = rd (((prSum c' pV om).ends rs).getD q 0) := by
  refine ends_same _ _ rs (by rw [pr_vars, hr, hz]) (by rw [pr_vars, hr, hz]) q fun i hi => ?_
  rw [hr] at hi
  have e : ∀ x : Law.NCells, (prSum x pV om).map q i = Law.fieldE x i q := fun x => by
    match q, hq with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  rw [e, e]
  exact fieldE_same h hi q

section Lookup
variable [FinalNorm.In]

/-- The library's rd_R, without three of the classes that its section lays on it and its statement
does not name: Norm.Heard, FinalNorm.Heard, FinalNorm.Reads. FinalNorm.In and this file's four stay
on it. -/
theorem rd_rec (c : Law.NCells) (t : Nat) :
    rd (Law.rowZ c t).R.const = ((Law.recZ c t : Int) : K) := by
  letI : Norm.Heard := Law.normHeardAt c #[]
  letI : FinalNorm.Heard := Law.finalHeardAt c
  letI : FinalNorm.Reads := Law.normReadsAtCells c
  exact Law.rd_R c t

theorem recMap_same (h : SameCells c c') {t : Nat} (ht : t < T) :
    rd (recMap c t) = rd (recMap c' t) := by
  unfold recMap
  rw [rd_rec, rd_rec, Law.Came.recZ_same h ht]

theorem streamMap_same (h : SameCells c c') {t : Nat} (ht : t < T) :
    streamMap c t = streamMap c' t := by
  unfold streamMap
  exact sumTo_congr d fun x hx => by rw [Law.Came.str_same h ht hx]

theorem nmLead_same (h : SameCells c c') : rd (nmLead c) = rd (nmLead c') := by
  unfold nmLead Law.trueNormed
  rw [Law.rd_sumTo, Law.rd_sumTo]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Law.rd_sumTo, Law.rd_sumTo]
  refine Finset.sum_congr rfl fun x hx => ?_
  have ht' := Finset.mem_range.1 ht
  rw [Law.rd_mul, Law.rd_mul _ (_ * (Law.rowZ c' t).R.const), Law.rd_mul (ofInt _),
    Law.rd_mul (ofInt (Law.str c' t x)), rd_rec, rd_rec, Law.Came.recZ_same h ht',
    Law.Came.str_same h ht' (Finset.mem_range.1 hx)]

/-- The end values of "the reciprocal times the stream". -/
theorem nmEnds_same (h : SameCells c c') (rs : List E) (hzt : (FinalNorm.zt).size = lt)
    (hr : rs.length = lt) {j : Nat} (hj : j < 2) :
    rd (((nmSum c).ends rs).getD j 0) = rd (((nmSum c').ends rs).getD j 0) := by
  refine ends_same _ _ rs (by rw [nm_vars, hr, hzt]) (by rw [nm_vars, hr, hzt]) j fun i hi => ?_
  rw [hr] at hi
  match j, hj with
  | 0, _ => exact recMap_same h hi
  | 1, _ =>
    show rd (streamMap c i) = rd (streamMap c' i)
    rw [streamMap_same h hi]

variable [In]

theorem UH_same (h : SameCells c c') (hreq : Request.ok = true) (hy : y < V) {k : Nat}
    (hk : k < d) (t : Nat) : UH c.toCells k t = UH c'.toCells k t := by
  unfold UH
  by_cases hc : checked t
  · rw [if_pos hc, if_pos hc]
    show wx .marginTop * ofInt (c.Wh k (win t)) -
        (∑ v < V, ew .marginTop v * ofInt (c.Wh k v)) =
      wx .marginTop * ofInt (c'.Wh k (win t)) -
        ∑ v < V, ew .marginTop v * ofInt (c'.Wh k v)
    rw [h.Wh k _ hk (Law.win_lt hreq hy t),
      sumTo_congr V fun v hv => by rw [h.Wh k v hk hv]]
  · rw [if_neg hc, if_neg hc]

theorem lgLead_same (h : SameCells c c') (hreq : Request.ok = true) (hy : y < V) :
    lgLead c.toCells = lgLead c'.toCells := by
  unfold lgLead trueSum
  rw [sumTo_congr T fun t ht => sumTo_congr d fun k hk => by
    rw [Law.Came.act_same h ht hk, UH_same h hreq hy hk t]]

/-- The logits' end values. -/
theorem lgEnds_same (h : SameCells c c') (hreq : Request.ok = true) (hy : y < V) (rs : List E)
    (hzt : (FinalNorm.zt).size = lt) (hr : rs.length = lt + lPd) {j : Nat} (hj : j < 2) :
    rd (((lgSum c.toCells).ends rs).getD j 0) = rd (((lgSum c'.toCells).ends rs).getD j 0) := by
  refine ends_same _ _ rs (by rw [lg_vars, hr, hzt]) (by rw [lg_vars, hr, hzt]) j fun i hi => ?_
  rw [hr, pow_add] at hi
  have ht : i / 2 ^ lPd < T := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  rw [lgSum_eq, lgSum_eq]
  match j, hj with
  | 0, _ =>
    show rd (actMap c.toCells i) = rd (actMap c'.toCells i)
    unfold actMap
    by_cases hk : i % 2 ^ lPd < d
    · rw [if_pos hk, if_pos hk, Law.Came.act_same h ht hk]
    · rw [if_neg hk, if_neg hk]
  | 1, _ =>
    show rd (uhMap c.toCells i) = rd (uhMap c'.toCells i)
    unfold uhMap
    by_cases hk : i % 2 ^ lPd < d
    · rw [if_pos hk, if_pos hk, UH_same h hreq hy hk]
    · rw [if_neg hk, if_neg hk]

/-! ## 4 The top -/

/-- **WHAT LIES HIDDEN IS Tables.lean'S VALUES AT THE ONE CELLS IF AT THE OTHER**, where the two
agree on what the head's relation names. The test on the request and "the next token is below V" are
spent at the logits alone: there the weights' column of a checked position's token is read. Five
sizes: an end value reads the table's indices alone only at as many challenges as variables; the
squares' sum is the same term, so that its challenges' number is not asked. Nine of the fourteen
clauses name the cells and are carried over; the four sumchecks' own forms and the clause on
canonical writing name none and are handed through as they come. -/
theorem HidesTables.same (h : SameCells c c') (hreq : Request.ok = true) (hy : y < V)
    {mask : Nat → E} {H : HeardAll} {G : Fork} (sPV : H.1.pV.size = lt)
    (sP : H.1.products.r.size = lt) (sN : H.2.1.normed.r.size = lt)
    (sL : H.2.2.logits.r.size = lt + lPd) (hzt : (FinalNorm.zt).size = lt)
    (A : HidesTables c mask H G) : HidesTables c' mask H G := by
  exact {
      w := fun s hs => by rw [← wScalars_same h]; exact A.w s hs
      p := fun n hn => (A.p n hn).trans (pScalars_same h _ hn)
      sqRow := A.sqRow
      sqEnd := fun j hj => by rw [← sqSum_same h]; exact A.sqEnd j hj
      prClaimed := A.prClaimed.trans (prLead_same h _ _)
      prRow := A.prRow
      prEnd := fun q hq => (A.prEnd q hq).trans
        (prEnds_same h _ _ _ sPV (by rw [Array.length_toList, sP]) hq)
      nmClaimed := A.nmClaimed.trans (nmLead_same h)
      nmRow := A.nmRow
      nmEnd := fun j hj => (A.nmEnd j hj).trans
        (nmEnds_same h _ hzt (by rw [Array.length_toList, sN]) hj)
      lgClaimed := by rw [← lgLead_same h hreq hy]; exact A.lgClaimed
      lgRow := A.lgRow
      lgEnd := fun j hj => (A.lgEnd j hj).trans
        (lgEnds_same h hreq hy _ hzt (by rw [Array.length_toList, sL]) hj)
      ok1 := A.ok1 }

end Lookup

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.end_sum
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.ends_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.limbZ_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.wsqZ_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.fieldE_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prodE_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.wScalars_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.pScalars_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.pScalars_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sqSum_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prLead_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.prEnds_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.rd_rec
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.recMap_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.streamMap_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.nmLead_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.nmEnds_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.UH_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lgLead_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.lgEnds_same
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.HidesTables.same
