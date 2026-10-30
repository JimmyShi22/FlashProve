-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/HonestN.lean: the head segment's honest trace, the hidden numbers included, for
every valid final normalisation.

The cells of the final normalisation are those of Inst/Model/Head/HonestBase.lean. The arrays d1,
d2, ex and the ledger's bytes 99 to 119 are written by the honest prover's rule, which the
implementation's protocol text (not in this repository) states for c_t and ov_t only
(in Lean: Inst/Model/Head/PolicyHonest.lean, Inst/Model/Head/PolicyCells.lean,
Inst/Model/Head/PolicyHonTrace.lean).
  `N.honCells np x H y`      the honest cells, from the residual stream x, the output matrix H and
                             what the head reads of the request and the policy: `honCellsP` at the
                             policy y.pol and the instance y.inst (Inst/Model/Head/Index.lean: the
                             rule is written for instances)
  `N.HonIn np x H y`         what is assumed: np is valid; NORM does not halt at any position; |H| ≤
                             2^12; every checked token is below V; the policy holds of the stream's
                             logits (`PolOK`); C, θ < 2^40, cap < 2^16
  `N.hon_small`              under `HonIn`: the honest cells are small (`Small`)
  `N.hon_cells_le`           under `HonIn`: every cell of the honest trace of the head, and of the
                             borrowed x, has absolute value at most 128
  `N.t_hf` .. `N.t_mg`       the cells and arrays of `honCells`: those taken over are `honBase`'s
                             (at `req0 y`), those of the policy are the rule's; read by
                             Policy/Rel/LedgerHeadHonest.lean
  `N.honIn_stream`           `HonIn` from the last clause of the program's "runs" and the policy,
                             with the definitions of Inst/Model/Program.lean, if also np is valid,
                             |H| ≤ 2^12, `y.OK`, C, θ < 2^40 and cap < 2^16
  `polOK_congr`, `polOK_inst`, `honCells_of`
                             sanity lemmas on the use of y.inst: the policy and the rule depend only
                             on r, e, the checked tokens and the announced token; at the request
                             `Req.of pol x'` of an instance x' the cells are
                             `honCellsP np x H pol x'`. `cells_ext`, `base_x`,
                             `base_hd`, `base_hr`, `base_x_indep`, `base_hd_indep`, `base_hr_indep`
                             are small steps for `honCells_of` (three fields of the base's cells do
                             not depend on the request)

Notation:
  `np : NormPar` (Inst/Model/Program.lean): exponent of the reciprocal (M); shift (K); constant (ϵ)
    of a normalisation; `np.OK` (`NormPar.OK`): a `Prop`: the conditions under which NORM is stated.
  `y : Req` (Inst/Model/Head/Index.lean): what the head reads of a request and of the policy: `y.r`,
    `y.e`: the two numbers that bound the covered positions; `y.win i`: the token that is checked at
    position i; `y.pol`: the three numbers of the acceptance policy.
  `Hid` (Inst/Model/Head/PolicyDefs.lean): the six hidden numbers of a position: c, b, u, k, z, zs.
  `Dig` (Inst/Model/Head/PolicyDefs.lean; the type of `Honest.honD`): the three digits of a margin
    and the looked-up value, at the pair (v, t): K0, K1, K2, ex.
  `d1` (2 cells), `d2` (1 cell) (Inst/Model/Head/Trace.lean): cells of the middle and of the low
    digit of a margin; `ex` (3 cells, +8,421,505): the looked-up value EX[K_1], which (Z) adds up.
  `N`: the namespace of the statements for every valid final normalisation `np`.
Limits. Nothing is said on the protocol. All is at the step table and at sh = 8 only
(`EX`, Inst/Model/Tables.lean; `costOf`, Inst/Model/ProgramR.lean). Outside `HonIn` the cells are
still defined, and mean nothing.
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.PolicyHonTrace

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model Finset

section
variable {P : Params} {lg : ℕ → ℕ → ℤ} {pol : AcceptancePolicy} {x x' : Instance P}

/-- the policy depends only on r, e, the checked tokens and y -/
theorem polOK_congr (er : x'.r = x.r) (ee : x'.e = x.e) (ew : x'.w = x.w)
    (ey : x'.y.val = x.y.val) (h : PolOK lg pol x) : PolOK lg pol x' := by
  have hc : x'.cnt = x.cnt := by unfold Instance.cnt; rw [er, ee]
  have hN : x'.NB = x.NB := by unfold Instance.NB; rw [er, ee]
  have hcost : ∀ t, costOf lg x' t = costOf lg x t := fun t => by unfold costOf; rw [ew]
  refine ⟨?_, ?_, fun hre he => ?_⟩
  · rw [hc, hN]
    simpa only [hcost] using h.a
  · rw [hc]
    simpa only [hcost] using h.b
  · rw [ey]
    exact h.c (by rw [← er, ← ee]; exact hre) (by rw [← ee]; exact he)

/-- the rule depends only on r, e and the checked tokens -/
theorem Honest.pre_congr (er : x'.r = x.r) (ee : x'.e = x.e) (ew : x'.w = x.w) :
    Honest.pre lg pol x' = Honest.pre lg pol x := by
  have hcnt : x'.cnt = x.cnt := by unfold Instance.cnt; rw [er, ee]
  have hN : x'.NB = x.NB := by unfold Instance.NB; rw [er, ee]
  have hcost : costOf lg x' = costOf lg x := funext fun t => by unfold costOf; rw [ew]
  have e1 : Honest.hc lg pol x' = Honest.hc lg pol x :=
    funext fun t => by unfold Honest.hc; rw [hcnt, hcost]
  have e2 : Honest.hb lg pol x' = Honest.hb lg pol x :=
    funext fun t => by unfold Honest.hb; rw [hcnt, hcost]
  have e3 : Honest.slack lg pol x' = Honest.slack lg pol x := by
    unfold Honest.slack; rw [hcnt, hN, e1, e2]
  have e4 : Honest.hu lg pol x' = Honest.hu lg pol x :=
    funext fun t => by unfold Honest.hu; rw [hcnt, e3, er]
  have e5 : Honest.hk lg pol x' = Honest.hk lg pol x :=
    funext fun t => by unfold Honest.hk; rw [hcnt, e1]
  have e6 : Honest.hz lg pol x' = Honest.hz lg pol x :=
    funext fun t => by unfold Honest.hz; rw [hcnt, hN, e2, er]
  unfold Honest.pre
  rw [e1, e2, e4, e5, e6]
theorem Honest.honD_congr (er : x'.r = x.r) (ee : x'.e = x.e) (ew : x'.w = x.w) :
    Honest.honD lg pol x' = Honest.honD lg pol x := by
  have hcnt : x'.cnt = x.cnt := by unfold Instance.cnt; rw [er, ee]
  have hm : marg lg x' (Honest.pre lg pol x') =
      marg lg x (Honest.pre lg pol x) := funext fun t => funext fun v => by
    unfold marg rhoC
    rw [Honest.pre_congr er ee ew, hcnt, ew]
  unfold Honest.honD
  rw [hm, er, ee]
theorem Honest.honH_congr (er : x'.r = x.r) (ee : x'.e = x.e) (ew : x'.w = x.w) :
    Honest.honH lg pol x' = Honest.honH lg pol x := by
  have hcnt : x'.cnt = x.cnt := by unfold Instance.cnt; rw [er, ee]
  unfold Honest.honH
  rw [Honest.pre_congr er ee ew, Honest.honD_congr er ee ew, hcnt]

end

theorem polOK_inst {lg : ℕ → ℕ → ℤ} {pol : AcceptancePolicy} {x : Instance ppref} (h : PolOK lg pol x) :
    PolOK lg pol (Req.of pol x).inst :=
  polOK_congr (Req.inst_of pol x).1
    (Req.inst_of pol x).2.1 (Req.inst_of pol x).2.2.1 (Req.inst_of pol x).2.2.2 h

end Inst.Model.Head.Policy

namespace Inst.Model.Head.N

open Finset Inst.Model.Head.Policy

/-- The honest cells. -/
def honCells (np : NormPar) (x : ℕ → Vec) (H : Mat) (y : Req) : Cells ℤ :=
  honCellsP np x H y.pol y.inst

/-- What is assumed of the run of the program and of the policy. -/
structure HonIn (np : NormPar) (x : ℕ → Vec) (H : Mat) (y : Req) : Prop where
  /-- the final normalisation is valid -/
  nf : np.OK
  ok : ∀ i < nT, NORM.OK np nD (x i)
  hH : ∀ j v, |H j v| ≤ 2 ^ 12
  /-- every checked token is below V -/
  win : y.OK
  /-- the policy holds of the logits of the residual stream -/
  pol : PolOK (lgv np x H) y.pol y.inst
  C : y.pol.C < 2 ^ 40
  theta : y.pol.theta < 2 ^ 40
  cap : y.pol.cap < 2 ^ 16

section Main
variable {np : NormPar} {x : ℕ → Vec} {H : Mat} {y : Req}

/-- the request without covered positions, at which the proofs below use `base_cells_le` -/
def req0 (y : Req) : Req := ⟨0, 0, y.win, y.pol⟩

theorem HonIn.base (h : HonIn np x H y) : HonIn0 np x H (req0 y) :=
  ⟨h.nf, h.ok, h.hH, fun i _ _ he => absurd (show i < 0 from he) (Nat.not_lt_zero i)⟩

theorem HonIn.fit (h : HonIn np x H y) : Fit ppref (lgv np x H) y.pol :=
  fit_lgv h.hH h.C h.theta h.cap

/-! ### The cells that are taken over -/

theorem base_hf_indep (y1 y2 : Req) {φ : ℕ} (hφ : φ < 20480) (i : ℕ) :
    (honBase np x H y1).hf φ i = (honBase np x H y2).hf φ i := by
  simp only [honBase]
  by_cases c : φ < 10240
  · rw [if_pos c, if_pos c]
  · rw [if_neg c, if_neg c, if_pos hφ, if_pos hφ]

theorem t_hf {φ : ℕ} (hφ : φ < 20480) (i : ℕ) :
    (honCells np x H y).hf φ i = (honBase np x H (req0 y)).hf φ i := by
  show (if φ < 20480 then (honBase np x H (Req.of y.pol y.inst)).hf φ i else _) = _
  rw [if_pos hφ]
  exact base_hf_indep _ _ hφ i
theorem t_hr {n : ℕ} (hn : n < 99) (i : ℕ) :
    (honCells np x H y).hr n i = (honBase np x H (req0 y)).hr n i := by
  show (if n < 99 then (honBase np x H (Req.of y.pol y.inst)).hr n i else _) = _
  rw [if_pos hn]
  rfl
theorem t_Dv {i : ℕ} :
    ∀ n < 99, Dv (honCells np x H y) n i = Dv (honBase np x H (req0 y)) n i := fun n hn => by
  unfold Dv
  rw [t_hr hn]
theorem t_nw {j : ℕ} (hj : j < nD) (i : ℕ) :
    nw (honCells np x H y) j i = nw (honBase np x H (req0 y)) j i := by
  unfold nw rd
  refine sum_congr rfl fun l hl => ?_
  have := mem_range.1 hl
  show 256 ^ l * (honCells np x H y).hf (fNw l j) i =
    256 ^ l * (honBase np x H (req0 y)).hf (fNw l j) i
  rw [t_hf (by unfold fNw; unfold nD at hj; omega)]
theorem t_rn {j : ℕ} (hj : j < nD) (i : ℕ) :
    rn (honCells np x H y) j i = rn (honBase np x H (req0 y)) j i := by
  unfold rn rd
  congr 1
  refine sum_congr rfl fun l hl => ?_
  have := mem_range.1 hl
  show 256 ^ l * (honCells np x H y).hf (fRn l j) i =
    256 ^ l * (honBase np x H (req0 y)).hf (fRn l j) i
  rw [t_hf (by unfold fRn; unfold nD at hj; omega)]

/-! ### The cells of the policy -/

section Pol
variable (h : HonIn np x H y)
include h

theorem t_hid : hidOf (honCells np x H y) = Honest.honH (lgv np x H) y.pol y.inst :=
  hidOf_hon (honP_holds np x H y.pol y.inst) h.pol h.fit

omit h in
theorem t_K1 {v : ℕ} (hv : v < nV) {i : ℕ} (hi : i < nT) :
    K1 (honCells np x H y) y v i = (Honest.honD (lgv np x H) y.pol y.inst).K1 v i := by
  rw [← pd1_K1 i (show v < ppref.V from hv), ← (honP_holds np x H y.pol y.inst).d1 i v hv]
  simp only [K1, y.rho_inst hi, rhoR, Int.cast_id]
  rfl
omit h in
theorem t_K2 {v : ℕ} (hv : v < nV) {i : ℕ} (hi : i < nT) :
    K2 (honCells np x H y) y v i = (Honest.honD (lgv np x H) y.pol y.inst).K2 v i := by
  rw [← pd2_K2 i (show v < ppref.V from hv), ← (honP_holds np x H y.pol y.inst).d2 i v hv]
  simp only [K2, y.rho_inst hi, rhoR, Int.cast_id]
  rfl
omit h in
theorem t_ex {v : ℕ} (hv : v < nV) (i : ℕ) :
    ex (honCells np x H y) v i = pex (lgv np x H) y.pol y.inst i v :=
  (honP_holds np x H y.pol y.inst).ex i v hv

theorem t_mg (v : ℕ) {i : ℕ} (hi : i < nT) :
    mg (honCells np x H y) H y v i =
      mgP (lgv np x H) y.inst (Honest.honH (lgv np x H) y.pol y.inst) i v := by
  have e := t_hid h
  have ec : hidC (honCells np x H y) i = (Honest.honH (lgv np x H) y.pol y.inst).c i :=
    congrFun (congrArg Hid.c e) i
  have eb : hidB (honCells np x H y) i = (Honest.honH (lgv np x H) y.pol y.inst).b i :=
    congrFun (congrArg Hid.b e) i
  have el : ∀ v, lg (honCells np x H y) H i v = lgv np x H i v := fun v =>
    honP_lg np x H y.pol y.inst i v
  unfold mg mgP rhoR rhoC
  rw [ec, eb, el, el, y.rho_inst hi, y.rhoC_inst, y.inst_w h.win hi]
  simp only [Int.cast_id]

omit h in
/-- a sum over the positions with the mask ρC is the sum over the counted positions -/
theorem sum_rhoC (f : ℕ → ℤ) : ∑ i ∈ range nT, y.rhoC i * f i = ∑ i ∈ y.inst.cnt, f i := by
  have e : ∀ i ∈ range nT, y.rhoC i * f i = if i ∈ y.inst.cnt then f i else 0 := fun i _ => by
    rw [y.rhoC_inst]
    split_ifs <;> simp
  have e2 : range nT ∩ y.inst.cnt = y.inst.cnt :=
    inter_eq_right.2 fun i hi => mem_range.2 (by have := y.mem_inst_cnt.1 hi; unfold nT; omega)
  rw [sum_congr rfl e, sum_ite_mem, e2]

end Pol

/-- under `HonIn`: every cell of the honest trace of the head, and of the borrowed x, has absolute
value at most 128 -/
theorem hon_cells_le (h : HonIn np x H y) {i : ℕ} (hi : i < nT) :
    (∀ φ < nFeat .hf, |(honCells np x H y).hf φ i| ≤ 128) ∧
    (∀ φ < nFeat .hd, |(honCells np x H y).hd φ i| ≤ 128) ∧
    (∀ φ < nFeat .hr, |(honCells np x H y).hr φ i| ≤ 128) ∧
    ∀ φ < nFeat .x, |(honCells np x H y).x φ i| ≤ 128 := by
  obtain ⟨a, b, c, d⟩ := base_cells_le h.base hi
  obtain ⟨p1, p2⟩ := honP_le h.pol h.fit i
  refine ⟨fun φ hφ => ?_, b, fun n hn => ?_, d⟩
  · by_cases c1 : φ < 20480
    · rw [t_hf c1]
      exact a φ hφ
    · exact p1 φ (by omega)
  · by_cases c1 : n < 99
    · rw [t_hr c1]
      exact c n hn
    · exact p2 n (by omega)

/-- Under `HonIn` the honest cells are small. -/
theorem hon_small (h : HonIn np x H y) : Small (honCells np x H y) := fun i hi => by
  obtain ⟨a, b, c, d⟩ := hon_cells_le h hi
  exact ⟨fun φ hφ => lt_of_le_of_lt (a φ hφ) (by norm_num),
    fun φ hφ => lt_of_le_of_lt (b φ hφ) (by norm_num),
    fun φ hφ => lt_of_le_of_lt (c φ hφ) (by norm_num),
    fun φ hφ => lt_of_le_of_lt (d φ hφ) (by norm_num)⟩

end Main

/-! ## From the last steps of the program -/

/-- `HonIn` from its clauses, with the logits written as in Inst/Model/Program.lean, so that the
hypotheses unfold from `RunsK` and `lgK`. -/
theorem honIn_stream {np : NormPar} (hn : np.OK) {X : ℕ → Vec} {H : Mat}
    (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {y : Req} (hok : ∀ i < nT, NORM.OK np nD (X i)) (hw : y.OK)
    (hp : PolOK (fun i v => dot nD (NORM.out np nD (X i)) fun j => H j v) y.pol y.inst)
    (hC : y.pol.C < 2 ^ 40) (hθ : y.pol.theta < 2 ^ 40) (hcap : y.pol.cap < 2 ^ 16) :
    HonIn np X H y :=
  ⟨hn, hok, hH, hw, hp, hC, hθ, hcap⟩

/-! ## Sanity lemmas on the use of y.inst -/

/-- two records of cells with the same four fields are the same -/
theorem cells_ext (a b : Cells ℤ) (h1 : a.hf = b.hf) (h2 : a.hd = b.hd)
    (h3 : a.hr = b.hr) (h4 : a.x = b.x) : a = b := by
  obtain ⟨⟩ := a
  obtain ⟨⟩ := b
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- three fields of the cells without hidden numbers, written out: none depends on the request -/
theorem base_x (np : NormPar) (X : ℕ → Vec) (H : Mat) (y : Req) :
    (honBase np X H y).x = fun φ i => cellW 5 (X i (φ % 5120)) (φ / 5120) := rfl
theorem base_hd (np : NormPar) (X : ℕ → Vec) (H : Mat) (y : Req) :
    (honBase np X H y).hd = fun φ i => cellW 2 (outv np X i (φ % 5120)) (φ / 5120) := rfl
theorem base_hr (np : NormPar) (X : ℕ → Vec) (H : Mat) (y : Req) :
    (honBase np X H y).hr =
      fun n i => if n < 99 then Ledger.hon np nD (bX X i) n - 128 else -128 := rfl
/-- so each is the same at any two requests; proved from the three equations above, so that a
checker need not unfold the two records to compare them -/
theorem base_x_indep (np : NormPar) (X : ℕ → Vec) (H : Mat) (y1 y2 : Req) :
    (honBase np X H y1).x = (honBase np X H y2).x :=
  (base_x np X H y1).trans (base_x np X H y2).symm
theorem base_hd_indep (np : NormPar) (X : ℕ → Vec) (H : Mat) (y1 y2 : Req) :
    (honBase np X H y1).hd = (honBase np X H y2).hd :=
  (base_hd np X H y1).trans (base_hd np X H y2).symm
theorem base_hr_indep (np : NormPar) (X : ℕ → Vec) (H : Mat) (y1 y2 : Req) :
    (honBase np X H y1).hr = (honBase np X H y2).hr :=
  (base_hr np X H y1).trans (base_hr np X H y2).symm

/-- Sanity lemma: at what the head reads of an instance the cells are those of the rule at that
instance. -/
theorem honCells_of (np : NormPar) (X : ℕ → Vec) (H : Mat) (pol : AcceptancePolicy) (x : Instance ppref) :
    honCells np X H (Req.of pol x) = honCellsP np X H pol x := by
  obtain ⟨er, ee, ew, -⟩ := Req.inst_of pol x
  have eD := Honest.honD_congr (lg := lgv np X H) (pol := pol) er ee ew
  have eH := Honest.honH_congr (lg := lgv np X H) (pol := pol) er ee ew
  refine cells_ext _ _ (funext fun φ => funext fun i => ?_)
    (base_hd_indep np X H (Req.of pol (Req.of pol x).inst) (Req.of pol x))
    (funext fun n => funext fun i => ?_)
    (base_x_indep np X H (Req.of pol (Req.of pol x).inst) (Req.of pol x))
  · show (honCellsP np X H pol (Req.of pol x).inst).hf φ i = _
    simp only [honCellsP, pd1, pd2, pex, eD, er, ee]
    by_cases c : φ < 20480
    · rw [if_pos c, if_pos c]
      exact base_hf_indep _ _ c i
    · rw [if_neg c, if_neg c]
  · show (honCellsP np X H pol (Req.of pol x).inst).hr n i = _
    simp only [honCellsP, phr, eH]
    rw [base_hr_indep np X H (Req.of pol (Req.of pol x).inst) (Req.of pol x)]

end Inst.Model.Head.N
