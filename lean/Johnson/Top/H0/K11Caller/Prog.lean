-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Prog.lean: THE TEXT IS THE PROGRAM's: PROVED, UNDER EVERY READING THAT TAKES NUMERALS TO NUMBERS.

Coef.lean writes a claim's coefficients on the cells of the committed matrix W in closed form. Here they are joined by
theorems to what Johnson/Road/FormsKeysFac.lean and Johnson/Road/FormsKeysMerge.lean prove of the program's OWN functions:
    colFac_val    the program's wsEpsT, read, is C(X) at the read factors and the read point
    gammaAt_val   member y of the program's wsGamma of wsRowPart, at the scalars 1, read, is gamma y
    eqIdx_val     the library's kernel eqN at the read point is eq(X, col)
    summand_share **the typed summand at the read point is OnBytes.Road.shareAt**: there «one claim's share of the function that the merge's sumcheck runs on»
    summand_cube · G_val_means   **the typed claim says what the program's claim speaks of**: the summand's sum over the cube is OnBytes.Road.claimVal (by OnBytes.Road.merge_sum)
    G_f_fmAt      the merge's summand behind the draw is OnBytes.Road.fmAt
    G_EV_pending  **the proved block's second output claim (MergeL.EV) is the pending row's equation with the program's own row weights Gam** (by OnBytes.Road.pending_gamma)
The premises: the layout has the claim's unit; the claim passes wsClaimShape (a test of wsForkEnd); the unit has OnBytes.Road.UnitOK and lies within W (both theorems for every layout out of
wsLayOf: OnBytes.Road.unitOK_of_layout; ofLay_unit, ofLay_in in AtLay.lean); the reading takes numerals to numbers (a theorem for the reading in the library's field: gl_numerals).
Limits: identities alone. Nothing on the state's reading, which is a premise. No instance of all premises at once is made here. How wsPending cuts Gam into vectors of product form and how
the test on the matrix reads the point is not looked at. On hiding nothing.

-/
import Johnson.Top.H0.K11Caller.Tie
import Johnson.Top.H0.K11Caller.AtLay
import Johnson.Road.FormsKeysMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (Reading WsGrp WsUnit WsLay WsFac WsClaim WsRecClaim wsEpsT wsRowPart wsGamma wsGammaAdd wsDigits wsClaimShape eqTab clog2)
open OnBytes.Road (GrpOK UnitOK Runs Numerals pt eqB rowHalf leftOff gamOf shareAt fmAt rowAt Wm)
open Finset

section
variable {K : Type} [Field K] (ρ : Reading K)

theorem prodTo_eq (f : ℕ → K) : ∀ n, prodTo n f = ∏ i ∈ range n, f i
  | 0 => by simp [prodTo]
  | n + 1 => by rw [prodTo, prodTo_eq f n, Finset.prod_range_succ]

theorem sumTo_eq (f : ℕ → K) : ∀ n, sumTo n f = ∑ i ∈ range n, f i
  | 0 => by simp [sumTo]
  | n + 1 => by rw [sumTo, sumTo_eq f n, Finset.sum_range_succ]

/-- A factor as the program holds it, read. -/
abbrev rdF (x : WsFac) : Fac K := (Fac.ofWs x).map ρ.val

/-- One factor on its group's column bits. -/
theorem facCols_val (x : WsFac) {g : WsGrp} (hg : GrpOK g) (X : ℕ → E) :
    ρ.val (x.onColumns g X) = facCols g (rdF ρ x) fun b => ρ.val (X b) := by
  rcases hg with ⟨hcls, -, ht, -⟩ | ⟨hcls, ht, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    unfold WsFac.onColumns facCols
    rw [if_pos hE, if_pos hE, OnBytes.Road.foldl_mul_range, ρ.one, one_mul, prodTo_eq]
    refine prod_congr rfl fun i _ => ?_
    rw [OnBytes.Road.wsEq1_value]
    rfl
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold WsFac.onColumns facCols
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    by_cases h0 : 0 < g.t
    · have hA : g.aTaken = true := by
        unfold WsGrp.aTaken
        rw [hcls]
        simp [h0]
      have htR : g.t = clog2 g.R := by
        rcases ht with h | h
        · exact h
        · omega
      have hR : g.R ≤ 2 ^ g.t := by
        rw [htR]
        exact OnBytes.Road.le_two_pow_ceilLog2 g.R
      simp only [hA, ↓reduceIte]
      rw [OnBytes.Road.wsDot_value, sumTo_eq]
      refine sum_congr rfl fun i hi => ?_
      have hiR : i < g.R := mem_range.mp hi
      have hs : (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val)).size = g.t := by simp
      rw [OnBytes.Road.eqTab_value ρ _ i (by rw [hs]; exact lt_of_lt_of_le hiR hR), hs, OnBytes.Road.eqN_low_bits]
      unfold eqIdx
      rw [if_pos (lt_of_lt_of_le hiR hR), prodTo_eq]
      congr 1
      refine prod_congr rfl fun j hj => ?_
      have hj' : j < g.t := mem_range.mp hj
      have e2 : pt ρ (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val)) (0 + (g.t - 1 - j)) = ρ.val (X (g.cb0 + j)) := by
        have h1 : g.t - 1 - j < g.t := by omega
        have h2 : g.cb0 + g.t - 1 - (g.t - 1 - j) = g.cb0 + j := by omega
        simp [pt, Array.getD, h1, h2]
      rw [e2]
      rfl
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      exact ρ.one

theorem groupsCols_val (X : ℕ → E) : ∀ (fs : List WsFac) (gs : List WsGrp), (∀ g ∈ gs, GrpOK g) →
    ((fs.zip gs).map fun y => ρ.val (y.1.onColumns y.2 X)).prod = groupsCols gs (fs.map (rdF ρ)) fun b => ρ.val (X b)
  | [], [], _ => by simp [groupsCols]
  | [], _ :: _, _ => by simp [groupsCols]
  | _ :: _, [], _ => by simp [groupsCols]
  | x :: fs, g :: gs, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.prod_cons, groupsCols]
    rw [facCols_val ρ x (h g List.mem_cons_self) X, groupsCols_val X fs gs fun g' hg' => h g' (List.mem_cons_of_mem _ hg')]

/-- **The program's wsEpsT, read, is C(X).** -/
theorem colFac_val {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u) (U : UnitOK lay.lk u) (rm : Array E) :
    ρ.val (wsEpsT lay c rm) = colFac lay.lk u (facsOf ρ c) fun b => ρ.val (colX lay.lk rm b) := by
  rw [OnBytes.Road.wsEpsT_value ρ hu, groupsCols_val ρ _ c.f u.g U.grp]
  unfold colFac
  rw [prodTo_eq]
  rfl

/-- One factor on the part of the index that is left to the rows. -/
theorem facRows_val (x : WsFac) {g : WsGrp} (hg : GrpOK g) (r : ℕ) : rowHalf ρ x g r = facRows g (rdF ρ x) r := by
  unfold rowHalf facRows
  by_cases hE : (g.cls == 'E') = true
  · have ht : g.t ≤ g.z := by
      rcases hg with ⟨-, -, ht, -⟩ | ⟨hcls, -, -⟩
      · exact ht
      · rw [hcls] at hE
        exact absurd hE (by decide)
    rw [if_pos hE, if_pos hE, OnBytes.Road.eqN_low_bits, prodTo_eq]
    congr 1
    refine prod_congr rfl fun i hi => ?_
    have hi' : i < g.z - g.t := mem_range.mp hi
    have e : leftOff g + (g.z - g.t - 1 - i) = g.z - 1 - untakenAt g i := by
      unfold leftOff untakenAt
      split <;> omega
    rw [e]
    rfl
  · rw [if_neg hE, if_neg hE]
    rfl

/-- The coefficients that the program's fold makes from a vector d of the digits' scalars, member by member. -/
theorem gamOf_val : ∀ (fs : List WsFac) (gs : List WsGrp), (∀ y ∈ fs.zip gs, GrpOK y.2 ∧ y.1.fits y.2 = true) → ∀ (d : Array E) (y : ℕ),
    y < (gamOf (fs.zip gs) d).size →
    ρ.val ((gamOf (fs.zip gs) d).getD y zeroE) = gammaGo (fun q => ρ.val (d.getD q zeroE)) gs (fs.map (rdF ρ)) y
  | [], [], _, d, y, _ => by simp [gamOf, gammaGo]
  | [], _ :: _, _, d, y, _ => by simp [gamOf, gammaGo]
  | _ :: _, [], _, d, y, _ => by simp [gamOf, gammaGo]
  | x :: fs, g :: gs, hok, d, y, hy => by
    obtain ⟨hg, hfit⟩ := hok (x, g) (by simp)
    have hT := OnBytes.Road.table_size hg hfit
    have e0 : gamOf ((x :: fs).zip (g :: gs)) d = Model.wsOuter (gamOf (fs.zip gs) d) ((x.onRows g).table g) := rfl
    rw [e0] at hy ⊢
    rw [OnBytes.Road.wsOuter_size, hT] at hy
    have hl : 0 < g.left := by
      rcases Nat.eq_zero_or_pos g.left with h | h
      · rw [h] at hy
        omega
      · exact h
    have hq : y % g.left < ((x.onRows g).table g).size := by
      rw [hT]
      exact Nat.mod_lt _ hl
    have hi : y / g.left < (gamOf (fs.zip gs) d).size := (Nat.div_lt_iff_lt_mul hl).2 hy
    have h1 := OnBytes.Road.wsOuter_getD (gamOf (fs.zip gs) d) ((x.onRows g).table g) hi hq
    rw [hT, Nat.div_add_mod' y g.left] at h1
    rw [h1, ρ.mul, gamOf_val fs gs (fun z hz => hok z (by simp only [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hz)) d _ hi,
      OnBytes.Road.table_at ρ hg hfit (Nat.mod_lt _ hl), facRows_val ρ x hg]
    simp only [List.map_cons, gammaGo]
    exact mul_comm _ _

theorem c256_eq : (c256 : K) = 256 := by
  simp only [c256]
  norm_num

variable {ρ} in
/-- The digits' scalars at the scalars 1, read. -/
theorem digit_val (hρ : Numerals ρ) (nlw q : ℕ) :
    ρ.val ((wsDigits nlw (mulE oneE oneE)).toArray.getD q zeroE) = digit nlw q := by
  unfold digit
  rw [OnBytes.Road.toArray_getD]
  by_cases hq : q < nlw
  · rw [if_pos hq, OnBytes.Road.wsDigits_value hρ _ _ _ hq, ρ.mul, ρ.one, prodTo_eq, c256_eq]
    simp
  · rw [if_neg hq, List.getD_eq_default _ _ (by rw [OnBytes.Road.wsDigits_length]; omega), ρ.zero]

variable {ρ} in
/-- **Member y of the program's wsGamma of wsRowPart, at the scalars 1, read, is gamma y.** -/
theorem gammaAt_val (hρ : Numerals ρ) {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (hs : wsClaimShape lay c = .ok ()) (U : UnitOK lay.lk u) {y : ℕ} (hy : y < u.rows) :
    ρ.val ((wsGamma u (wsRowPart lay c oneE) oneE).getD y zeroE) = gammaAt u (facsOf ρ c) y := by
  obtain ⟨hlen, hfits⟩ := OnBytes.Road.shape_of_claim hu hs
  have hmap : (c.f.zip u.g).map (·.2) = u.g := List.map_snd_zip (by omega)
  have hok : ∀ z ∈ c.f.zip u.g, GrpOK z.2 ∧ z.1.fits z.2 = true := fun z hz => ⟨U.grp z.2 (by
    have h1 : z.2 ∈ (c.f.zip u.g).map (·.2) := List.mem_map_of_mem hz
    rw [hmap] at h1
    exact h1), hfits z hz⟩
  rw [OnBytes.Road.wsGamma_eq hu]
  have hsz : (gamOf (c.f.zip u.g) (wsDigits u.nlw (mulE oneE oneE)).toArray).size = u.rows := by
    have hp : u.g.map (·.left) = (c.f.zip u.g).map (·.2.left) := by
      have h2 := congrArg (List.map (·.left)) hmap
      rw [List.map_map] at h2
      exact h2.symm
    rw [OnBytes.Road.gamOf_size _ hok, U.rows, hp]
    simp [OnBytes.Road.wsDigits_length]
  rw [gamOf_val ρ c.f u.g hok _ y (by rw [hsz]; exact hy)]
  unfold gammaAt facsOf
  congr 1
  exact funext fun q => digit_val hρ u.nlw q

/-- **The library's kernel at the read point is eq(X, col).** -/
theorem eqIdx_val (lk : ℕ) (rm : Array E) {C : ℕ} (hC : C < 2 ^ lk) :
    eqIdx lk (fun b => ρ.val (colX lk rm b)) C = Blocks.eqN lk 0 (pt ρ rm) C := by
  rw [OnBytes.Road.eqN_eqB]
  unfold eqIdx eqB
  rw [if_pos hC, prodTo_eq]
  refine prod_congr rfl fun i _ => ?_
  rw [Nat.zero_add]
  rfl

/-- A sum over the rows of W of a map that is 0 outside a unit's rows. -/
theorem sum_window (g : ℕ → K) (off rows m0 : ℕ) (h : off + rows ≤ m0) (h0 : ∀ y, ¬(off ≤ y ∧ y < off + rows) → g y = 0) :
    ∑ y ∈ range m0, g y = ∑ j ∈ range rows, g (off + j) := by
  rw [← Finset.sum_subset (s₁ := Ico off (off + rows))
    (fun y hy => mem_range.2 (lt_of_lt_of_le (mem_Ico.1 hy).2 h)) (fun y _ hy => h0 y (by simpa [mem_Ico] using hy)),
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

end

/-- A sum over the cells of W as a sum over two ranges. -/
theorem sum_cells {K : Type} [Field K] (P : Place) (F : ℕ → ℕ → K) :
    ∑ rc : P.Cell, F rc.1.val rc.2.val = ∑ y ∈ range P.lay.m0, ∑ C ∈ range (2 ^ P.lay.lk), F y C := by
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun y => ∑ C ∈ range (2 ^ P.lay.lk), F y C)]
  exact sum_congr rfl fun y _ => Fin.sum_univ_eq_sum_range (F y.val) _

section Share
variable {E' : Type} [Field E'] (ρ : Reading E')

/-- The entries of W as a function of two numbers; 0 outside W. -/
def Wof (P : Place) (w : P.Cell → E') : Wm E' := fun y C => if h : y < P.lay.m0 ∧ C < 2 ^ P.lay.lk then w (⟨y, h.1⟩, ⟨C, h.2⟩) else 0

variable {ρ} in
/-- **THE TYPED SUMMAND AT THE READ POINT IS OnBytes.Road.shareAt.** -/
theorem summand_share (hρ : Numerals ρ) (P : Place) (c : WsClaim) (rm : Array E) (w : P.Cell → E') {u : WsUnit}
    (hu : P.lay.U[c.ui]? = some u) (hs : wsClaimShape P.lay c = .ok ()) (U : UnitOK P.lay.lk u) (hin : u.off + u.rows ≤ P.lay.m0)
    (hk : 0 < P.lay.lk) :
    summand P c.ui (facsOf ρ c) w (pointOf ρ P.lay.lk rm) = shareAt ρ P.lay (Wof P w) rm c := by
  have hX : XOf (pointOf ρ P.lay.lk rm) = fun b => ρ.val (colX P.lay.lk rm b) := funext fun b => (colX_val ρ P.lay.lk rm hk b).symm
  unfold summand shareAt
  rw [hX]
  simp only [hu]
  set A := colFac P.lay.lk u (facsOf ρ c) fun b => ρ.val (colX P.lay.lk rm b) with hA
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → E', F = fun y C => (if u.off ≤ y ∧ y < u.off + u.rows then
      A * (gammaAt u (facsOf ρ c) (y - u.off) * eqIdx P.lay.lk (fun b => ρ.val (colX P.lay.lk rm b)) C) else 0) * Wof P w y C := ⟨_, rfl⟩
  have step : ∀ rc : P.Cell, coef P.lay c.ui (facsOf ρ c) (fun b => ρ.val (colX P.lay.lk rm b)) rc.1.val rc.2.val * w rc = F rc.1.val rc.2.val := by
    intro rc
    have e1 : Wof P w rc.1.val rc.2.val = w rc := by
      unfold Wof
      rw [dif_pos ⟨rc.1.isLt, rc.2.isLt⟩]
    rw [hF]
    simp only [e1]
    unfold coef
    simp only [hu]
    rfl
  rw [sum_congr rfl fun rc _ => step rc, sum_cells P F,
    sum_window (fun y => ∑ C ∈ range (2 ^ P.lay.lk), F y C) u.off u.rows P.lay.m0 hin
      (fun y hy => sum_eq_zero fun C _ => by rw [hF]; simp only [if_neg hy, zero_mul]),
    colFac_val ρ hu U rm, ← hA, Finset.mul_sum]
  subst hF
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < u.rows := mem_range.mp hj
  rw [gammaAt_val hρ hu hs U hj']
  unfold rowAt
  rw [Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun C hC => ?_
  beta_reduce
  rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left, eqIdx_val ρ P.lay.lk rm (mem_range.mp hC)]
  ring

/-- The point that spells a column, read, is the cube's corner. -/
theorem point_corner {k : ℕ} (b : Fin k → Bool) : pointOf ρ k (OnBytes.Road.bitsOf k (Alg.num b)) = Alg.corner b := by
  funext i
  have h : (Alg.num b).testBit (k - 1 - i.val) = b i := congrFun (Alg.bits_num b) i
  unfold pointOf OnBytes.Road.bitsOf Alg.corner
  have e : (Array.ofFn (n := k) fun j => if (Alg.num b).testBit (k - 1 - j.val) then oneE else zeroE).getD i.val zeroE =
      if (Alg.num b).testBit (k - 1 - i.val) then oneE else zeroE := by simp [Array.getD, i.isLt]
  rw [e, h]
  cases b i
  · simpa using ρ.zero
  · simpa using ρ.one

variable {ρ} in
/-- **THE SUM OF THE TYPED SUMMAND OVER THE CUBE IS THE SUM THAT THE CLAIM SPEAKS OF** (OnBytes.Road.claimVal: the weights of the unit, each times the product of what the claim's factors weigh
its indices with). By OnBytes.Road.merge_sum. -/
theorem summand_cube (hρ : Numerals ρ) (P : Place) (c : WsClaim) (w : P.Cell → E') {u : WsUnit}
    (hu : P.lay.U[c.ui]? = some u) (hs : wsClaimShape P.lay c = .ok ()) (U : UnitOK P.lay.lk u) (hin : u.off + u.rows ≤ P.lay.m0)
    (hk : 0 < P.lay.lk) :
    ∑ b : Fin P.lay.lk → Bool, summand P c.ui (facsOf ρ c) w (Alg.corner b) = OnBytes.Road.claimVal ρ P.lay (Wof P w) c := by
  have h1 := OnBytes.Road.merge_sum hρ (Wof P w) [(c, oneE)] (lay := P.lay) (by
    intro y hy
    rw [List.mem_singleton.1 hy]
    exact ⟨u, hu, hs, U⟩)
  simp only [fmAt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ρ.one, one_mul] at h1
  rw [← h1, ← Alg.sum_num (fun C => shareAt ρ P.lay (Wof P w) (OnBytes.Road.bitsOf P.lay.lk C) c)]
  refine sum_congr rfl fun b _ => ?_
  rw [← summand_share hρ P c _ w hu hs U hin hk, point_corner]

end Share

section AtG2
variable {E' : Type} [Field E'] [Fintype E'] {ρ : Reading E'}

/-- What is asked of the program's claims at a place and a state: claim a is on the place's unit, passes wsClaimShape, its unit has OnBytes.Road.UnitOK, and the state's factors are its
factors, read. -/
structure Fit (ρ : Reading E') (P : Place) (T : Letters E' P) (st : T.St) (cl : Fin P.n → WsClaim) : Prop where
  ui : ∀ a, (cl a).ui = P.ui a
  shape : ∀ a, wsClaimShape P.lay (cl a) = .ok ()
  unit : ∀ a u, P.lay.U[P.ui a]? = some u → UnitOK P.lay.lk u
  fs : ∀ a, (T.rd st).fs a = facsOf ρ (cl a)

theorem Place.within (P : Place) (a : Fin P.n) : ∃ u, P.lay.U[P.ui a]? = some u ∧ u.off + u.rows ≤ P.lay.m0 := by
  obtain ⟨u, h1, h2⟩ := P.ok a
  simp only [unitOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  exact ⟨u, h1, h2.2⟩

/-- **WHAT CLAIM a OF THE TYPED RECORD SAYS**: its value is the sum that the program's claim speaks of (claimVal), plus the mask entry times its factor. -/
theorem G_val_means (hρ : Numerals ρ) (P : Place) (T : Letters E' P) (st : T.St) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (hk : 0 < P.lay.lk) (F : Fit ρ P T st cl) (a : Fin P.n) :
    (G P T).val st m a = OnBytes.Road.claimVal ρ P.lay (Wof P fun rc => m (.inl rc)) (cl a) + m (.inr (T.nm a)) * (T.rd st).be a := by
  obtain ⟨u, h1, hin⟩ := P.within a
  show ∑ b : Fin P.lay.lk → Bool, summand P (P.ui a) ((T.rd st).fs a) (fun rc => m (.inl rc)) (Alg.corner b) + _ = _
  rw [F.fs a, ← F.ui a, summand_cube hρ P (cl a) _ (by rw [F.ui a]; exact h1) (F.shape a) (F.unit a u h1) hin hk]
  rfl

/-- **THE MERGE's SUMMAND BEHIND THE DRAW IS OnBytes.Road.fmAt**, at the read point. rho: the program's coefficients, which read as the powers of b. -/
theorem G_f_fmAt (hρ : Numerals ρ) (P : Place) (T : Letters E' P) (st : T.St) (b : E') (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (rho : Fin P.n → E) (rm : Array E) (hk : 0 < P.lay.lk) (F : Fit ρ P T st cl) (hr : ∀ a, ρ.val (rho a) = b ^ (a : ℕ)) :
    (G P T).L.f (st, b) m (pointOf ρ P.lay.lk rm) =
      fmAt ρ P.lay (Wof P fun rc => m (.inl rc)) (List.ofFn fun a => (cl a, rho a)) rm := by
  show ∑ a : Fin P.n, b ^ (a : ℕ) * summand P (P.ui a) ((T.rd st).fs a) (fun rc => m (.inl rc)) (pointOf ρ P.lay.lk rm) = _
  unfold fmAt
  rw [List.map_ofFn, List.sum_ofFn]
  refine sum_congr rfl fun a _ => ?_
  obtain ⟨u, h1, hin⟩ := P.within a
  rw [F.fs a, ← F.ui a, summand_share hρ P (cl a) rm _ (by rw [F.ui a]; exact h1) (F.shape a) (F.unit a u h1) hin hk, ← hr a]
  rfl

/-- **THE PROVED BLOCK's SECOND OUTPUT CLAIM IS THE PENDING ROW's EQUATION, WITH THE PROGRAM's OWN ROW WEIGHTS.** Gam: what folding wsGammaAdd over what wsForkEnd leaves of the claims makes
of N zeros, as wsPending folds it. Then MergeL.EV at the output o says: the sum over the rows y below N of Gam[y], read, times row y of W read at the point, plus the entry cAt times beta, is
the end value. By OnBytes.Road.pending_gamma. -/
theorem G_EV_pending (hρ : Numerals ρ) (P : Place) (T : Letters E' P) (o : (G P T).L.T.par.Out) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (rho : Fin P.n → E) (rm : Array E) (hk : 0 < P.lay.lk) (F : Fit ρ P T o.st.1 cl) (hr : ∀ a, ρ.val (rho a) = o.st.2 ^ (a : ℕ))
    (hp : (G P T).L.oPt o = pointOf ρ P.lay.lk rm) {N : ℕ} {Gam : Array E}
    (h : ((List.ofFn fun a => (cl a, rho a)).map fun y => wsRowPart P.lay y.1 (mulE y.2 (wsEpsT P.lay y.1 rm))).foldlM
      (fun G c => wsGammaAdd G P.lay c oneE) (Array.replicate N zeroE) = .ok Gam) :
    (G P T).L.EV o m ↔
      ∑ y ∈ range N, ρ.val (Gam.getD y zeroE) * rowAt ρ P.lay.lk rm (Wof P fun rc => m (.inl rc)) y +
        m (.inr T.cAt) * (G P T).L.oBe o = o.vals () := by
  unfold Cb.Pv.Lay.MergeL.EV
  rw [hp, show (G P T).L.f o.st m (pointOf ρ P.lay.lk rm) = _ from G_f_fmAt hρ P T o.st.1 o.st.2 m cl rho rm hk F hr,
    OnBytes.Road.pending_gamma hρ P.lay _ rm _ h]
  exact Iff.rfl

end AtG2


end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.colFac_val
#print axioms VerifiableInference.Desc.First.K11Caller.gammaAt_val
#print axioms VerifiableInference.Desc.First.K11Caller.summand_share
#print axioms VerifiableInference.Desc.First.K11Caller.summand_cube
#print axioms VerifiableInference.Desc.First.K11Caller.G_val_means
#print axioms VerifiableInference.Desc.First.K11Caller.G_f_fmAt
#print axioms VerifiableInference.Desc.First.K11Caller.G_EV_pending
