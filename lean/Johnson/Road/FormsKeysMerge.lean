-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysMerge.lean: identities under the merge, the part of a sub-proof that reduces
its claims on the committed matrix of weights W to one equation on W.

The merge (OnBytes/Model/Merge.lean) draws coefficients rho for the claims and runs a sumcheck over
the column bits of W, whose sum must equal the sum of rho[a] times the hidden value under the slot
of claim a, and which ends at a point rm. What is left of each claim goes into the row weights of
the pending row (OnBytes/Model/Pending.lean). The verifier never forms the function on which that
sumcheck runs. This file writes it (fmAt) and shows what ties it to the claims and to the pending
row.

What is compared with what: the verifier's own functions wsEpsT, wsRowPart, wsGamma, wsGammaAdd and
wsForkStart with definitions of these files: claimVal (Johnson/Road/FormsKeysWm.lean), and rowAt,
shareAt and fmAt of this file. The library is not mentioned, but for its kernel eqN.

Which value is which. rho and rm are public: in a run, powers of one drawn element and the rounds'
challenges; here any elements. W is any function; nothing ties it to a commitment. In
wsForkStart_value, W.slot (sv a) is the HIDDEN value under the slot of claim a, not what was sent
for it. The value fv' that the prover sends at the merge's end, the mask entry c and the challenge
beta do not occur in this file.

Main definitions: eqB, colProd; rowAt, shareAt, fmAt.
Main theorems, each with the verifier's text that it is about.
 - eps_multilinear (wsEpsT, WsFac.onColumns in OnBytes/Model/Weights.lean): the value of a claim's
   factors on the columns at any point rm is the sum over the columns C of the equality weight of C
   at rm times the value at the point that spells C.
 - merge_sum (claim_cells of Johnson/Road/FormsKeysFac.lean, summed): the sum of fmAt over the
   points that spell the columns is the sum of rho[a] times claimVal of claim a.
 - wsForkStart_value (wsForkStart in OnBytes/Model/Merge.lean): the form that the sum of the
   sumcheck must equal is worth the sum of rho[a] times the hidden value under sv[a]. merge_start:
   if each hidden value is what its claim speaks of, that form is worth the sum of fmAt over the
   points that spell the columns: the direction of completeness. That "if" is what the merge is
   there to show; it is not shown here.
 - pending_gamma, gamma_fold (the line of wsForkEnd that makes recs; the line of wsPending that
   folds wsGammaAdd over recs from an array of zeros; wsGammaAdd): fmAt at rm is the sum over the
   rows y of W of the folded coefficient on y times row y of W read at rm. That is the left form of
   the pending row without its mask.
 - eq_psi (the line of wsPending that sets psi to rm reversed): the equality weight of a column at
   rm, written with coordinate b of psi at bit b of the column.

The hypotheses, and where they are met. UnitOK: a theorem for every unit of a layout that the
verifier builds (unitOK_of_layout, Johnson/Road/FormsKeysWLay.lean). That the layout has each
claim's unit and each claim passes wsClaimShape: tests of wsForkEnd; run on the verifier's own list
of claims at made-up numbers in Johnson/Road/FormsKeysRunW.lean (W5). Numerals: gl_numerals
(Johnson/Road/FormsKeysKit.lean). That the fold of wsGammaAdd returns: run there (W8), from an array
of as many zeros as W has rows. W8 also runs eps_multilinear and pending_gamma in the program's own
field, at a made-up point.

What is not claimed. All statements are identities; no challenge's distribution is used. The
sumcheck itself, its hiding polynomial, the claim that the merge adds to the sub-proof, the equation
"left form plus beta c equals fv'" and its test are not looked at. How wsPending cuts the folded
coefficients to the stretch of the claims' units and into vectors of product form, and how the test
on the matrix reads psi, is not looked at. The program does not import this file.
-/
import Johnson.Road.FormsKeysFac
import OnBytes.Model.Merge

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff WsGrp WsUnit WsLay WsFac WsClaim WsRecClaim wsOuter wsDot
  wsEq1 wsEpsT wsRowPart wsGamma wsGammaAdd wsDigits wsClaimShape wsForkStart eqTab clog2)

/-! ## Bits -/

/-- The low bits of a number made of c below 2^t and of more above. -/
theorem bits_low {t β c i : ℕ} (hc : c < 2 ^ t) (hi : i < t) :
    (β * 2 ^ t + c).testBit i = c.testBit i := by
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hc, if_pos hi]

/-- Its high bits. -/
theorem bits_high {t β c : ℕ} (hc : c < 2 ^ t) (i : ℕ) :
    (β * 2 ^ t + c).testBit (t + i) = β.testBit i := by
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hc, if_neg (by omega), Nat.add_sub_cancel_left]

section Multi

variable {K : Type} [Field K] (ρ : Reading K)

/-- A product of t sums of two terms, multiplied out: one product for each number c below 2^t, which
takes the first term where c has the bit 1 and the second where it has 0. -/
theorem prod_add_bits (a b : ℕ → K) : ∀ t : ℕ,
    ∏ i ∈ range t, (a i + b i) =
      ∑ c ∈ range (2 ^ t), ∏ i ∈ range t, (if c.testBit i then a i else b i)
  | 0 => by simp
  | t + 1 => by
    have h2 : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
      rw [pow_succ]
      omega
    rw [Finset.prod_range_succ, prod_add_bits a b t, h2, Finset.sum_range_add, mul_add,
      Finset.sum_mul, Finset.sum_mul, add_comm]
    congr 1
    · refine sum_congr rfl fun c hc => ?_
      have hc' : c < 2 ^ t := mem_range.mp hc
      rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow hc']
      simp
    · refine sum_congr rfl fun c hc => ?_
      have hc' : c < 2 ^ t := mem_range.mp hc
      have e : 2 ^ t + c = 1 * 2 ^ t + c := by rw [Nat.one_mul]
      have ht : (1 * 2 ^ t + c).testBit t = true := by
        have h3 := bits_high (β := 1) hc' 0
        rw [Nat.add_zero] at h3
        rw [h3]
        rfl
      rw [Finset.prod_range_succ, e, ht]
      simp only [if_true]
      congr 1
      exact prod_congr rfl fun i hi => by rw [bits_low hc' (mem_range.mp hi)]

/-- The equality weight of the number C at the coordinates X (cb), .., X (cb + T - 1), the lowest
bit of C with the first of them. -/
def eqB (X : ℕ → E) (cb T C : ℕ) : K :=
  ∏ i ∈ range T, (if C.testBit i then ρ.val (X (cb + i)) else 1 - ρ.val (X (cb + i)))

/-- The weight of a number made of c below 2^t and of C2 above is the product of the two weights. -/
theorem eqB_split (X : ℕ → E) (cb T t C2 : ℕ) {c : ℕ} (hc : c < 2 ^ t) :
    eqB ρ X cb (T + t) (C2 * 2 ^ t + c) = eqB ρ X cb t c * eqB ρ X (cb + t) T C2 := by
  unfold eqB
  rw [Nat.add_comm T t, Finset.prod_range_add]
  congr 1
  · exact prod_congr rfl fun i hi => by rw [bits_low hc (mem_range.mp hi)]
  · exact prod_congr rfl fun i _ => by rw [bits_high hc i, Nat.add_assoc]

/-- The library's kernel at a point, the first coordinate with the top bit, is eqB at the
coordinates in reversed order. -/
theorem eqN_eqB (lk : ℕ) (rm : Array E) (C : ℕ) :
    Blocks.eqN lk 0 (pt ρ rm) C = eqB ρ (fun b => rm.getD (lk - 1 - b) zeroE) 0 lk C := by
  rw [eqN_low_bits]
  unfold eqB pt
  exact prod_congr rfl fun i _ => by rw [Nat.zero_add, Nat.zero_add]

/-- wsEq1 reads as p x + (1 - p) (1 - x). -/
theorem wsEq1_value (p x : E) :
    ρ.val (wsEq1 p x) = ρ.val p * ρ.val x + (1 - ρ.val p) * (1 - ρ.val x) := by
  unfold wsEq1
  rw [ρ.add, ρ.mul, ρ.mul, ρ.sub, ρ.sub, ρ.one]

/-- A factor's value on its group's column bits, at any coordinates: the sum over the numbers c that
the bits can spell of the equality weight of c at the coordinates, times the column half at c. -/
theorem onColumns_multi (x : WsFac) {g : WsGrp} (hg : GrpOK g) (X : ℕ → E) :
    ρ.val (x.onColumns g X) = ∑ c ∈ range (2 ^ g.t), eqB ρ X g.cb0 g.t c * colHalf ρ x g c := by
  rcases hg with ⟨hcls, -, ht, -⟩ | ⟨hcls, ht, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hcls]; rfl
    unfold WsFac.onColumns colHalf
    rw [if_pos hE, foldl_mul_range, ρ.one, one_mul]
    simp only [hE, ↓reduceIte, wsEq1_value]
    rw [prod_add_bits]
    refine sum_congr rfl fun c _ => ?_
    rw [eqN_low_bits]
    unfold eqB
    rw [← Finset.prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    have hi' : i < g.t := mem_range.mp hi
    have e : g.z - 1 - g.takenAt i = takenOff g + (g.t - 1 - i) := by
      unfold WsGrp.takenAt takenOff
      split <;> omega
    rw [e]
    unfold pt
    cases c.testBit i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    · simp only [↓reduceIte]
      ring
  · have hE : (g.cls == 'E') = false := by rw [hcls]; rfl
    unfold WsFac.onColumns colHalf
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
        exact le_two_pow_ceilLog2 g.R
      simp only [hA, ↓reduceIte]
      rw [wsDot_value, ← Finset.sum_subset (range_subset_range.mpr hR)]
      · refine sum_congr rfl fun i hi => ?_
        have hiR : i < g.R := mem_range.mp hi
        have hs : (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val)).size = g.t := by
          simp
        rw [eqTab_value ρ _ i (by rw [hs]; exact lt_of_lt_of_le hiR hR), hs, eqN_low_bits,
          if_pos hiR, mul_comm]
        congr 1
        unfold eqB
        refine prod_congr rfl fun j hj => ?_
        have hj' : j < g.t := mem_range.mp hj
        have e2 : pt ρ (Array.ofFn (n := g.t) fun s => X (g.cb0 + g.t - 1 - s.val))
            (0 + (g.t - 1 - j)) = ρ.val (X (g.cb0 + j)) := by
          have h1 : g.t - 1 - j < g.t := by omega
          have h2 : g.cb0 + g.t - 1 - (g.t - 1 - j) = g.cb0 + j := by omega
          simp [pt, Array.getD, h1, h2]
        rw [e2]
      · intro c _ hc
        rw [if_neg (fun h => hc (mem_range.mpr h)), mul_zero]
    · have hA : g.aTaken = false := by
        unfold WsGrp.aTaken
        simp [h0]
      have ht0 : g.t = 0 := by omega
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [ht0]
      simp [eqB, ρ.one]

/-- The product of the column halves of a list of factors at the number C, whose lowest bits belong
to the first group. -/
def colProd : List (WsFac × WsGrp) → ℕ → K
  | [], _ => 1
  | (x, g) :: rest, C => colHalf ρ x g (C % 2 ^ g.t) * colProd rest (C / 2 ^ g.t)

/-- The product of the factors' values on their column bits, at any coordinates. -/
theorem cols_multi (X : ℕ → E) : ∀ (l : List (WsFac × WsGrp)) (cb : ℕ),
    (∀ y ∈ l, GrpOK y.2) → Runs (l.map (·.2)) cb →
    (l.map fun p => ρ.val (p.1.onColumns p.2 X)).prod =
      ∑ C ∈ range (2 ^ (l.map (·.2.t)).sum), eqB ρ X cb (l.map (·.2.t)).sum C * colProd ρ l C
  | [], cb, _, _ => by simp [eqB, colProd]
  | (x, g) :: rest, cb, hok, hr => by
    have hg := hok (x, g) List.mem_cons_self
    have hcb : g.cb0 = cb := hr.1
    have hsum : (((x, g) :: rest).map (·.2.t)).sum = (rest.map (·.2.t)).sum + g.t := by
      rw [List.map_cons, List.sum_cons, Nat.add_comm]
    rw [List.map_cons, List.prod_cons, onColumns_multi ρ x hg X,
      cols_multi X rest (cb + g.t) (fun y hy => hok y (List.mem_cons_of_mem _ hy)) hr.2, hsum,
      Nat.pow_add, sum_blocks, Finset.sum_mul_sum, Finset.sum_comm]
    refine sum_congr rfl fun C2 _ => sum_congr rfl fun c hc => ?_
    have hc' : c < 2 ^ g.t := mem_range.mp hc
    obtain ⟨d1, d2⟩ := div_mod_block (i := C2) hc'
    show _ = _ * (colHalf ρ x g ((C2 * 2 ^ g.t + c) % 2 ^ g.t) *
      colProd ρ rest ((C2 * 2 ^ g.t + c) / 2 ^ g.t))
    rw [eqB_split ρ X cb _ g.t C2 hc', d1, d2, hcb]
    ring

/-- The same product at coordinates that spell the number C of a column on the bits below lk. -/
theorem cols_bool (lk C : ℕ) (X : ℕ → E)
    (hX : ∀ b, b < lk → X b = if C.testBit b then oneE else zeroE) :
    ∀ (l : List (WsFac × WsGrp)) (cb : ℕ), (∀ y ∈ l, GrpOK y.2) → Runs (l.map (·.2)) cb →
    cb + (l.map (·.2.t)).sum ≤ lk →
    (l.map fun p => ρ.val (p.1.onColumns p.2 X)).prod = colProd ρ l (C / 2 ^ cb)
  | [], _, _, _, _ => by simp [colProd]
  | (x, g) :: rest, cb, hok, hr, hle => by
    have hg := hok (x, g) List.mem_cons_self
    have hcb : g.cb0 = cb := hr.1
    have hsum : (((x, g) :: rest).map (·.2.t)).sum = (rest.map (·.2.t)).sum + g.t := by
      rw [List.map_cons, List.sum_cons, Nat.add_comm]
    rw [hsum] at hle
    have hbit : ∀ i, i < g.t → cb + i < lk := by
      intro i hi
      omega
    have e1 : ρ.val (x.onColumns g X) = colHalf ρ x g (C / 2 ^ cb % 2 ^ g.t) := by
      refine onColumns_at ρ hg (Nat.mod_lt _ (Nat.pow_pos (by norm_num))) fun i hi => ?_
      have hi' : i < g.t := hi
      rw [hcb, hX _ (hbit i hi'), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      simp only [hi', decide_true, Bool.true_and]
      rw [Nat.add_comm cb i]
    rw [List.map_cons, List.prod_cons, e1,
      cols_bool lk C X hX rest (cb + g.t) (fun y hy => hok y (List.mem_cons_of_mem _ hy)) hr.2
        (by omega), Nat.pow_add, ← Nat.div_div_eq_div_mul]
    rfl

/-- wsEpsT is multilinear in the merge's point: its value at any point rm is the sum over the
columns C of the equality weight of C at rm, the first coordinate of rm with the top bit of C, times
its value at the point of zeros and ones that spells C. -/
theorem eps_multilinear {lay : WsLay} {c : WsClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    (hlen : c.f.length = u.g.length) (U : UnitOK lay.lk u) (rm : Array E) :
    ρ.val (wsEpsT lay c rm) = ∑ C ∈ range (2 ^ lay.lk),
      Blocks.eqN lay.lk 0 (pt ρ rm) C * ρ.val (wsEpsT lay c (bitsOf lay.lk C)) := by
  have hmap : (c.f.zip u.g).map (·.2) = u.g := List.map_snd_zip (by omega)
  have hok : ∀ y ∈ c.f.zip u.g, GrpOK y.2 := fun y hy => U.grp y.2 (by
    have h1 : y.2 ∈ (c.f.zip u.g).map (·.2) := List.mem_map_of_mem hy
    rw [hmap] at h1
    exact h1)
  have htsum : ((c.f.zip u.g).map (·.2.t)).sum = u.ncb := by
    have h1 : (((c.f.zip u.g).map (·.2)).map (·.t)).sum = (u.g.map (·.t)).sum := by rw [hmap]
    rw [U.ncb, ← h1, List.map_map]
    rfl
  have hruns : Runs ((c.f.zip u.g).map (·.2)) 0 := by
    rw [hmap]
    exact U.runs
  have hle2 : 2 ^ u.ncb ≤ 2 ^ lay.lk := Nat.pow_le_pow_right (by norm_num) U.le
  -- the value at a column
  have hbool : ∀ C, C < 2 ^ lay.lk → ρ.val (wsEpsT lay c (bitsOf lay.lk C)) =
      colProd ρ (c.f.zip u.g) C * if C < 2 ^ u.ncb then 1 else 0 := by
    intro C hC
    rw [wsEpsT_value ρ hu, tail_bits ρ hC
      (fun b => (bitsOf lay.lk C).getD (lay.lk - 1 - b) zeroE) (fun b hb => bitsOf_at hb),
      cols_bool ρ lay.lk C _ (fun b hb => bitsOf_at hb) _ 0 hok hruns
        (by rw [htsum, Nat.zero_add]; exact U.le), pow_zero, Nat.div_one]
  rw [← Finset.sum_subset (range_subset_range.mpr hle2)]
  · rw [wsEpsT_value ρ hu, cols_multi ρ _ _ 0 hok hruns, htsum, Finset.sum_mul]
    refine sum_congr rfl fun C hC => ?_
    have hC' : C < 2 ^ u.ncb := mem_range.mp hC
    have hsplit := eqB_split ρ (fun b => rm.getD (lay.lk - 1 - b) zeroE) 0 (lay.lk - u.ncb) u.ncb 0
      hC'
    rw [Nat.sub_add_cancel U.le, Nat.zero_mul, Nat.zero_add, Nat.zero_add] at hsplit
    have htail : ∏ i ∈ range (lay.lk - u.ncb),
        (1 - ρ.val (rm.getD (lay.lk - 1 - (u.ncb + i)) zeroE)) =
        eqB ρ (fun b => rm.getD (lay.lk - 1 - b) zeroE) u.ncb (lay.lk - u.ncb) 0 := by
      unfold eqB
      exact prod_congr rfl fun i _ => by simp
    rw [hbool C (lt_of_lt_of_le hC' hle2), if_pos hC', eqN_eqB, hsplit, htail]
    ring
  · intro C hC hC2
    rw [hbool C (mem_range.mp hC), if_neg (fun h => hC2 (mem_range.mpr h))]
    ring

/-- The equality weight of a column at the merge's point, in the order in which the pending row
carries the point: psi is rm reversed, so that coordinate b of psi goes with bit b of the column. -/
theorem eq_psi (rm : Array E) (C : ℕ) :
    Blocks.eqN rm.size 0 (pt ρ rm) C = ∏ b ∈ range rm.size,
      (if C.testBit b then ρ.val (rm.toList.reverse.getD b zeroE)
        else 1 - ρ.val (rm.toList.reverse.getD b zeroE)) := by
  rw [eqN_low_bits]
  refine prod_congr rfl fun b hb => ?_
  have hb' : b < rm.size := mem_range.mp hb
  have e : rm.toList.reverse.getD b zeroE = rm.getD (0 + (rm.size - 1 - b)) zeroE := by
    have h1 : rm.size - 1 - b < rm.size := by omega
    simp [List.getD_eq_getElem?_getD, Array.getD, hb', h1]
  rw [e]
  rfl

end Multi

/-! ## The function that the merge's sumcheck runs on -/

section Fm

variable {K : Type} [Field K] (ρ : Reading K)

/-- Row y of W read at the point rm: the sum over the columns C of the equality weight of C at rm
times the entry. -/
def rowAt (lk : ℕ) (rm : Array E) (W : Wm K) (y : ℕ) : K :=
  ∑ C ∈ range (2 ^ lk), Blocks.eqN lk 0 (pt ρ rm) C * W y C

/-- One claim's share of that function at the point rm, without its coefficient: the value of the
claim's factors on the columns at rm, times the sum over the unit's rows of the claim's coefficient
on the row, at the scalars 1, times the row read at rm. 0 if the layout has no such unit. -/
def shareAt (lay : WsLay) (W : Wm K) (rm : Array E) (c : WsClaim) : K :=
  match lay.U[c.ui]? with
  | none => 0
  | some u => ρ.val (wsEpsT lay c rm) * ∑ y ∈ range u.rows,
      ρ.val ((wsGamma u (wsRowPart lay c oneE) oneE).getD y zeroE) *
        rowAt ρ lay.lk rm W (u.off + y)

/-- The function at the point rm: the sum over the claims, each with its coefficient, of the
coefficient times the claim's share. -/
def fmAt (lay : WsLay) (W : Wm K) (cr : List (WsClaim × E)) (rm : Array E) : K :=
  (cr.map fun y => ρ.val y.2 * shareAt ρ lay W rm y.1).sum

/-- A row read at the point that spells a column is the entry in that column. -/
theorem rowAt_bool {lk C : ℕ} (hC : C < 2 ^ lk) (W : Wm K) (y : ℕ) :
    rowAt ρ lk (bitsOf lk C) W y = W y C := by
  unfold rowAt
  have h : ∀ C' ∈ range (2 ^ lk), Blocks.eqN lk 0 (pt ρ (bitsOf lk C)) C' * W y C' =
      if C' = C then W y C' else 0 := by
    intro C' hC'
    rw [eqN_bool lk 0 _ hC (mem_range.mp hC') ?_]
    · by_cases e : C' = C
      · rw [if_pos e, if_pos e, one_mul]
      · rw [if_neg e, if_neg e, zero_mul]
    · intro s hs
      have h1 := bitsOf_at (lk := lk) (C := C) (b := lk - 1 - s) (by omega)
      rw [show lk - 1 - (lk - 1 - s) = s by omega] at h1
      unfold pt
      rw [Nat.zero_add, h1]
      cases C.testBit (lk - 1 - s)
      · simp [ρ.zero]
      · simp [ρ.one]
  rw [sum_congr rfl h, Finset.sum_ite_eq', if_pos (mem_range.mpr hC)]

/-- A sum over a finite set of sums over a list, with the two sums exchanged. -/
theorem sum_list_comm {α : Type} (s : Finset ℕ) (f : ℕ → α → K) : ∀ l : List α,
    ∑ C ∈ s, (l.map (f C)).sum = (l.map fun a => ∑ C ∈ s, f C a).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, sum_list_comm s f l]

variable {ρ} in
/-- The sum of the function over the cube. For claims that pass wsClaimShape on units as the layout
leaves them: the sum over all columns C of the function at the point that spells C is the sum over
the claims of the coefficient times the sum that the claim speaks of. -/
theorem merge_sum (hρ : Numerals ρ) {lay : WsLay} (W : Wm K) (cr : List (WsClaim × E))
    (hcl : ∀ y ∈ cr, ∃ u, lay.U[y.1.ui]? = some u ∧ wsClaimShape lay y.1 = .ok () ∧
      UnitOK lay.lk u) :
    ∑ C ∈ range (2 ^ lay.lk), fmAt ρ lay W cr (bitsOf lay.lk C) =
      (cr.map fun y => ρ.val y.2 * claimVal ρ lay W y.1).sum := by
  unfold fmAt
  rw [sum_list_comm]
  refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
  obtain ⟨u, hu, hs, U⟩ := hcl y hy
  rw [← Finset.mul_sum]
  congr 1
  have h := claim_cells hρ hu hs U W oneE oneE
  rw [ρ.one, one_mul, one_mul] at h
  rw [← h]
  refine sum_congr rfl fun C hC => ?_
  unfold shareAt
  rw [hu]
  show ρ.val (wsEpsT lay y.1 (bitsOf lay.lk C)) * ∑ y' ∈ range u.rows, _ = _
  rw [Finset.mul_sum]
  refine sum_congr rfl fun y' _ => ?_
  rw [rowAt_bool ρ (mem_range.mp hC)]
  ring

/-- The form that the sum of the merge's sumcheck must equal, in a world: the sum of the
coefficients times the hidden values under the claims' slots. -/
theorem wsForkStart_value (W : World K) (sv : Array ℕ) (rho : Array E) :
    (wsForkStart sv rho).value ρ W =
      ((sv.zip rho).toList.map fun y => ρ.val y.2 * W.slot y.1).sum := by
  unfold wsForkStart
  rw [← Array.foldl_toList]
  have H : ∀ (l : List (ℕ × E)) (s : Aff),
      (l.foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) s).value ρ W =
        s.value ρ W + (l.map fun y => ρ.val y.2 * W.slot y.1).sum := by
    intro l
    induction l with
    | nil =>
      intro s
      simp
    | cons y l ih =>
      intro s
      rw [List.foldl_cons, ih, Aff.value_addMul, Aff.value_slot, List.map_cons, List.sum_cons]
      ring
  rw [H, Aff.value_empty, zero_add]

/-- Two lists whose members correspond, each paired with one list of coefficients. -/
theorem sum_zip_congr {α β : Type} (f : α → K) (g : β → K) : ∀ (l1 : List α) (l2 : List β),
    List.Forall₂ (fun a b => f a = g b) l1 l2 → ∀ r : List E,
    ((l1.zip r).map fun y => ρ.val y.2 * f y.1).sum =
      ((l2.zip r).map fun y => ρ.val y.2 * g y.1).sum
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, [] => by simp
  | _ :: l1, _ :: l2, .cons h t, x :: r => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    rw [h, sum_zip_congr f g l1 l2 t r]

variable {ρ} in
/-- The form that the sum of the merge's sumcheck must equal. If in the world Wd the hidden value
under the slot of each claim is the sum that the claim speaks of in the matrix W, then that form,
wsForkStart, is worth the sum of the function over the points that spell the columns. This is the
direction of completeness, and a corollary; a step towards soundness would use merge_sum with
wsForkStart_value, which give the difference of the two as the sum of the coefficients times "hidden
value less the claim's sum". The verifier's running claim does not begin at this form's value: it
begins at a sent sum plus a challenge times the form's public part, which is made of the values that
were sent (pscBegin, OnBytes/Model/Psc.lean). cl, sv, rho: the claims, their slots and their
coefficients, as wsForkEnd has them. -/
theorem merge_start (hρ : Numerals ρ) {lay : WsLay} (W : Wm K) (Wd : World K)
    (cl : Array WsClaim) (sv : Array ℕ) (rho : Array E)
    (hcl : ∀ c ∈ cl, ∃ u, lay.U[c.ui]? = some u ∧ wsClaimShape lay c = .ok () ∧ UnitOK lay.lk u)
    (hslot : List.Forall₂ (fun s c => Wd.slot s = claimVal ρ lay W c) sv.toList cl.toList) :
    (wsForkStart sv rho).value ρ Wd =
      ∑ C ∈ range (2 ^ lay.lk), fmAt ρ lay W (cl.zip rho).toList (bitsOf lay.lk C) := by
  rw [wsForkStart_value, merge_sum hρ W _ (fun y hy => hcl y.1 (by
    rw [Array.toList_zip] at hy
    exact Array.mem_def.mpr (List.of_mem_zip hy).1)), Array.toList_zip, Array.toList_zip]
  exact sum_zip_congr ρ _ _ _ _ hslot _

end Fm

/-! ## The coefficients on the rows of W that the claims add up to -/

section Gamma

variable {K : Type} [Field K] (ρ : Reading K)

/-- Adding x to member p of an array adds x H p to the sum of the members times H. -/
theorem modify_sum (G : Array E) {p : ℕ} (hp : p < G.size) (x : E) (H : ℕ → K) :
    ∑ y ∈ range G.size, ρ.val ((G.modify p fun z => addE z x).getD y zeroE) * H y =
      ∑ y ∈ range G.size, ρ.val (G.getD y zeroE) * H y + ρ.val x * H p := by
  have h : ∀ y ∈ range G.size, ρ.val ((G.modify p fun z => addE z x).getD y zeroE) * H y =
      ρ.val (G.getD y zeroE) * H y + if y = p then ρ.val x * H y else 0 := by
    intro y hy
    have hy' : y < G.size := mem_range.mp hy
    by_cases e : y = p
    · subst e
      rw [if_pos rfl]
      have e1 : (G.modify y fun z => addE z x).getD y zeroE = addE (G.getD y zeroE) x := by
        simp [Array.getD, hy', Array.getElem_modify]
      rw [e1, ρ.add]
      ring
    · rw [if_neg e, add_zero]
      have e1 : (G.modify p fun z => addE z x).getD y zeroE = G.getD y zeroE := by
        have e' : p ≠ y := fun h => e h.symm
        simp [Array.getD, hy', Array.getElem_modify, e']
      rw [e1]
  rw [sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (mem_range.mpr hp)]

/-- Adding the members of a list to the members p, p + 1 and so on of an array. -/
theorem addAt_sum (H : ℕ → K) : ∀ (l : List E) (G : Array E) (p : ℕ), p + l.length ≤ G.size →
    (l.foldl (fun (s : Array E × ℕ) x => (s.1.modify s.2 fun y => addE y x, s.2 + 1))
      (G, p)).1.size = G.size ∧
    ∑ y ∈ range G.size, ρ.val ((l.foldl
      (fun (s : Array E × ℕ) x => (s.1.modify s.2 fun y => addE y x, s.2 + 1))
      (G, p)).1.getD y zeroE) * H y =
      ∑ y ∈ range G.size, ρ.val (G.getD y zeroE) * H y +
        ∑ j ∈ range l.length, ρ.val (l.getD j zeroE) * H (p + j)
  | [], G, p, _ => by simp
  | x :: l, G, p, h => by
    have hl : (x :: l).length = l.length + 1 := rfl
    rw [hl] at h
    have hs : (G.modify p fun y => addE y x).size = G.size := by simp
    obtain ⟨i1, i2⟩ := addAt_sum H l (G.modify p fun y => addE y x) (p + 1) (by rw [hs]; omega)
    rw [hs] at i1 i2
    rw [List.foldl_cons]
    refine ⟨i1, ?_⟩
    rw [i2, modify_sum ρ G (by omega) x H, hl, Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun j _ => by
      rw [show p + 1 + j = p + (j + 1) by omega]
      rfl

/-- What wsGammaAdd adds: the claim's coefficients, from the unit's first row on. -/
theorem gammaAdd_sum {lay : WsLay} {c : WsRecClaim} {u : WsUnit} (hu : lay.U[c.ui]? = some u)
    {Gam G' : Array E} {wgt : E} (h : wsGammaAdd Gam lay c wgt = .ok G') (H : ℕ → K) :
    G'.size = Gam.size ∧ (wsGamma u c wgt).size = u.rows ∧
    ∑ y ∈ range Gam.size, ρ.val (G'.getD y zeroE) * H y =
      ∑ y ∈ range Gam.size, ρ.val (Gam.getD y zeroE) * H y +
        ∑ j ∈ range u.rows, ρ.val ((wsGamma u c wgt).getD j zeroE) * H (u.off + j) := by
  unfold wsGammaAdd at h
  rw [hu] at h
  have h2 : (if ((wsGamma u c wgt).size != u.rows || c.f.length != u.g.length ||
        decide (Gam.size < u.off + u.rows)) = true then
      (throw "internal-gamma-rows" : Except String (Array E)) else
      pure ((wsGamma u c wgt).foldl
        (fun (s : Array E × ℕ) x => (s.1.modify s.2 fun y => addE y x, s.2 + 1))
        (Gam, u.off)).1) = .ok G' := h
  by_cases hc : ((wsGamma u c wgt).size != u.rows || c.f.length != u.g.length ||
      decide (Gam.size < u.off + u.rows)) = true
  · rw [if_pos hc] at h2
    cases h2
  · rw [if_neg hc] at h2
    have e := Except.ok.inj h2
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, not_not,
      not_lt] at hc
    obtain ⟨⟨c1, -⟩, c3⟩ := hc
    rw [← Array.foldl_toList] at e
    obtain ⟨a1, a2⟩ := addAt_sum ρ H (wsGamma u c wgt).toList Gam u.off
      (by rw [Array.length_toList, c1]; exact c3)
    rw [e] at a1 a2
    refine ⟨a1, c1, ?_⟩
    rw [a2, Array.length_toList, c1]
    congr 1
    exact sum_congr rfl fun j _ => by rw [← toArray_getD, Array.toArray_toList]

/-- The coefficients depend on the digits' scalars linearly: if each member of d reads as a times
the member of d', the sum of the coefficients times any H is a times the other sum. -/
theorem gamOf_scale (a : K) : ∀ (l : List (WsFac × WsGrp)) (d d' : Array E), d.size = d'.size →
    (∀ q, q < d.size → ρ.val (d.getD q zeroE) = a * ρ.val (d'.getD q zeroE)) → ∀ H : ℕ → K,
    (gamOf l d).size = (gamOf l d').size ∧
    ∑ j ∈ range (gamOf l d).size, ρ.val ((gamOf l d).getD j zeroE) * H j =
      a * ∑ j ∈ range (gamOf l d').size, ρ.val ((gamOf l d').getD j zeroE) * H j
  | [], d, d', hs, hd, H => by
    refine ⟨hs, ?_⟩
    show ∑ j ∈ range d.size, _ = a * ∑ j ∈ range d'.size, _
    rw [← hs, Finset.mul_sum]
    refine sum_congr rfl fun q hq => ?_
    show ρ.val (d.getD q zeroE) * H q = a * (ρ.val (d'.getD q zeroE) * H q)
    rw [hd q (mem_range.mp hq), mul_assoc]
  | (x, g) :: rest, d, d', hs, hd, H => by
    obtain ⟨s1, -⟩ := gamOf_scale a rest d d' hs hd H
    refine ⟨?_, ?_⟩
    · show (wsOuter (gamOf rest d) _).size = (wsOuter (gamOf rest d') _).size
      rw [wsOuter_size, wsOuter_size, s1]
    · show ∑ j ∈ range (wsOuter (gamOf rest d) ((x.onRows g).table g)).size,
          ρ.val ((wsOuter (gamOf rest d) ((x.onRows g).table g)).getD j zeroE) * H j =
        a * ∑ j ∈ range (wsOuter (gamOf rest d') ((x.onRows g).table g)).size,
          ρ.val ((wsOuter (gamOf rest d') ((x.onRows g).table g)).getD j zeroE) * H j
      rw [sum_wsOuter, sum_wsOuter]
      have i2 := (gamOf_scale a rest d d' hs hd fun i =>
        ∑ q ∈ range ((x.onRows g).table g).size,
          ρ.val (((x.onRows g).table g).getD q zeroE) *
            H (i * ((x.onRows g).table g).size + q)).2
      simp only [Finset.mul_sum, mul_assoc] at i2 ⊢
      exact i2

variable {ρ} in
/-- The scalar ka of what is left of a claim comes out of the sum of its coefficients. -/
theorem wsGamma_scale (hρ : Numerals ρ) {lay : WsLay} {c : WsClaim} {u : WsUnit}
    (hu : lay.U[c.ui]? = some u) (ka : E) (H : ℕ → K) :
    (wsGamma u (wsRowPart lay c ka) oneE).size = (wsGamma u (wsRowPart lay c oneE) oneE).size ∧
    ∑ j ∈ range (wsGamma u (wsRowPart lay c ka) oneE).size,
      ρ.val ((wsGamma u (wsRowPart lay c ka) oneE).getD j zeroE) * H j =
    ρ.val ka * ∑ j ∈ range (wsGamma u (wsRowPart lay c oneE) oneE).size,
      ρ.val ((wsGamma u (wsRowPart lay c oneE) oneE).getD j zeroE) * H j := by
  rw [wsGamma_eq hu, wsGamma_eq hu]
  refine gamOf_scale ρ (ρ.val ka) _ _ _ (by simp [wsDigits_length]) (fun q hq => ?_) H
  have hq' : q < u.nlw := by simpa [wsDigits_length] using hq
  rw [toArray_getD, toArray_getD, wsDigits_value hρ _ _ _ hq', wsDigits_value hρ _ _ _ hq', ρ.mul,
    ρ.mul, ρ.one]
  ring

variable {ρ} in
/-- The row weights of the pending row. cr: the claims with their coefficients; recs, what the merge
leaves of them at the point rm, each under the scalar "coefficient times the value of the claim's
factors on the columns at rm"; Gam: what folding wsGammaAdd over recs makes of an array G0. Then the
sum over the rows of Gam's member times any H is that sum for G0, plus the sum over the claims of
the scalar times the sum over the unit's rows of the claim's coefficient at the scalars 1 times H at
the row. -/
theorem gamma_fold (hρ : Numerals ρ) (lay : WsLay) (rm : Array E) (H : ℕ → K) :
    ∀ (cr : List (WsClaim × E)) (G0 Gam : Array E),
    (cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))).foldlM
      (fun G c => wsGammaAdd G lay c oneE) G0 = .ok Gam →
    Gam.size = G0.size ∧
    ∑ y ∈ range G0.size, ρ.val (Gam.getD y zeroE) * H y =
      ∑ y ∈ range G0.size, ρ.val (G0.getD y zeroE) * H y +
        (cr.map fun y => ρ.val y.2 * (match lay.U[y.1.ui]? with
          | none => 0
          | some u => ρ.val (wsEpsT lay y.1 rm) * ∑ j ∈ range u.rows,
              ρ.val ((wsGamma u (wsRowPart lay y.1 oneE) oneE).getD j zeroE) *
                H (u.off + j))).sum
  | [], G0, Gam, h => by
    have e : G0 = Gam := Except.ok.inj h
    subst e
    simp
  | y :: cr, G0, Gam, h => by
    rw [List.map_cons, List.foldlM_cons] at h
    obtain ⟨G1, h1, h2⟩ := ok_of_bind h
    have hui : (wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))).ui = y.1.ui := by
      unfold wsRowPart
      split <;> rfl
    cases hu : lay.U[y.1.ui]? with
    | none =>
      unfold wsGammaAdd at h1
      rw [hui, hu] at h1
      cases h1
    | some u =>
      obtain ⟨a1, a2, a3⟩ := gammaAdd_sum ρ (by rw [hui]; exact hu) h1 H
      obtain ⟨b1, b2⟩ := gamma_fold hρ lay rm H cr G1 Gam h2
      obtain ⟨s1, s2⟩ := wsGamma_scale hρ hu (mulE y.2 (wsEpsT lay y.1 rm))
        (fun j => H (u.off + j))
      rw [a1] at b1 b2
      refine ⟨b1, ?_⟩
      rw [b2, a3, List.map_cons, List.sum_cons, add_assoc]
      congr 1
      congr 1
      rw [a2] at s2
      rw [← s1, a2] at s2
      rw [s2, ρ.mul]
      simp only [hu]
      ring

variable {ρ} in
/-- The function at the merge's point is the pending row's left form on W. With Gam folded from an
array of n zeros as wsPending folds it: the function at rm is the sum over the rows y below n of
Gam's member times row y of W read at rm. -/
theorem pending_gamma (hρ : Numerals ρ) (lay : WsLay) (W : Wm K) (rm : Array E)
    (cr : List (WsClaim × E)) {n : ℕ} {Gam : Array E}
    (h : (cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))).foldlM
      (fun G c => wsGammaAdd G lay c oneE) (Array.replicate n zeroE) = .ok Gam) :
    fmAt ρ lay W cr rm =
      ∑ y ∈ range n, ρ.val (Gam.getD y zeroE) * rowAt ρ lay.lk rm W y := by
  obtain ⟨-, h2⟩ := gamma_fold hρ lay rm (rowAt ρ lay.lk rm W) cr _ Gam h
  rw [Array.size_replicate] at h2
  have h0 : ∑ y ∈ range n, ρ.val ((Array.replicate n zeroE).getD y zeroE) *
      rowAt ρ lay.lk rm W y = 0 := by
    refine sum_eq_zero fun y hy => ?_
    have e : (Array.replicate n zeroE).getD y zeroE = zeroE := by
      simp [Array.getD, mem_range.mp hy]
    rw [e, ρ.zero, zero_mul]
  rw [h2, h0, zero_add]
  rfl

end Gamma

#print axioms eps_multilinear
#print axioms eq_psi
#print axioms merge_sum
#print axioms wsForkStart_value
#print axioms merge_start
#print axioms gamma_fold
#print axioms pending_gamma

end OnBytes.Road
