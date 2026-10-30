-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysEnd.lean: what the end of the batched sumcheck of a layer sub-proof leaves.

Every statement in this file is on the verifier's side alone. The only name of the library that
stands in a statement is the kernel Blocks.eqN. How the verifier's quantities stand to the
library's (SA, SB, AipV, BipV, offP and the order of the list pans in Inst/Model/FF/Objects.lean)
is said below by reading alone: no theorem here compares them.

The summand of the batched sumcheck is a product A B of two long vectors. A panel takes a stretch
of places in them (SBlk in OnBytes/Model/LayerPanels.lean): place off + i 2^wy + yv is the entry of
the panel at row i and column yv. At the sumcheck's end point the verifier gathers, panel by panel,
two forms and two elements of the field (stackEndOf and stackEnd there), and takes the product of
the two elements for the summand. This file says what the four are worth, and of which two vectors
the two elements would be the extensions if they were computed from the hidden end values; what
they are as the verifier computes them, from the values that were sent, is said beside it.

The file goes in six steps.
 1. The verifier's equality weights over a stretch of bits, read in K (eqR).
 2. What one panel adds, in each of the five branches of stackEndOf, and in all (stackEndOf_rd).
 3. What all panels add (stackEnd_rd).
 4. The meaning, on any end values of the never-sent vectors and of the weight claims that are true
    of two families of vectors (EndsTrue). For one panel: what it adds to a side is the weight of
    the panel's number times the sum over its places of the place's weight times the side
    (panel_mean). For all: the form's value plus what the panels add at these end values is the
    extension of a long vector (ends_mean; on the sent values: stackEnd_mean). The hypothesis on
    the end values can be met (ends_met, shown_met). What the verifier's own two elements are if
    each sent value is a hidden one plus a factor times a mask entry: stackEnd_affine; for that the
    panels must read inside the two arrays, which the verifier's own panels do (reads_inside).
 5. The places that placePanels gives do not overlap (placePanels_apart), so the sum over the
    places of the product of the two long vectors is the sum of the panels' shares (placed_sum);
    and at every place the product of the two sides is the claim's weight times the call's weight
    times the row's weight times what is left of the two sides (side_mul, share_rows).
 6. All of it in one statement, on any end values: for any list of panels that have the shape
    (stack_at), for the verifier's own list under the caller's own test of the number of places
    (stack_hidden), and there at the hidden values of a world (stack_slots); with the masks:
    stack_masked. The same on the sent values: stack_whole, stack_own.

Sent and hidden. What follows is read in texts of the verifier which no theorem here unfolds.
hearStack (OnBytes/Model/Layer.lean) gives stackEnd the values that were SENT for the end values of
the two sides, of the never-sent vectors and of the weight claims (SubM.shown, shownRun): an array
of NVIRT values, the number that nVirt copies, and one of NCLp values, after the test that the
number of the next claim behind the last panel is NCLp. The check of a layer sub-proof in the same
file adds the two claims Aff.slot sA0 - fin.Alin and Aff.slot sB0 - fin.Blin: they speak of the
HIDDEN values under the slots. By the docstring of pscEnds (OnBytes/Model/Psc.lean) what was sent
is the hidden value plus beta times a mask entry, where beta is drawn by a rule that never gives 0,
and is 0 in the dry run. So "the sent value of a side is the value of its form" and "the sent end
values are true of the vectors that the sub-proof means" do not follow from the verifier's claims,
and stack_whole and stack_own, which ask them, meet the caller's own run only where the masks'
share is 0. stack_slots asks the two claims as the caller adds them, and EndsTrue of the hidden
values. Its left sides, AsAt and BsAt at the hidden values, are not the elements that the verifier
computes; stackEnd_affine says how the two stand to each other, and stack_masked joins the two on
the verifier's own list. More sent values are left as they are: ALL values that the second token
sumcheck sent (shownT in hearStack and in panelT, OnBytes/Model/LayerPanels.lean) stand in the long
A vector as they were sent, and in the form Alin as constants: as the selector's factors b.sl in
the panels of the routed products G, U, D, and as the whole A sides of the panels N1, N2, XR, DD,
MR. By the text of claimsTerms (OnBytes/Model/Layer.lean) the verifier's claims on these values
speak of the hidden ones. They stand in aG, c1K and sideK as the verifier has them, throughout this
file.

Against the library, by reading. In four of the five branches the verifier's two sides have the
shape of the library's, factor by factor. Whether each factor is the library's number (the claim's
weight, the call's weight, the rows' weights) has not been compared. In the fifth, the down
product's panel, whose whole A side is a never-sent vector, neither side has the library's shape,
for two reasons. First, the verifier has the call's weight and the rows' weights on the B side, the
library on the A side. Second, on a layer with routed experts the library cuts both sides at column
fe, the number of hidden units that are not routed. The verifier's row has f columns on every
layer, and its never-sent vector holds the gated products in the columns fe to f - 1 of such a row
too. Nothing on the A side makes the product of the two sides 0 there. It is 0 if the vector of the
row's weight claim is 0 there, which is left to the part of the sub-proof that settles the weight
claims. So for this panel one can hope for the equality of the sums of the products of the two
sides, not of the sides. side_mul shows that in every panel of the verifier, this one too, the
product at a place has one shape. That this is the shape of the library's product is by reading.

The import of OnBytes.Slice.ProgCodes is for one fact on the rounded-up logarithm
(le_two_pow_ceilLog2).

Main definitions: eqR; rd, valsOf, dEnd; gsum, PanelOK; aG, bG, EndsTrue, ShownTrue; vecOf, AsAt,
BsAt, ReadsIn, shareOf; nRows, rowW, aRaw, bRaw; Shape; nVirt, ReadsAll. Main theorems:
eqLow_value, eqLowAt_value, eqR_split, eqR_lib; end_tri_virt, end_tri_forms, end_plain_virt,
end_plain_weights, end_plain_forms, stackEndOf_rd; stackEnd_rd; PanelOK.places, panel_mean,
stackEnd_mean, ends_met, shown_met; dEnd_forms, dEnd_linear, stackEnd_four, ends_mean, dEnd_congr,
AsAt_congr, AsAt_linear, stackEnd_affine; sum_vec_mul, placePanels_apart, placed_list, placed_sum,
side_mul, share_rows; shape_plain, shape_tri, shape_panels, placed_ok, reads_inside, reads_placed,
stack_at, stack_hidden, stack_slots, stack_masked, stack_whole, stack_own.

What is not claimed. Every theorem on the verifier's functions begins "if the function returns a
value": none says that it does. That the end values of the never-sent vectors and of the weight
claims are true of the vectors that the sub-proof means (EndsTrue) is a hypothesis; whether other
parts of the sub-proof show it of the hidden values is not looked at. What such a vector holds is
not said anywhere here: where a panel has such vectors on both sides, the products are whatever the
two vectors hold, in every column below 2^wy. That the two end values of the sides are the values
of the two forms, and that there is one challenge for each bit, are hypotheses. How the sumcheck's
last test, which the verifier makes on the product of its own two elements, stands to the product
of AsAt and BsAt at the hidden values is not looked at. Nothing is said about the sumcheck's
rounds, about probability, or about what a verifier's acceptance shows. See also
Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysPan
import OnBytes.Slice.ProgCodes

set_option autoImplicit false

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab eqOne eqIndexOK eqLow eqLowAt)
open OnBytes.Model.Layer (SBlk StackEnd stackEndOf stackEnd Lay placePanels Panels PanelEnv panelA
  panelT panelsA panelsT)

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-! ## The equality weights over a stretch of bits -/

/-- The equality weight of the number c over the bits lo to hi - 1, where rs[v] is the coordinate of
bit v: the product over the bits j below hi - lo of rs[lo + j] if bit j of c is set, and of
1 - rs[lo + j] if not. It is written with the library's kernel, whose first coordinate belongs to
the top bit. -/
def eqR (rs : Array E) (lo hi c : ℕ) : K :=
  Blocks.eqN (hi - lo) 0 (fun j => ρ.val (rs.getD (hi - 1 - j) zeroE)) c

/-- The stretch of coordinates, turned round, has hi - lo members. -/
theorem rev_size (rs : Array E) {lo hi : ℕ} (hhi : hi ≤ rs.size) :
    (rs.extract lo hi).reverse.size = hi - lo := by
  rw [Array.size_reverse, Array.size_extract]
  omega

/-- Member j of the stretch, turned round, is rs[hi - 1 - j]. -/
theorem rev_getD (rs : Array E) {lo hi : ℕ} (hhi : hi ≤ rs.size) {j : ℕ} (hj : j < hi - lo) :
    (rs.extract lo hi).reverse.getD j zeroE = rs.getD (hi - 1 - j) zeroE := by
  have h2 : hi - 1 - j < rs.size := by omega
  have h3 : (rs.extract lo hi).size = hi - lo := by rw [Array.size_extract]; omega
  have e : lo + (hi - lo - 1 - j) = hi - 1 - j := by omega
  simp [Array.getD, h2, h3, e, hj]

/-- The library's kernel at the stretch, turned round, is eqR. -/
theorem eqN_rev (rs : Array E) {lo hi : ℕ} (hhi : hi ≤ rs.size) (c : ℕ) :
    Blocks.eqN (hi - lo) 0 (pt ρ (rs.extract lo hi).reverse) c = eqR ρ rs lo hi c := by
  unfold eqR
  refine eqN_congr' _ _ (fun j hj => ?_) c
  unfold pt
  rw [Nat.zero_add, rev_getD rs hhi hj]

/-- Entry c of the verifier's table over the bits lo to hi - 1. -/
theorem eqLow_value (rs : Array E) {lo hi : ℕ} (hhi : hi ≤ rs.size) {c : ℕ}
    (hc : c < 2 ^ (hi - lo)) : ρ.val ((eqLow rs lo hi).getD c zeroE) = eqR ρ rs lo hi c := by
  unfold eqLow
  rw [eqTab_value ρ _ c (by rw [rev_size rs hhi]; exact hc), rev_size rs hhi, eqN_rev ρ rs hhi]

/-- The fold of eqOne, on a list, from any state: coordinate number t goes with bit n - 1 - t. -/
theorem foldOne (c : ℕ) : ∀ (l : List E) (s : E) (n : ℕ),
    ρ.val (l.foldl (fun (s : E × ℕ) zv =>
      (if c.testBit (s.2 - 1) then mulE s.1 zv else subE s.1 (mulE s.1 zv), s.2 - 1)) (s, n)).1 =
      ρ.val s * ∏ t ∈ range l.length,
        (if c.testBit (n - 1 - t) then ρ.val (l.getD t zeroE) else 1 - ρ.val (l.getD t zeroE))
  | [], s, n => by simp
  | zv :: l, s, n => by
    rw [List.foldl_cons, foldOne c l, List.length_cons, Finset.prod_range_succ']
    have e : ∀ t, n - 1 - (t + 1) = n - 1 - 1 - t := fun t => by omega
    have P : ∀ t, (if c.testBit (n - 1 - (t + 1)) then ρ.val ((zv :: l).getD (t + 1) zeroE)
        else 1 - ρ.val ((zv :: l).getD (t + 1) zeroE)) =
        (if c.testBit (n - 1 - 1 - t) then ρ.val (l.getD t zeroE)
        else 1 - ρ.val (l.getD t zeroE)) := fun t => by rw [e t, List.getD_cons_succ]
    simp only [P, List.getD_cons_zero, Nat.sub_zero]
    by_cases hb : c.testBit (n - 1) = true
    · simp only [hb, if_true, ρ.mul]
      ring
    · simp only [hb, Bool.false_eq_true, if_false, ρ.sub, ρ.mul]
      ring

/-- A single entry, computed without the table, where the index is in range. -/
theorem eqOne_value (z : Array E) (c : ℕ) (hok : eqIndexOK z c = true) :
    ρ.val (eqOne z c) = Blocks.eqN z.size 0 (pt ρ z) c := by
  unfold eqOne
  rw [if_pos hok, ← Array.foldl_toList]
  have r := foldOne ρ c z.toList oneE z.size
  rw [ρ.one, one_mul] at r
  refine r.trans ?_
  unfold Blocks.eqN pt
  rw [Array.length_toList]
  refine prod_congr rfl fun t _ => ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- Entry c over the bits lo to hi - 1, computed without the table, under the test that the verifier
makes. -/
theorem eqLowAt_value (rs : Array E) {lo hi : ℕ} (hhi : hi ≤ rs.size) {c : ℕ}
    (hok : eqIndexOK (rs.extract lo hi) c = true) :
    ρ.val (eqLowAt rs lo hi c) = eqR ρ rs lo hi c := by
  have hok' : eqIndexOK (rs.extract lo hi).reverse c = true := by
    unfold eqIndexOK at hok ⊢
    rw [Array.size_reverse]
    exact hok
  unfold eqLowAt
  rw [eqOne_value ρ _ c hok', rev_size rs hhi, eqN_rev ρ rs hhi]

/-- The weight over the bits lo to hi - 1 is the product of the weight over the bits from mid on and
the weight over the bits below mid. -/
theorem eqR_split (rs : Array E) {lo mid hi : ℕ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) (c : ℕ) {c' : ℕ}
    (hc' : c' < 2 ^ (mid - lo)) :
    eqR ρ rs lo hi (c * 2 ^ (mid - lo) + c') = eqR ρ rs mid hi c * eqR ρ rs lo mid c' := by
  unfold eqR
  have e : hi - lo = (hi - mid) + (mid - lo) := by omega
  rw [e, Blocks.eqN_append' (E := K) _ _ _ _ c hc', Nat.zero_add,
    ← eqN_shift' (mid - lo) (hi - mid)]
  congr 1
  refine eqN_congr' _ _ (fun j hj => ?_) c'
  have e2 : hi - 1 - (hi - mid + (0 + j)) = mid - 1 - (0 + j) := by omega
  show ρ.val (rs.getD (hi - 1 - (hi - mid + (0 + j))) zeroE) = _
  rw [e2]

/-! ## Folds -/

/-- A sum over a list of the first n numbers is the sum over the range. -/
theorem list_range_sumM {M : Type} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ x ∈ range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A fold of steps that may refuse: if the step at x adds g x to a state's measure, the fold adds
the sum. -/
theorem foldlM_add {σ α M : Type} [AddCommMonoid M] (val : σ → M) (step : σ → α → Option σ)
    (g : α → M) (H : ∀ x s s', step s x = some s' → val s' = val s + g x) :
    ∀ (l : List α) (s a : σ), l.foldlM step s = some a → val a = val s + (l.map g).sum
  | [], s, a, h => by
    have hs : s = a := by simpa using h
    subst hs
    simp
  | x :: l, s, a, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s', hq, h2⟩ := bind_some h
    rw [foldlM_add val step g H l s' a h2, H x s s' hq, List.map_cons, List.sum_cons, add_assoc]

/-- The same for a fold of steps that do not refuse. -/
theorem foldl_add {σ α M : Type} [AddCommMonoid M] (val : σ → M) (step : σ → α → σ)
    (g : α → M) (H : ∀ x s, val (step s x) = val s + g x) :
    ∀ (l : List α) (s : σ), val (l.foldl step s) = val s + (l.map g).sum
  | [], s => by simp
  | x :: l, s => by
    rw [List.foldl_cons, foldl_add val step g H l, H, List.map_cons, List.sum_cons, add_assoc]

/-! ## The five numbers of a StackEnd, and what one panel adds to them -/

/-- The five numbers of a StackEnd: the values of the two forms, the readings of the two elements of
the field, and the number of bits of the down product's panel. -/
def rd (s : StackEnd) : K × K × K × K × ℕ :=
  (s.Alin.value ρ W, s.Blin.value ρ W, ρ.val s.As, ρ.val s.Bs, s.wD)

variable {ρ W} in
/-- Two states whose five numbers differ by five given numbers. -/
theorem rd_ext {s s' : StackEnd} {a b c d : K} {e : ℕ}
    (h1 : s'.Alin.value ρ W = s.Alin.value ρ W + a) (h2 : s'.Blin.value ρ W = s.Blin.value ρ W + b)
    (h3 : ρ.val s'.As = ρ.val s.As + c) (h4 : ρ.val s'.Bs = ρ.val s.Bs + d)
    (h5 : s'.wD = s.wD + e) : rd ρ W s' = rd ρ W s + (a, b, c, d, e) := by
  unfold rd
  rw [h1, h2, h3, h4, h5]
  rfl

/-- The value of a form that may be absent: 0 if it is. -/
def ov (o : Option Aff) : K :=
  match o with
  | some f => f.value ρ W
  | none => 0

/-- The value of a panel's side at (row, column): 0 if the side is not given as a form. -/
def sideK (S : Option (ℕ → ℕ → Option Aff)) (i yv : ℕ) : K :=
  match S with
  | some A => ov ρ W (A i yv)
  | none => 0

section Parts

variable (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E) (h1 vv : ℕ → K) (b : SBlk)

/-- The weight of the panel's number among the stretches of its size. -/
def sbK : K := ρ.val (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
/-- The weight of column yv. -/
def eyK (yv : ℕ) : K := ρ.val ((eqLow rs 0 b.wy).getD yv zeroE)
/-- The weight of row i. -/
def eiK (i : ℕ) : K := ρ.val ((eqLow rs b.wy b.w).getD i zeroE)
/-- The weight of the panel's claim. -/
def omK : K := ρ.val (om.getD b.claim zeroE)
/-- The public weight of row i. -/
def wtK (i : ℕ) : K := ρ.val (b.wt.getD i zeroE)

/-- For a panel with the selector: all factors of the A side that do not depend on the column, as
the verifier computes them. -/
def c1E : E :=
  mulE (mulE (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (om.getD b.claim zeroE)) b.ec)
    (b.wt.getD 0 zeroE))
    ((List.range y.h.NE).foldl
      (fun a e => addE a (mulE (b.sl.getD e zeroE) ((eqLow rs b.wy b.w).getD e zeroE))) zeroE)

/-- The same, read in K. -/
def c1K : K :=
  sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b 0 *
    ∑ e ∈ range y.h.NE, ρ.val (b.sl.getD e zeroE) * eiK ρ rs b e

/-- The verifier's product of these factors reads as c1K. -/
theorem c1E_value : ρ.val (c1E y rs lam om b) = c1K ρ y rs lam om b := by
  unfold c1E c1K sbK omK wtK eiK
  rw [ρ.mul, ρ.mul, ρ.mul, ρ.mul,
    foldl_add ρ.val _ (fun e => ρ.val (b.sl.getD e zeroE) *
      ρ.val ((eqLow rs b.wy b.w).getD e zeroE)) (fun e s => by rw [ρ.add, ρ.mul]),
    ρ.zero, zero_add, list_range_sumM]

/-- The members of an array of elements of the field, read in K. Past the array's end the program's
zero is read. -/
def valsOf (A : Array E) : ℕ → K := fun k => ρ.val (A.getD k zeroE)

/-- What one panel adds to the five numbers, if h1 k stands for the end value of never-sent vector
number k and vv n for that of weight claim number n. The two are any numbers here; stackEndOf_rd has
them at the readings of the arrays that the verifier's function is given. The first two numbers,
what is added to the forms, read neither (dEnd_forms). The last line stands for panels that the
verifier refuses. -/
def dEnd : K × K × K × K × ℕ :=
  match b.tri, b.virt, b.v0 with
  | true, some k, some v0 =>
    (0, 0, c1K ρ y rs lam om b * h1 k,
      sbK ρ rs lam b * vv v0, 0)
  | true, none, some v0 =>
    (∑ k2 ∈ range b.ny, c1K ρ y rs lam om b * eyK ρ rs b k2 * (b.xx.getD k2 {}).value ρ W, 0, 0,
      sbK ρ rs lam b * vv v0, 0)
  | false, some k, some v0 =>
    (0, 0, sbK ρ rs lam b * omK ρ om b * h1 k,
      ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
        vv (v0 + i), b.w)
  | false, none, some v0 =>
    (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
        eiK ρ rs b i * eyK ρ rs b yv * sideK ρ W b.A i yv, 0, 0,
      ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * vv (v0 + i), 0)
  | false, none, none =>
    (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
        eiK ρ rs b i * eyK ρ rs b yv * sideK ρ W b.A i yv,
      ∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * eiK ρ rs b i * eyK ρ rs b yv *
        sideK ρ W b.B i yv, 0, 0, 0)
  | _, _, none => 0

end Parts

/-! ## One panel, branch by branch -/

section Branches

variable {ρ W}
variable {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {s s' : StackEnd} {b : SBlk}

omit [Field K] in
/-- A panel that is not refused has passed the test of its number. -/
theorem stackEndOf_ok (h : stackEndOf y rs lam om H1 V s b = some s') :
    eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true := by
  cases hc : eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) with
  | true => rfl
  | false =>
    unfold stackEndOf at h
    rw [hc] at h
    cases h

/-- A panel with the selector whose column factor is a never-sent vector. -/
theorem end_tri_virt (ht : b.tri = true) {k : ℕ} (hk : b.virt = some k)
    (h : stackEndOf y rs lam om H1 V s b = some s') :
    ∃ v0, b.v0 = some v0 ∧ b.wy = y.lfe ∧ rd ρ W s' = rd ρ W s +
      (0, 0, c1K ρ y rs lam om b * ρ.val (H1.getD k zeroE),
        sbK ρ rs lam b * ρ.val (V.getD v0 zeroE), 0) := by
  have hc := stackEndOf_ok h
  unfold stackEndOf at h
  rw [hc, ht, hk] at h
  have h' : (do
      let v0 ← b.v0
      if b.wy != y.lfe then none
      else pure { s with
        As := addE s.As (mulE (c1E y rs lam om b) (H1.getD k zeroE))
        Bs := addE s.Bs (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (V.getD v0 zeroE)) }) =
      some s' := h
  obtain ⟨v0, hv0, h'⟩ := bind_some h'
  by_cases hwy : (b.wy != y.lfe) = true
  · rw [if_pos hwy] at h'
    cases h'
  · rw [if_neg hwy] at h'
    cases h'
    refine ⟨v0, hv0, by simpa using hwy, rd_ext (add_zero _).symm (add_zero _).symm ?_ ?_ rfl⟩
    · show ρ.val (addE s.As (mulE (c1E y rs lam om b) (H1.getD k zeroE))) = _
      rw [ρ.add, ρ.mul, c1E_value]
    · show ρ.val (addE s.Bs (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (V.getD v0 zeroE))) = _
      rw [ρ.add, ρ.mul]
      rfl

/-- A panel with the selector whose column factor is given in forms. -/
theorem end_tri_forms (ht : b.tri = true) (hk : b.virt = none)
    (h : stackEndOf y rs lam om H1 V s b = some s') :
    ∃ v0, b.v0 = some v0 ∧ rd ρ W s' = rd ρ W s +
      (∑ k2 ∈ range b.ny, c1K ρ y rs lam om b * eyK ρ rs b k2 * (b.xx.getD k2 {}).value ρ W, 0, 0,
        sbK ρ rs lam b * ρ.val (V.getD v0 zeroE), 0) := by
  have hc := stackEndOf_ok h
  unfold stackEndOf at h
  rw [hc, ht, hk] at h
  have h' : (do
      let v0 ← b.v0
      pure { s with
        Alin := (List.range b.ny).foldl (fun a k2 => a.addMul (b.xx.getD k2 {})
          (mulE (c1E y rs lam om b) ((eqLow rs 0 b.wy).getD k2 zeroE))) s.Alin
        Bs := addE s.Bs (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (V.getD v0 zeroE)) }) =
      some s' := h
  obtain ⟨v0, hv0, h'⟩ := bind_some h'
  cases h'
  refine ⟨v0, hv0, rd_ext ?_ (add_zero _).symm (add_zero _).symm ?_ rfl⟩
  · show ((List.range b.ny).foldl (fun a k2 => a.addMul (b.xx.getD k2 {})
      (mulE (c1E y rs lam om b) ((eqLow rs 0 b.wy).getD k2 zeroE))) s.Alin).value ρ W = _
    rw [foldl_add (fun a : Aff => a.value ρ W) _
      (fun k2 => c1K ρ y rs lam om b * eyK ρ rs b k2 * (b.xx.getD k2 {}).value ρ W)
      (fun k2 a => by
        show (Aff.addMul a _ _).value ρ W = a.value ρ W + _
        rw [Aff.value_addMul, ρ.mul, c1E_value]
        rfl), list_range_sumM]
  · show ρ.val (addE s.Bs (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (V.getD v0 zeroE))) = _
    rw [ρ.add, ρ.mul]
    rfl

/-- The panel whose whole A side is a never-sent vector: the down product's. The call's weight and
the rows' weights stand on the B side here. -/
theorem end_plain_virt (ht : b.tri = false) {k : ℕ} (hk : b.virt = some k)
    (h : stackEndOf y rs lam om H1 V s b = some s') :
    ∃ v0, b.v0 = some v0 ∧ s.wD = 0 ∧ rd ρ W s' = rd ρ W s +
      (0, 0, sbK ρ rs lam b * omK ρ om b * ρ.val (H1.getD k zeroE),
        ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
          ρ.val (V.getD (v0 + i) zeroE), b.w) := by
  have hc := stackEndOf_ok h
  unfold stackEndOf at h
  rw [hc, ht, hk] at h
  have h' : (do
      let v0 ← b.v0
      if s.wD != 0 then none
      else pure { s with
        wD := b.w
        As := addE s.As (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
          (om.getD b.claim zeroE)) (H1.getD k zeroE))
        Bs := (List.range b.ni).foldl (fun a i => addE a (mulE (mulE (mulE (mulE
          (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) ((eqLow rs b.wy b.w).getD i zeroE)) b.ec)
          (b.wt.getD i zeroE)) (V.getD (v0 + i) zeroE))) s.Bs }) = some s' := h
  obtain ⟨v0, hv0, h'⟩ := bind_some h'
  by_cases hwD : (s.wD != 0) = true
  · rw [if_pos hwD] at h'
    cases h'
  · rw [if_neg hwD] at h'
    cases h'
    have h0 : s.wD = 0 := by simpa using hwD
    refine ⟨v0, hv0, h0, rd_ext (add_zero _).symm (add_zero _).symm ?_ ?_ ?_⟩
    · show ρ.val (addE s.As (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
        (om.getD b.claim zeroE)) (H1.getD k zeroE))) = _
      rw [ρ.add, ρ.mul, ρ.mul]
      rfl
    · show ρ.val ((List.range b.ni).foldl (fun a i => addE a (mulE (mulE (mulE (mulE
        (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) ((eqLow rs b.wy b.w).getD i zeroE)) b.ec)
        (b.wt.getD i zeroE)) (V.getD (v0 + i) zeroE))) s.Bs) = _
      rw [foldl_add ρ.val _ (fun i => sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
        ρ.val (V.getD (v0 + i) zeroE))
        (fun i a => by rw [ρ.add, ρ.mul, ρ.mul, ρ.mul, ρ.mul]; rfl), list_range_sumM]
    · show b.w = s.wD + b.w
      rw [h0, Nat.zero_add]

/-- A sum of tuples is the tuple of the sums. -/
theorem sum5 (n : ℕ) (a b c d : ℕ → K) (e : ℕ → ℕ) :
    ∑ i ∈ range n, (a i, b i, c i, d i, e i) =
      (∑ i ∈ range n, a i, ∑ i ∈ range n, b i, ∑ i ∈ range n, c i, ∑ i ∈ range n, d i,
        ∑ i ∈ range n, e i) := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; rfl
  | succ n ih => simp only [Finset.sum_range_succ, ih]; rfl

/-- The two nested folds of a panel whose A side is given in forms: over the rows, and in each row
over the columns, with one more step at the row's end. -/
theorem plain_fold {ni ny : ℕ} {stepIn : ℕ → StackEnd → ℕ → Option StackEnd}
    {fin : ℕ → StackEnd → StackEnd} (gin : ℕ → ℕ → K × K × K × K × ℕ) (gfin : ℕ → K × K × K × K × ℕ)
    (Hin : ∀ i yv t t', stepIn i t yv = some t' → rd ρ W t' = rd ρ W t + gin i yv)
    (Hfin : ∀ i t, rd ρ W (fin i t) = rd ρ W t + gfin i)
    (h : (List.range ni).foldlM (fun s i => do
      let s ← (List.range ny).foldlM (stepIn i) s
      pure (fin i s)) s = some s') :
    rd ρ W s' = rd ρ W s + ∑ i ∈ range ni, (∑ yv ∈ range ny, gin i yv + gfin i) := by
  rw [foldlM_add (rd ρ W) _ (fun i => ∑ yv ∈ range ny, gin i yv + gfin i) ?_ _ _ _ h,
    list_range_sumM]
  intro i s1 s2 hs
  obtain ⟨s3, hin, hs⟩ := bind_some hs
  cases hs
  rw [Hfin, foldlM_add (rd ρ W) _ (gin i) (Hin i) _ _ _ hin, list_range_sumM, add_assoc]

/-- A panel with two factors whose B side is a weight matrix. -/
theorem end_plain_weights (ht : b.tri = false) (hk : b.virt = none) {v0 : ℕ} (h0 : b.v0 = some v0)
    (h : stackEndOf y rs lam om H1 V s b = some s') :
    rd ρ W s' = rd ρ W s +
      (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
          eiK ρ rs b i * eyK ρ rs b yv * sideK ρ W b.A i yv, 0, 0,
        ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val (V.getD (v0 + i) zeroE), 0) := by
  have hc := stackEndOf_ok h
  unfold stackEndOf at h
  rw [hc, ht, hk, h0] at h
  have h' : (do
      let A ← b.A
      (List.range b.ni).foldlM (fun s i => do
        let s ← (List.range b.ny).foldlM (fun (s : StackEnd) yv => do
          let a ← A i yv
          pure { s with Alin := s.Alin.addMul a (mulE (mulE (mulE (mulE (mulE
            (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (om.getD b.claim zeroE)) b.ec)
            (b.wt.getD i zeroE)) ((eqLow rs b.wy b.w).getD i zeroE))
            ((eqLow rs 0 b.wy).getD yv zeroE)) }) s
        pure { s with Bs := addE s.Bs (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
          ((eqLow rs b.wy b.w).getD i zeroE)) (V.getD (v0 + i) zeroE)) }) s) = some s' := h
  obtain ⟨A, hA, h'⟩ := bind_some h'
  rw [hA, plain_fold
    (fun i yv => (sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
      eiK ρ rs b i * eyK ρ rs b yv * ov ρ W (A i yv), 0, 0, 0, 0))
    (fun i => (0, 0, 0, sbK ρ rs lam b * eiK ρ rs b i * ρ.val (V.getD (v0 + i) zeroE), 0))
    ?_ ?_ h']
  · congr 1
    simp only [sum5, Prod.mk_add_mk, Finset.sum_const_zero, add_zero, zero_add]
    rfl
  · intro i yv t t' hs
    obtain ⟨a, ha, hs⟩ := bind_some hs
    cases hs
    refine rd_ext ?_ (add_zero _).symm (add_zero _).symm (add_zero _).symm rfl
    show (Aff.addMul t.Alin a _).value ρ W = _
    rw [Aff.value_addMul, ha, ρ.mul, ρ.mul, ρ.mul, ρ.mul, ρ.mul]
    rfl
  · intro i t
    refine rd_ext (add_zero _).symm (add_zero _).symm (add_zero _).symm ?_ rfl
    show ρ.val (addE t.Bs _) = _
    rw [ρ.add, ρ.mul, ρ.mul]
    rfl

/-- A panel with two factors, both given in forms. -/
theorem end_plain_forms (ht : b.tri = false) (hk : b.virt = none) (h0 : b.v0 = none)
    (h : stackEndOf y rs lam om H1 V s b = some s') :
    rd ρ W s' = rd ρ W s +
      (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
          eiK ρ rs b i * eyK ρ rs b yv * sideK ρ W b.A i yv,
        ∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * eiK ρ rs b i * eyK ρ rs b yv *
          sideK ρ W b.B i yv, 0, 0, 0) := by
  have hc := stackEndOf_ok h
  unfold stackEndOf at h
  rw [hc, ht, hk, h0] at h
  cases hB : b.B with
  | none =>
    rw [hB] at h
    have h' : (do
        let A ← b.A
        (List.range b.ni).foldlM (fun s i => do
          let s ← (List.range b.ny).foldlM (fun (_ : StackEnd) yv => do
            let _ ← A i yv
            none) s
          pure s) s) = some s' := h
    obtain ⟨A, hA, h'⟩ := bind_some h'
    rw [hA, plain_fold (fin := fun _ s => s)
      (fun i yv => (sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
        eiK ρ rs b i * eyK ρ rs b yv * ov ρ W (A i yv),
        sbK ρ rs lam b * eiK ρ rs b i * eyK ρ rs b yv * 0, 0, 0, 0))
      (fun _ => 0) ?_ (fun _ _ => (add_zero _).symm) h']
    · congr 1
      simp only [sum5, Finset.sum_const_zero, add_zero]
      rfl
    · intro i yv t t' hs
      obtain ⟨a, _, hs⟩ := bind_some hs
      cases hs
  | some B =>
    rw [hB] at h
    have h' : (do
        let A ← b.A
        (List.range b.ni).foldlM (fun s i => do
          let s ← (List.range b.ny).foldlM (fun (s : StackEnd) yv => do
            let a ← A i yv
            let c ← B i yv
            pure { s with
              Alin := s.Alin.addMul a (mulE (mulE (mulE (mulE (mulE
                (eqLowAt rs b.w lam (b.off / 2 ^ b.w)) (om.getD b.claim zeroE)) b.ec)
                (b.wt.getD i zeroE)) ((eqLow rs b.wy b.w).getD i zeroE))
                ((eqLow rs 0 b.wy).getD yv zeroE))
              Blin := s.Blin.addMul c (mulE (mulE (eqLowAt rs b.w lam (b.off / 2 ^ b.w))
                ((eqLow rs b.wy b.w).getD i zeroE)) ((eqLow rs 0 b.wy).getD yv zeroE)) }) s
          pure s) s) = some s' := h
    obtain ⟨A, hA, h'⟩ := bind_some h'
    rw [hA, plain_fold (fin := fun _ s => s)
      (fun i yv => (sbK ρ rs lam b * omK ρ om b * ρ.val b.ec * wtK ρ b i *
        eiK ρ rs b i * eyK ρ rs b yv * ov ρ W (A i yv),
        sbK ρ rs lam b * eiK ρ rs b i * eyK ρ rs b yv * ov ρ W (B i yv), 0, 0, 0))
      (fun _ => 0) ?_ (fun _ _ => (add_zero _).symm) h']
    · congr 1
      simp only [sum5, Finset.sum_const_zero, add_zero]
      rfl
    · intro i yv t t' hs
      obtain ⟨a, ha, hs⟩ := bind_some hs
      obtain ⟨c, hcB, hs⟩ := bind_some hs
      cases hs
      refine rd_ext ?_ ?_ (add_zero _).symm (add_zero _).symm rfl
      · show (Aff.addMul t.Alin a _).value ρ W = _
        rw [Aff.value_addMul, ha, ρ.mul, ρ.mul, ρ.mul, ρ.mul, ρ.mul]
        rfl
      · show (Aff.addMul t.Blin c _).value ρ W = _
        rw [Aff.value_addMul, hcB, ρ.mul, ρ.mul]
        rfl

/-- What one panel adds to the five numbers, in all branches: dEnd at the readings of the two arrays
that the verifier's function is given. -/
theorem stackEndOf_rd (h : stackEndOf y rs lam om H1 V s b = some s') :
    rd ρ W s' = rd ρ W s + dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b := by
  unfold dEnd
  cases ht : b.tri with
  | true =>
    cases hk : b.virt with
    | some k =>
      obtain ⟨v0, hv, _, r⟩ := end_tri_virt (ρ := ρ) (W := W) ht hk h
      rw [hv]
      exact r
    | none =>
      obtain ⟨v0, hv, r⟩ := end_tri_forms (ρ := ρ) (W := W) ht hk h
      rw [hv]
      exact r
  | false =>
    cases hk : b.virt with
    | some k =>
      obtain ⟨v0, hv, _, r⟩ := end_plain_virt (ρ := ρ) (W := W) ht hk h
      rw [hv]
      exact r
    | none =>
      cases h0 : b.v0 with
      | some v0 => exact end_plain_weights ht hk h0 h
      | none => exact end_plain_forms ht hk h0 h

/-! ## All panels -/

/-- The end of the batched sumcheck: the five numbers are those of the start, where the two elements
of the field are the two shown values, plus what the panels add; and the bits of the down product's
panel are as many as the verifier asks. -/
theorem stackEnd_rd {bl : Array SBlk} {shownA shownB : E}
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    rd ρ W s' = (0, 0, ρ.val shownA, ρ.val shownB, 0) +
      (bl.toList.map (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V))).sum ∧
      s'.wD = y.h.ll + y.lPf := by
  unfold stackEnd at h
  obtain ⟨s1, hf, h⟩ := bind_some h
  by_cases hw : (s1.wD != y.h.ll + y.lPf) = true
  · rw [if_pos hw] at h
    cases h
  · rw [if_neg hw] at h
    cases h
    rw [← Array.foldlM_toList] at hf
    refine ⟨?_, by simpa using hw⟩
    rw [foldlM_add (rd ρ W) _ (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V))
      (fun _ _ _ hs => stackEndOf_rd hs) _ _ _ hf]
    congr 1
    show (({} : Aff).value ρ W, ({} : Aff).value ρ W, ρ.val shownA, ρ.val shownB, 0) = _
    rw [Aff.value_empty]

end Branches

/-! ## Sums over a panel's places -/

section Grid

/-- A sum of terms that vanish from n on. -/
theorem sum_trunc {n N : ℕ} (h : n ≤ N) (f : ℕ → K) :
    ∑ i ∈ range N, (if i < n then f i else 0) = ∑ i ∈ range n, f i := by
  rw [← Finset.sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_range]
  omega

/-- The sum over the places of a panel, as rows and columns, of the equality weight of the place in
the panel times F at (row, column). -/
def gsum (rs : Array E) (b : SBlk) (F : ℕ → ℕ → K) : K :=
  ∑ i ∈ range (2 ^ (b.w - b.wy)), ∑ yv ∈ range (2 ^ b.wy),
    eqR ρ rs b.wy b.w i * eqR ρ rs 0 b.wy yv * F i yv

/-- What is asked of a panel's numbers: the bits fit, the rows and columns fit their bits, and the
panel's first place is a multiple of its size. -/
structure PanelOK (y : Lay) (rs : Array E) (lam : ℕ) (b : SBlk) : Prop where
  /-- the bits of a column are among the bits of a place -/
  wy_le : b.wy ≤ b.w
  /-- the bits of a place are among the sumcheck's -/
  w_le : b.w ≤ lam
  /-- one challenge for each bit -/
  lam_le : lam ≤ rs.size
  /-- the rows fit -/
  ni_le : b.ni ≤ 2 ^ (b.w - b.wy)
  /-- the columns fit -/
  ny_le : b.ny ≤ 2 ^ b.wy
  /-- with the selector: the experts fit -/
  ne_le : b.tri = true → y.h.NE ≤ 2 ^ (b.w - b.wy)
  /-- the first place -/
  dvd : 2 ^ b.w ∣ b.off

variable {ρ}
variable {y : Lay} {rs : Array E} {lam : ℕ} {b : SBlk} (ok : PanelOK y rs lam b)
include ok

/-- The verifier's weight of a row. -/
theorem PanelOK.ei {i : ℕ} (hi : i < 2 ^ (b.w - b.wy)) : eiK ρ rs b i = eqR ρ rs b.wy b.w i :=
  eqLow_value ρ rs (Nat.le_trans ok.w_le ok.lam_le) hi

/-- The verifier's weight of a column. -/
theorem PanelOK.ey {yv : ℕ} (hy : yv < 2 ^ b.wy) : eyK ρ rs b yv = eqR ρ rs 0 b.wy yv :=
  eqLow_value ρ rs (Nat.le_trans ok.wy_le (Nat.le_trans ok.w_le ok.lam_le)) hy

/-- A function that vanishes from row n on. -/
theorem PanelOK.rows {n : ℕ} (hn : n ≤ 2 ^ (b.w - b.wy)) (F : ℕ → ℕ → K) :
    gsum ρ rs b (fun i yv => if i < n then F i yv else 0) =
      ∑ i ∈ range n, eiK ρ rs b i * ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv * F i yv := by
  unfold gsum
  rw [← sum_trunc hn]
  refine sum_congr rfl fun i hi => ?_
  by_cases h : i < n
  · simp only [if_pos h]
    rw [ok.ei (mem_range.mp hi), Finset.mul_sum]
    exact sum_congr rfl fun yv _ => by ring
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero]

/-- A function that vanishes from row n on and from column m on. -/
theorem PanelOK.rowsCols {n m : ℕ} (hn : n ≤ 2 ^ (b.w - b.wy)) (hm : m ≤ 2 ^ b.wy)
    (F : ℕ → ℕ → K) :
    gsum ρ rs b (fun i yv => if i < n then (if yv < m then F i yv else 0) else 0) =
      ∑ i ∈ range n, ∑ yv ∈ range m, eiK ρ rs b i * eyK ρ rs b yv * F i yv := by
  rw [ok.rows hn]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_trunc hm, Finset.mul_sum]
  refine sum_congr rfl fun yv hy => ?_
  split_ifs with h
  · rw [ok.ey (mem_range.mp hy)]
    ring
  · simp

/-- The sum over a panel's places, as places of the long vectors: the weight of the panel's number
times the weight of the place in the panel is the weight of the place in the long vectors. -/
theorem PanelOK.places (hix : eqIndexOK (rs.extract b.w lam) (b.off / 2 ^ b.w) = true)
    (F : ℕ → ℕ → K) :
    sbK ρ rs lam b * gsum ρ rs b F = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
      (if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
        F ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0) := by
  obtain ⟨q0, hq0⟩ := ok.dvd
  have hpw : 0 < 2 ^ b.w := by positivity
  have hpy : 0 < 2 ^ b.wy := by positivity
  have hdiv : b.off / 2 ^ b.w = q0 := by rw [hq0, Nat.mul_div_cancel_left _ hpw]
  have hsz : (rs.extract b.w lam).size = lam - b.w := by
    rw [Array.size_extract]
    have := ok.lam_le
    omega
  have hq : q0 < 2 ^ (lam - b.w) := by
    unfold eqIndexOK at hix
    rw [hdiv, hsz] at hix
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hix
    exact hix.2
  have e1 : (2 : ℕ) ^ lam = 2 ^ (lam - b.w) * 2 ^ b.w := by
    rw [← pow_add]
    congr 1
    have := ok.w_le
    omega
  have e2 : (2 : ℕ) ^ b.w = 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
    rw [← pow_add]
    congr 1
    have := ok.wy_le
    omega
  rw [e1, sum_blocks, Finset.sum_eq_single q0]
  · unfold sbK gsum
    rw [eqLowAt_value ρ rs ok.lam_le hix, hdiv, Finset.mul_sum, e2, sum_blocks]
    refine sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun yv hy => ?_
    have hy' : yv < 2 ^ b.wy := mem_range.mp hy
    have hi' : i < 2 ^ (b.w - b.wy) := mem_range.mp hi
    have hp : i * 2 ^ b.wy + yv < 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
      calc i * 2 ^ b.wy + yv < i * 2 ^ b.wy + 2 ^ b.wy := by omega
        _ = (i + 1) * 2 ^ b.wy := by ring
        _ ≤ 2 ^ (b.w - b.wy) * 2 ^ b.wy := Nat.mul_le_mul_right _ hi'
    have hY : q0 * (2 ^ (b.w - b.wy) * 2 ^ b.wy) + (i * 2 ^ b.wy + yv) - b.off =
        i * 2 ^ b.wy + yv := by
      rw [hq0, e2, Nat.mul_comm q0]
      omega
    have hin : b.off ≤ q0 * (2 ^ (b.w - b.wy) * 2 ^ b.wy) + (i * 2 ^ b.wy + yv) ∧
        q0 * (2 ^ (b.w - b.wy) * 2 ^ b.wy) + (i * 2 ^ b.wy + yv) <
          b.off + 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
      rw [hq0, e2, Nat.mul_comm q0]
      omega
    have s1 := eqR_split ρ rs (Nat.zero_le b.w) ok.w_le q0 (c' := i * 2 ^ b.wy + yv)
      (by rw [Nat.sub_zero, e2]; exact hp)
    have s2 := eqR_split ρ rs (Nat.zero_le b.wy) ok.wy_le i (c' := yv)
      (by rw [Nat.sub_zero]; exact hy')
    rw [Nat.sub_zero] at s1 s2
    rw [e2] at s1
    rw [if_pos hin, hY, s1, s2, Nat.mul_comm i, Nat.mul_add_div hpy, Nat.mul_add_mod,
      Nat.div_eq_of_lt hy', Nat.mod_eq_of_lt hy', Nat.add_zero]
    ring
  · intro q _ hne
    refine sum_eq_zero fun p hp => ?_
    have hp' : p < 2 ^ b.w := mem_range.mp hp
    rw [if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    apply hne
    rw [hq0, Nat.mul_comm (2 ^ b.w) q0] at h1 h2
    have a1 : q0 * 2 ^ b.w < (q + 1) * 2 ^ b.w := by
      calc q0 * 2 ^ b.w ≤ q * 2 ^ b.w + p := h1
        _ < q * 2 ^ b.w + 2 ^ b.w := by omega
        _ = (q + 1) * 2 ^ b.w := by ring
    have a2 : q * 2 ^ b.w < (q0 + 1) * 2 ^ b.w := by
      calc q * 2 ^ b.w ≤ q * 2 ^ b.w + p := Nat.le_add_right _ _
        _ < q0 * 2 ^ b.w + 2 ^ b.w := h2
        _ = (q0 + 1) * 2 ^ b.w := by ring
    have b1 := Nat.lt_of_mul_lt_mul_right a1
    have b2 := Nat.lt_of_mul_lt_mul_right a2
    omega
  · intro hn
    exact absurd (mem_range.mpr hq) hn

end Grid

/-! ## The meaning of what one panel adds -/

section Meaning

variable (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E) (h1 vv : ℕ → K) (hv wv : ℕ → ℕ → K)
  (b : SBlk)

/-- The A side of a panel at (row, column), with all the factors that the verifier computes. With
the selector one of them is the selector's shown value, which is no public number. hv k: the
never-sent vector number k. For the panel whose whole A side is such a vector, the call's weight and
the rows' weights are not here: the verifier has them on the B side. -/
def aG (i yv : ℕ) : K :=
  match b.tri, b.virt with
  | true, some k =>
    if i < y.h.NE then
      omK ρ om b * ρ.val b.ec * wtK ρ b 0 * ρ.val (b.sl.getD i zeroE) * hv k yv else 0
  | true, none =>
    if i < y.h.NE then
      (if yv < b.ny then omK ρ om b * ρ.val b.ec * wtK ρ b 0 * ρ.val (b.sl.getD i zeroE) *
        (b.xx.getD yv {}).value ρ W else 0) else 0
  | false, some k => omK ρ om b * hv k (i * 2 ^ b.wy + yv)
  | false, none =>
    if i < b.ni then
      (if yv < b.ny then omK ρ om b * ρ.val b.ec * wtK ρ b i * sideK ρ W b.A i yv else 0) else 0

/-- The B side of a panel at (row, column). wv n: the vector of weight claim number n. -/
def bG (i yv : ℕ) : K :=
  match b.tri, b.virt, b.v0 with
  | true, _, some v0 => wv v0 (i * 2 ^ b.wy + yv)
  | false, some _, some v0 => if i < b.ni then ρ.val b.ec * wtK ρ b i * wv (v0 + i) yv else 0
  | false, none, some v0 => if i < b.ni then wv (v0 + i) yv else 0
  | false, none, none => if i < b.ni then (if yv < b.ny then sideK ρ W b.B i yv else 0) else 0
  | _, _, none => 0

/-- The end values h1, vv that a panel reads are true of the vectors hv, wv: each is the extension,
at the end point's coordinates of the panel's columns or places, of the vector that it stands for.
The end values are any numbers. -/
structure EndsTrue : Prop where
  /-- a never-sent vector that is the column factor of a panel with the selector -/
  colH : ∀ k, b.tri = true → b.virt = some k →
    h1 k = ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv * hv k yv
  /-- a never-sent vector that is a whole A side -/
  allH : ∀ k, b.tri = false → b.virt = some k →
    h1 k = gsum ρ rs b (fun i yv => hv k (i * 2 ^ b.wy + yv))
  /-- the one weight claim of a panel with the selector -/
  allV : ∀ v0, b.tri = true → b.v0 = some v0 →
    vv v0 = gsum ρ rs b (fun i yv => wv v0 (i * 2 ^ b.wy + yv))
  /-- the weight claim of each row of another panel -/
  rowV : ∀ v0 i, b.tri = false → b.v0 = some v0 → i < b.ni →
    vv (v0 + i) = ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv * wv (v0 + i) yv

/-- EndsTrue at the readings of the two arrays that the verifier's function is given. By the text of
its caller these hold the values that were sent, not the hidden ones: see this file's head. -/
def ShownTrue (ρ : Reading K) (rs H1 V : Array E) (hv wv : ℕ → ℕ → K) (b : SBlk) : Prop :=
  EndsTrue ρ rs (valsOf ρ H1) (valsOf ρ V) hv wv b

variable {ρ W y rs lam om h1 vv hv wv b}

/-- What one panel adds to the A side, to the form and to the element of the field together, at end
values that are true: the weight of the panel's number times the sum over the panel's places of the
place's weight times the A side. The like for the B side. h: the verifier's function has not refused
the panel, whatever arrays it was given: only the panel's own fields are read from that. -/
theorem panel_mean (ok : PanelOK y rs lam b) (tr : EndsTrue ρ rs h1 vv hv wv b)
    {H1 V : Array E} {s s' : StackEnd} (h : stackEndOf y rs lam om H1 V s b = some s') :
    (dEnd ρ W y rs lam om h1 vv b).1 + (dEnd ρ W y rs lam om h1 vv b).2.2.1 =
        sbK ρ rs lam b * gsum ρ rs b (aG ρ W y om hv b) ∧
      (dEnd ρ W y rs lam om h1 vv b).2.1 + (dEnd ρ W y rs lam om h1 vv b).2.2.2.1 =
        sbK ρ rs lam b * gsum ρ rs b (bG ρ W wv b) := by
  unfold dEnd aG bG
  cases ht : b.tri with
  | true =>
    have hne := ok.ne_le ht
    cases hk : b.virt with
    | some k =>
      obtain ⟨v0, hv0, _, _⟩ := end_tri_virt (ρ := ρ) (W := W) ht hk h
      rw [hv0]
      refine ⟨?_, ?_⟩
      · show 0 + c1K ρ y rs lam om b * h1 k = _
        rw [ok.rows hne, tr.colH k ht hk, zero_add]
        have e1 : ∀ e, ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv *
            (omK ρ om b * ρ.val b.ec * wtK ρ b 0 * ρ.val (b.sl.getD e zeroE) * hv k yv) =
            omK ρ om b * ρ.val b.ec * wtK ρ b 0 * ρ.val (b.sl.getD e zeroE) *
              ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv * hv k yv := by
          intro e
          rw [Finset.mul_sum]
          exact sum_congr rfl fun yv _ => by ring
        simp only [e1]
        generalize (∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv * hv k yv) = S
        unfold c1K
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact sum_congr rfl fun e _ => by ring
      · show 0 + sbK ρ rs lam b * vv v0 = _
        rw [tr.allV v0 ht hv0, zero_add]
    | none =>
      obtain ⟨v0, hv0, _⟩ := end_tri_forms (ρ := ρ) (W := W) ht hk h
      rw [hv0]
      refine ⟨?_, ?_⟩
      · show (∑ k2 ∈ range b.ny, c1K ρ y rs lam om b * eyK ρ rs b k2 *
          (b.xx.getD k2 {}).value ρ W) + 0 = _
        rw [ok.rowsCols hne ok.ny_le, add_zero, Finset.sum_comm, Finset.mul_sum]
        refine sum_congr rfl fun k2 _ => ?_
        unfold c1K
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact sum_congr rfl fun e _ => by ring
      · show 0 + sbK ρ rs lam b * vv v0 = _
        rw [tr.allV v0 ht hv0, zero_add]
  | false =>
    cases hk : b.virt with
    | some k =>
      obtain ⟨v0, hv0, _, _⟩ := end_plain_virt (ρ := ρ) (W := W) ht hk h
      rw [hv0]
      refine ⟨?_, ?_⟩
      · show 0 + sbK ρ rs lam b * omK ρ om b * h1 k = _
        rw [tr.allH k ht hk, zero_add, mul_assoc]
        congr 1
        unfold gsum
        rw [Finset.mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun yv _ => by ring
      · show 0 + ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
          vv (v0 + i) = _
        rw [ok.rows ok.ni_le, zero_add, Finset.mul_sum]
        refine sum_congr rfl fun i hi => ?_
        rw [tr.rowV v0 i ht hv0 (mem_range.mp hi)]
        have e1 : ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv *
            (ρ.val b.ec * wtK ρ b i * wv (v0 + i) yv) = ρ.val b.ec * wtK ρ b i *
              ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv * wv (v0 + i) yv := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun yv _ => by ring
        rw [e1]
        ring
    | none =>
      have hA : (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * omK ρ om b * ρ.val b.ec *
          wtK ρ b i * eiK ρ rs b i * eyK ρ rs b yv * sideK ρ W b.A i yv) =
          sbK ρ rs lam b * gsum ρ rs b (fun i yv => if i < b.ni then
            (if yv < b.ny then omK ρ om b * ρ.val b.ec * wtK ρ b i * sideK ρ W b.A i yv else 0)
            else 0) := by
        rw [ok.rowsCols ok.ni_le ok.ny_le, Finset.mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact sum_congr rfl fun yv _ => by ring
      cases h0 : b.v0 with
      | some v0 =>
        refine ⟨?_, ?_⟩
        · show _ + 0 = _
          rw [add_zero]
          exact hA
        · show 0 + ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i *
            vv (v0 + i) = _
          rw [ok.rows ok.ni_le, zero_add, Finset.mul_sum]
          refine sum_congr rfl fun i hi => ?_
          rw [tr.rowV v0 i ht h0 (mem_range.mp hi)]
          ring
      | none =>
        refine ⟨?_, ?_⟩
        · show _ + 0 = _
          rw [add_zero]
          exact hA
        · show (∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, sbK ρ rs lam b * eiK ρ rs b i *
            eyK ρ rs b yv * sideK ρ W b.B i yv) + 0 = _
          rw [ok.rowsCols ok.ni_le ok.ny_le, add_zero, Finset.mul_sum]
          refine sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact sum_congr rfl fun yv _ => by ring

variable (ρ) in
/-- The equality weights over a stretch of bits sum to 1. -/
theorem eqR_sum (rs : Array E) (lo hi : ℕ) (c : K) :
    ∑ x ∈ range (2 ^ (hi - lo)), eqR ρ rs lo hi x * c = c :=
  Blocks.ext_const (hi - lo) c _

variable (ρ) in
/-- The sum over a panel's places of the place's weight times a constant is the constant. -/
theorem gsum_const (rs : Array E) (b : SBlk) (c : K) : gsum ρ rs b (fun _ _ => c) = c := by
  unfold gsum
  have e : ∀ i, ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs b.wy b.w i * eqR ρ rs 0 b.wy yv * c =
      eqR ρ rs b.wy b.w i * c := by
    intro i
    have s := eqR_sum ρ rs 0 b.wy c
    rw [Nat.sub_zero] at s
    rw [← s, Finset.mul_sum, s]
    exact sum_congr rfl fun yv _ => by ring
  simp only [e]
  exact eqR_sum ρ rs b.wy b.w c

variable (ρ) in
/-- The hypothesis EndsTrue can be met, whatever the end values: take for each never-sent vector and
for each weight claim's vector the constant vector of its end value. So the theorems that ask
EndsTrue are not empty. This says nothing on whether the vectors that the sub-proof means are the
true ones. -/
theorem ends_met (rs : Array E) (h1 vv : ℕ → K) (b : SBlk) :
    EndsTrue ρ rs h1 vv (fun k _ => h1 k) (fun n _ => vv n) b where
  colH k _ _ := by
    have s := eqR_sum ρ rs 0 b.wy (h1 k)
    rw [Nat.sub_zero] at s
    exact s.symm
  allH k _ _ := (gsum_const ρ rs b _).symm
  allV v0 _ _ := (gsum_const ρ rs b _).symm
  rowV v0 i _ _ _ := by
    have s := eqR_sum ρ rs 0 b.wy (vv (v0 + i))
    rw [Nat.sub_zero] at s
    exact s.symm

variable (ρ) in
/-- The same for the values that were sent. -/
theorem shown_met (rs H1 V : Array E) (b : SBlk) :
    ShownTrue ρ rs H1 V (fun k _ => ρ.val (H1.getD k zeroE)) (fun n _ => ρ.val (V.getD n zeroE))
      b :=
  ends_met ρ rs (valsOf ρ H1) (valsOf ρ V) b

end Meaning

/-! ## The two long vectors -/

section Long

/-- A fold of steps that may refuse, where the step's law is known for the list's members alone. -/
theorem foldlM_addOn {σ α M : Type} [AddCommMonoid M] (val : σ → M) (step : σ → α → Option σ)
    (g : α → M) : ∀ (l : List α), (∀ x ∈ l, ∀ s s', step s x = some s' → val s' = val s + g x) →
      ∀ (s a : σ), l.foldlM step s = some a → val a = val s + (l.map g).sum
  | [], _, s, a, h => by
    have hs : s = a := by simpa using h
    subst hs
    simp
  | x :: l, H, s, a, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s', hq, h2⟩ := bind_some h
    rw [foldlM_addOn val step g l (fun z hz => H z (List.mem_cons_of_mem _ hz)) s' a h2,
      H x List.mem_cons_self s s' hq, List.map_cons, List.sum_cons, add_assoc]

/-- A long vector at place Y: the sum over the panels of the panel's side G at the (row, column) of
Y, for the panels that hold the place Y. -/
def vecOf (G : SBlk → ℕ → ℕ → K) (l : List SBlk) (Y : ℕ) : K :=
  (l.map fun b => if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
    G b ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0).sum

/-- A sum over panels of weighted sums over places is the weighted sum over places of the sums over
panels. -/
theorem list_sum_places (N : ℕ) (e : ℕ → K) (f : SBlk → ℕ → K) : ∀ l : List SBlk,
    (l.map fun b => ∑ Y ∈ range N, e Y * f b Y).sum =
      ∑ Y ∈ range N, e Y * (l.map fun b => f b Y).sum
  | [] => by simp
  | b :: l => by
    simp only [List.map_cons, List.sum_cons, list_sum_places N e f l, mul_add,
      Finset.sum_add_distrib]

variable {ρ W}
variable {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {hv wv : ℕ → ℕ → K}

/-- The end of the batched sumcheck, as values of two long vectors at the end point, on the values
that were sent. On each side the form's value and the element of the field together are the sent
value plus the extension of the long vector. So if the sent value is the form's value, the element
of the field is the extension. The long vectors are made of the list's own panels at their own
places. The like on any end values: ends_mean. -/
theorem stackEnd_mean {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd}
    (ok : ∀ b ∈ bl.toList, PanelOK y rs lam b)
    (tr : ∀ b ∈ bl.toList, ShownTrue ρ rs H1 V hv wv b)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    s'.Alin.value ρ W + ρ.val s'.As = ρ.val shownA +
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y * vecOf (aG ρ W y om hv) bl.toList Y ∧
      s'.Blin.value ρ W + ρ.val s'.Bs = ρ.val shownB +
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y * vecOf (bG ρ W wv) bl.toList Y := by
  unfold stackEnd at h
  obtain ⟨s1, hf, h⟩ := bind_some h
  by_cases hw : (s1.wD != y.h.ll + y.lPf) = true
  · rw [if_pos hw] at h
    cases h
  · rw [if_neg hw] at h
    cases h
    rw [← Array.foldlM_toList] at hf
    have z : ({} : Aff).value ρ W = 0 := Aff.value_empty ρ W
    unfold vecOf
    refine ⟨?_, ?_⟩
    · rw [← list_sum_places, foldlM_addOn (fun s : StackEnd => s.Alin.value ρ W + ρ.val s.As) _
        (fun b => ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          (if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
            aG ρ W y om hv b ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0))
        _ ?_ _ _ hf]
      · show ({} : Aff).value ρ W + ρ.val shownA + _ = _
        rw [z, zero_add]
      · intro b hb s s2 hs
        have r : s2.Alin.value ρ W + ρ.val s2.As =
            (s.Alin.value ρ W + (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b).1) +
              (ρ.val s.As + (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b).2.2.1) :=
          congrArg (fun m : K × K × K × K × ℕ => m.1 + m.2.2.1) (stackEndOf_rd (ρ := ρ) (W := W) hs)
        show s2.Alin.value ρ W + ρ.val s2.As = s.Alin.value ρ W + ρ.val s.As + _
        rw [r]
        beta_reduce
        rw [← (ok b hb).places (ρ := ρ) (stackEndOf_ok hs) (aG ρ W y om hv b),
          ← (panel_mean (h1 := valsOf ρ H1) (vv := valsOf ρ V) (ok b hb) (tr b hb) hs).1]
        ring
    · rw [← list_sum_places, foldlM_addOn (fun s : StackEnd => s.Blin.value ρ W + ρ.val s.Bs) _
        (fun b => ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          (if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
            bG ρ W wv b ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0))
        _ ?_ _ _ hf]
      · show ({} : Aff).value ρ W + ρ.val shownB + _ = _
        rw [z, zero_add]
      · intro b hb s s2 hs
        have r : s2.Blin.value ρ W + ρ.val s2.Bs =
            (s.Blin.value ρ W + (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b).2.1) +
              (ρ.val s.Bs + (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b).2.2.2.1) :=
          congrArg (fun m : K × K × K × K × ℕ => m.2.1 + m.2.2.2.1)
            (stackEndOf_rd (ρ := ρ) (W := W) hs)
        show s2.Blin.value ρ W + ρ.val s2.Bs = s.Blin.value ρ W + ρ.val s.Bs + _
        rw [r]
        beta_reduce
        rw [← (ok b hb).places (ρ := ρ) (stackEndOf_ok hs) (bG ρ W wv b),
          ← (panel_mean (h1 := valsOf ρ H1) (vv := valsOf ρ V) (ok b hb) (tr b hb) hs).2]
        ring

/-! ### On any end values -/

/-- Every member of a list over which a fold of steps that may refuse has returned was taken by a
step that returned. -/
theorem foldlM_each {σ α : Type} (step : σ → α → Option σ) :
    ∀ (l : List α) (s a : σ), l.foldlM step s = some a → ∀ x ∈ l, ∃ s1 s2, step s1 x = some s2
  | [], _, _, _, _, hx => by simp at hx
  | z :: l, s, a, h, x, hx => by
    rw [List.foldlM_cons] at h
    obtain ⟨s', hq, h2⟩ := bind_some h
    rcases List.mem_cons.mp hx with e | hx'
    · exact ⟨s, s', by rw [e]; exact hq⟩
    · exact foldlM_each step l s' a h2 x hx'

/-- If the end of the batched sumcheck returns, no panel of the list was refused. -/
theorem stackEnd_each {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd}
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    ∀ b ∈ bl.toList, ∃ s1 s2, stackEndOf y rs lam om H1 V s1 b = some s2 := by
  unfold stackEnd at h
  obtain ⟨s1, hf, -⟩ := bind_some h
  rw [← Array.foldlM_toList] at hf
  exact foldlM_each _ _ _ _ hf

variable (ρ W y rs lam om) in
/-- What a panel adds to the two forms does not hang on the end values. -/
theorem dEnd_forms (h1 vv h1' vv' : ℕ → K) (b : SBlk) :
    (dEnd ρ W y rs lam om h1 vv b).1 = (dEnd ρ W y rs lam om h1' vv' b).1 ∧
      (dEnd ρ W y rs lam om h1 vv b).2.1 = (dEnd ρ W y rs lam om h1' vv' b).2.1 := by
  unfold dEnd
  cases b.tri <;> cases b.virt <;> cases b.v0 <;> exact ⟨rfl, rfl⟩

variable (ρ W y rs lam om) in
/-- What a panel adds to the two elements of the field is linear in the end values. -/
theorem dEnd_linear (h1 vv m1 mv : ℕ → K) (β : K) (b : SBlk) :
    (dEnd ρ W y rs lam om (fun k => h1 k + β * m1 k) (fun n => vv n + β * mv n) b).2.2.1 =
        (dEnd ρ W y rs lam om h1 vv b).2.2.1 + β * (dEnd ρ W y rs lam om m1 mv b).2.2.1 ∧
      (dEnd ρ W y rs lam om (fun k => h1 k + β * m1 k) (fun n => vv n + β * mv n) b).2.2.2.1 =
        (dEnd ρ W y rs lam om h1 vv b).2.2.2.1 +
          β * (dEnd ρ W y rs lam om m1 mv b).2.2.2.1 := by
  have z : (0 : K) = 0 + β * 0 := by ring
  have sm : ∀ (n : ℕ) (c : ℕ → K) (f g : ℕ → K), ∑ i ∈ range n, c i * (f i + β * g i) =
      ∑ i ∈ range n, c i * f i + β * ∑ i ∈ range n, c i * g i := by
    intro n c f g
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  unfold dEnd
  cases b.tri with
  | true =>
    cases b.virt with
    | some k =>
      cases b.v0 with
      | some v0 => exact ⟨by ring, by ring⟩
      | none => exact ⟨z, z⟩
    | none =>
      cases b.v0 with
      | some v0 => exact ⟨z, by ring⟩
      | none => exact ⟨z, z⟩
  | false =>
    cases b.virt with
    | some k =>
      cases b.v0 with
      | some v0 => exact ⟨by ring, sm _ _ _ _⟩
      | none => exact ⟨z, z⟩
    | none =>
      cases b.v0 with
      | some v0 => exact ⟨z, sm _ _ _ _⟩
      | none => exact ⟨z, z⟩

/-- What the verifier's element of the field for the A side would be at other end values: a0 for
the part of the side that is a form in the reads, h1 and vv for the never-sent vectors and the
weight claims. -/
def AsAt (ρ : Reading K) (W : World K) (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E)
    (h1 vv : ℕ → K) (a0 : K) (l : List SBlk) : K :=
  a0 + (l.map fun b => (dEnd ρ W y rs lam om h1 vv b).2.2.1).sum

/-- The same for the B side. -/
def BsAt (ρ : Reading K) (W : World K) (y : Lay) (rs : Array E) (lam : ℕ) (om : Array E)
    (h1 vv : ℕ → K) (b0 : K) (l : List SBlk) : K :=
  b0 + (l.map fun b => (dEnd ρ W y rs lam om h1 vv b).2.2.2.1).sum

/-- The four values that the end of the batched sumcheck leaves. The two forms are worth what the
panels add to them, whatever end values dEnd is given. The two elements of the field are AsAt and
BsAt at the values that the function was given. -/
theorem stackEnd_four (h1 vv : ℕ → K) {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd}
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    s'.Alin.value ρ W = (bl.toList.map fun b => (dEnd ρ W y rs lam om h1 vv b).1).sum ∧
      s'.Blin.value ρ W = (bl.toList.map fun b => (dEnd ρ W y rs lam om h1 vv b).2.1).sum ∧
      ρ.val s'.As =
        AsAt ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) (ρ.val shownA) bl.toList ∧
      ρ.val s'.Bs =
        BsAt ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) (ρ.val shownB) bl.toList := by
  have st : ∀ (b : SBlk) (s s2 : StackEnd), stackEndOf y rs lam om H1 V s b = some s2 →
      rd ρ W s2 = rd ρ W s + dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b :=
    fun _ _ _ hs => stackEndOf_rd hs
  unfold stackEnd at h
  obtain ⟨s1, hf, h⟩ := bind_some h
  by_cases hw : (s1.wD != y.h.ll + y.lPf) = true
  · rw [if_pos hw] at h
    cases h
  · rw [if_neg hw] at h
    cases h
    rw [← Array.foldlM_toList] at hf
    have z : ({} : Aff).value ρ W = 0 := Aff.value_empty ρ W
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [foldlM_add (fun s : StackEnd => s.Alin.value ρ W) _
        (fun b => (dEnd ρ W y rs lam om h1 vv b).1) (fun b s s2 hs => by
          show s2.Alin.value ρ W = s.Alin.value ρ W + (dEnd ρ W y rs lam om h1 vv b).1
          rw [(dEnd_forms ρ W y rs lam om h1 vv (valsOf ρ H1) (valsOf ρ V) b).1]
          exact congrArg (fun m : K × K × K × K × ℕ => m.1) (st b s s2 hs)) _ _ _ hf]
      show ({} : Aff).value ρ W + _ = _
      rw [z, zero_add]
    · rw [foldlM_add (fun s : StackEnd => s.Blin.value ρ W) _
        (fun b => (dEnd ρ W y rs lam om h1 vv b).2.1) (fun b s s2 hs => by
          show s2.Blin.value ρ W = s.Blin.value ρ W + (dEnd ρ W y rs lam om h1 vv b).2.1
          rw [(dEnd_forms ρ W y rs lam om h1 vv (valsOf ρ H1) (valsOf ρ V) b).2]
          exact congrArg (fun m : K × K × K × K × ℕ => m.2.1) (st b s s2 hs)) _ _ _ hf]
      show ({} : Aff).value ρ W + _ = _
      rw [z, zero_add]
    · exact foldlM_add (fun s : StackEnd => ρ.val s.As) _
        (fun b => (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b).2.2.1) (fun b s s2 hs =>
          congrArg (fun m : K × K × K × K × ℕ => m.2.2.1) (st b s s2 hs)) _ _ _ hf
    · exact foldlM_add (fun s : StackEnd => ρ.val s.Bs) _
        (fun b => (dEnd ρ W y rs lam om (valsOf ρ H1) (valsOf ρ V) b).2.2.2.1) (fun b s s2 hs =>
          congrArg (fun m : K × K × K × K × ℕ => m.2.2.2.1) (st b s s2 hs)) _ _ _ hf

/-- The end of the batched sumcheck, as values of two long vectors at the end point, on any end
values that are true of the vectors hv, wv. On each side: the form's value, in the place of the
side's own end value, plus what the panels add at these end values, is the extension of the long
vector. The arrays that the verifier's function was given are not read: only that it returned. -/
theorem ends_mean {h1 vv : ℕ → K} {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd}
    (ok : ∀ b ∈ bl.toList, PanelOK y rs lam b)
    (tr : ∀ b ∈ bl.toList, EndsTrue ρ rs h1 vv hv wv b)
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') :
    AsAt ρ W y rs lam om h1 vv (s'.Alin.value ρ W) bl.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y * vecOf (aG ρ W y om hv) bl.toList Y ∧
      BsAt ρ W y rs lam om h1 vv (s'.Blin.value ρ W) bl.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y * vecOf (bG ρ W wv) bl.toList Y := by
  have each := stackEnd_each h
  obtain ⟨fA, fB, -, -⟩ := stackEnd_four (ρ := ρ) (W := W) h1 vv h
  unfold AsAt BsAt vecOf
  rw [fA, fB, ← List.sum_map_add, ← List.sum_map_add, ← list_sum_places, ← list_sum_places]
  refine ⟨congrArg List.sum (List.map_congr_left fun b hb => ?_),
    congrArg List.sum (List.map_congr_left fun b hb => ?_)⟩
  · obtain ⟨s1, s2, hs⟩ := each b hb
    rw [← (ok b hb).places (ρ := ρ) (stackEndOf_ok hs) (aG ρ W y om hv b)]
    exact (panel_mean (ok b hb) (tr b hb) hs).1
  · obtain ⟨s1, s2, hs⟩ := each b hb
    rw [← (ok b hb).places (ρ := ρ) (stackEndOf_ok hs) (bG ρ W wv b)]
    exact (panel_mean (ok b hb) (tr b hb) hs).2

/-- The end values that a panel reads have numbers below nv (never-sent vectors) and below n (weight
claims): the panel's never-sent vector, if it has one; its one weight claim if it has the selector,
else one for each row. -/
def ReadsIn (nv n : ℕ) (b : SBlk) : Prop :=
  (∀ k, b.virt = some k → k < nv) ∧
    ∀ v0, b.v0 = some v0 → v0 + (if b.tri then 1 else b.ni) ≤ n

variable (ρ W y rs lam om) in
/-- What a panel adds hangs on the end values that it reads alone. -/
theorem dEnd_congr {nv n : ℕ} {b : SBlk} (R : ReadsIn nv n b) {h1 h1' vv vv' : ℕ → K}
    (e1 : ∀ k, k < nv → h1 k = h1' k) (eV : ∀ m, m < n → vv m = vv' m) :
    dEnd ρ W y rs lam om h1 vv b = dEnd ρ W y rs lam om h1' vv' b := by
  obtain ⟨R1, R2⟩ := R
  unfold dEnd
  cases ht : b.tri with
  | true =>
    rw [ht] at R2
    cases h0 : b.v0 with
    | none => cases b.virt <;> rfl
    | some v0 =>
      have hv : vv v0 = vv' v0 := eV v0 (by have := R2 v0 h0; simp at this; omega)
      cases hk : b.virt with
      | some k =>
        show (0, 0, c1K ρ y rs lam om b * h1 k, sbK ρ rs lam b * vv v0, 0) =
          ((0, 0, c1K ρ y rs lam om b * h1' k, sbK ρ rs lam b * vv' v0, 0) : K × K × K × K × ℕ)
        rw [e1 k (R1 k hk), hv]
      | none =>
        show (_, 0, 0, sbK ρ rs lam b * vv v0, 0) =
          ((_, 0, 0, sbK ρ rs lam b * vv' v0, 0) : K × K × K × K × ℕ)
        rw [hv]
  | false =>
    rw [ht] at R2
    cases h0 : b.v0 with
    | none => cases b.virt <;> rfl
    | some v0 =>
      have hv : ∀ i, i < b.ni → vv (v0 + i) = vv' (v0 + i) := fun i hi =>
        eV (v0 + i) (by have := R2 v0 h0; simp at this; omega)
      cases hk : b.virt with
      | some k =>
        show (0, 0, sbK ρ rs lam b * omK ρ om b * h1 k,
            ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
              vv (v0 + i), b.w) =
          ((0, 0, sbK ρ rs lam b * omK ρ om b * h1' k,
            ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
              vv' (v0 + i), b.w) : K × K × K × K × ℕ)
        have es : ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec * wtK ρ b i *
            vv (v0 + i) = ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * ρ.val b.ec *
              wtK ρ b i * vv' (v0 + i) :=
          sum_congr rfl fun i hi => by rw [hv i (mem_range.mp hi)]
        rw [e1 k (R1 k hk), es]
      | none =>
        show (_, 0, 0, ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * vv (v0 + i), 0) =
          ((_, 0, 0, ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * vv' (v0 + i), 0) :
            K × K × K × K × ℕ)
        have es : ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * vv (v0 + i) =
            ∑ i ∈ range b.ni, sbK ρ rs lam b * eiK ρ rs b i * vv' (v0 + i) :=
          sum_congr rfl fun i hi => by rw [hv i (mem_range.mp hi)]
        rw [es]

variable (ρ W y rs lam om) in
/-- AsAt and BsAt hang on the end values that the list's panels read alone. -/
theorem AsAt_congr {nv n : ℕ} {l : List SBlk} (R : ∀ b ∈ l, ReadsIn nv n b)
    {h1 h1' vv vv' : ℕ → K} (e1 : ∀ k, k < nv → h1 k = h1' k) (eV : ∀ m, m < n → vv m = vv' m)
    (a0 : K) :
    AsAt ρ W y rs lam om h1 vv a0 l = AsAt ρ W y rs lam om h1' vv' a0 l ∧
      BsAt ρ W y rs lam om h1 vv a0 l = BsAt ρ W y rs lam om h1' vv' a0 l := by
  unfold AsAt BsAt
  refine ⟨congrArg (a0 + ·) (congrArg List.sum (List.map_congr_left fun b hb => ?_)),
    congrArg (a0 + ·) (congrArg List.sum (List.map_congr_left fun b hb => ?_))⟩
  · rw [dEnd_congr ρ W y rs lam om (R b hb) e1 eV]
  · rw [dEnd_congr ρ W y rs lam om (R b hb) e1 eV]

variable (ρ W y rs lam om) in
/-- AsAt and BsAt are linear in the end values. -/
theorem AsAt_linear (h1 vv m1 mv : ℕ → K) (β a0 mA : K) (l : List SBlk) :
    AsAt ρ W y rs lam om (fun k => h1 k + β * m1 k) (fun n => vv n + β * mv n) (a0 + β * mA) l =
        AsAt ρ W y rs lam om h1 vv a0 l + β * AsAt ρ W y rs lam om m1 mv mA l ∧
      BsAt ρ W y rs lam om (fun k => h1 k + β * m1 k) (fun n => vv n + β * mv n) (a0 + β * mA) l =
        BsAt ρ W y rs lam om h1 vv a0 l + β * BsAt ρ W y rs lam om m1 mv mA l := by
  have sl : ∀ (l : List SBlk) (f g : SBlk → K),
      (l.map fun b => f b + β * g b).sum = (l.map f).sum + β * (l.map g).sum := by
    intro l f g
    induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  unfold AsAt BsAt
  simp only [(dEnd_linear ρ W y rs lam om h1 vv m1 mv β _).1,
    (dEnd_linear ρ W y rs lam om h1 vv m1 mv β _).2, sl]
  exact ⟨by ring, by ring⟩

/-- What the verifier's own two elements of the field are in a run that hides. If every value that
the function was given is a hidden value plus β times a mask entry, each of the two elements is what
it would be at the hidden values, plus β times what it would be at the mask entries. The equations
are asked of the arrays' members alone (e1, eV); for that the panels must read inside the arrays: R,
hH, hV. The factors b.sl and the sides b.A of the panels stand in AsAt as the verifier has them:
see this file's head. -/
theorem stackEnd_affine {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd}
    (h : stackEnd y bl rs lam om H1 V shownA shownB = some s') {nv n : ℕ}
    (R : ∀ b ∈ bl.toList, ReadsIn nv n b) (hH : nv ≤ H1.size) (hV : n ≤ V.size)
    {β a0 b0 mA mB : K} {h1 vv m1 mv : ℕ → K} (eA : ρ.val shownA = a0 + β * mA)
    (eB : ρ.val shownB = b0 + β * mB)
    (e1 : ∀ k, k < H1.size → ρ.val (H1.getD k zeroE) = h1 k + β * m1 k)
    (eV : ∀ m, m < V.size → ρ.val (V.getD m zeroE) = vv m + β * mv m) :
    ρ.val s'.As = AsAt ρ W y rs lam om h1 vv a0 bl.toList +
        β * AsAt ρ W y rs lam om m1 mv mA bl.toList ∧
      ρ.val s'.Bs = BsAt ρ W y rs lam om h1 vv b0 bl.toList +
        β * BsAt ρ W y rs lam om m1 mv mB bl.toList := by
  obtain ⟨-, -, fA, fB⟩ := stackEnd_four (ρ := ρ) (W := W) h1 vv h
  have c1 : ∀ k, k < nv → valsOf ρ H1 k = h1 k + β * m1 k :=
    fun k hk => e1 k (Nat.lt_of_lt_of_le hk hH)
  have cV : ∀ m, m < n → valsOf ρ V m = vv m + β * mv m :=
    fun m hm => eV m (Nat.lt_of_lt_of_le hm hV)
  rw [fA, fB, eA, eB, (AsAt_congr ρ W y rs lam om R c1 cV _).1,
    (AsAt_congr ρ W y rs lam om R c1 cV _).2]
  exact ⟨(AsAt_linear ρ W y rs lam om h1 vv m1 mv β a0 mA _).1,
    (AsAt_linear ρ W y rs lam om h1 vv m1 mv β b0 mB _).2⟩

/-- A sent value is a hidden value plus β times some number, whatever the two, if β is not 0. -/
theorem mask_met {β : K} (hβ : β ≠ 0) (sent hidden : K) :
    sent = hidden + β * ((sent - hidden) / β) := by
  have e : β * ((sent - hidden) / β) = sent - hidden := by field_simp
  rw [e]
  ring

variable (ρ) in
/-- The weight over a stretch of bits in the library's way of writing: one point for all lam bits,
the top bit's coordinate first, and the stretch's coordinates from number lam - hi on. -/
theorem eqR_lib (rs : Array E) {lo hi lam : ℕ} (h : hi ≤ lam) (c : ℕ) :
    eqR ρ rs lo hi c =
      Blocks.eqN (hi - lo) (lam - hi) (fun t => ρ.val (rs.getD (lam - 1 - t) zeroE)) c := by
  unfold eqR
  rw [← eqN_shift' (hi - lo) (lam - hi)]
  refine eqN_congr' (K := K) _ _ (fun j _ => ?_) c
  have e : lam - 1 - (lam - hi + (0 + j)) = hi - 1 - (0 + j) := by omega
  show ρ.val (rs.getD (hi - 1 - (0 + j)) zeroE) =
    ρ.val (rs.getD (lam - 1 - (lam - hi + (0 + j))) zeroE)
  rw [e]

end Long

/-! ## The panels do not overlap -/

section Apart

/-- A sum over places of a function that lives on the window from a on, of length n. -/
theorem sum_window {a n N : ℕ} (h : a + n ≤ N) (f : ℕ → K) :
    ∑ Y ∈ range N, (if a ≤ Y ∧ Y < a + n then f (Y - a) else 0) = ∑ p ∈ range n, f p := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have z1 : ∑ Y ∈ range a, (if a ≤ Y ∧ Y < a + n then f (Y - a) else 0) = 0 :=
    sum_eq_zero fun Y hY => if_neg (by have := mem_range.mp hY; omega)
  have z2 : ∑ x ∈ range r,
      (if a ≤ a + n + x ∧ a + n + x < a + n then f (a + n + x - a) else 0) = 0 :=
    sum_eq_zero fun Y _ => if_neg (by omega)
  rw [z1, z2, zero_add, add_zero]
  refine sum_congr rfl fun p hp => ?_
  have := mem_range.mp hp
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A long vector is 0 at a place that no panel holds. -/
theorem vecOf_zero (G : SBlk → ℕ → ℕ → K) (Y : ℕ) : ∀ l : List SBlk,
    (∀ b ∈ l, ¬ (b.off ≤ Y ∧ Y < b.off + 2 ^ b.w)) → vecOf G l Y = 0
  | [], _ => rfl
  | b :: l, H => by
    have ih := vecOf_zero G Y l fun c hc => H c (List.mem_cons_of_mem _ hc)
    unfold vecOf at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, if_neg (H b List.mem_cons_self), add_zero]

/-- The share of a panel in the sum of the products of the two long vectors. -/
def shareOf (GA GB : SBlk → ℕ → ℕ → K) (b : SBlk) : K :=
  ∑ p ∈ range (2 ^ b.w), GA b (p / 2 ^ b.wy) (p % 2 ^ b.wy) * GB b (p / 2 ^ b.wy) (p % 2 ^ b.wy)

/-- If no two panels of the list hold a common place and all lie below N, the sum over the places of
the product of the two long vectors is the sum of the panels' shares. -/
theorem sum_vec_mul (GA GB : SBlk → ℕ → ℕ → K) (N : ℕ) : ∀ l : List SBlk,
    l.Pairwise (fun b c => b.off + 2 ^ b.w ≤ c.off ∨ c.off + 2 ^ c.w ≤ b.off) →
    (∀ b ∈ l, b.off + 2 ^ b.w ≤ N) →
    ∑ Y ∈ range N, vecOf GA l Y * vecOf GB l Y = (l.map (shareOf GA GB)).sum
  | [], _, _ => by simp [vecOf]
  | b :: l, hp, hN => by
    rw [List.pairwise_cons] at hp
    have ih := sum_vec_mul GA GB N l hp.2 fun c hc => hN c (List.mem_cons_of_mem _ hc)
    have e : ∀ Y, vecOf GA (b :: l) Y * vecOf GB (b :: l) Y =
        (if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
          GA b ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) *
            GB b ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0) +
          vecOf GA l Y * vecOf GB l Y := by
      intro Y
      have c1 : ∀ G : SBlk → ℕ → ℕ → K, vecOf G (b :: l) Y =
          (if b.off ≤ Y ∧ Y < b.off + 2 ^ b.w then
            G b ((Y - b.off) / 2 ^ b.wy) ((Y - b.off) % 2 ^ b.wy) else 0) + vecOf G l Y := by
        intro G
        unfold vecOf
        rw [List.map_cons, List.sum_cons]
      rw [c1 GA, c1 GB]
      by_cases hY : b.off ≤ Y ∧ Y < b.off + 2 ^ b.w
      · have hz : ∀ c ∈ l, ¬ (c.off ≤ Y ∧ Y < c.off + 2 ^ c.w) := by
          intro c hc hcY
          rcases hp.1 c hc with h1 | h1 <;> omega
        rw [if_pos hY, if_pos hY, if_pos hY, vecOf_zero GA Y l hz, vecOf_zero GB Y l hz]
        ring
      · rw [if_neg hY, if_neg hY, if_neg hY]
        ring
    simp only [e]
    rw [Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons,
      sum_window (hN b List.mem_cons_self)
        (fun p => GA b (p / 2 ^ b.wy) (p % 2 ^ b.wy) * GB b (p / 2 ^ b.wy) (p % 2 ^ b.wy))]
    rfl

end Apart

/-! ## The places that the verifier gives -/

section Placing

/-- The placing of a list of panels, each listed once: the first free place does not fall, every
placed panel lies between the first free place before and the first free place after and keeps its
size, and a panel that is placed earlier ends before a later one begins. -/
theorem place_span (bl : Array SBlk) : ∀ (l : List ℕ) (s : Array SBlk × ℕ), l.Nodup →
    (∀ i ∈ l, i < s.1.size) → (∀ i ∈ l, (s.1.getD i {}).w = wOf bl i) →
    s.2 ≤ (l.foldl (placeStep bl) s).2 ∧
      (∀ i ∈ l, s.2 ≤ ((l.foldl (placeStep bl) s).1.getD i {}).off ∧
        ((l.foldl (placeStep bl) s).1.getD i {}).off + 2 ^ wOf bl i ≤
          (l.foldl (placeStep bl) s).2 ∧
        ((l.foldl (placeStep bl) s).1.getD i {}).w = wOf bl i) ∧
      l.Pairwise (fun i j => ((l.foldl (placeStep bl) s).1.getD i {}).off + 2 ^ wOf bl i ≤
        ((l.foldl (placeStep bl) s).1.getD j {}).off)
  | [], s, _, _, _ => ⟨Nat.le_refl _, fun _ h => by simp at h, List.Pairwise.nil⟩
  | a :: l, s, hn, hs, hw => by
    have hn' := List.nodup_cons.mp hn
    have ha : a < s.1.size := hs a List.mem_cons_self
    have s2 : (placeStep bl s a).2 = s.2 + 2 ^ wOf bl a := rfl
    have hs' : ∀ i ∈ l, i < (placeStep bl s a).1.size := fun i hi => by
      have := hs i (List.mem_cons_of_mem _ hi)
      simpa [placeStep] using this
    have hw' : ∀ i ∈ l, ((placeStep bl s a).1.getD i {}).w = wOf bl i := fun i hi => by
      have hne : i ∉ [a] := by
        intro e
        rw [List.mem_singleton] at e
        exact hn'.1 (e ▸ hi)
      have e := place_other bl [a] s i hne
      have e' : (placeStep bl s a).1.getD i {} = s.1.getD i {} := e
      rw [e', hw i (List.mem_cons_of_mem _ hi)]
    obtain ⟨r1, r2, r3⟩ := place_span bl l (placeStep bl s a) hn'.2 hs' hw'
    have ea : ((a :: l).foldl (placeStep bl) s).1.getD a {} =
        { s.1.getD a {} with off := s.2 } := by
      rw [List.foldl_cons, place_other bl l _ a hn'.1, placeStep_self bl s a ha]
    rw [s2] at r1 r2
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons]
      exact Nat.le_trans (Nat.le_add_right _ _) r1
    · intro i hi
      rcases List.mem_cons.mp hi with e | hil
      · subst e
        rw [ea]
        refine ⟨Nat.le_refl _, ?_, hw i List.mem_cons_self⟩
        rw [List.foldl_cons]
        exact r1
      · rw [List.foldl_cons]
        obtain ⟨q1, q2, q3⟩ := r2 i hil
        exact ⟨Nat.le_trans (Nat.le_add_right _ _) q1, q2, q3⟩
    · rw [List.pairwise_cons]
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [ea, List.foldl_cons]
        exact (r2 j hj).1
      · rw [List.foldl_cons]
        exact r3

/-- The places that placePanels gives: every panel keeps its size and ends at or before the number
of all places, and two panels hold no common place. -/
theorem placePanels_apart (bl : Array SBlk) :
    (∀ i, i < bl.size → ((placePanels bl).1.getD i {}).w = wOf bl i ∧
      ((placePanels bl).1.getD i {}).off + 2 ^ wOf bl i ≤ (placePanels bl).2) ∧
    ∀ i j, i < bl.size → j < bl.size → i ≠ j →
      ((placePanels bl).1.getD i {}).off + 2 ^ wOf bl i ≤ ((placePanels bl).1.getD j {}).off ∨
      ((placePanels bl).1.getD j {}).off + 2 ^ wOf bl j ≤ ((placePanels bl).1.getD i {}).off := by
  obtain ⟨_, hn, hm⟩ := placeOrder_spec bl
  obtain ⟨_, r2, r3⟩ := place_span bl (placeOrder bl) (bl, 0) hn (fun i hi => (hm i).mp hi)
    (fun _ _ => rfl)
  rw [← placePanels_eq] at r2 r3
  refine ⟨fun i hi => ⟨(r2 i ((hm i).mpr hi)).2.2, (r2 i ((hm i).mpr hi)).2.1⟩, ?_⟩
  intro i j hi hj hij
  exact (r3.imp (S := fun i j =>
    ((placePanels bl).1.getD i {}).off + 2 ^ wOf bl i ≤ ((placePanels bl).1.getD j {}).off ∨
    ((placePanels bl).1.getD j {}).off + 2 ^ wOf bl j ≤ ((placePanels bl).1.getD i {}).off)
    Or.inl).forall (fun _ _ h => h.symm) ((hm i).mpr hi) ((hm j).mpr hj) hij

/-- The number of panels after the placing. -/
theorem placePanels_size (bl : Array SBlk) : (placePanels bl).1.size = bl.size := by
  rw [placePanels_eq, place_size]

/-- The same for the list of the placed panels. -/
theorem placed_list (bl : Array SBlk) :
    (placePanels bl).1.toList.Pairwise
        (fun b c => b.off + 2 ^ b.w ≤ c.off ∨ c.off + 2 ^ c.w ≤ b.off) ∧
      ∀ b ∈ (placePanels bl).1.toList, b.off + 2 ^ b.w ≤ (placePanels bl).2 ∧ 2 ^ b.w ∣ b.off := by
  obtain ⟨h1, h2⟩ := placePanels_apart bl
  have hsz := placePanels_size bl
  have get : ∀ i (hi : i < (placePanels bl).1.toList.length),
      (placePanels bl).1.toList[i] = (placePanels bl).1.getD i {} := by
    intro i hi
    have hi' : i < (placePanels bl).1.size := by simpa using hi
    simp [Array.getD, hi']
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < bl.size := by rw [← hsz]; simpa using hi
    have hj' : j < bl.size := by rw [← hsz]; simpa using hj
    rw [get i hi, get j hj, (h1 i hi').1, (h1 j hj').1]
    exact h2 i j hi' hj' (Nat.ne_of_lt hij)
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi' : i < bl.size := by rw [← hsz]; simpa using hi
    rw [get i hi, (h1 i hi').1]
    exact ⟨(h1 i hi').2, placePanels_dvd bl i hi'⟩

/-- On the places that the verifier gives, the sum over the places of the product of the two long
vectors is the sum of the panels' shares. -/
theorem placed_sum (GA GB : SBlk → ℕ → ℕ → K) (bl : Array SBlk) {lam : ℕ}
    (hN : (placePanels bl).2 ≤ 2 ^ lam) :
    ∑ Y ∈ range (2 ^ lam), vecOf GA (placePanels bl).1.toList Y *
      vecOf GB (placePanels bl).1.toList Y =
        ((placePanels bl).1.toList.map (shareOf GA GB)).sum :=
  sum_vec_mul GA GB _ _ (placed_list bl).1
    fun b hb => Nat.le_trans ((placed_list bl).2 b hb).1 hN

end Placing

/-! ## The product of the two sides at one place -/

section Shares

variable (y : Lay) (om : Array E) (hv wv : ℕ → ℕ → K) (b : SBlk)

/-- The rows of a panel that hold something. -/
def nRows : ℕ := if b.tri then y.h.NE else b.ni

/-- The weight of a row; with the selector, the one weight times the selector's shown value. -/
def rowW (i : ℕ) : K :=
  if b.tri then wtK ρ b 0 * ρ.val (b.sl.getD i zeroE) else wtK ρ b i

/-- What is left of the A side without the weights of the claim, of the call and of the row. -/
def aRaw (i yv : ℕ) : K :=
  match b.tri, b.virt with
  | true, some k => hv k yv
  | true, none => if yv < b.ny then (b.xx.getD yv {}).value ρ W else 0
  | false, some k => hv k (i * 2 ^ b.wy + yv)
  | false, none => if yv < b.ny then sideK ρ W b.A i yv else 0

/-- What is left of the B side without the weights of the call and of the row. -/
def bRaw (i yv : ℕ) : K :=
  match b.tri, b.virt, b.v0 with
  | true, _, some v0 => wv v0 (i * 2 ^ b.wy + yv)
  | false, _, some v0 => wv (v0 + i) yv
  | false, none, none => if yv < b.ny then sideK ρ W b.B i yv else 0
  | _, _, none => 0

/-- At every place of every panel the product of the two sides is the claim's weight times the
call's weight times the row's weight times what is left of the two sides. The first two are public.
The row's weight is public too, except with the selector, where it holds the selector's shown value.
So it does not matter for the summand on which side the verifier puts the call's weight and the
rows' weights. -/
theorem side_mul (i yv : ℕ) :
    aG ρ W y om hv b i yv * bG ρ W wv b i yv =
      if i < nRows y b then
        omK ρ om b * ρ.val b.ec * rowW ρ b i * (aRaw ρ W hv b i yv * bRaw ρ W wv b i yv)
      else 0 := by
  unfold aG bG nRows rowW aRaw bRaw
  cases b.tri <;> cases b.virt <;> cases b.v0 <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> (try split_ifs) <;> ring

variable {y b} in
/-- The share of a panel, by rows and columns. -/
theorem share_rows (hwy : b.wy ≤ b.w) (hn : nRows y b ≤ 2 ^ (b.w - b.wy)) :
    shareOf (aG ρ W y om hv) (bG ρ W wv) b =
      omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows y b), rowW ρ b i *
        ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv := by
  have hpy : 0 < 2 ^ b.wy := by positivity
  have e2 : (2 : ℕ) ^ b.w = 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
    rw [← pow_add]
    congr 1
    omega
  unfold shareOf
  rw [e2, sum_blocks, ← sum_trunc hn, Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ yv ∈ range (2 ^ b.wy),
      aG ρ W y om hv b ((i * 2 ^ b.wy + yv) / 2 ^ b.wy) ((i * 2 ^ b.wy + yv) % 2 ^ b.wy) *
        bG ρ W wv b ((i * 2 ^ b.wy + yv) / 2 ^ b.wy) ((i * 2 ^ b.wy + yv) % 2 ^ b.wy) =
      if i < nRows y b then
        omK ρ om b * ρ.val b.ec * rowW ρ b i * (aRaw ρ W hv b i yv * bRaw ρ W wv b i yv)
      else 0 := by
    intro yv hy
    have hy' : yv < 2 ^ b.wy := mem_range.mp hy
    rw [Nat.mul_comm i, Nat.mul_add_div hpy, Nat.mul_add_mod, Nat.div_eq_of_lt hy',
      Nat.mod_eq_of_lt hy', Nat.add_zero, side_mul]
  rw [sum_congr rfl e]
  by_cases h : i < nRows y b
  · simp only [if_pos h]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact sum_congr rfl fun yv _ => by ring
  · simp only [if_neg h, Finset.sum_const_zero, mul_zero]

end Shares

/-! ## From the panels' shape and the placing to the whole -/

section Whole

/-- What is asked of a panel's numbers before it is placed. -/
structure Shape (y : Lay) (b : SBlk) : Prop where
  /-- the bits of a column are among the bits of a place -/
  wy_le : b.wy ≤ b.w
  /-- the rows fit -/
  ni_le : b.ni ≤ 2 ^ (b.w - b.wy)
  /-- the columns fit -/
  ny_le : b.ny ≤ 2 ^ b.wy
  /-- with the selector: the experts fit -/
  ne_le : b.tri = true → y.h.NE ≤ 2 ^ (b.w - b.wy)

/-- The panel that plain appends has the shape. -/
theorem shape_plain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ)
    (s : OnBytes.Model.Layer.Panels) (hs : ∀ b ∈ s.bl.toList, Shape y b) :
    ∀ b ∈ (OnBytes.Model.Layer.plain y ec claim moeSet ny A B wt virt s).bl.toList, Shape y b := by
  intro b hb
  unfold OnBytes.Model.Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · refine ⟨Nat.le_add_left _ _, ?_, Slice.le_two_pow_ceilLog2 _, fun h => by cases h⟩
    show _ ≤ 2 ^ (ceilLog2 _ + ceilLog2 ny - ceilLog2 ny)
    rw [Nat.add_sub_cancel]
    exact Slice.le_two_pow_ceilLog2 _

/-- The panel that tri appends has the shape. -/
theorem shape_tri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : OnBytes.Model.Layer.Panels)
    (hs : ∀ b ∈ s.bl.toList, Shape y b) :
    ∀ b ∈ (OnBytes.Model.Layer.tri y ec claim nk sl xx virt wt s).bl.toList, Shape y b := by
  intro b hb
  unfold OnBytes.Model.Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · have e : y.h.NE ≤ 2 ^ (ceilLog2 (max y.h.NE 1) + ceilLog2 nk - ceilLog2 nk) := by
      rw [Nat.add_sub_cancel]
      exact Nat.le_trans (Nat.le_max_left _ _) (Slice.le_two_pow_ceilLog2 _)
    exact ⟨Nat.le_add_left _ _, e, Slice.le_two_pow_ceilLog2 _, fun _ => e⟩

/-- The placing changes nothing of a panel but its first place. -/
theorem place_keeps (bl : Array SBlk) : ∀ (l : List ℕ) (s : Array SBlk × ℕ) (i : ℕ),
    i < s.1.size → ∃ o, (l.foldl (placeStep bl) s).1.getD i {} = { s.1.getD i {} with off := o }
  | [], s, i, _ => ⟨(s.1.getD i {}).off, rfl⟩
  | a :: l, s, i, hi => by
    rw [List.foldl_cons]
    obtain ⟨o, ho⟩ := place_keeps bl l (placeStep bl s a) i (by simpa [placeStep] using hi)
    by_cases e : i = a
    · subst e
      rw [placeStep_self bl s i hi] at ho
      exact ⟨o, ho⟩
    · have e' : (placeStep bl s a).1.getD i {} = s.1.getD i {} :=
        place_other bl [a] s i (by simpa using e)
      rw [e'] at ho
      exact ⟨o, ho⟩

/-- Panels that have the shape, placed by the verifier in at most 2^lam places, meet all that the
theorems above ask of a panel's numbers. -/
theorem placed_ok {y : Lay} {rs : Array E} {lam : ℕ} (bl : Array SBlk)
    (sh : ∀ b ∈ bl.toList, Shape y b) (hN : (placePanels bl).2 ≤ 2 ^ lam) (hrs : lam ≤ rs.size) :
    ∀ b ∈ (placePanels bl).1.toList, PanelOK y rs lam b := by
  intro b hb
  obtain ⟨h1, h2⟩ := (placed_list bl).2 b hb
  obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
  have hi' : i < bl.size := by rw [← placePanels_size bl]; simpa using hi
  have hi2 : i < (placePanels bl).1.size := by simpa using hi
  obtain ⟨o, ho⟩ := place_keeps bl (placeOrder bl) (bl, 0) i hi'
  rw [← placePanels_eq] at ho
  have hbe : b = { bl.getD i {} with off := o } := by
    rw [← hbi, ← ho]
    simp [Array.getD, hi2]
  have hmem : bl.getD i {} ∈ bl.toList := by simp [Array.getD, hi']
  have S := sh _ hmem
  have hw : b.w ≤ lam := by
    have : 2 ^ b.w ≤ 2 ^ lam := Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) h1) hN
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  subst hbe
  exact ⟨S.wy_le, hw, hrs, S.ni_le, S.ny_le, S.ne_le, h2⟩

/-- A fold keeps what each of its steps keeps. -/
theorem foldl_inv {σ α : Type} (P : σ → Prop) (f : σ → α → σ) (H : ∀ s x, P s → P (f s x)) :
    ∀ (l : List α) (s : σ), P s → P (l.foldl f s)
  | [], _, h => h
  | x :: l, s, h => foldl_inv P f H l (f s x) (H s x h)

/-- The same for a fold of steps that may refuse. -/
theorem foldlM_inv {σ α : Type} (P : σ → Prop) (f : σ → α → Option σ)
    (H : ∀ s x s', P s → f s x = some s' → P s') :
    ∀ (l : List α) (s a : σ), P s → l.foldlM f s = some a → P a
  | [], s, a, h, e => by
    have hs : s = a := by simpa using e
    exact hs ▸ h
  | x :: l, s, a, h, e => by
    rw [List.foldlM_cons] at e
    obtain ⟨s', hq, e2⟩ := bind_some e
    exact foldlM_inv P f H l s' a (H s x s' h hq) e2

/-- What panelA appends has the shape. -/
theorem shape_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, Shape p.v.y b) :
    ∀ b ∈ (panelA p ec el sn s).bl.toList, Shape p.v.y b := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact shape_plain _ _ _ _ _ _ _ _ _ _ hs

/-- What panelT appends has the shape. -/
theorem shape_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ∀ b ∈ s.bl.toList, Shape p.v.y b) (h : panelT p ec el sn s = some s') :
    ∀ b ∈ s'.bl.toList, Shape p.v.y b := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact hs)
    | (cases h; exact shape_plain _ _ _ _ _ _ _ _ _ _ hs)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; exact shape_plain _ _ _ _ _ _ _ _ _ _ hs)
    | exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, Shape p.v.y b) _
        (fun s _ s' hs h => by
          first
            | (cases h; exact shape_tri _ _ _ _ _ _ _ _ _ hs)
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h; exact shape_tri _ _ _ _ _ _ _ _ _ hs))
        _ _ _ hs h

/-- Every panel of the verifier's own list has the shape. -/
theorem shape_panels (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ∀ b ∈ pans.bl.toList, Shape p.v.y b := by
  have h0 : ∀ b ∈ ({} : Panels).bl.toList, Shape p.v.y b := fun b hb => absurd hb List.not_mem_nil
  have hA : ∀ b ∈ (panelsA p {}).bl.toList, Shape p.v.y b := by
    unfold panelsA
    refine foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, Shape p.v.y b) _ (fun s q hs => ?_)
      _ _ h0
    exact foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, Shape p.v.y b) _
      (fun s g hs => shape_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, Shape p.v.y b) _
    (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, Shape p.v.y b) _
    (fun s g s' hs e => shape_panelT p _ _ _ s s' hs e) _ _ _ hs e

/-! ### The end values that the verifier's own panels read -/

/-- The number of never-sent vectors, as the verifier's caller counts them: one for the down
product, and one for each layer with routed experts if there are such. -/
def nVirt (y : Lay) : ℕ := 1 + (if y.h.p3 then y.LamM else 0)

/-- Every panel so far reads never-sent vectors below nv and weight claims below the number of the
next claim. -/
def ReadsAll (nv : ℕ) (s : Panels) : Prop := ∀ b ∈ s.bl.toList, ReadsIn nv s.nextV b

/-- No never-sent vector. -/
theorem virt_none (nv : ℕ) : ∀ k, (none : Option ℕ) = some k → k < nv := fun _ e => nomatch e

/-- One never-sent vector with a number below nv. -/
theorem virt_some {nv a : ℕ} (h : a < nv) : ∀ k, some a = some k → k < nv :=
  fun _ e => Option.some.inj e ▸ h

/-- plain keeps ReadsAll. -/
theorem reads_plain (nv : ℕ) (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ)
    (s : OnBytes.Model.Layer.Panels) (hv : ∀ k, virt = some k → k < nv) (hs : ReadsAll nv s) :
    ReadsAll nv (OnBytes.Model.Layer.plain y ec claim moeSet ny A B wt virt s) := by
  have en : (OnBytes.Model.Layer.plain y ec claim moeSet ny A B wt virt s).nextV =
      if B.isNone then s.nextV + (if moeSet then y.LamM else y.Lam) else s.nextV := rfl
  intro b hb
  rw [en]
  unfold OnBytes.Model.Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · refine ⟨(hs b hb).1, fun v0 h0 => Nat.le_trans ((hs b hb).2 v0 h0) ?_⟩
    split_ifs <;> omega
  · refine ⟨hv, fun v0 h0 => ?_⟩
    have h0' : (if B.isNone then some s.nextV else none) = some v0 := h0
    show v0 + (if moeSet then y.LamM else y.Lam) ≤ _
    by_cases hB : B.isNone = true
    · rw [if_pos hB] at h0' ⊢
      rw [← Option.some.inj h0']
    · rw [if_neg hB] at h0'
      cases h0'

/-- tri keeps ReadsAll. -/
theorem reads_tri (nv : ℕ) (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : OnBytes.Model.Layer.Panels)
    (hv : ∀ k, virt = some k → k < nv) (hs : ReadsAll nv s) :
    ReadsAll nv (OnBytes.Model.Layer.tri y ec claim nk sl xx virt wt s) := by
  intro b hb
  show ReadsIn nv (s.nextV + 1) b
  unfold OnBytes.Model.Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact ⟨(hs b hb).1, fun v0 h0 => Nat.le_trans ((hs b hb).2 v0 h0) (Nat.le_add_right _ _)⟩
  · refine ⟨hv, fun v0 h0 => ?_⟩
    have h0' : some s.nextV = some v0 := h0
    show v0 + 1 ≤ s.nextV + 1
    rw [← Option.some.inj h0']

/-- A fold of steps that may refuse keeps what each of its steps at a member of the list keeps. -/
theorem foldlM_inv_mem {σ α : Type} (P : σ → Prop) (f : σ → α → Option σ) :
    ∀ (l : List α), (∀ s x s', x ∈ l → P s → f s x = some s' → P s') →
      ∀ (s a : σ), P s → l.foldlM f s = some a → P a
  | [], _, s, a, h, e => by
    have hs : s = a := by simpa using e
    exact hs ▸ h
  | x :: l, H, s, a, h, e => by
    rw [List.foldlM_cons] at e
    obtain ⟨s', hq, e2⟩ := bind_some e
    exact foldlM_inv_mem P f l (fun s y s' hy => H s y s' (List.mem_cons_of_mem _ hy)) s' a
      (H s x s' List.mem_cons_self h hq) e2

/-- There is at least one never-sent vector. -/
theorem nVirt_pos (y : Lay) : 0 < nVirt y := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right _ _)

/-- panelA keeps ReadsAll. -/
theorem reads_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ReadsAll (nVirt p.v.y) s) : ReadsAll (nVirt p.v.y) (panelA p ec el sn s) := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact reads_plain _ _ _ _ _ _ _ _ _ _ _ (virt_none _) hs
    | exact reads_plain _ _ _ _ _ _ _ _ _ _ _ (virt_some (nVirt_pos _)) hs

/-- panelT keeps ReadsAll. -/
theorem reads_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ReadsAll (nVirt p.v.y) s) (h : panelT p ec el sn s = some s') :
    ReadsAll (nVirt p.v.y) s' := by
  cases h3 : p.v.y.h.p3 with
  | false =>
    simp only [panelT, h3, Bool.not_false, ↓reduceIte] at h
    split_ifs at h <;> first
      | (cases h; exact hs)
      | (cases h; exact reads_plain _ _ _ _ _ _ _ _ _ _ _ (virt_none _) hs)
      | (obtain ⟨_, _, h⟩ := bind_some h; cases h
         exact reads_plain _ _ _ _ _ _ _ _ _ _ _ (virt_none _) hs)
  | true =>
    have en : nVirt p.v.y = 1 + p.v.y.LamM := by simp [nVirt, h3]
    simp only [panelT] at h
    split_ifs at h <;> first
      | (cases h; exact hs)
      | (cases h; exact reads_plain _ _ _ _ _ _ _ _ _ _ _ (virt_none _) hs)
      | (obtain ⟨_, _, h⟩ := bind_some h; cases h
         exact reads_plain _ _ _ _ _ _ _ _ _ _ _ (virt_none _) hs)
      | exact foldlM_inv_mem (ReadsAll (nVirt p.v.y)) _ _
          (fun s lm s' hm hs h => by
            have hlt : 1 + lm < nVirt p.v.y := by
              have := List.mem_range.mp hm
              omega
            first
              | (cases h; exact reads_tri _ _ _ _ _ _ _ _ _ _ (virt_some hlt) hs)
              | (obtain ⟨_, _, h⟩ := bind_some h; cases h
                 exact reads_tri _ _ _ _ _ _ _ _ _ _ (virt_none _) hs))
          _ _ hs h

/-- Every panel of the verifier's own list reads never-sent vectors below the caller's number of
them, and weight claims below the number of the next claim after the last panel. -/
theorem reads_inside (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ReadsAll (nVirt p.v.y) pans := by
  have h0 : ReadsAll (nVirt p.v.y) ({} : Panels) := fun b hb => absurd hb List.not_mem_nil
  have hA : ReadsAll (nVirt p.v.y) (panelsA p {}) := by
    unfold panelsA
    refine foldl_inv (ReadsAll (nVirt p.v.y)) _ (fun s q hs => ?_) _ _ h0
    exact foldl_inv (ReadsAll (nVirt p.v.y)) _ (fun s g hs => reads_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (ReadsAll (nVirt p.v.y)) _ (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (ReadsAll (nVirt p.v.y)) _ (fun s g s' hs e => reads_panelT p _ _ _ s s' hs e)
    _ _ _ hs e

/-- A placed panel is a panel of the list with another first place. -/
theorem placed_from (bl : Array SBlk) :
    ∀ b ∈ (placePanels bl).1.toList, ∃ b0 ∈ bl.toList, ∃ o, b = { b0 with off := o } := by
  intro b hb
  obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
  have hi' : i < bl.size := by rw [← placePanels_size bl]; simpa using hi
  have hi2 : i < (placePanels bl).1.size := by simpa using hi
  obtain ⟨o, ho⟩ := place_keeps bl (placeOrder bl) (bl, 0) i hi'
  rw [← placePanels_eq] at ho
  refine ⟨bl.getD i {}, by simp [Array.getD, hi'], o, ?_⟩
  rw [← hbi, ← ho]
  simp [Array.getD, hi2]

/-- The placing does not change what a panel reads. -/
theorem reads_placed {nv n : ℕ} {bl : Array SBlk} (R : ∀ b ∈ bl.toList, ReadsIn nv n b) :
    ∀ b ∈ (placePanels bl).1.toList, ReadsIn nv n b := by
  intro b hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from bl b hb
  exact R b0 h0

/-- The caller's test on the number of places gives that they are at most 2^lam. -/
theorem places_le {n lam : ℕ} (h : (ceilLog2 n == lam) = true) : n ≤ 2 ^ lam :=
  (beq_iff_eq.mp h) ▸ Slice.le_two_pow_ceilLog2 n

variable {ρ W}

/-- The whole, on any end values. The panels have the shape and are placed by the verifier in at
most 2^lam places; the verifier's function has returned, on whatever arrays; the end values h1, vv
of the never-sent vectors and of the weight claims are true of the vectors hv, wv; a0 and b0 are the
values of the two forms. Then AsAt and BsAt at these values are the extensions of two long vectors
at the end point; and the sum over all places of the product of these two vectors is the sum over
the panels of the claim's weight times the call's weight times the sum over the rows of the row's
weight times the inner product of the row's two sides. -/
theorem stack_at {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {hv wv : ℕ → ℕ → K}
    {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd} (sh : ∀ b ∈ bl.toList, Shape y b)
    (hN : (placePanels bl).2 ≤ 2 ^ lam) (hrs : lam ≤ rs.size) {h1 vv : ℕ → K}
    (tr : ∀ b ∈ (placePanels bl).1.toList, EndsTrue ρ rs h1 vv hv wv b)
    (h : stackEnd y (placePanels bl).1 rs lam om H1 V shownA shownB = some s') {a0 b0 : K}
    (hA : s'.Alin.value ρ W = a0) (hB : s'.Blin.value ρ W = b0) :
    AsAt ρ W y rs lam om h1 vv a0 (placePanels bl).1.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (aG ρ W y om hv) (placePanels bl).1.toList Y ∧
      BsAt ρ W y rs lam om h1 vv b0 (placePanels bl).1.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (bG ρ W wv) (placePanels bl).1.toList Y ∧
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ W y om hv) (placePanels bl).1.toList Y *
        vecOf (bG ρ W wv) (placePanels bl).1.toList Y =
        ((placePanels bl).1.toList.map fun b =>
          omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows y b), rowW ρ b i *
            ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv).sum := by
  have ok := placed_ok (y := y) (rs := rs) bl sh hN hrs
  obtain ⟨mA, mB⟩ := ends_mean (W := W) ok tr h
  rw [hA] at mA
  rw [hB] at mB
  refine ⟨mA, mB, ?_⟩
  rw [placed_sum _ _ bl hN]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  refine share_rows ρ W om hv wv (ok b hb).wy_le ?_
  unfold nRows
  by_cases ht : b.tri = true
  · rw [if_pos ht]
    exact (ok b hb).ne_le ht
  · rw [if_neg ht]
    exact (ok b hb).ni_le

/-- The whole, on the verifier's own list of panels and under the caller's own test of the number of
places, on any end values. What is still asked: one challenge for each bit, that the end values are
true, and that a0 and b0 are the values of the two forms. Two things to mind (see this file's head):
AsAt and BsAt are not the elements on whose product the verifier makes the sumcheck's last test; and
the long A vector holds the values that the second token sumcheck sent, as they were sent. -/
theorem stack_hidden {p : PanelEnv} {TS : List ℕ} {pans : Panels} {rs : Array E} {lam : ℕ}
    {om H1 V : Array E} {hv wv : ℕ → ℕ → K} {shownA shownB : E} {s' : StackEnd}
    (hp : panelsT p TS (panelsA p {}) = some pans)
    (hl : (ceilLog2 (placePanels pans.bl).2 == lam) = true) (hrs : lam ≤ rs.size)
    {h1 vv : ℕ → K} (tr : ∀ b ∈ (placePanels pans.bl).1.toList, EndsTrue ρ rs h1 vv hv wv b)
    (h : stackEnd p.v.y (placePanels pans.bl).1 rs lam om H1 V shownA shownB = some s')
    {a0 b0 : K} (hA : s'.Alin.value ρ W = a0) (hB : s'.Blin.value ρ W = b0) :
    AsAt ρ W p.v.y rs lam om h1 vv a0 (placePanels pans.bl).1.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y ∧
      BsAt ρ W p.v.y rs lam om h1 vv b0 (placePanels pans.bl).1.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y ∧
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y *
        vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y =
        ((placePanels pans.bl).1.toList.map fun b =>
          omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows p.v.y b), rowW ρ b i *
            ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv).sum :=
  stack_at (shape_panels p TS hp) (places_le hl) hrs tr h hA hB

/-- stack_hidden at the hidden values of a world: those under the slots sA0 and sB0 for the two
sides, from sH1 on for the never-sent vectors, from sV on for the weight claims. cA, cB: the forms
"the hidden value under the slot, less the form that the end of the sumcheck leaves" are worth 0 in
the world. "Hidden" is said of these four runs of slots alone: the long A vector holds the values
that the second token sumcheck sent, as they were sent; and AsAt, BsAt at the hidden values are not
the elements on whose product the verifier makes the sumcheck's last test (stack_masked says what
these are). -/
theorem stack_slots {p : PanelEnv} {TS : List ℕ} {pans : Panels} {rs : Array E} {lam : ℕ}
    {om H1 V : Array E} {hv wv : ℕ → ℕ → K} {shownA shownB : E} {s' : StackEnd}
    (hp : panelsT p TS (panelsA p {}) = some pans)
    (hl : (ceilLog2 (placePanels pans.bl).2 == lam) = true) (hrs : lam ≤ rs.size)
    {sA0 sH1 sB0 sV : ℕ}
    (tr : ∀ b ∈ (placePanels pans.bl).1.toList,
      EndsTrue ρ rs (fun k => W.slot (sH1 + k)) (fun n => W.slot (sV + n)) hv wv b)
    (h : stackEnd p.v.y (placePanels pans.bl).1 rs lam om H1 V shownA shownB = some s')
    (cA : (Aff.slot sA0 - s'.Alin).value ρ W = 0) (cB : (Aff.slot sB0 - s'.Blin).value ρ W = 0) :
    AsAt ρ W p.v.y rs lam om (fun k => W.slot (sH1 + k)) (fun n => W.slot (sV + n))
        (W.slot sA0) (placePanels pans.bl).1.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y ∧
      BsAt ρ W p.v.y rs lam om (fun k => W.slot (sH1 + k)) (fun n => W.slot (sV + n))
        (W.slot sB0) (placePanels pans.bl).1.toList =
        ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y ∧
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y *
        vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y =
        ((placePanels pans.bl).1.toList.map fun b =>
          omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows p.v.y b), rowW ρ b i *
            ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv).sum := by
  rw [Aff.value_sub, Aff.value_slot] at cA cB
  exact stack_hidden hp hl hrs tr h (sub_eq_zero.mp cA).symm (sub_eq_zero.mp cB).symm

/-- stack_slots and stackEnd_affine joined: what the verifier's own two elements of the field are
in a run that hides, on the verifier's own list. Asked beside stack_slots' hypotheses: the two
arrays hold at least as many values as nVirt counts never-sent vectors and as the list has weight
claims (hH, hV; on the caller's arrays see this file's head); each value that the function was
given is the hidden value under its slot plus β times a number (eA, eB, e1, eV, on the arrays'
members alone). Then each element is the extension of its long vector at the end point, plus β
times what the element would be at these numbers. The long A vector holds the values that the
second token sumcheck sent, as they were sent: see this file's head. -/
theorem stack_masked {p : PanelEnv} {TS : List ℕ} {pans : Panels} {rs : Array E} {lam : ℕ}
    {om H1 V : Array E} {hv wv : ℕ → ℕ → K} {shownA shownB : E} {s' : StackEnd}
    (hp : panelsT p TS (panelsA p {}) = some pans)
    (hl : (ceilLog2 (placePanels pans.bl).2 == lam) = true) (hrs : lam ≤ rs.size)
    {sA0 sH1 sB0 sV : ℕ}
    (tr : ∀ b ∈ (placePanels pans.bl).1.toList,
      EndsTrue ρ rs (fun k => W.slot (sH1 + k)) (fun n => W.slot (sV + n)) hv wv b)
    (h : stackEnd p.v.y (placePanels pans.bl).1 rs lam om H1 V shownA shownB = some s')
    (cA : (Aff.slot sA0 - s'.Alin).value ρ W = 0) (cB : (Aff.slot sB0 - s'.Blin).value ρ W = 0)
    (hH : nVirt p.v.y ≤ H1.size) (hV : pans.nextV ≤ V.size) {β mA mB : K} {m1 mv : ℕ → K}
    (eA : ρ.val shownA = W.slot sA0 + β * mA) (eB : ρ.val shownB = W.slot sB0 + β * mB)
    (e1 : ∀ k, k < H1.size → ρ.val (H1.getD k zeroE) = W.slot (sH1 + k) + β * m1 k)
    (eV : ∀ n, n < V.size → ρ.val (V.getD n zeroE) = W.slot (sV + n) + β * mv n) :
    ρ.val s'.As = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y +
        β * AsAt ρ W p.v.y rs lam om m1 mv mA (placePanels pans.bl).1.toList ∧
      ρ.val s'.Bs = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
          vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y +
        β * BsAt ρ W p.v.y rs lam om m1 mv mB (placePanels pans.bl).1.toList := by
  obtain ⟨xA, xB, -⟩ := stack_slots hp hl hrs tr h cA cB
  obtain ⟨fA, fB⟩ := stackEnd_affine (W := W) h (reads_placed (reads_inside p TS hp)) hH hV eA eB
    e1 eV
  rw [fA, fB, xA, xB]
  exact ⟨rfl, rfl⟩

/-- stack_at on the values that were sent. Asked: these are true of the vectors hv, wv (ShownTrue),
and the two sent values of the sides are the values of the two forms (hA, hB). Then the verifier's
own two elements of the field are the extensions of the two long vectors. By the text of the
verifier's caller (see this file's head) its claims give hA and hB of the hidden values, not of the
sent ones; so this form meets the caller's run only where the masks' share in the sent values is 0.
stackEnd_affine says what the two elements are otherwise. -/
theorem stack_whole {y : Lay} {rs : Array E} {lam : ℕ} {om H1 V : Array E} {hv wv : ℕ → ℕ → K}
    {bl : Array SBlk} {shownA shownB : E} {s' : StackEnd} (sh : ∀ b ∈ bl.toList, Shape y b)
    (hN : (placePanels bl).2 ≤ 2 ^ lam) (hrs : lam ≤ rs.size)
    (tr : ∀ b ∈ (placePanels bl).1.toList, ShownTrue ρ rs H1 V hv wv b)
    (h : stackEnd y (placePanels bl).1 rs lam om H1 V shownA shownB = some s')
    (hA : s'.Alin.value ρ W = ρ.val shownA) (hB : s'.Blin.value ρ W = ρ.val shownB) :
    ρ.val s'.As = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
        vecOf (aG ρ W y om hv) (placePanels bl).1.toList Y ∧
      ρ.val s'.Bs = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
        vecOf (bG ρ W wv) (placePanels bl).1.toList Y ∧
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ W y om hv) (placePanels bl).1.toList Y *
        vecOf (bG ρ W wv) (placePanels bl).1.toList Y =
        ((placePanels bl).1.toList.map fun b =>
          omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows y b), rowW ρ b i *
            ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv).sum := by
  obtain ⟨-, -, fA, fB⟩ := stackEnd_four (ρ := ρ) (W := W) (valsOf ρ H1) (valsOf ρ V) h
  obtain ⟨mA, mB, mS⟩ := stack_at (W := W) sh hN hrs tr h hA hB
  exact ⟨fA.trans mA, fB.trans mB, mS⟩

/-- stack_whole on the verifier's own list of panels and under the caller's own test of the number
of places: on the values that were sent, with stack_whole's limit. The form on the hidden values is
stack_slots. -/
theorem stack_own {p : PanelEnv} {TS : List ℕ} {pans : Panels} {rs : Array E} {lam : ℕ}
    {om H1 V : Array E} {hv wv : ℕ → ℕ → K} {shownA shownB : E} {s' : StackEnd}
    (hp : panelsT p TS (panelsA p {}) = some pans)
    (hl : (ceilLog2 (placePanels pans.bl).2 == lam) = true) (hrs : lam ≤ rs.size)
    (tr : ∀ b ∈ (placePanels pans.bl).1.toList, ShownTrue ρ rs H1 V hv wv b)
    (h : stackEnd p.v.y (placePanels pans.bl).1 rs lam om H1 V shownA shownB = some s')
    (hA : s'.Alin.value ρ W = ρ.val shownA) (hB : s'.Blin.value ρ W = ρ.val shownB) :
    ρ.val s'.As = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
        vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y ∧
      ρ.val s'.Bs = ∑ Y ∈ range (2 ^ lam), eqR ρ rs 0 lam Y *
        vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y ∧
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ W p.v.y om hv) (placePanels pans.bl).1.toList Y *
        vecOf (bG ρ W wv) (placePanels pans.bl).1.toList Y =
        ((placePanels pans.bl).1.toList.map fun b =>
          omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows p.v.y b), rowW ρ b i *
            ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv).sum :=
  stack_whole (shape_panels p TS hp) (places_le hl) hrs tr h hA hB

end Whole

#print axioms eqLow_value
#print axioms eqLowAt_value
#print axioms eqR_split
#print axioms stackEndOf_rd
#print axioms stackEnd_rd
#print axioms PanelOK.places
#print axioms panel_mean
#print axioms stackEnd_mean
#print axioms eqR_lib
#print axioms sum_vec_mul
#print axioms placePanels_apart
#print axioms placed_list
#print axioms placed_sum
#print axioms side_mul
#print axioms share_rows
#print axioms shape_plain
#print axioms shape_tri
#print axioms placed_ok
#print axioms ends_mean
#print axioms stackEnd_four
#print axioms stackEnd_affine
#print axioms mask_met
#print axioms ends_met
#print axioms stack_at
#print axioms stack_hidden
#print axioms stack_slots
#print axioms reads_inside
#print axioms AsAt_congr
#print axioms stack_masked
#print axioms stack_whole
#print axioms shown_met
#print axioms shape_panels
#print axioms stack_own

end OnBytes.Road
