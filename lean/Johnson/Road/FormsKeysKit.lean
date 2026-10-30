-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysKit.lean: what the forms of a layer sub-proof's lookup keys are worth on
cells: the tools.

Two texts describe the keys that a layer sub-proof looks up. The verifier in OnBytes/ builds, for
each segment of a lookup call, an affine form in entries of the reads (Env.line in
OnBytes/Model/LayerForms.lean). The library defines, for each family, the key at one layer, one
entry and one position as a polynomial in the cells (FFSeg.key in Inst/Model/FF/Trace.lean), and its
part that is affine in the cells (FFSeg.lin in Inst/Model/FF/Objects.lean). The files
Johnson/Road/FormsKeys*.lean state in what sense the first is the second, family by family. This
file has what they share.

The sense. An entry of the reads stands for a sum of cells under the equality weights of a point. In
a world where every entry holds that sum (ShortTrue, LongTrue), the value of the form of a segment
is the sum, over the segment's entries x, of the weight of x times the multilinear extension, over
the positions, of the affine part of the keys at x.

Main definitions: Numerals, Cells, ShortTrue, LongTrue, Tied, Blocked, raw, wsum; arrName, segName,
byBlocks, readLong, readShort; HasLong, HasShort, Fits, Wts.
Main theorems: sumForms_value, limbs_value; short_true, long_true, blocks_true, shA_true,
shSum_true, SA_true, SBA_true, SxsA_true (what the readings of a tensor are worth); site_value,
high_value; Fits.shA, Fits.shSum, Fits.SA, Fits.SBA, Fits.Sxs (the same from the one record of
hypotheses); gl_numerals.

What is not claimed. Where a tensor lies in its matrix is taken from the verifier's layout (Tied): a
theorem here checks a form's index against the tensor's own place, not that place against the
library's rule; Johnson/Road/FormsKeysFits.lean does that. Which point and which matrix the name of
a family of tables stands for is not shown here: the record Fits says that the tables found under
"…@Z" are true at (low | u) and those under "…@zt" at u, and a theorem checks only that a form reads
the names that the record has; Johnson/Road/FormsKeysPoint.lean ties the names
to the verifier's own points and weights. Nothing is said about when a world is true, about the
products that some keys hold, about the weights' origin, or about what a verifier's acceptance
shows. Every theorem on a form begins "if the function returns a form": none says that it does. That
the record Fits holds of every layout that the verifier's function returns, under the switches and
in a world with true tables, is shown in Johnson/Road/FormsKeysAdmit.lean, not
here. The program does not import this file.

Files named above that a package may lack. Johnson/Road/FormsKeysFits.lean,
Johnson/Road/FormsKeysPoint.lean, Johnson/Road/FormsKeysAdmit.lean
and most of the files Johnson/Road/FormsKeys*.lean, those that go family by
family among them, are in the library's full tree and are not imported by this file; a package that
is cut to what its front theorems need may not hold them. Where they lack, what this comment says of
them cannot be checked there.

-/
import OnBytes.Model.LayerForms
import OnBytes.Model.HideLaws
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff tenCell TenAt)
open OnBytes.Model.Layer (Env Ten sumForms aff0 pw sumE)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW)

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-! ## Numerals -/

/-- A reading that takes the program's numerals, multiples and negatives to those of K. The three
are asked here as hypotheses: this file derives none of them from the laws of a reading. -/
structure Numerals : Prop where
  /-- a natural number -/
  ofNat : ∀ n : ℕ, ρ.val (Model.ofNat n) = (n : K)
  /-- a multiple by a natural number -/
  scaleNat : ∀ (x : E) (n : ℕ), ρ.val (Model.scaleNat x n) = (n : K) * ρ.val x
  /-- a negative -/
  neg : ∀ x : E, ρ.val (negE x) = -ρ.val x

variable {ρ} in
/-- The program's 2^k reads as 2^k. -/
theorem Numerals.pw (hρ : Numerals ρ) (k : ℕ) : ρ.val (pw k) = (2 : K) ^ k := by
  unfold Model.Layer.pw
  rw [hρ.ofNat, Nat.cast_pow, Nat.cast_ofNat]

/-! ## Sums -/

/-- A sum over a list of the first n numbers is the sum over the range. -/
theorem list_range_sum (g : ℕ → K) (n : ℕ) :
    ((List.range n).map g).sum = ∑ x ∈ range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A sum over a · b numbers, taken in a blocks of b numbers. -/
theorem sum_blocks (F : ℕ → K) (a b : ℕ) :
    ∑ x ∈ range (a * b), F x = ∑ xh ∈ range a, ∑ r ∈ range b, F (xh * b + r) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.add_mul, Nat.one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The sum of an array's members reads as the sum of their readings. -/
theorem sumE_value (v : Array E) :
    ρ.val (sumE v) = ∑ x ∈ range v.size, ρ.val (v.getD x zeroE) := by
  unfold Model.Layer.sumE
  refine Array.foldl_induction
    (motive := fun i acc => ρ.val acc = ∑ x ∈ range i, ρ.val (v.getD x zeroE)) ?_ ?_
  · simp [ρ.zero]
  · intro i b hb
    have hi : v.getD i.1 zeroE = v[i] := by simp [Array.getD, i.2]
    rw [ρ.add, hb, Finset.sum_range_succ, hi]

/-- If a pair made from an optional value is there, so is the value. -/
theorem map_pair_some {α β : Type} {o : Option α} {k k' : β} {b : α}
    (h : o.map (fun a => (a, k)) = some (b, k')) : o = some b ∧ k = k' := by
  cases o with
  | none => cases h
  | some a => cases h; exact ⟨rfl, rfl⟩

/-- The same for a pair that is made in a do block. -/
theorem bind_pair_some {α β : Type} {o : Option α} {k k' : β} {b : α}
    (h : (do let a ← o; pure (a, k)) = some (b, k')) : o = some b ∧ k = k' := by
  cases o with
  | none => cases h
  | some a => cases h; exact ⟨rfl, rfl⟩

/-- If the image of an optional value is there, so is the value. -/
theorem map_some {α β : Type} {o : Option α} {f : α → β} {y : β} (h : o.map f = some y) :
    ∃ a, o = some a ∧ f a = y := by
  cases o with
  | none => cases h
  | some a => cases h; exact ⟨a, rfl, rfl⟩

/-- If a do block that binds one optional value returns a value, the bound value is there. -/
theorem bind_some {α β : Type} {o : Option α} {k : α → Option β} {y : β}
    (h : (do let a ← o; k a) = some y) : ∃ a, o = some a ∧ k a = some y := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- The sum of the members a to b - 1 of an array reads as the sum of their readings. -/
theorem sumR_value (v : Array E) (a b : ℕ) (hb : b ≤ v.size) :
    ρ.val (Model.Layer.sumR v a b) = ∑ y ∈ range (b - a), ρ.val (v.getD (a + y) zeroE) := by
  have e : Model.Layer.sumR v a b = sumE (v.extract a b) := rfl
  have hs : (v.extract a b).size = b - a := by rw [Array.size_extract]; omega
  rw [e, sumE_value, hs]
  refine sum_congr rfl fun y hy => ?_
  have hy' : y < b - a := mem_range.mp hy
  have h1 : y < min b v.size - a := by omega
  have h2 : a + y < v.size := by omega
  simp [Array.getD, h1, h2]

/-! ## The value of a sum of forms -/

/-- The form 0 has the value 0. -/
theorem aff0_value : aff0.value ρ W = 0 := by
  unfold Model.Layer.aff0
  rw [Aff.value_ofConst, ρ.zero]

/-- The fold that sumForms runs, from any form s on: it adds the terms' values to the value of s. -/
theorem foldForms_value (f : ℕ → Option (Aff × E)) (g : ℕ → K)
    (H : ∀ x b k, f x = some (b, k) → ρ.val k * b.value ρ W = g x) :
    ∀ (l : List ℕ) (s a : Aff),
      l.foldlM (fun a x => (f x).map fun t => a.addMul t.1 t.2) s = some a →
      a.value ρ W = s.value ρ W + (l.map g).sum
  | [], s, a, h => by
    have hs : s = a := by simpa using h
    subst hs
    simp
  | x :: l, s, a, h => by
    rw [List.foldlM_cons] at h
    cases hq : f x with
    | none => simp [hq] at h
    | some t =>
      obtain ⟨b, k⟩ := t
      rw [hq] at h
      have h2 : l.foldlM (fun a x => (f x).map fun t => a.addMul t.1 t.2) (s.addMul b k) =
          some a := by simpa using h
      rw [foldForms_value f g H l _ a h2, Aff.value_addMul, H x b k hq, List.map_cons,
        List.sum_cons]
      ring

/-- The value of a sum of forms under coefficients: if term x is worth g x, the sum is worth the sum
of the g x. -/
theorem sumForms_value (n : ℕ) (f : ℕ → Option (Aff × E)) (g : ℕ → K)
    (H : ∀ x b k, f x = some (b, k) → ρ.val k * b.value ρ W = g x)
    {a : Aff} (h : sumForms n f = some a) : a.value ρ W = ∑ x ∈ range n, g x := by
  rw [foldForms_value ρ W f g H (List.range n) aff0 a h, aff0_value, zero_add, list_range_sum]

/-! ## Readings of a tensor, in terms of what the entries of one family of tables are worth -/

section Readings

variable {ρ W}
variable {v : Env} {tb : ℕ} (hρ : Numerals ρ) (r : ℕ → K)
  (H : ∀ φ a, v.U3at tb φ = some a → a.value ρ W = r φ)
include hρ H

/-- The limbs of a value, under the powers of 256. -/
theorem limbs_value {nl : ℕ} {cell : ℕ → ℕ} {a : Aff} (h : v.limbs tb nl cell = some a) :
    a.value ρ W = ∑ l ∈ range nl, (256 : K) ^ l * r (cell l) := by
  unfold Env.limbs at h
  refine sumForms_value ρ W nl _ _ ?_ h
  intro l b k hb
  obtain ⟨h1, h2⟩ := map_pair_some hb
  subst h2
  rw [hρ.ofNat, H _ _ h1, Nat.cast_pow, Nat.cast_ofNat]

end Readings

/-! ## True reads -/

/-- The cells of a sub-proof's matrices: the matrix's number, the feature, the position. The number
is that of Ten.mat (0 af, 1 ad, 2 ar, 3 qa); 4 and 5, by this file's own choice, stand for the
matrices of the stream that comes in and of the stream that goes out. A feature is counted across
all parts of a matrix, as the entries of its tables are. -/
abbrev Cells (K : Type) : Type := ℕ → ℕ → ℕ → K

/-- The short tables of one matrix at one point are true: every entry that the verifier can name in
the family that begins at tb holds its feature's cells, summed over the 2^lt positions under the
equality weights of the point u. -/
def ShortTrue (v : Env) (tb mat lt : ℕ) (c : Cells K) (u : ℕ → K) : Prop :=
  ∀ φ a, v.U3at tb φ = some a → a.value ρ W = Blocks.ext lt (fun i => c mat φ i) u

/-- The long tables of one matrix at one point are true: every entry that the verifier can name
holds the cells of its block of 2^ls features, summed under the equality weights of low over the
features of the block and of u over the positions. -/
def LongTrue (v : Env) (tb mat ls lt : ℕ) (c : Cells K) (low u : ℕ → K) : Prop :=
  ∀ b a, v.U3at tb b = some a → a.value ρ W =
    ∑ r ∈ range (2 ^ ls),
      Blocks.eqN ls 0 low r * Blocks.ext lt (fun i => c mat (b * 2 ^ ls + r) i) u

/-- The library's names of the cells of the array X are the cells of matrix mat at the verifier's
own places pl, and the library's value has as many cells as the verifier's tensor has limbs. The
library's own rule for the place of a cell is not read here: Johnson/Road/FormsKeysFits.lean
compares the two rules. All names are tied, those that the library never reads among them. -/
def Tied (c : Cells K) (t : Cell → K) (X : Arr) (mat : ℕ) (pl : TenAt) : Prop :=
  pl.nl = X.nCell ∧ ∀ k inst j i, t ⟨X, k, inst, j, i⟩ = c mat (tenCell pl k inst j) i

/-- The weights of the blocks and the weights of the entries are one set of weights: the weight of
entry r of block xh is the block's weight times the equality weight of low at r. This is asked of
every xh: past the last block both arrays read as 0, so ew may have no entry beyond wh's blocks. -/
def Blocked (ew wh : Array E) (ls : ℕ) (low : ℕ → K) : Prop :=
  ∀ xh r, r < 2 ^ ls →
    ρ.val (ew.getD (xh * 2 ^ ls + r) zeroE) = ρ.val (wh.getD xh zeroE) * Blocks.eqN ls 0 low r

/-- The library's value without its offset: what the cells alone spell. -/
def raw (t : Cell → K) (X : Arr) (inst j i : ℕ) : K :=
  Inst.Model.FFSeg.val t X inst j i - ((X.off : ℤ) : K)

/-- The limbs of a tied array spell the library's value without its offset. -/
theorem tied_raw {c : Cells K} {t : Cell → K} {X : Arr} {mat : ℕ} {pl : TenAt}
    (T : Tied c t X mat pl) (inst j i : ℕ) :
    ∑ k ∈ range pl.nl, (256 : K) ^ k * c mat (tenCell pl k inst j) i = raw t X inst j i := by
  unfold raw Inst.Model.FFSeg.val
  rw [T.1, add_sub_cancel_right]
  exact sum_congr rfl fun k _ => by rw [T.2]

/-- The extension of a value is spelt by the extensions of its limbs. -/
theorem ext_limbs (lt nl : ℕ) (F : ℕ → ℕ → K) (u : ℕ → K) :
    ∑ l ∈ range nl, (256 : K) ^ l * Blocks.ext lt (F l) u =
      Blocks.ext lt (fun i => ∑ l ∈ range nl, (256 : K) ^ l * F l i) u := by
  rw [Blocks.ext_sum]
  exact sum_congr rfl fun l _ => (Blocks.ext_smul lt _ (F l) u).symm

/-! ## Weighted sums of extensions -/

/-- The sum over x below n of g x times the extension of F x over the 2^lt positions at u. -/
def wsum (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) (F : ℕ → ℕ → K) : K :=
  ∑ x ∈ range n, g x * Blocks.ext lt (F x) u

section Wsum

variable (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ)

/-- A weighted sum is additive. -/
theorem wsum_add (F G : ℕ → ℕ → K) :
    wsum g lt u n (fun x i => F x i + G x i) = wsum g lt u n F + wsum g lt u n G := by
  unfold wsum
  rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by rw [Blocks.ext_add]; ring

/-- A weighted sum takes differences to differences. -/
theorem wsum_sub (F G : ℕ → ℕ → K) :
    wsum g lt u n (fun x i => F x i - G x i) = wsum g lt u n F - wsum g lt u n G := by
  unfold wsum
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun x _ => by rw [Blocks.ext_sub]; ring

/-- A constant factor moves out of a weighted sum. -/
theorem wsum_smul (k : K) (F : ℕ → ℕ → K) :
    wsum g lt u n (fun x i => k * F x i) = k * wsum g lt u n F := by
  unfold wsum
  rw [mul_sum]
  exact sum_congr rfl fun x _ => by rw [Blocks.ext_smul]; ring

/-- The weighted sum of a constant is the sum of the weights times the constant. -/
theorem wsum_const (k : K) :
    wsum g lt u n (fun _ _ => k) = (∑ x ∈ range n, g x) * k := by
  unfold wsum
  rw [sum_mul]
  exact sum_congr rfl fun x _ => by rw [Blocks.ext_const]

/-- A weighted sum reads F at the indices below n alone. -/
theorem wsum_congr {F G : ℕ → ℕ → K} (h : ∀ x, x < n → ∀ i, F x i = G x i) :
    wsum g lt u n F = wsum g lt u n G := by
  unfold wsum
  refine sum_congr rfl fun x hx => ?_
  have e : F x = G x := funext (h x (mem_range.mp hx))
  rw [e]

/-- A weighted sum over n + m indices, cut at n. -/
theorem wsum_split (m : ℕ) (F : ℕ → ℕ → K) :
    wsum g lt u (n + m) F =
      wsum g lt u n F + wsum (fun y => g (n + y)) lt u m (fun y => F (n + y)) := by
  unfold wsum
  rw [Finset.sum_range_add]

end Wsum

/-! ## Readings of a tensor from true tables -/

section True

variable {ρ W}
variable {v : Env} {tb lt : ℕ} (hρ : Numerals ρ) {c : Cells K} {t : Cell → K} {u : ℕ → K}
  {A : Arr} {mat : ℕ} {pl : TenAt} (T : Tied c t A mat pl)
include hρ T

/-- One entry, read limb by limb from true short tables. -/
theorem short_true (R : ShortTrue ρ W v tb mat lt c u) {i j : ℕ} {a : Aff}
    (h : v.limbs tb pl.nl (fun l => tenCell pl l i j) = some a) :
    a.value ρ W = Blocks.ext lt (raw t A i j) u := by
  rw [limbs_value hρ _ R h, ext_limbs]
  simp only [tied_raw T]

/-- One block, read limb by limb from true long tables. -/
theorem long_true {low : ℕ → K} (R : LongTrue ρ W v tb mat v.y.ls lt c low u)
    (hS2 : v.y.S2 = 2 ^ v.y.ls) {i : ℕ} (hal : ∀ l, v.y.S2 ∣ tenCell pl l i 0) {jh : ℕ} {a : Aff}
    (h : v.limbs tb pl.nl (fun l => tenCell pl l i 0 / v.y.S2 + jh) = some a) :
    a.value ρ W = ∑ r ∈ range (2 ^ v.y.ls),
      Blocks.eqN v.y.ls 0 low r * Blocks.ext lt (raw t A i (jh * 2 ^ v.y.ls + r)) u := by
  rw [limbs_value hρ _ R h]
  have idx : ∀ l r, (tenCell pl l i 0 / v.y.S2 + jh) * 2 ^ v.y.ls + r =
      tenCell pl l i (jh * 2 ^ v.y.ls + r) := by
    intro l r
    obtain ⟨q, hq⟩ := hal l
    have hpos : 0 < v.y.S2 := by rw [hS2]; positivity
    have e : tenCell pl l i (jh * 2 ^ v.y.ls + r) =
        tenCell pl l i 0 + (jh * 2 ^ v.y.ls + r) := rfl
    rw [e, hq, Nat.mul_div_cancel_left q hpos, ← hS2]
    ring
  simp only [idx, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun r _ => ?_
  have e : raw t A i (jh * 2 ^ v.y.ls + r) =
      fun p => ∑ k ∈ range pl.nl, (256 : K) ^ k * c mat (tenCell pl k i (jh * 2 ^ v.y.ls + r)) p :=
    funext fun p => (tied_raw T i _ p).symm
  rw [e, ← ext_limbs, mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-- A run of n blocks under the blocks' weights. Block number k of the run is block jh k = j0 + k of
the tensor's layer and has the weight of block xf k = k0 + k of the segment. -/
theorem blocks_true {low : ℕ → K} (R : LongTrue ρ W v tb mat v.y.ls lt c low u)
    (hS2 : v.y.S2 = 2 ^ v.y.ls) {i : ℕ} (hal : ∀ l, v.y.S2 ∣ tenCell pl l i 0)
    {ew wh : Array E} (hB : Blocked ρ ew wh v.y.ls low) (n : ℕ) (jh xf : ℕ → ℕ) (j0 k0 : ℕ)
    (hj : ∀ k, jh k = j0 + k) (hx : ∀ k, xf k = k0 + k) {a : Aff}
    (h : sumForms n (fun k => (v.limbs tb pl.nl (fun l => tenCell pl l i 0 / v.y.S2 + jh k)).map
      fun f => (f, wh.getD (xf k) zeroE)) = some a) :
    a.value ρ W = wsum (fun y => ρ.val (ew.getD (k0 * 2 ^ v.y.ls + y) zeroE)) lt u
      (n * 2 ^ v.y.ls) (fun y => raw t A i (j0 * 2 ^ v.y.ls + y)) := by
  unfold wsum
  rw [sum_blocks]
  refine sumForms_value ρ W n _ _ ?_ h
  intro k b q hb
  obtain ⟨h1, h2⟩ := map_pair_some hb
  subst h2
  rw [long_true hρ T R hS2 hal h1, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have e1 : k0 * 2 ^ v.y.ls + (k * 2 ^ v.y.ls + r) = xf k * 2 ^ v.y.ls + r := by rw [hx]; ring
  have e2 : j0 * 2 ^ v.y.ls + (k * 2 ^ v.y.ls + r) = jh k * 2 ^ v.y.ls + r := by rw [hj]; ring
  beta_reduce
  rw [e1, e2, hB _ r (mem_range.mp hr)]
  ring

end True

section TrueTen

variable {ρ W}
variable {v : Env} {tb lt : ℕ} (hρ : Numerals ρ) {c : Cells K} {t : Cell → K} {u : ℕ → K}
  {A : Arr} {ten : Ten} (T : Tied c t A ten.mat ten.place)
include hρ T

/-- One entry of a tensor, read from true short tables. -/
theorem shA_true (R : ShortTrue ρ W v tb ten.mat lt c u) {X P : String} {i j : ℕ}
    (hX : v.tensorAt X P = some (ten, tb)) {a : Aff} (h : v.shA X P i j = some a) :
    a.value ρ W = Blocks.ext lt (raw t A i j) u := by
  unfold Env.shA at h
  rw [hX] at h
  have h3 : v.limbs tb ten.place.nl (fun l => tenCell ten.place l i j) = some a := h
  exact short_true hρ T R h3

/-- A weighted sum over a tensor's entries, read from true short tables. -/
theorem shSum_true (R : ShortTrue ρ W v tb ten.mat lt c u) {ew : Array E} {n : ℕ} {X P : String}
    {i : ℕ} (hX : v.tensorAt X P = some (ten, tb)) {a : Aff} (h : v.shSum ew n X P i = some a) :
    a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) lt u n (raw t A i) := by
  unfold Env.shSum at h
  rw [hX] at h
  refine sumForms_value ρ W n _ _ ?_ h
  intro x b k hb
  obtain ⟨h1, h2⟩ := map_pair_some hb
  subst h2
  have h3 : v.limbs tb ten.place.nl (fun l => tenCell ten.place l i x) = some b := h1
  rw [short_true hρ T R h3]

variable {low : ℕ → K} (R : LongTrue ρ W v tb ten.mat v.y.ls lt c low u)
  (hS2 : v.y.S2 = 2 ^ v.y.ls) {i : ℕ} (hal : ∀ l, v.y.S2 ∣ tenCell ten.place l i 0)
  {ew wh : Array E} (hB : Blocked ρ ew wh v.y.ls low)
include R hS2 hal hB

/-- A weighted sum over all blocks of a tensor's layer, read from true long tables. -/
theorem SA_true {X Z : String} (hX : v.tensorAt X Z = some (ten, tb)) {a : Aff}
    (h : v.SA wh X i Z = some a) :
    a.value ρ W =
      wsum (fun x => ρ.val (ew.getD x zeroE)) lt u (wh.size * 2 ^ v.y.ls) (raw t A i) := by
  unfold Env.SA at h
  rw [hX] at h
  have h' : sumForms wh.size (fun k =>
      (v.limbs tb ten.place.nl (fun l => tenCell ten.place l i 0 / v.y.S2 + k)).map
        fun f => (f, wh.getD k zeroE)) = some a := h
  have e := blocks_true hρ T R hS2 hal hB wh.size (fun k => k) (fun k => k) 0 0
    (fun k => (Nat.zero_add k).symm) (fun k => (Nat.zero_add k).symm) h'
  simp only [Nat.zero_mul, Nat.zero_add] at e
  exact e

/-- A weighted sum over the blocks of the stretch from entry a0 to entry b0 of a segment. Entry x0
of the segment is the tensor's first feature and does not lie after a0. All three are whole numbers
of blocks. -/
theorem SBA_true {X Z : String} (hX : v.tensorAt X Z = some (ten, tb)) {a0 b0 x0 qa qb q0 : ℕ}
    (ha : a0 = qa * 2 ^ v.y.ls) (hb : b0 = qb * 2 ^ v.y.ls) (h0 : x0 = q0 * 2 ^ v.y.ls)
    (hle : q0 ≤ qa) {a : Aff} (h : v.SBA wh a0 b0 X i Z x0 = some a) :
    a.value ρ W = wsum (fun y => ρ.val (ew.getD (a0 + y) zeroE)) lt u ((qb - qa) * 2 ^ v.y.ls)
      (fun y => raw t A i ((qa - q0) * 2 ^ v.y.ls + y)) := by
  unfold Env.SBA at h
  rw [hX] at h
  have hpos : 0 < 2 ^ v.y.ls := by positivity
  have da : a0 / v.y.S2 = qa := by rw [hS2, ha, Nat.mul_div_cancel _ hpos]
  have db : b0 / v.y.S2 = qb := by rw [hS2, hb, Nat.mul_div_cancel _ hpos]
  have d0 : x0 / v.y.S2 = q0 := by rw [hS2, h0, Nat.mul_div_cancel _ hpos]
  have h' : sumForms (b0 / v.y.S2 - a0 / v.y.S2) (fun k =>
      (v.limbs tb ten.place.nl
        (fun l => tenCell ten.place l i 0 / v.y.S2 + (a0 / v.y.S2 + k - x0 / v.y.S2))).map
        fun f => (f, wh.getD (a0 / v.y.S2 + k) zeroE)) = some a := h
  have e := blocks_true hρ T R hS2 hal hB (b0 / v.y.S2 - a0 / v.y.S2)
    (fun k => a0 / v.y.S2 + k - x0 / v.y.S2) (fun k => a0 / v.y.S2 + k) (qa - q0) qa
    (fun k => by show a0 / v.y.S2 + k - x0 / v.y.S2 = qa - q0 + k; rw [da, d0]; omega)
    (fun k => by show a0 / v.y.S2 + k = qa + k; rw [da]) h'
  rw [da, db, ← ha] at e
  exact e

end TrueTen

/-! ## The residual stream -/

section Stream

variable {ρ W}

/-- The stream before the group's first write is the array x0. -/
theorem xS_first (D : Dim) (t : Cell → K) (j i : ℕ) :
    Inst.Model.FFSeg.xS D t 0 j i = raw t .x0 0 j i := by
  simp [Inst.Model.FFSeg.xS, Inst.Model.FFSeg.streamAt, raw, Arr.off]

/-- The stream after the group's last write is the array x8. -/
theorem xS_last (D : Dim) (t : Cell → K) {s : ℕ} (h0 : s ≠ 0) (h1 : s = 2 * D.nl) (j i : ℕ) :
    Inst.Model.FFSeg.xS D t s j i = raw t .x8 0 j i := by
  have hn : D.nl ≠ 0 := fun hz => h0 (by rw [h1, hz])
  simp [Inst.Model.FFSeg.xS, Inst.Model.FFSeg.streamAt, raw, Arr.off, hn, h1]

/-- The stream after any other write is a layer of the array xs. -/
theorem xS_mid (D : Dim) (t : Cell → K) {s : ℕ} (h0 : s ≠ 0) (h1 : s ≠ 2 * D.nl) (j i : ℕ) :
    Inst.Model.FFSeg.xS D t s j i = raw t .xs (s - 1) j i := by
  simp [Inst.Model.FFSeg.xS, Inst.Model.FFSeg.streamAt, raw, Arr.off, h0, h1]

/-- A weighted sum over the blocks of the residual stream after write number sg of the group, read
from true long tables. The verifier reads one of three matrices; the library names one of three
arrays; the two choices agree. The numbers 4 and 5 stand for the matrices of the stream that comes
in and of the stream that goes out. -/
theorem SxsA_true (hρ : Numerals ρ) {v : Env} {lt : ℕ} {c : Cells K} {t : Cell → K} {low u : ℕ → K}
    (D : Dim) (hlast : v.y.NW * v.y.Lam = 2 * D.nl) {Z : String} {bI bO bF : ℕ} {txs : Ten}
    (hI : v.tabAt ("xbI" ++ "@" ++ Z) = some bI) (hO : v.tabAt ("xbO" ++ "@" ++ Z) = some bO)
    (hF : v.tabAt ("af" ++ "@" ++ Z) = some bF) (hxs : v.y.T_ "xs" = some txs)
    (T0 : Tied c t .x0 4 v.y.xb) (T8 : Tied c t .x8 5 v.y.xb)
    (Ts : Tied c t .xs txs.mat txs.place)
    (R0 : LongTrue ρ W v bI 4 v.y.ls lt c low u) (R8 : LongTrue ρ W v bO 5 v.y.ls lt c low u)
    (Rs : LongTrue ρ W v bF txs.mat v.y.ls lt c low u)
    (hS2 : v.y.S2 = 2 ^ v.y.ls) (halb : ∀ l, v.y.S2 ∣ tenCell v.y.xb l 0 0)
    (hals : ∀ i l, v.y.S2 ∣ tenCell txs.place l i 0)
    {ew wh : Array E} (hB : Blocked ρ ew wh v.y.ls low) {sg : ℕ} {a : Aff}
    (h : v.SxsA wh Z sg = some a) :
    a.value ρ W = wsum (fun x => ρ.val (ew.getD x zeroE)) lt u
      (v.y.h.d / v.y.S2 * 2 ^ v.y.ls) (fun x i => Inst.Model.FFSeg.xS D t sg x i) := by
  have z : ∀ k : ℕ, k = 0 + k := fun k => (Nat.zero_add k).symm
  unfold Env.SxsA at h
  by_cases h0 : sg = 0
  · subst h0
    simp only [beq_self_eq_true, Bool.true_or, if_true, hI, hxs] at h
    have h' : sumForms (v.y.h.d / v.y.S2) (fun k =>
        (v.limbs bI v.y.xb.nl (fun l => tenCell v.y.xb l 0 0 / v.y.S2 + k)).map
          fun f => (f, wh.getD k zeroE)) = some a := h
    have e := blocks_true hρ T0 R0 hS2 halb hB _ (fun k => k) (fun k => k) 0 0 z z h'
    simp only [Nat.zero_mul, Nat.zero_add] at e
    rw [e]
    exact wsum_congr _ _ _ _ fun x _ i => (xS_first D t x i).symm
  · have b0 : (sg == 0) = false := by simp [h0]
    by_cases h1 : sg = 2 * D.nl
    · have b1 : (sg == v.y.NW * v.y.Lam) = true := by simp [hlast, h1]
      simp only [b0, b1, Bool.or_true, Bool.false_eq_true, if_false, if_true, hO, hxs] at h
      have h' : sumForms (v.y.h.d / v.y.S2) (fun k =>
          (v.limbs bO v.y.xb.nl (fun l => tenCell v.y.xb l 0 0 / v.y.S2 + k)).map
            fun f => (f, wh.getD k zeroE)) = some a := h
      have e := blocks_true hρ T8 R8 hS2 halb hB _ (fun k => k) (fun k => k) 0 0 z z h'
      simp only [Nat.zero_mul, Nat.zero_add] at e
      rw [e]
      exact wsum_congr _ _ _ _ fun x _ i => (xS_last D t h0 h1 x i).symm
    · have b1 : (sg == v.y.NW * v.y.Lam) = false := by simp [hlast, h1]
      simp only [b0, b1, Bool.or_false, Bool.false_eq_true, if_false, hF, hxs] at h
      have h' : sumForms (v.y.h.d / v.y.S2) (fun k =>
          (v.limbs bF txs.place.nl (fun l => tenCell txs.place l (sg - 1) 0 / v.y.S2 + k)).map
            fun f => (f, wh.getD k zeroE)) = some a := h
      have e := blocks_true hρ Ts Rs hS2 (hals (sg - 1)) hB _ (fun k => k) (fun k => k) 0 0 z z h'
      simp only [Nat.zero_mul, Nat.zero_add] at e
      rw [e]
      exact wsum_congr _ _ _ _ fun x _ i => (xS_mid D t h0 h1 x i).symm

end Stream

/-! ## The two keys of a rounding site, as forms -/

section Sites

variable {ρ W}

/-- The offset of a digit tensor of form 1 reads as 128. -/
theorem oOf_one (hρ : Numerals ρ) : ρ.val (Env.oOf 1) = 128 := by
  show ρ.val (Model.ofNat 128) = 128
  rw [hρ.ofNat]
  norm_num

/-- The offset of a digit tensor of form 2 reads as 32896. -/
theorem oOf_two (hρ : Numerals ρ) : ρ.val (Env.oOf 2) = 32896 := by
  show ρ.val (Model.ofNat 32896) = 32896
  rw [hρ.ofNat]
  norm_num

/-- The value of the key of the high digits. -/
theorem high_value (hρ : Numerals ρ) (w : E) (S : Aff) (k form : ℕ) :
    (Env.high w S k form).value ρ W =
      (2 : K) ^ ((if form == 1 then 24 else 32) - max k 16) *
        (ρ.val (Env.oOf form) * ρ.val w + S.value ρ W) := by
  unfold Env.high
  rw [Aff.value_scale, Aff.value_add, Aff.value_ofConst, ρ.mul, hρ.pw]

/-- The value of the low key without its accumulator, at a digit form other than 0. -/
theorem site_value (hρ : Numerals ρ) {w : E} {SQ : Aff} {k form : ℕ} {Srh : Unit → Option Aff}
    (hf : (form == 0) = false) {f : Aff} (h : Env.site w SQ k form Srh = some f) :
    ∃ S, Srh () = some S ∧ f.value ρ W =
      (2 : K) ^ (16 - k) * (ρ.val w * (2 : K) ^ (k - 1) - (2 : K) ^ k * SQ.value ρ W) -
        (2 : K) ^ 16 * (ρ.val (Env.oOf form) * ρ.val w + S.value ρ W) := by
  unfold Env.site at h
  rw [hf] at h
  cases hS : Srh () with
  | none => rw [hS] at h; cases h
  | some S =>
    rw [hS] at h
    cases h
    refine ⟨S, rfl, ?_⟩
    rw [Aff.value_sub, Aff.value_scale, Aff.value_sub, Aff.value_ofConst, Aff.value_scale,
      Aff.value_scale, Aff.value_add, Aff.value_ofConst, ρ.mul, ρ.mul, hρ.pw, hρ.pw, hρ.pw, hρ.pw]
    rfl

end Sites

/-! ## The reading in the library's field takes numerals to numbers -/

/-- Reading.gl has the three properties of Numerals. -/
theorem gl_numerals : Numerals Reading.gl where
  ofNat n := by
    have e : Model.fOfNat n = Fmt.Fld.two.red n := rfl
    show Slice.toE (ofF (Model.fOfNat n)).triple = _
    rw [ofF_triple, Slice.toE_ofF, e, Slice.toF_red, map_natCast]
  scaleNat x n := by
    have e : Model.fOfNat n = Fmt.Fld.two.red n := rfl
    show Slice.toE (scaleE (Model.fOfNat n) x).triple = _ * Slice.toE x.triple
    rw [scaleE_triple, Slice.toE_scaleE, e, Slice.toF_red, Algebra.smul_def, map_natCast]
  neg x := by
    show Slice.toE (negE x).triple = -Slice.toE x.triple
    rw [negE_triple, Slice.toE_negE]

/-- The constant of a clamp's key reads as 2^15 + 2^39. -/
theorem clampKey_value {ρ : Reading K} (hρ : Numerals ρ) :
    ρ.val Env.clampKey = (2 : K) ^ 15 + (2 : K) ^ 39 := by
  unfold Env.clampKey
  rw [hρ.ofNat]
  push_cast
  ring

/-! ## Names -/

/-- The verifier's name of the tensor that holds the library's array. The two arrays at the borders
of the residual stream are no tensors of the verifier's list: they have matrices of their own. -/
def arrName : Arr → String
  | .g0 => "g0" | .gc => "gc" | .sl => "s" | .up => "u" | .rg => "rg" | .ru => "ru" | .xs => "xs"
  | .ro => "ro" | .rd => "rd" | .aw => "aw" | .ra => "ra" | .mw => "mw" | .rm => "rm"
  | .qkw => "qkw" | .rqk => "rqk" | .vw => "vw" | .rv => "rv" | .gh => "gh"
  | .a => "a" | .m => "m" | .xr => "xr"
  | .lr => "lr" | .rl => "rl" | .sel => "sel" | .sc => "sc" | .D => "row" | .ly => "ly"
  | .l3 => "l3"
  | .q => "q" | .kx => "kx" | .v => "v" | .o => "o"
  | .x0 => "" | .x8 => ""

/-- The verifier's name of the segment that holds the library's family. -/
def segName : Fam → String
  | .G => "G" | .U => "U" | .UT => "UT" | .QK => "QK" | .N1 => "N1" | .N2 => "N2" | .O => "O"
  | .D => "D" | .V => "V" | .LR => "LR" | .XR => "XR" | .LT => "LT" | .DD => "DD" | .GH => "GH"
  | .UH => "UH" | .OH => "OH" | .DH => "DH" | .VH => "VH" | .LH => "LH" | .QKH => "QKH"
  | .N1H => "N1H" | .N2H => "N2H" | .ROW => "ROW" | .SEL => "SEL" | .L3 => "L3" | .G0 => "G0"
  | .CN1 => "CN1" | .CN2 => "CN2" | .CQK => "CQK" | .CV => "CV" | .CLR => "CLR" | .F => "F"
  | .MR => "MR" | .CG => "CG"

/-- True for a family whose form reads some tensor by blocks, and so reads the blocks' weights. -/
def byBlocks : Fam → Bool
  | .LR | .XR | .LT | .DD | .LH | .ROW | .SEL | .L3 | .CLR | .MR => false
  | _ => true

/-- True for an array that some segment's form reads by blocks, from long tables at the lookup's
point: the arrays of the matrix af, and q, kx and v of the matrix qa. The attention output o, the
fourth array of qa, is read by no segment's form. -/
def readLong : Arr → Bool
  | .g0 | .gc | .sl | .up | .rg | .ru | .xs | .ro | .rd | .aw | .ra | .mw | .rm | .qkw | .rqk | .vw
  | .rv | .gh | .q | .kx | .v => true
  | _ => false

/-- True for an array that some segment's form reads entry by entry, from short tables at the
lookup's token point: the arrays of the matrices ad and ar. The rows of digits (the array D) are
read in a way of their own and have their own field in Fits. -/
def readShort : Arr → Bool
  | .a | .m | .xr | .lr | .rl | .sel | .sc | .ly | .l3 => true
  | _ => false

/-! ## One record for the hypotheses -/

section Record

variable [scl : Scl] (v : Env) (D : Dim) (c : Cells K) (t : Cell → K) (low u : ℕ → K)

/-- The array X is read by blocks at the lookup's point: the verifier finds its tensor and the long
tables of its matrix at the point Z, the library's cell names are tied to the tensor's places, the
tables are true, and every run of the tensor begins at a whole block. -/
def HasLong (X : Arr) : Prop :=
  ∃ (ten : Ten) (b : ℕ), v.tensorAt (arrName X) "Z" = some (ten, b) ∧
    Tied c t X ten.mat ten.place ∧ LongTrue ρ W v b ten.mat v.y.ls D.lT c low u ∧
    ∀ i l, v.y.S2 ∣ tenCell ten.place l i 0

/-- The array X is read entry by entry at the lookup's token point: the same for the short tables at
the point zt. -/
def HasShort (X : Arr) : Prop :=
  ∃ (ten : Ten) (b : ℕ), v.tensorAt (arrName X) "zt" = some (ten, b) ∧
    Tied c t X ten.mat ten.place ∧ ShortTrue ρ W v b ten.mat D.lT c u

/-- All that the theorems on the forms of the lookup's segments ask: of the reading, of the world,
of the verifier's layout and scales against the library's sizes and table of scales, and of the
switches for which alone the library has keys. low: the coordinates of a feature's low bits in the
lookup's point; u: those of the position. -/
structure Fits : Prop where
  /-- the reading takes numerals to numbers -/
  num : Numerals ρ
  /-- a block has 2^ls features -/
  S2 : v.y.S2 = 2 ^ v.y.ls
  /-- the positions: the reads are true over as many positions as the verifier's shape has tokens -/
  lT : v.y.h.lt = D.lT
  /-- the width of the stream -/
  d : v.y.h.d = D.d
  /-- the hidden units of a layer -/
  f : v.y.h.f = D.f
  /-- the hidden units of one expert -/
  fe : v.y.h.fe = D.fe
  /-- the experts -/
  NE : v.y.h.NE = D.nx
  /-- the width of the queries -/
  dq : v.y.dq = D.dq
  /-- the width of the keys, and of the values -/
  dkv : v.y.dkv = D.dkv
  /-- the width of queries and keys together -/
  nqk : v.y.nqk = D.dqk
  /-- the stream's width is a whole number of blocks -/
  bd : ∃ n, D.d = n * 2 ^ v.y.ls
  /-- so is the number of a layer's hidden units -/
  bf : ∃ n, D.f = n * 2 ^ v.y.ls
  /-- and of one expert's -/
  bfe : ∃ n, D.fe = n * 2 ^ v.y.ls
  /-- so is the width of the queries -/
  bdq : ∃ n, D.dq = n * 2 ^ v.y.ls
  /-- and of the keys -/
  bdkv : ∃ n, D.dkv = n * 2 ^ v.y.ls
  /-- a layer with experts has f = 2 fe hidden units: the shared expert's and the routed one's -/
  ffe : D.f = D.fe + D.fe
  /-- the layers of a group -/
  Lam : v.y.Lam = D.nl
  /-- those of them that have routed experts -/
  LamM : v.y.LamM = D.ne
  /-- two norms in a layer -/
  NN : v.y.NN = 2
  /-- the writes to the stream in a group -/
  last : v.y.NW * v.y.Lam = 2 * D.nl
  /-- the odd layers have routed experts -/
  p3 : v.y.h.p3 = true
  /-- the gate's clamp is on -/
  gcl : v.y.h.gcl = true
  /-- the router's clamp is on -/
  rcl : v.y.h.rcl = true
  /-- a value of the stream has five limbs -/
  xl : v.y.h.xl = 5
  /-- the digit form of the roundings of queries and keys: two cells of high digits -/
  hq : v.y.h.hq = 2
  /-- of the values: one cell -/
  hv : v.y.h.hv = 1
  /-- of the attention output's product -/
  ho : v.y.h.ho = 1
  /-- of the gate -/
  hgD : v.y.h.hgD = 1
  /-- of the up product -/
  huD : v.y.h.huD = 1
  /-- of the down product -/
  hdD : v.y.h.hdD = 1
  /-- of the router -/
  hr : v.y.h.hr = 1
  /-- the shifts, on the layers of the group: the verifier's at the layer's number in the model, the
  library's at the layer's number in the group. Nothing is asked past the group's last layer: there
  the verifier may read another group's words or, past the end of the scale file, 0, while the
  library's theorems ask for lawful words at every number -/
  kq : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lkq = (D.Pl lam).kq
  /-- the keys' shift -/
  kk : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lkk = (D.Pl lam).kk
  /-- the values' -/
  kv : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lkv = (D.Pl lam).kv
  /-- the attention output's product's -/
  ko : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lko = (D.Pl lam).ko
  /-- the gate's -/
  kg : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lkg = (D.Pl lam).kg
  /-- the up product's -/
  ku : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lku = (D.Pl lam).ku
  /-- the down product's -/
  kd : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.Lkd = (D.Pl lam).kd
  /-- the first norm's -/
  K1 : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.LK1 = (D.Pl lam).n1.K
  /-- the second norm's -/
  K2 : ∀ lam, lam < D.nl → v.sc.kl (v.lay lam) Model.Layer.LK2 = (D.Pl lam).n2.K
  /-- the router's shift, on a layer with experts -/
  kr : ∀ lam, lam < D.nl → lam % 2 = 1 → v.sc.klM (v.lay lam) 0 = (D.Pl lam).kr
  /-- the routed expert's gate's -/
  kgR : ∀ lam, lam < D.nl → lam % 2 = 1 → v.sc.klM (v.lay lam) 1 = (D.Pl lam).kg'
  /-- the routed expert's up product's -/
  kuR : ∀ lam, lam < D.nl → lam % 2 = 1 → v.sc.klM (v.lay lam) 2 = (D.Pl lam).ku'
  /-- on the layers of the group the first norm's shift is at least 16: below, the library's two
  keys of a norm are not the verifier's -/
  K1le : ∀ lam, lam < D.nl → 16 ≤ (D.Pl lam).n1.K
  /-- the same for the second norm -/
  K2le : ∀ lam, lam < D.nl → 16 ≤ (D.Pl lam).n2.K
  /-- the arrays that are read by blocks -/
  long : ∀ X : Arr, readLong X = true → HasLong ρ W v D c t low u X
  /-- the arrays that are read entry by entry -/
  short : ∀ X : Arr, readShort X = true → HasShort ρ W v D c t u X
  /-- the tensor of rows: its short tables under the name that the verifier writes out, the matrix
  (ar, number 2) that this name belongs to, and the length of a row -/
  rowTab : ∃ (trow : Ten) (b : ℕ), v.tabAt "ar@zt" = some b ∧ v.y.T_ "row" = some trow ∧
    trow.mat = 2 ∧ Tied c t .D trow.mat trow.place ∧ trow.J = 99 ∧
    ShortTrue ρ W v b trow.mat D.lT c u
  /-- the residual stream: the three families of long tables under the names that the verifier
  writes out, the tensor xs in the matrix af (number 0), the two matrices at the borders (numbered 4
  and 5 here) -/
  stream : ∃ (bI bO bF : ℕ) (txs : Ten),
    v.tabAt ("xbI" ++ "@" ++ "Z") = some bI ∧ v.tabAt ("xbO" ++ "@" ++ "Z") = some bO ∧
    v.tabAt ("af" ++ "@" ++ "Z") = some bF ∧ v.y.T_ "xs" = some txs ∧ txs.mat = 0 ∧
    Tied c t .x0 4 v.y.xb ∧ Tied c t .x8 5 v.y.xb ∧ Tied c t .xs txs.mat txs.place ∧
    LongTrue ρ W v bI 4 v.y.ls D.lT c low u ∧ LongTrue ρ W v bO 5 v.y.ls D.lT c low u ∧
    LongTrue ρ W v bF txs.mat v.y.ls D.lT c low u ∧
    (∀ l, v.y.S2 ∣ tenCell v.y.xb l 0 0) ∧ ∀ i l, v.y.S2 ∣ tenCell txs.place l i 0

/-- What is asked of the weights of a segment with n entries that is read by blocks. -/
structure Wts (ew wh : Array E) (ls : ℕ) (low : ℕ → K) (n : ℕ) : Prop where
  /-- one weight for each entry -/
  size : ew.size = n
  /-- one weight for each block -/
  blocks : wh.size * 2 ^ ls = n
  /-- the two are one set of weights -/
  blocked : Blocked ρ ew wh ls low

variable {ρ W v D c t low u}

/-- The weight of entry x, read in K. -/
abbrev wt (ρ : Reading K) (ew : Array E) : ℕ → K := fun x => ρ.val (ew.getD x zeroE)

/-- One entry of an array that is read entry by entry. -/
theorem Fits.shA (F : Fits ρ W v D c t low u) (X : Arr) (hX : readShort X = true) {i j : ℕ}
    {a : Aff} (h : v.shA (arrName X) "zt" i j = some a) :
    a.value ρ W = Blocks.ext D.lT (raw t X i j) u := by
  obtain ⟨ten, b, h1, T, R⟩ := F.short X hX
  exact shA_true F.num T R h1 h

/-- A weighted sum over the entries of such an array. -/
theorem Fits.shSum (F : Fits ρ W v D c t low u) (X : Arr) (hX : readShort X = true)
    {ew : Array E} {n i : ℕ} {a : Aff} (h : v.shSum ew n (arrName X) "zt" i = some a) :
    a.value ρ W = wsum (wt ρ ew) D.lT u n (raw t X i) := by
  obtain ⟨ten, b, h1, T, R⟩ := F.short X hX
  exact shSum_true F.num T R h1 h

/-- A weighted sum over all blocks of a layer of an array that is read by blocks. -/
theorem Fits.SA (F : Fits ρ W v D c t low u) (X : Arr) (hX : readLong X = true)
    {ew wh : Array E} {n : ℕ} (hw : Wts ρ ew wh v.y.ls low n) {i : ℕ} {a : Aff}
    (h : v.SA wh (arrName X) i "Z" = some a) :
    a.value ρ W = wsum (wt ρ ew) D.lT u n (raw t X i) := by
  obtain ⟨ten, b, h1, T, R, hal⟩ := F.long X hX
  rw [SA_true F.num T R F.S2 (hal i) hw.blocked h1 h, hw.blocks]

/-- A weighted sum over the blocks of a stretch of a segment. The stretch begins at entry a0 and has
m entries; entry x0 of the segment is the array's first channel. -/
theorem Fits.SBA (F : Fits ρ W v D c t low u) (X : Arr) (hX : readLong X = true)
    {ew wh : Array E} {n : ℕ} (hw : Wts ρ ew wh v.y.ls low n) {i a0 m x0 : ℕ}
    (ha : ∃ q, a0 = q * 2 ^ v.y.ls) (hm : ∃ q, m = q * 2 ^ v.y.ls) (h0 : ∃ q, x0 = q * 2 ^ v.y.ls)
    (hle : x0 ≤ a0) {a : Aff} (h : v.SBA wh a0 (a0 + m) (arrName X) i "Z" x0 = some a) :
    a.value ρ W =
      wsum (fun y => wt ρ ew (a0 + y)) D.lT u m (fun y => raw t X i (a0 - x0 + y)) := by
  obtain ⟨ten, b, h1, T, R, hal⟩ := F.long X hX
  obtain ⟨qa, ha⟩ := ha
  obtain ⟨qm, hm⟩ := hm
  obtain ⟨q0, h0⟩ := h0
  have hpos : 0 < 2 ^ v.y.ls := by positivity
  have hq : q0 ≤ qa := by
    rw [ha, h0] at hle
    exact Nat.le_of_mul_le_mul_right hle hpos
  have e := SBA_true F.num T R F.S2 (hal i) hw.blocked h1 (qb := qa + qm) ha
    (by rw [ha, hm]; ring) h0 hq h
  rw [Nat.add_sub_cancel_left, ← hm, Nat.sub_mul, ← ha, ← h0] at e
  exact e

/-- A weighted sum over the blocks of the residual stream after write number sg of the group. -/
theorem Fits.Sxs (F : Fits ρ W v D c t low u) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.d) {sg : ℕ} {a : Aff} (h : v.SxsA wh "Z" sg = some a) :
    a.value ρ W = wsum (wt ρ ew) D.lT u D.d (fun x i => Inst.Model.FFSeg.xS D t sg x i) := by
  obtain ⟨bI, bO, bF, txs, hI, hO, hF, hxs, _, T0, T8, Ts, R0, R8, Rs, halb, hals⟩ := F.stream
  obtain ⟨n, hn⟩ := F.bd
  have hpos : 0 < 2 ^ v.y.ls := by positivity
  have hd : v.y.h.d / v.y.S2 * 2 ^ v.y.ls = D.d := by
    rw [F.d, F.S2, hn, Nat.mul_div_cancel _ hpos]
  rw [SxsA_true F.num D F.last hI hO hF hxs T0 T8 Ts R0 R8 Rs F.S2 halb hals hw.blocked h, hd]

omit scl in
/-- The sum of a segment's weights. -/
theorem Wts.sumE {ew wh : Array E} {ls n : ℕ} (hw : Wts ρ ew wh ls low n) :
    ρ.val (sumE ew) = ∑ x ∈ range n, wt ρ ew x := by
  rw [sumE_value, hw.size]

/-- A layer of the group has routed experts for the verifier exactly if it has for the library. -/
theorem Fits.isMoe (F : Fits ρ W v D c t low u) (lam : ℕ) :
    v.isMoe lam = Inst.Model.FFSeg.isExpL lam := by
  unfold Env.isMoe Inst.Model.FFSeg.isExpL
  rw [F.p3, Bool.true_and]

end Record

#print axioms gl_numerals
#print axioms SxsA_true
#print axioms Fits.SBA

end OnBytes.Road
