-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NumbersHalf.lean: the numbers that the library's proximity blocks ask of the codes of
a stage, at radii below half the distance.

OnBytes/Slice/Numbers.lean bounds the exceptional points of a line (MCAat) by e + 1, at radii e
below a third of the distance. That bound holds for every code with the laws and a distance. The
codes of the format are Reed-Solomon codes, and for these the library proves more: below half the
distance a line of tables has at most as many exceptional points as the code has positions
(Code/Half.lean, Cb/Gl/GlAgreeHalf.lean). This file carries that bound to the codes of a stage
(OnBytes/Slice/Stage.lean). The lists are those of Numbers.lean: one code word below half the
distance.

A stage's mask code may be shorter than its main code. A mask row is then taken under the mask code
repeated along the main code's 2^a positions, the copies not compared (`ldRep`,
OnBytes/Slice/LinkAt.lean): a word has a symbol of its own at each position, and only a code word
repeats. With c = 2^(a - b) copies of a code of length 2^b and degree at most K, the repeated code
words are values of polynomials in X^c, of degree at most c K, at 2^a different points chosen for
this purpose (`repPt`: the main code's points without the factor 7, in another order). That larger
Reed-Solomon code has the repeated code's own distance, c (2^b - K), and below half the distance a
subcode inherits the bound (Code/Mutual.lean: `MCAOn.subcode`). So the count for a mask row is 2^a
too: the number of the main code's positions, not of the mask code's.

Throughout, a code (a, l, r) of the format has 2^a positions and r + l coefficients, and its
distance is d = 2^a - (r + l) + 1. So 2 e < d says 2 e + (r + l) ≤ 2^a.

Main definitions: ptE, polyOf, repPt, repCode, Sg.Pos (each of a stage's two codes has a
coefficient).
Main theorems.
 onCode_iff_onRS   on a set of positions a word agrees with a code word of one row exactly if it
                   agrees with a polynomial of degree below r + l.
 mca_half_at       one row: at most 2^a exceptional points, for 2 e + (r + l) ≤ 2^a.
 repPt_pow         7 times the power c of the point of x is the short code's point at x modulo 2^b.
 repCode_le        the repeated code lies in the code of degree at most c K at the points repPt.
 mca_half_rep      one row under a code of length 2^b repeated to 2^a positions, b ≤ a ≤ 32,
                   0 < r + l ≤ 2^b: at most 2^a exceptional points, for 2 e below the repeated
                   code's distance c (2^b - (r + l) + 1).
 Fit.fam           laws and distance pass to a finite family of codes side by side.
 Fit.mcaRows       what bounds the exceptional points of a line through two words bounds them for
                   two tables, however many rows these have.
 errOK_of          for every folding: ErrOK with all lists 1, from CodesOK at d and e with 2 e < d
                   and a count of exceptional points for each of its three codes.
 Sg.mcaHalf_cM, mcaHalf_cZ, mcaHalf_cIn, mcaHalf_cMid   the codes of a stage, for 2 e below the
                   stage's distance (`Sg.d`): 2^a for a row, a the main code's, twice that for the
                   tables before the fold, three times for the folded rows.
 Sg.errOK_half     ErrOK for a folding over the codes of a stage, for 2 e below the stage's
                   distance, with the counts 2^a, a the main code's.
 toySg1_pos and its like   the three stages of the small test configuration meet Pos.

 toySg1_cZ and its like   at these three stages the repeated mask code is the mask code itself.

Not claimed. Nothing at a radius of half the distance or more. Nothing at lengths above 2^32.
Nothing on how many positions of a word are hidden. Nothing on protocols. In this file no theorem is
applied at a stage whose mask code is shorter: the three stages of the small test configuration have
equal lengths.
That 2^a is the least count for a repeated row is not claimed. Where 3 e is below the
repeated code's own distance, `Fit.mca` with `fit_ldRep` (OnBytes/Slice/Numbers.lean) gives the
smaller count e + 1. So does the planner wherever it prices a mask row by `atDistance`
(OnBytes/Params/Distance.lean), which tries the source `.third` first
(`analysisAt`, OnBytes/Params/Group.lean). At such a stage the counts here for a mask row are
above the planner's number, so an error made of them is not within the planner's. `errOK_of` takes a
count of its own for each of the three codes.
-/
import Cb.Gl.GlAgreeHalf
import Cb.Ld.LdRelRowsE
import Cb.Obj.LdObjectToyKit
import OnBytes.Slice.Numbers
import OnBytes.Slice.RepPoints

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Prob Polynomial
open Cb.CodeListRS

/-! ## A row of the format is a polynomial's word -/

/-- The point of a position, in the extension field. -/
def ptE (C : Fmt.M1.Code) (x : Fin (2 ^ C.a)) : GE := algebraMap GF GE (ptOf C.a x)

/-- The polynomial with the coefficients v. -/
noncomputable def polyOf {n : ℕ} (v : Fin n → GE) : GE[X] := ∑ k : Fin n, C (v k) * X ^ k.val

/-- The generator matrix evaluates the polynomial with the given coefficients. -/
theorem genOf_mulVec (Cd : Fmt.M1.Code) (v : Fin (Cd.r + Cd.l) → GE) (x : Fin (2 ^ Cd.a)) :
    (genOf Cd).mulVec v x = (polyOf v).eval (ptE Cd x) := by
  unfold polyOf
  rw [eval_finset_sum]
  show ∑ k, genOf Cd x k * v k = ∑ k, eval (ptE Cd x) (C (v k) * X ^ k.val)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]
  show v k * algebraMap GF GE (ptOf Cd.a x ^ k.val) = v k * ptE Cd x ^ k.val
  rw [map_pow]
  rfl

/-- A polynomial of degree below n has, at every point, the value of the polynomial of its first n
coefficients. -/
theorem eval_polyOf_coeff {n : ℕ} (p : GE[X]) (hp : p.natDegree < n) (z : GE) :
    (polyOf fun k : Fin n => p.coeff k.val).eval z = p.eval z := by
  unfold polyOf
  rw [eval_finset_sum, eval_eq_sum_range' hp, Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- On a set of positions, what is read agrees with a code word exactly if it agrees with a
polynomial of degree below the number of coefficients. -/
theorem onCode_iff_onRS (Cd : Fmt.M1.Code) (hK : 0 < Cd.r + Cd.l)
    (g : Fin (2 ^ Cd.a) → Unit → GE) (S : Finset (Fin (2 ^ Cd.a))) :
    (ldOf Cd Cd.a).OnCode g S ↔ OnRS (ptE Cd) (Cd.r + Cd.l - 1) (fun x => g x ()) S := by
  constructor
  · rintro ⟨m, r, h⟩
    refine ⟨polyOf (Fin.append r m), ?_, fun x hx => ?_⟩
    · have h1 : Cd.r + Cd.l - 1 + 1 = Cd.r + Cd.l := by omega
      rw [h1]
      exact degree_sum_fin_lt _
    · have h1 : g x () = (ldOf Cd Cd.a).enc m r (posIn Cd x) () := congrFun (h x hx) ()
      show g x () = eval (ptE Cd x) (polyOf (Fin.append r m))
      rw [h1, ldOf_enc, posIn_self, genOf_mulVec]
  · rintro ⟨p, hp, h⟩
    have hn : p.natDegree < Cd.r + Cd.l := by
      by_cases h0 : p = 0
      · rw [h0, natDegree_zero]
        exact hK
      · have h1 : Cd.r + Cd.l - 1 + 1 = Cd.r + Cd.l := by omega
        rw [h1] at hp
        exact (natDegree_lt_iff_degree_lt h0).mpr hp
    refine ⟨fun j => p.coeff (Cd.r + j.val), fun q => p.coeff q.val, fun x hx => funext fun _ => ?_⟩
    have hv : Fin.append (fun q : Fin Cd.r => p.coeff q.val)
        (fun j : Fin Cd.l => p.coeff (Cd.r + j.val)) =
        fun k : Fin (Cd.r + Cd.l) => p.coeff k.val := by
      funext k
      refine Fin.addCases (fun q => ?_) (fun j => ?_) k
      · rw [Fin.append_left]
        rfl
      · rw [Fin.append_right]
        rfl
    show g x () = (ldOf Cd Cd.a).enc _ _ (posIn Cd x) ()
    rw [ldOf_enc, posIn_self, genOf_mulVec, hv, eval_polyOf_coeff p hn]
    exact h x hx

/-- Agreement below half the distance, for one row read at the code's own positions. -/
theorem mca_half_self (Cd : Fmt.M1.Code) (ha : Cd.a ≤ 32) (hK : 0 < Cd.r + Cd.l) (e : ℕ)
    (h2 : 2 * e + (Cd.r + Cd.l) ≤ 2 ^ Cd.a) : (ldOf Cd Cd.a).MCAat e (2 ^ Cd.a) := by
  intro f₀ f₁
  have h := half_rows GF GE (2 ^ Cd.a) (Cd.r + Cd.l - 1) e (ptOf Cd.a) (ptOf_inj Cd.a ha)
    (by omega) Unit (fun _ x => (ldOf Cd Cd.a).T f₀ x ()) (fun _ x => (ldOf Cd Cd.a).T f₁ x ())
  refine le_trans (cnt_mono fun θ hθ => ?_) h
  obtain ⟨S, hS, h1, hn⟩ := hθ
  rw [Fintype.card_fin] at hS
  exact ⟨S, hS, fun _ => (onCode_iff_onRS Cd hK _ S).1 h1, fun hc =>
    hn ⟨(onCode_iff_onRS Cd hK _ S).2 (hc.1 ()), (onCode_iff_onRS Cd hK _ S).2 (hc.2 ())⟩⟩

/-- Agreement below half the distance, one row, read at as many positions as the code has: a
line has at most 2^a exceptional points. -/
theorem mca_half_at (Cd : Fmt.M1.Code) (a : ℕ) (h : Cd.a = a) (ha : a ≤ 32) (hK : 0 < Cd.r + Cd.l)
    (e : ℕ) (h2 : 2 * e + (Cd.r + Cd.l) ≤ 2 ^ a) : (ldOf Cd a).MCAat e (2 ^ a) := by
  subst h
  exact mca_half_self Cd ha hK e h2

/-! ## A row repeated along a longer domain: the points -/

/-- The point that stands for the position x of the longer domain, for the code Cd repeated to 2^a
positions: the point, without the factor 7, of a code of length 2^a at the position x with its
Cd.a low bits and its other bits exchanged. It is not the point of x in a code of length 2^a. -/
def repPt (Cd : Fmt.M1.Code) (a : ℕ) (x : Fin (2 ^ a)) : GE :=
  algebraMap GF GE (unitPt a (turn Cd.a (a - Cd.a) x.val))

/-- For Cd.a ≤ a ≤ 32, different positions have different points. -/
theorem repPt_inj (Cd : Fmt.M1.Code) (a : ℕ) (hle : Cd.a ≤ a) (ha : a ≤ 32) :
    Function.Injective (repPt Cd a) := by
  intro x y h
  have hab : Cd.a + (a - Cd.a) = a := by omega
  have hx : x.val < 2 ^ (Cd.a + (a - Cd.a)) := by rw [hab]; exact x.isLt
  have hy : y.val < 2 ^ (Cd.a + (a - Cd.a)) := by rw [hab]; exact y.isLt
  have hx' := turn_lt Cd.a (a - Cd.a) x.val hx
  have hy' := turn_lt Cd.a (a - Cd.a) y.val hy
  rw [hab] at hx' hy'
  exact Fin.ext (turn_inj Cd.a (a - Cd.a) hx hy
    (unitPt_inj a ha hx' hy' ((algebraMap GF GE).injective h)))

/-- For Cd.a ≤ a ≤ 32: seven times the power 2^(a - Cd.a) of the point of x is the short code's
point at x modulo its length. -/
theorem repPt_pow (Cd : Fmt.M1.Code) (a : ℕ) (hle : Cd.a ≤ a) (ha : a ≤ 32) (x : Fin (2 ^ a)) :
    algebraMap GF GE (toF 7) * repPt Cd a x ^ 2 ^ (a - Cd.a) = ptE Cd (posIn Cd x) := by
  have hab : Cd.a + (a - Cd.a) = a := by omega
  have hx : x.val < 2 ^ (Cd.a + (a - Cd.a)) := by rw [hab]; exact x.isLt
  have h1 : unitPt a (turn Cd.a (a - Cd.a) x.val) ^ 2 ^ (a - Cd.a) =
      unitPt Cd.a (x.val % 2 ^ Cd.a) := by
    have h2 := unitPt_pow Cd.a (a - Cd.a) (turn Cd.a (a - Cd.a) x.val) (by omega)
    rw [hab, turn_div Cd.a (a - Cd.a) x.val hx] at h2
    exact h2
  show algebraMap GF GE (toF 7) * algebraMap GF GE (unitPt a (turn Cd.a (a - Cd.a) x.val)) ^
      2 ^ (a - Cd.a) = algebraMap GF GE (toF (Fmt.M1.point Cd.a (x.val % 2 ^ Cd.a)))
  rw [← map_pow, ← map_mul, h1, toF_point_unit]

/-! ## The repeated code as a subspace -/

/-- The words of polynomials of degree at most K, each read at the short code's point at x modulo
the short code's length. -/
def repCode (Cd : Fmt.M1.Code) (a K : ℕ) : Submodule GE (Fin (2 ^ a) → GE) where
  carrier := {w | ∃ p : GE[X], p.natDegree ≤ K ∧ ∀ x, w x = p.eval (ptE Cd (posIn Cd x))}
  add_mem' := by
    rintro v w ⟨p, hp, hv⟩ ⟨q, hq, hw⟩
    exact ⟨p + q, (natDegree_add_le _ _).trans (max_le hp hq),
      fun x => by rw [Pi.add_apply, hv, hw, eval_add]⟩
  zero_mem' := ⟨0, by simp, fun x => by simp⟩
  smul_mem' := by
    rintro c v ⟨p, hp, hv⟩
    exact ⟨C c * p, (natDegree_C_mul_le _ _).trans hp,
      fun x => by rw [Pi.smul_apply, hv, eval_mul, eval_C, smul_eq_mul]⟩

/-- For Cd.a ≤ a ≤ 32: the repeated code lies in the code of the polynomials of degree at most
2^(a - Cd.a) K at the points `repPt`. -/
theorem repCode_le (Cd : Fmt.M1.Code) (a K : ℕ) (hle : Cd.a ≤ a) (ha : a ≤ 32) :
    repCode Cd a K ≤ Code.rsCode ⟨repPt Cd a, repPt_inj Cd a hle ha⟩ (2 ^ (a - Cd.a) * K) := by
  rintro w ⟨p, hp, hw⟩
  refine ⟨p.comp (C (algebraMap GF GE (toF 7)) * X ^ 2 ^ (a - Cd.a)), ?_, fun x => ?_⟩
  · refine natDegree_comp_le.trans ?_
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul (natDegree_C_mul_X_pow_le _ _) hp
  · rw [hw x, eval_comp, eval_mul, eval_C, eval_pow, eval_X]
    show eval (ptE Cd (posIn Cd x)) p =
      eval (algebraMap GF GE (toF 7) * repPt Cd a x ^ 2 ^ (a - Cd.a)) p
    rw [repPt_pow Cd a hle ha x]

/-- Single words under the repeated code, for Cd.a ≤ a ≤ 32 and 2 e + 2^(a - Cd.a) K + 1 ≤ 2^a: a
line through two words has at most 2^a exceptional points. From the library's bound for the larger
code (`Code.mca_rsCode`) and its passage to a subcode (`Code.MCAOn.subcode`). -/
theorem mcaOn_repCode (Cd : Fmt.M1.Code) (a K : ℕ) (hle : Cd.a ≤ a) (ha : a ≤ 32) (e : ℕ)
    (hn : 2 * e + 2 ^ (a - Cd.a) * K + 1 ≤ 2 ^ a) :
    Code.MCAOn Unit (repCode Cd a K) e (2 ^ a) := by
  have h : Code.MCAOn Unit (Code.rsCode ⟨repPt Cd a, repPt_inj Cd a hle ha⟩ (2 ^ (a - Cd.a) * K)) e
      (Fintype.card (Fin (2 ^ a))) :=
    Code.mca_rsCode (L := GE) ⟨repPt Cd a, repPt_inj Cd a hle ha⟩ (e := e)
      (K := 2 ^ (a - Cd.a) * K) (by rw [Fintype.card_fin]; exact hn) Unit
  have hd := Code.minDist_rsCode (L := GE) ⟨repPt Cd a, repPt_inj Cd a hle ha⟩ (2 ^ (a - Cd.a) * K)
  rw [Fintype.card_fin] at h hd
  exact h.subcode hd (by omega) (repCode_le Cd a K hle ha) (by omega) Nat.one_le_two_pow

/-! ## From the subspace to the record of the repeated code -/

/-- The polynomial of n coefficients has degree at most n - 1. -/
theorem natDegree_polyOf_le {n : ℕ} (v : Fin n → GE) : (polyOf v).natDegree ≤ n - 1 := by
  have hd : (polyOf v).degree < (n : WithBot ℕ) := degree_sum_fin_lt _
  rcases eq_or_ne (polyOf v) 0 with h0 | h0
  · rw [h0, natDegree_zero]
    exact Nat.zero_le _
  · have h1 := (natDegree_lt_iff_degree_lt h0).mpr hd
    omega

/-- On a set of positions, what is read agrees with a word of the repeated code's record exactly if
it agrees with a member of `repCode` at K = r + l - 1, if the code has a coefficient. Without one
the two differ: the record's only word is 0, and `repCode` at K = 0 holds the constants. -/
theorem onRep_iff (Cd : Fmt.M1.Code) (a : ℕ) (hK : 0 < Cd.r + Cd.l)
    (g : Fin (2 ^ a) → Unit → GE) (S : Finset (Fin (2 ^ a))) :
    (ldRep Cd a).OnCode g S ↔
      (fun x => g x ()) ∈ Code.agreeOn (repCode Cd a (Cd.r + Cd.l - 1)) S := by
  constructor
  · rintro ⟨m, r, h⟩
    refine ⟨fun x => (polyOf (Fin.append r m)).eval (ptE Cd (posIn Cd x)),
      ⟨polyOf (Fin.append r m), natDegree_polyOf_le _, fun _ => rfl⟩, fun x hx => ?_⟩
    have h1 : g x () = (ldOf Cd Cd.a).enc m r (posIn Cd x) () := congrFun (h x hx) ()
    show g x () = eval (ptE Cd (posIn Cd x)) (polyOf (Fin.append r m))
    rw [h1, ldOf_enc, genOf_mulVec]
  · rintro ⟨u, ⟨p, hp, hu⟩, h⟩
    have hn : p.natDegree < Cd.r + Cd.l := by omega
    refine ⟨fun j => p.coeff (Cd.r + j.val), fun q => p.coeff q.val, fun x hx => funext fun _ => ?_⟩
    have hv : Fin.append (fun q : Fin Cd.r => p.coeff q.val)
        (fun j : Fin Cd.l => p.coeff (Cd.r + j.val)) =
        fun k : Fin (Cd.r + Cd.l) => p.coeff k.val := by
      funext k
      refine Fin.addCases (fun q => ?_) (fun j => ?_) k
      · rw [Fin.append_left]
        rfl
      · rw [Fin.append_right]
        rfl
    show g x () = (ldOf Cd Cd.a).enc _ _ (posIn Cd x) ()
    rw [ldOf_enc, genOf_mulVec, hv, eval_polyOf_coeff p hn, ← hu x]
    exact h x hx

/-- Agreement below half the distance for one row under the code Cd repeated to 2^a positions, the
copies not compared. Let Cd.a ≤ a ≤ 32, let Cd have a coefficient and no more coefficients than
positions, and let 2 e be below the repeated code's distance, 2^(a - Cd.a) (2^Cd.a - (r + l) + 1)
(`ldRep_dist`). Then a line through two words, whatever their symbols, has at most 2^a exceptional
points at the radius e. A count of elements of the extension field, not a probability. At a = Cd.a
this says what `mca_half_at` says (`ldRep_eq`). -/
theorem mca_half_rep (Cd : Fmt.M1.Code) (a : ℕ) (hle : Cd.a ≤ a) (ha : a ≤ 32)
    (hK : 0 < Cd.r + Cd.l) (hk : Cd.r + Cd.l ≤ 2 ^ Cd.a) (e : ℕ)
    (h2 : 2 * e < 2 ^ (a - Cd.a) * (2 ^ Cd.a - (Cd.r + Cd.l) + 1)) :
    (ldRep Cd a).MCAat e (2 ^ a) := by
  have hn : 2 * e + 2 ^ (a - Cd.a) * (Cd.r + Cd.l - 1) + 1 ≤ 2 ^ a := by
    have hab : 2 ^ a = 2 ^ (a - Cd.a) * 2 ^ Cd.a := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : 2 ^ Cd.a = (2 ^ Cd.a - (Cd.r + Cd.l) + 1) + (Cd.r + Cd.l - 1) := by omega
    rw [hab]
    conv_rhs => rw [h3, Nat.mul_add]
    omega
  intro f₀ f₁
  have h := mcaOn_repCode Cd a (Cd.r + Cd.l - 1) hle ha e hn
    (fun _ x => f₀ x ()) (fun _ x => f₁ x ())
  refine le_trans (cnt_mono fun θ hθ => ?_) h
  obtain ⟨S, hS, h1, hno⟩ := hθ
  exact ⟨S, hS, fun _ => (onRep_iff Cd a hK _ S).1 h1, fun hc =>
    hno ⟨(onRep_iff Cd a hK _ S).2 (hc.1 ()), (onRep_iff Cd a hK _ S).2 (hc.2 ())⟩⟩

/-! ## Any code: families, from two words to tables, and the record of a folding -/

/-- A finite family of codes side by side has the laws and the distance d if each member has. -/
theorem Fit.fam {E P A : Type} [Field E] [Fintype P] [Fintype A] [DecidableEq A]
    {C : A → LdCode E P} {d : ℕ} (h : ∀ a, Fit (C a) d) : Fit (LdCode.fam C) d :=
  ⟨ld_laws_fam E P A C fun a => (h a).laws, ld_dist_fam C d fun a => (h a).dist⟩

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P]

/-- From words to tables: what bounds the exceptional points of a line through two words bounds
them for two tables with the rows R. -/
theorem Fit.mcaRows {C : LdCode E P} {d e b : ℕ} (h : Fit C d) (hb : C.MCAat e b) (R : Type)
    [Fintype R] [DecidableEq R] : (C.il R).MCAat e b :=
  ld_rows_free E P C e b h.laws hb R

/-- The numbers of a folding below half the distance. If the three codes of the folding Y have
the laws and the distance d, and lines of words under them have at most bC, bZ and bW exceptional
points at a radius e with 2 e < d, then every stage has lists of one code word, and every halving
of the three tables has at most bC, bZ and bW exceptional points. -/
theorem errOK_of (Y : SumPar E P) (d e bC bZ bW : ℕ) (h : Spec.CodesOK E P Y.C Y.Z Y.Zw d e)
    (h2 : 2 * e < d) (hbC : Y.C.MCAat e bC) (hbZ : Y.Z.MCAat e bZ) (hbW : Y.Zw.MCAat e bW) :
    Y.ErrOK e (fun _ => 1) (fun _ => bC) (fun _ => bZ) (fun _ => bW) :=
  have hC : Fit Y.C d := ⟨h.1.1, h.2.1.1⟩
  have hZ : Fit Y.Z d := ⟨h.1.2.1, h.2.1.2.1⟩
  have hW : Fit Y.Zw d := ⟨h.1.2.2, h.2.1.2.2⟩
  { list := fun _ _ => ((hC.il _).pair ((hZ.il _).pair (hW.il _))).list h2
    mcaC := fun _ _ _ => hC.mcaRows hbC _
    mcaS := fun _ _ _ => hZ.mcaRows hbZ _
    mcaW := fun _ _ _ => hW.mcaRows hbW _ }

end

/-! ## The codes of a stage -/

namespace Sg

/-- Each of a stage's two codes has a coefficient. -/
structure Pos (s : Sg) : Prop where
  /-- a main row has a coefficient -/
  someC : 0 < s.C.r + s.C.l
  /-- a mask row has a coefficient -/
  someZ : 0 < s.Z.r + s.Z.l

variable {s : Sg}

/-- A radius below half the distance of the stage, in the sizes of the main rows. -/
theorem Sized.halfC (h : s.Sized) {e : ℕ} (h2 : 2 * e < s.d) :
    2 * e + (s.C.r + s.C.l) ≤ 2 ^ s.C.a := by
  have h1 : s.d ≤ s.dC := Nat.min_le_left _ _
  have h3 := h.roomC
  unfold Sg.dC at h1
  omega

/-- One main row. -/
theorem mcaHalf_cM (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cM.MCAat e (2 ^ s.C.a) :=
  mca_half_at s.C s.C.a rfl h.small hp.someC e (h.halfC h2)

/-- One mask row, under the mask code repeated to the main code's length. The mask code may be
shorter than the main code. -/
theorem mcaHalf_cZ (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cZ.MCAat e (2 ^ s.C.a) :=
  mca_half_rep s.Z s.C.a h.short h.small hp.someZ h.roomZ e
    (lt_of_lt_of_le h2 (Nat.min_le_right _ _))

/-- The tables before the fold. -/
theorem mcaHalf_cIn (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cIn.MCAat e (2 ^ s.C.a + 2 ^ s.C.a) :=
  ld_mca_pair GE s.Ps _ _ e _ _ ((fit_cM h).mcaRows (mcaHalf_cM h hp h2) _)
    ((fit_cZ h).mcaRows (mcaHalf_cZ h hp h2) _)

/-- The three folded rows. -/
theorem mcaHalf_cMid (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.cMid.MCAat e (2 ^ s.C.a + (2 ^ s.C.a + 2 ^ s.C.a)) :=
  ld_mca_pair GE s.Ps _ _ e _ _ (mcaHalf_cM h hp h2)
    (ld_mca_pair GE s.Ps _ _ e _ _ (mcaHalf_cZ h hp h2) (mcaHalf_cZ h hp h2))

/-- The numbers of a folding over the codes of a stage, below half the distance: lists of one
code word, and at most 2^a exceptional points, a the main code's, at every halving of each table. -/
theorem errOK_half (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) (Y : SumPar GE s.Ps)
    (hC : Y.C = s.cM) (hZ : Y.Z = s.cZ) (hW : Y.Zw = s.cZ) :
    Y.ErrOK e (fun _ => 1) (fun _ => 2 ^ s.C.a) (fun _ => 2 ^ s.C.a) (fun _ => 2 ^ s.C.a) := by
  have he : e < s.d := by omega
  refine errOK_of Y s.d e _ _ _ ?_ h2 ?_ ?_ ?_
  · rw [hC, hZ, hW]
    exact codesOK h he
  · rw [hC]
    exact mcaHalf_cM h hp h2
  · rw [hZ]
    exact mcaHalf_cZ h hp h2
  · rw [hW]
    exact mcaHalf_cZ h hp h2

end Sg

/-! ## The three stages of the small test configuration -/

/-- Both codes of the first stage have a coefficient. -/
theorem toySg1_pos : toySg1.Pos := ⟨by decide, by decide⟩

/-- Both codes of the second stage have a coefficient. -/
theorem toySg2_pos : toySg2.Pos := ⟨by decide, by decide⟩

/-- Both codes of the third stage have a coefficient. -/
theorem toySg3_pos : toySg3.Pos := ⟨by decide, by decide⟩

/-- At the first stage the mask code, taken as repeated to the main code's length, is the mask code
itself, read at the main code's positions, which are as many as its own. -/
theorem toySg1_cZ : toySg1.cZ = ldOf toySg1.Z toySg1.C.a := ldRep_eq _ _ rfl

/-- The same at the second stage. -/
theorem toySg2_cZ : toySg2.cZ = ldOf toySg2.Z toySg2.C.a := ldRep_eq _ _ rfl

/-- The same at the third stage. -/
theorem toySg3_cZ : toySg3.cZ = ldOf toySg3.Z toySg3.C.a := ldRep_eq _ _ rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.onCode_iff_onRS
#print axioms OnBytes.Slice.mca_half_at
#print axioms OnBytes.Slice.mca_half_rep
#print axioms OnBytes.Slice.Fit.fam
#print axioms OnBytes.Slice.Fit.mcaRows
#print axioms OnBytes.Slice.errOK_of
#print axioms OnBytes.Slice.Sg.mcaHalf_cM
#print axioms OnBytes.Slice.Sg.mcaHalf_cZ
#print axioms OnBytes.Slice.Sg.mcaHalf_cIn
#print axioms OnBytes.Slice.Sg.mcaHalf_cMid
#print axioms OnBytes.Slice.Sg.errOK_half
#print axioms OnBytes.Slice.toySg1_pos
#print axioms OnBytes.Slice.toySg2_pos
#print axioms OnBytes.Slice.toySg3_pos
#print axioms OnBytes.Slice.toySg1_cZ
#print axioms OnBytes.Slice.toySg2_cZ
#print axioms OnBytes.Slice.toySg3_cZ
