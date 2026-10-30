-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/BridgeCore.lean: THE PER-POSITION BRIDGE OF A NORM, FLOOR A: algebra over
a
finite field K. No text of a verifier, no bytes, no world, no routine in a context. Definitions,
statements and proofs.

WHAT IT IS ABOUT. NI norms are checked at once. For each norm i and each of the 2^lt positions t the
prover has committed to five limbs of d features (limb i l j t) and to a row of 99 digits
(dig i n t). The library's 17 identities of a normalisation's ledger (Inst/Model/Common/Ledger.lean:
idn) must hold AT EVERY POSITION (Data.Holds). The verifier looks at no position. THE ROUNDS, IN
THEIR
ORDER (the letters of a run, under "for all" in bridge):
  1. P: a point of lt coordinates over the positions, drawn in ONE message;
  2. Wt: 9 NI hidden sums, sent; sum s of norm i stands at 9 i + s;
  3. gam: one element, drawn; its powers 0..8 batch the nine sums, the same powers for every norm;
  4. rho: a point of lNI coordinates over the norms' numbers, drawn in ONE message;
  5. the squares' masked sumcheck (not here: its CONCLUSION is the premise hsq);
  6. Pt: 7 NI hidden products, sent; product n of norm i stands at 7 i + n;
  7. om: one element, drawn; its powers 0..7 NI - 1 batch the products;
  8. the products' masked sumcheck at the same P (not here: its CONCLUSION is the premise hpr).
Behind all rounds stand the 17 NI linear claims at P (the premise hlines).

FIXED FIRST: c : Data K (sizes, constants, limbs, digits). Nothing else.
THE BAD SETS ARE DEFINITIONS, AND THEIR ARGUMENTS ARE ALL THAT THEY READ:
  BadP c           a set of points P.   Reads c alone: in front of round 1.
  BadG c P Wt      a set of gam.        Reads c, P (round 1), Wt (round 2): in front of round 3.
  BadI c P Wt gam  a set of points rho. Reads c, rounds 1, 2, 3: in front of round 4.
  BadO c P Pt      a set of om.         Reads c, P (round 1), Pt (round 6): in front of round 7.
THEIR SIZES (counts of values of one verifier message; q = the number of K's elements):
  cnt_BadP: lt q^(lt - 1) of the q^lt points.      cnt_BadG: 8 of q.
  cnt_BadI: lNI q^(lNI - 1) of the q^lNI points.   cnt_BadO: 7 NI - 1 of q.
MANY RIDERS ON ONE DRAW COST THE MAXIMUM, NOT THE SUM: all 17 NI identities ride on the one point P,
and all NI norms on the one gam. A draw is bad only if the data (or what was sent) are false AND
EVERY rider's equation holds at the draw: that set lies inside the zero set of any ONE rider that is
not zero.

  bridge: THE LAW. hlines, hsq, hpr, and none of the four draws bad: then c.Holds.
THE CHECKS, as theorems:
  honest_lines, honest_sq, honest_pr, honest_not_bad: at data that hold, with the true sums and
    products sent, all three premises hold at EVERY draw and NO draw is bad: the law is not empty
    wherever data that hold exist.
  false_data: at data that do not hold, no run without a bad draw meets the three premises.
  not_lines_of_false: at data that do not hold and true sums and products, behind a point that is
  not
    bad some linear claim is FALSE: the premise hlines bears load.

LIBRARY LEMMAS TAKEN: Inst/Model/Common/LedgerForms.lean
ext_idn, idnP_j1, idnP_of_le; LedgerSound.lean sum_pow_Wsum; Blocks/Ext.lean ext_sum, ext_smul,
cnt_ext_zero_le; Blocks/EqN.lean cnt_eqN_zero_le; Alg/Poly.lean count_powers_le; Prob/Cnt.lean cnt,
cnt_mono, cnt_false. COPIED with their proofs, because their file imports the older frame:
idnP_congr, idnP_congr_pv (Cb/Pv/Head/Norm.lean). THE ROAD IS THAT FILE's (norm_ext, norm_point,
norm_knowAt: one norm, the older frame's blocks); the form of a bad set is
Cb/G6/Johnson/Layers/Rounds.lean's (badPow, badPt).

NOT CLAIMED. That hsq and hpr hold: the masked sumcheck's law, with bad sets of its own (eps: 1;
each
round: 2). That hlines holds: the link's one equation, and that a read's entry is the extension of
the
cells. That c stands in front of round 1 IN TIME, and that Wt and Pt (hidden = shown - factor *
mask)
stand in front of their draws in time: the commitment's rows. From the field to the integers: the
library's LedgerSound.lean, under ranges on the digits. Probabilities: sets are counted. Nothing on
hiding.
-/
import Inst.Model.Common.LedgerForms
import Alg.Poly
import Prob.Cnt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Bridge
open Finset Prob
open Blocks (ext eqN nat)
open Inst.Model (NormPar)
open Inst.Model.Ledger (idnP prods Wsum)

/-! ## 0. Two lemmas of Cb/Pv/Head/Norm.lean, copied -/

/-- An identity reads the sums at the numbers below 9 alone. -/
theorem idnP_congr {K : Type} [CommRing K] (np : NormPar) {Ws Ws' : ℕ → K} (D pv : ℕ → K) (k : ℕ)
    (h : ∀ t < 9, Ws t = Ws' t) : idnP np Ws D pv k = idnP np Ws' D pv k := by
  by_cases hk : k < 9
  · rw [Inst.Model.Ledger.idnP_j1 np _ _ _ hk, Inst.Model.Ledger.idnP_j1 np _ _ _ hk, h k hk]
  · unfold Inst.Model.Ledger.idnP
    rw [if_neg hk, if_neg hk]

/-- An identity reads the products at the numbers below 7 alone. -/
theorem idnP_congr_pv {K : Type} [CommRing K] (np : NormPar) (Ws D : ℕ → K) {pv pv' : ℕ → K}
    (k : ℕ) (h : ∀ j < 7, pv j = pv' j) : idnP np Ws D pv k = idnP np Ws D pv' k := by
  have p0 := h 0 (by omega)
  have p1 := h 1 (by omega)
  have p2 := h 2 (by omega)
  have p3 := h 3 (by omega)
  have p4 := h 4 (by omega)
  have p5 := h 5 (by omega)
  have p6 := h 6 (by omega)
  unfold Inst.Model.Ledger.idnP
  split
  · rfl
  · split <;> simp only [p0, p1, p2, p3, p4, p5, p6]

/-! ## 1. What is fixed first -/

/-- What stands in front of all rounds. -/
structure Data (K : Type) where
  /-- there are 2^lt positions -/
  lt : ℕ
  /-- the number of features -/
  d : ℕ
  /-- the number of norms; at most 2^lNI where that is asked -/
  NI : ℕ
  /-- the number of coordinates of a point over the norms' numbers -/
  lNI : ℕ
  /-- norm i's constants -/
  np : ℕ → NormPar
  /-- limb l of feature j of norm i's stream at position t: limb i l j t -/
  limb : ℕ → ℕ → ℕ → ℕ → K
  /-- digit n of norm i's row at position t: dig i n t -/
  dig : ℕ → ℕ → ℕ → K

variable {K : Type} [Field K]

namespace Data
variable (c : Data K)

/-- The sum of limb products number s of norm i at position t, in truth. -/
def sumW (i s t : ℕ) : K := Wsum c.d (fun l j => c.limb i l j t) s

/-- Row product number n of norm i at position t, in truth. -/
def prodR (i n t : ℕ) : K := prods (fun m => c.dig i m t) n

/-- Identity number k of norm i at position t: left side minus right side. -/
def idAt (i k t : ℕ) : K :=
  Inst.Model.Ledger.idn (c.np i) (fun s => c.sumW i s t) (fun m => c.dig i m t) k

/-- **Every identity of every norm holds at every position.** -/
def Holds : Prop := ∀ i < c.NI, ∀ k < 17, ∀ t < 2 ^ c.lt, c.idAt i k t = 0

/-- The extensions over the positions, at a point u: of a sum, of a product, of a digit. -/
def sumWAt (u : ℕ → K) (i s : ℕ) : K := ext c.lt (c.sumW i s) u
def prodRAt (u : ℕ → K) (i n : ℕ) : K := ext c.lt (c.prodR i n) u
def digAt (u : ℕ → K) (i n : ℕ) : K := ext c.lt (c.dig i n) u

/-- By how much a sent sum misses the truth at u. -/
def dW (u : ℕ → K) (Wt : ℕ → K) (i s : ℕ) : K := Wt (9 * i + s) - c.sumWAt u i s

/-- By how much norm i's batch of sent sums misses the truth. -/
def dWg (u : ℕ → K) (Wt : ℕ → K) (gam : K) (i : ℕ) : K := ∑ s ∈ range 9, gam ^ s * c.dW u Wt i s

/-- By how much sent product number m (of all 7 NI) misses the truth at u. -/
def dP (u : ℕ → K) (Pt : ℕ → K) (m : ℕ) : K := Pt m - c.prodRAt u (m / 7) (m % 7)

/-! ## 2. The bad sets -/

/-- A bad point over the positions: the data do not hold, and yet every identity's extension
vanishes
at it. -/
def BadP (P : Fin c.lt → K) : Prop :=
  ¬ c.Holds ∧ ∀ i < c.NI, ∀ k < 17, ext c.lt (c.idAt i k) (nat P) = 0

/-- A bad batching element of the sums: some sent sum is false, and yet every norm's batch is
right. -/
def BadG (u : ℕ → K) (Wt : ℕ → K) (gam : K) : Prop :=
  (∃ i < c.NI, ∃ s < 9, c.dW u Wt i s ≠ 0) ∧ ∀ i < c.NI, c.dWg u Wt gam i = 0

/-- A bad point over the norms' numbers: some norm's batch is false, and yet their sum under the
equality weights is right. -/
def BadI (u : ℕ → K) (Wt : ℕ → K) (gam : K) (rho : Fin c.lNI → K) : Prop :=
  (∃ i < c.NI, c.dWg u Wt gam i ≠ 0) ∧
    ∑ i ∈ range c.NI, eqN c.lNI 0 (nat rho) i * c.dWg u Wt gam i = 0

/-- A bad batching element of the products: some sent product is false, and yet the batch is
right. -/
def BadO (u : ℕ → K) (Pt : ℕ → K) (om : K) : Prop :=
  (∃ m < 7 * c.NI, c.dP u Pt m ≠ 0) ∧ ∑ m ∈ range (7 * c.NI), om ^ m * c.dP u Pt m = 0

/-! ## 3. The three premises -/

/-- The 17 NI linear claims at the point u: the identities with letters, on the extensions of the
digits, the sent sums and the sent products. -/
def Lines (u : ℕ → K) (Wt Pt : ℕ → K) : Prop :=
  ∀ i < c.NI, ∀ k < 17,
    idnP (c.np i) (fun s => Wt (9 * i + s)) (c.digAt u i) (fun n => Pt (7 * i + n)) k = 0

/-- What the squares' sumcheck shows: the batch of the sent sums is the sum, over norms under v's
equality weights, positions under u's, and features, of the square of the limbs' batch. -/
def Squares (u : ℕ → K) (Wt : ℕ → K) (gam : K) (v : ℕ → K) : Prop :=
  ∑ i ∈ range c.NI, eqN c.lNI 0 v i * ∑ s ∈ range 9, gam ^ s * Wt (9 * i + s) =
    ∑ i ∈ range c.NI, eqN c.lNI 0 v i *
      ext c.lt (fun t => ∑ j ∈ range c.d, (∑ l ∈ range 5, gam ^ l * c.limb i l j t) ^ 2) u

/-- What the products' sumcheck shows: the batch of the sent products is the sum, over positions
under u's equality weights, of the batch of the rows' products. -/
def Products (u : ℕ → K) (Pt : ℕ → K) (om : K) : Prop :=
  ∑ m ∈ range (7 * c.NI), om ^ m * Pt m =
    ext c.lt (fun t => ∑ m ∈ range (7 * c.NI), om ^ m * c.prodR (m / 7) (m % 7) t) u

end Data

/-! ## 4. The counts -/

/-- Powers of one element, as a sum over a range. -/
theorem cnt_pow_range [Fintype K] (m : ℕ) (a : ℕ → K) (ha : ∃ j < m, a j ≠ 0) :
    cnt (fun g : K => ∑ j ∈ range m, g ^ j * a j = 0) ≤ m - 1 := by
  have ha' : (fun j : Fin m => a j) ≠ 0 := by
    obtain ⟨j, hj, hne⟩ := ha
    intro h0
    exact hne (congrFun h0 ⟨j, hj⟩)
  have h := Alg.count_powers_le (fun j : Fin m => a j) ha' 0
  refine le_trans
    (cnt_mono (Q := fun g : K => ∑ j : Fin m, g ^ (j : ℕ) * a j = 0) fun g hg => ?_) ?_
  · exact (Fin.sum_univ_eq_sum_range (fun j => g ^ j * a j) m).trans hg
  · simpa using h

variable (c : Data K)

theorem cnt_BadP [Fintype K] : cnt c.BadP ≤ c.lt * Fintype.card K ^ (c.lt - 1) := by
  by_cases h : c.Holds
  · rw [cnt_false fun P hP => hP.1 h]
    exact Nat.zero_le _
  · have h' := h
    unfold Data.Holds at h'
    push Not at h'
    obtain ⟨i, hi, k, hk, t, ht, hne⟩ := h'
    exact le_trans (cnt_mono fun P hP => hP.2 i hi k hk)
      (Blocks.cnt_ext_zero_le c.lt (c.idAt i k) ⟨t, ht, hne⟩)

theorem cnt_BadG [Fintype K] (u : ℕ → K) (Wt : ℕ → K) : cnt (c.BadG u Wt) ≤ 8 := by
  by_cases h : ∃ i < c.NI, ∃ s < 9, c.dW u Wt i s ≠ 0
  · obtain ⟨i, hi, s, hs, hne⟩ := h
    exact le_trans (cnt_mono fun g hg => hg.2 i hi) (cnt_pow_range 9 (c.dW u Wt i) ⟨s, hs, hne⟩)
  · rw [cnt_false fun g hg => h hg.1]
    exact Nat.zero_le _

theorem cnt_BadI [Fintype K] (hN : c.NI ≤ 2 ^ c.lNI) (u : ℕ → K) (Wt : ℕ → K) (gam : K) :
    cnt (c.BadI u Wt gam) ≤ c.lNI * Fintype.card K ^ (c.lNI - 1) := by
  by_cases h : ∃ i < c.NI, c.dWg u Wt gam i ≠ 0
  · exact le_trans (cnt_mono fun r hr => hr.2)
      (Blocks.cnt_eqN_zero_le c.lNI c.NI hN (c.dWg u Wt gam) h)
  · rw [cnt_false fun r hr => h hr.1]
    exact Nat.zero_le _

theorem cnt_BadO [Fintype K] (u : ℕ → K) (Pt : ℕ → K) : cnt (c.BadO u Pt) ≤ 7 * c.NI - 1 := by
  by_cases h : ∃ m < 7 * c.NI, c.dP u Pt m ≠ 0
  · exact le_trans (cnt_mono fun g hg => hg.2) (cnt_pow_range (7 * c.NI) (c.dP u Pt) h)
  · rw [cnt_false fun g hg => h hg.1]
    exact Nat.zero_le _

/-! ## 5. Extensions -/

/-- The extension of an identity is the identity with letters on the extensions. -/
theorem ext_idAt (u : ℕ → K) (i k : ℕ) :
    ext c.lt (c.idAt i k) u = idnP (c.np i) (c.sumWAt u i) (c.digAt u i) (c.prodRAt u i) k :=
  Inst.Model.Ledger.ext_idn c.lt (c.dig i) u (c.np i) (c.sumW i) k

/-- The extension of the sum of the squares of the limbs' batch is the batch of the sums'
extensions. -/
theorem ext_squares (u : ℕ → K) (gam : K) (i : ℕ) :
    ext c.lt (fun t => ∑ j ∈ range c.d, (∑ l ∈ range 5, gam ^ l * c.limb i l j t) ^ 2) u =
      ∑ s ∈ range 9, gam ^ s * c.sumWAt u i s := by
  have e : (fun t => ∑ j ∈ range c.d, (∑ l ∈ range 5, gam ^ l * c.limb i l j t) ^ 2) =
      fun t => ∑ s ∈ range 9, gam ^ s * c.sumW i s t := by
    funext t
    exact (Inst.Model.Ledger.sum_pow_Wsum gam c.d fun l j => c.limb i l j t).symm
  rw [e, Blocks.ext_sum]
  exact sum_congr rfl fun s _ => Blocks.ext_smul c.lt _ _ u

/-- The extension of the batch of the rows' products is the batch of the products' extensions. -/
theorem ext_products (u : ℕ → K) (om : K) :
    ext c.lt (fun t => ∑ m ∈ range (7 * c.NI), om ^ m * c.prodR (m / 7) (m % 7) t) u =
      ∑ m ∈ range (7 * c.NI), om ^ m * c.prodRAt u (m / 7) (m % 7) := by
  rw [Blocks.ext_sum]
  exact sum_congr rfl fun m _ => Blocks.ext_smul c.lt _ _ u

theorem dWg_eq (u : ℕ → K) (Wt : ℕ → K) (gam : K) (i : ℕ) :
    c.dWg u Wt gam i =
      ∑ s ∈ range 9, gam ^ s * Wt (9 * i + s) - ∑ s ∈ range 9, gam ^ s * c.sumWAt u i s := by
  unfold Data.dWg
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun s _ => by
    unfold Data.dW
    ring

/-- The squares' premise says that the norms' misses add up to 0 under the equality weights. -/
theorem squares_iff (u : ℕ → K) (Wt : ℕ → K) (gam : K) (v : ℕ → K) :
    c.Squares u Wt gam v ↔ ∑ i ∈ range c.NI, eqN c.lNI 0 v i * c.dWg u Wt gam i = 0 := by
  have e : ∑ i ∈ range c.NI, eqN c.lNI 0 v i * c.dWg u Wt gam i =
      ∑ i ∈ range c.NI, eqN c.lNI 0 v i * ∑ s ∈ range 9, gam ^ s * Wt (9 * i + s) -
        ∑ i ∈ range c.NI, eqN c.lNI 0 v i *
          ext c.lt (fun t => ∑ j ∈ range c.d, (∑ l ∈ range 5, gam ^ l * c.limb i l j t) ^ 2) u := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by rw [dWg_eq, ext_squares, mul_sub]
  constructor
  · intro h
    rw [e]
    exact sub_eq_zero.mpr h
  · intro h
    rw [e] at h
    exact sub_eq_zero.mp h

/-- The products' premise says that the batch of the misses is 0. -/
theorem products_iff (u : ℕ → K) (Pt : ℕ → K) (om : K) :
    c.Products u Pt om ↔ ∑ m ∈ range (7 * c.NI), om ^ m * c.dP u Pt m = 0 := by
  have e : ∑ m ∈ range (7 * c.NI), om ^ m * c.dP u Pt m =
      ∑ m ∈ range (7 * c.NI), om ^ m * Pt m -
        ext c.lt (fun t => ∑ m ∈ range (7 * c.NI), om ^ m * c.prodR (m / 7) (m % 7) t) u := by
    rw [ext_products, ← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by
      unfold Data.dP
      ring
  constructor
  · intro h
    rw [e]
    exact sub_eq_zero.mpr h
  · intro h
    rw [e] at h
    exact sub_eq_zero.mp h

/-- With sums and products that are true at u, the linear claims are the identities' extensions. -/
theorem lines_iff_of_true (u : ℕ → K) (Wt Pt : ℕ → K)
    (hW : ∀ i < c.NI, ∀ s < 9, c.dW u Wt i s = 0) (hP : ∀ m < 7 * c.NI, c.dP u Pt m = 0) :
    c.Lines u Wt Pt ↔ ∀ i < c.NI, ∀ k < 17, ext c.lt (c.idAt i k) u = 0 := by
  have key : ∀ i < c.NI, ∀ k,
      idnP (c.np i) (fun s => Wt (9 * i + s)) (c.digAt u i) (fun n => Pt (7 * i + n)) k =
        ext c.lt (c.idAt i k) u := by
    intro i hi k
    rw [ext_idAt]
    refine (idnP_congr (c.np i) _ _ k fun s hs => ?_).trans
      (idnP_congr_pv (c.np i) _ _ k fun n hn => ?_)
    · exact sub_eq_zero.mp (hW i hi s hs)
    · have h := hP (7 * i + n) (by omega)
      unfold Data.dP at h
      rw [show (7 * i + n) / 7 = i by omega, show (7 * i + n) % 7 = n by omega] at h
      exact sub_eq_zero.mp h
  constructor
  · intro h i hi k hk
    rw [← key i hi k]
    exact h i hi k hk
  · intro h i hi k hk
    rw [key i hi k]
    exact h i hi k hk

/-! ## 6. The law -/

/-- **THE PER-POSITION BRIDGE, FLOOR A.** The data stand first. A run: the point P, the sent sums,
gam,
the point rho, the sent products, om. If the 17 NI linear claims hold at P, the two sumchecks'
conclusions hold, and none of the four draws is bad for what stands in front of it, then every
identity of every norm holds at every position. -/
theorem bridge (P : Fin c.lt → K) (Wt : ℕ → K) (gam : K) (rho : Fin c.lNI → K) (Pt : ℕ → K) (om : K)
    (hlines : c.Lines (nat P) Wt Pt)
    (hsq : c.Squares (nat P) Wt gam (nat rho))
    (hpr : c.Products (nat P) Pt om)
    (hP : ¬ c.BadP P) (hG : ¬ c.BadG (nat P) Wt gam) (hI : ¬ c.BadI (nat P) Wt gam rho)
    (hO : ¬ c.BadO (nat P) Pt om) : c.Holds := by
  have h1 := (squares_iff c (nat P) Wt gam (nat rho)).mp hsq
  have h2 : ∀ i < c.NI, c.dWg (nat P) Wt gam i = 0 := by
    by_contra hne
    push Not at hne
    exact hI ⟨hne, h1⟩
  have h3 : ∀ i < c.NI, ∀ s < 9, c.dW (nat P) Wt i s = 0 := by
    by_contra hne
    push Not at hne
    exact hG ⟨hne, h2⟩
  have h4 : ∀ m < 7 * c.NI, c.dP (nat P) Pt m = 0 := by
    by_contra hne
    push Not at hne
    exact hO ⟨hne, (products_iff c (nat P) Pt om).mp hpr⟩
  have h5 := (lines_iff_of_true c (nat P) Wt Pt h3 h4).mp hlines
  by_contra hH
  exact hP ⟨hH, h5⟩

/-- The identities from number 17 on are 0 by definition: so all hold. -/
theorem holds_all (h : c.Holds) : ∀ i < c.NI, ∀ k, ∀ t < 2 ^ c.lt, c.idAt i k t = 0 := by
  intro i hi k t ht
  by_cases hk : k < 17
  · exact h i hi k hk t ht
  · exact Inst.Model.Ledger.idn_of_le _ (c.np i) _ (by omega)

/-! ## 7. The trials -/

/-- The true sums at u, as they are sent. -/
def Data.trueW (c : Data K) (u : ℕ → K) : ℕ → K := fun m => c.sumWAt u (m / 9) (m % 9)

/-- The true products at u, as they are sent. -/
def Data.trueP (c : Data K) (u : ℕ → K) : ℕ → K := fun m => c.prodRAt u (m / 7) (m % 7)

theorem dW_true (u : ℕ → K) (i s : ℕ) (hs : s < 9) : c.dW u (c.trueW u) i s = 0 := by
  unfold Data.dW Data.trueW
  rw [show (9 * i + s) / 9 = i by omega, show (9 * i + s) % 9 = s by omega, sub_self]

theorem dWg_true (u : ℕ → K) (gam : K) (i : ℕ) : c.dWg u (c.trueW u) gam i = 0 := by
  unfold Data.dWg
  exact sum_eq_zero fun s hs => by rw [dW_true c u i s (mem_range.mp hs), mul_zero]

theorem dP_true (u : ℕ → K) (m : ℕ) : c.dP u (c.trueP u) m = 0 := by
  unfold Data.dP Data.trueP
  exact sub_self _

/-- At data that hold, the true sums and products meet the linear claims at every point. -/
theorem honest_lines (h : c.Holds) (u : ℕ → K) : c.Lines u (c.trueW u) (c.trueP u) :=
  (lines_iff_of_true c u _ _ (fun i _ s hs => dW_true c u i s hs) fun m _ => dP_true c u m).mpr
    fun i hi k hk => Blocks.ext_zero_of_forall (fun t ht => h i hi k hk t ht) u

/-- The true sums meet the squares' premise at every draw, whatever the data. -/
theorem honest_sq (u : ℕ → K) (gam : K) (v : ℕ → K) : c.Squares u (c.trueW u) gam v :=
  (squares_iff c u _ gam v).mpr (sum_eq_zero fun i _ => by rw [dWg_true, mul_zero])

/-- The true products meet the products' premise at every draw, whatever the data. -/
theorem honest_pr (u : ℕ → K) (om : K) : c.Products u (c.trueP u) om :=
  (products_iff c u _ om).mpr (sum_eq_zero fun m _ => by rw [dP_true, mul_zero])

/-- At data that hold, with the true sums and products, no draw is bad. -/
theorem honest_not_bad (h : c.Holds) (P : Fin c.lt → K) (gam : K) (rho : Fin c.lNI → K) (om : K) :
    ¬ c.BadP P ∧ ¬ c.BadG (nat P) (c.trueW (nat P)) gam ∧
      ¬ c.BadI (nat P) (c.trueW (nat P)) gam rho ∧ ¬ c.BadO (nat P) (c.trueP (nat P)) om :=
  ⟨fun hb => hb.1 h,
   fun hb => by
    obtain ⟨i, _, s, hs, hne⟩ := hb.1
    exact hne (dW_true c _ i s hs),
   fun hb => by
    obtain ⟨i, _, hne⟩ := hb.1
    exact hne (dWg_true c _ gam i),
   fun hb => by
    obtain ⟨m, _, hne⟩ := hb.1
    exact hne (dP_true c _ m)⟩

/-- At data that do not hold, no run without a bad draw meets the three premises. -/
theorem false_data (h : ¬ c.Holds) (P : Fin c.lt → K) (Wt : ℕ → K) (gam : K) (rho : Fin c.lNI → K)
    (Pt : ℕ → K) (om : K) (hP : ¬ c.BadP P) (hG : ¬ c.BadG (nat P) Wt gam)
    (hI : ¬ c.BadI (nat P) Wt gam rho) (hO : ¬ c.BadO (nat P) Pt om) :
    ¬ (c.Lines (nat P) Wt Pt ∧ c.Squares (nat P) Wt gam (nat rho) ∧ c.Products (nat P) Pt om) :=
  fun hh => h (bridge c P Wt gam rho Pt om hh.1 hh.2.1 hh.2.2 hP hG hI hO)

/-- At data that do not hold, behind a point that is not bad, the true sums and products FAIL a
linear claim. -/
theorem not_lines_of_false (h : ¬ c.Holds) (P : Fin c.lt → K) (hP : ¬ c.BadP P) :
    ¬ c.Lines (nat P) (c.trueW (nat P)) (c.trueP (nat P)) := fun hl =>
  hP ⟨h, (lines_iff_of_true c (nat P) _ _ (fun i _ s hs => dW_true c _ i s hs)
    fun m _ => dP_true c _ m).mp hl⟩

end D6.Bridge

#print axioms D6.Bridge.bridge
#print axioms D6.Bridge.cnt_BadP
#print axioms D6.Bridge.cnt_BadG
#print axioms D6.Bridge.cnt_BadI
#print axioms D6.Bridge.cnt_BadO
#print axioms D6.Bridge.honest_lines
#print axioms D6.Bridge.honest_not_bad
#print axioms D6.Bridge.false_data
#print axioms D6.Bridge.not_lines_of_false
