-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Caller.lean: the merge of the claims on the weights: THE TYPED RECORD OF THE PROVED BLOCK (Cb.Pv.Lay.WeightsL) AT A PLACE, WITH ITS FIELD deg PROVED.

The library's proved block for the merge (Johnson/Top/H/Merge.lean: kMerge) is Good at every caller. A caller holds a record G : WeightsL E, whose field
    deg : each claim's summand has degree at most 2 in each variable
is, by Cb/Pv/Lay/Weights.lean's own Limits, to be paid by whoever fills the record. Here the record is made from a place's public data, and deg is a theorem.

THE SUMMAND. fa a st m z = the sum over ALL cells (row, col) of the committed matrix W of coef (row, col) * m (the cell), where coef is the ONE text of Coef.lean, read at the field E:
the text that Prog.lean proves, under every reading that takes numerals to numbers, to be what the program's wsEpsT, wsRowPart and wsGamma compute. z i is the coordinate of column bit k - 1 - i:
the sumcheck's first variable is the HIGHEST column bit.

WHY THE DEGREE IS 2. coef = C(X) * gamma * eq(X, col). gamma does not depend on the point. eq(X, col) is linear in each variable. C(X) is a product of factors, one for each index group
of the unit and one for each column bit that no group takes; it is linear in each variable BECAUSE NO COLUMN BIT BELONGS TO TWO OF THEM. That is a condition on the layout (unitOK): with
two groups on one column bit the degree would be 3. It is a field of the place (Place.ok). AtLay.lean pays it for every layout out of the program's wsLayOf, by OnBytes.Road.unitOK_of_layout (Johnson/Road/FormsKeysWLay.lean): Place.ofLay makes the place from such a layout.

WHAT IS A LETTER, AND WHOSE (structure Letters): all are the link's law's:
  Jm       the names of the mask entries (the sub-proof's mask row; the request's index-mask message). A name is a cell of W or one of these: no mask's name is a cell.
  St, rd   the link's state in front of the merge, and its ONE reading as In: for each claim its factors, the factor be under its mask entry, the scalar sh that was sent.
           St := In E n with rd := id is the plain member.
  nm wAt cAt   the names of the claims' mask entries, of the sumcheck's own 2 k + 2 mask entries, of the end value's mask entry
  Rd       what else rides
NOT GIVEN: the caller's other fields (Ex, Kc, Wp, Sg, R0, msg). That be is the closing challenge of an earlier sumcheck (1 for the embedding's value) is the state's reading's to say.
BESIDE THIS FILE. Cb/Pv/Lay/At/FootW.lean fills the same record (FootW0.wt, FootW0.wf) from a pair of coefficients on the rows and on the columns for each claim, which stays a letter there, and
proves the degree for it (summand_deg); Cb/Pv/Lay/End/WeightsPay.lean reads its row on the end value as an equation on the matrix. Both say in their Limits that the programs' summands and row
weights are not shown to be these. Johnson/Top/H/MergeSome.lean [not in this library] has a written
toy caller. This file's record is made of the program's own layout and claims. NO THEOREM JOINS IT
TO FootW0's.
On hiding nothing: of a mask only that it is a named entry.

-/
import Johnson.Top.H0.K11Caller.Coef
import Cb.Pv.Lay.WeightsFirst
import OnBytes.Model.HideLaws
import Alg.Mle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes.Model (WsGrp WsUnit WsLay WsFac WsClaim)
open Alg Finset

/-! ### the point as coordinates of column bits -/

section Deg
variable {K : Type} [CommRing K] {k : ℕ}

/-- Coordinate i of the point; 0 beyond it. -/
def ptOf (z : Fin k → K) (i : ℕ) : K := if h : i < k then z ⟨i, h⟩ else 0

/-- The coordinate of column bit b: the point has the highest column bit first. -/
def XOf (z : Fin k → K) (b : ℕ) : K := ptOf z (k - 1 - b)

/-- 1 at the variables of the column bits lo … hi - 1, 0 at the others. -/
def bnd (k lo hi : ℕ) (i : Fin k) : ℕ := if lo ≤ k - 1 - i.val ∧ k - 1 - i.val < hi then 1 else 0

theorem bnd_add (a b c : ℕ) (i : Fin k) (hab : a ≤ b) (hbc : b ≤ c) : bnd k a b i + bnd k b c i ≤ bnd k a c i := by
  unfold bnd
  split_ifs <;> omega

theorem bnd_le_one (a b : ℕ) (i : Fin k) : bnd k a b i ≤ 1 := by
  unfold bnd
  split_ifs <;> omega

theorem deg_X (b : ℕ) (hb : b < k) : DegLE (bnd k b (b + 1)) (fun z : Fin k → K => XOf z b) := by
  have hlt : k - 1 - b < k := by omega
  have e : ∀ z : Fin k → K, XOf z b = z ⟨k - 1 - b, hlt⟩ := fun z => by
    unfold XOf ptOf
    rw [dif_pos hlt]
  simp only [e]
  intro z i
  by_cases h : (⟨k - 1 - b, hlt⟩ : Fin k) = i
  · subst h
    refine ⟨Polynomial.X, ?_, fun t => by simp⟩
    have h1 : bnd k b (b + 1) ⟨k - 1 - b, hlt⟩ = 1 := by
      unfold bnd
      rw [if_pos]
      show b ≤ k - 1 - (k - 1 - b) ∧ k - 1 - (k - 1 - b) < b + 1
      omega
    rw [h1]
    exact Polynomial.natDegree_X_le
  · exact ⟨Polynomial.C (z ⟨k - 1 - b, hlt⟩), by simp, fun t => by simp [Function.update_of_ne h]⟩

theorem deg_eq1 {d : Fin k → ℕ} {g : (Fin k → K) → K} (p : K) (hg : DegLE d g) : DegLE d (fun z => eq1 p (g z)) := by
  unfold eq1
  exact (hg.const_mul p).add (((DegLE.const d 1).sub hg).const_mul (1 - p))

theorem deg_pick {d : Fin k → ℕ} {g : (Fin k → K) → K} (b : Bool) (hg : DegLE d g) : DegLE d (fun z => pick b (g z)) := by
  unfold pick
  cases b
  · simpa using (DegLE.const d 1).sub hg
  · simpa using hg

/-- A product of t maps, the i-th in the variable of column bit cb + i alone and linear in it. -/
theorem deg_prodTo (cb : ℕ) : ∀ (t : ℕ) (f : ℕ → (Fin k → K) → K), (∀ i, i < t → DegLE (bnd k (cb + i) (cb + i + 1)) (f i)) →
    DegLE (bnd k cb (cb + t)) (fun z => prodTo t fun i => f i z)
  | 0, _, _ => by simpa [prodTo] using DegLE.const (bnd k cb (cb + 0)) (1 : K)
  | t + 1, f, h => by
    have h1 := deg_prodTo cb t f fun i hi => h i (by omega)
    have h2 := h t (by omega)
    exact (h1.mul h2).mono fun i => bnd_add cb (cb + t) (cb + (t + 1)) i (by omega) (by omega)

theorem deg_sumTo {d : Fin k → ℕ} : ∀ (n : ℕ) (f : ℕ → (Fin k → K) → K), (∀ i, i < n → DegLE d (f i)) →
    DegLE d (fun z => sumTo n fun i => f i z)
  | 0, _, _ => by simpa [sumTo] using DegLE.const d (0 : K)
  | n + 1, f, h => (deg_sumTo n f fun i hi => h i (by omega)).add (h n (by omega))

theorem deg_eqIdx (cb t idx : ℕ) (h : cb + t ≤ k) :
    DegLE (bnd k cb (cb + t)) (fun z : Fin k → K => eqIdx t (fun s => XOf z (cb + s)) idx) := by
  unfold eqIdx
  by_cases hi : idx < 2 ^ t
  · simp only [if_pos hi]
    exact deg_prodTo cb t (fun s z => pick (idx.testBit s) (XOf z (cb + s))) fun s hs => deg_pick _ (deg_X (cb + s) (by omega))
  · simp only [if_neg hi]
    exact DegLE.const _ 0

theorem deg_facCols (g : WsGrp) (x : Fac K) (h : g.cb0 + g.t ≤ k) :
    DegLE (bnd k g.cb0 (g.cb0 + g.t)) (fun z : Fin k → K => facCols g x (XOf z)) := by
  unfold facCols
  by_cases hE : (g.cls == 'E') = true
  · simp only [if_pos hE]
    exact deg_prodTo g.cb0 g.t (fun i z => eq1 (x.pt (g.z - 1 - g.takenAt i)) (XOf z (g.cb0 + i))) fun i hi =>
      deg_eq1 _ (deg_X (g.cb0 + i) (by omega))
  · simp only [if_neg hE]
    by_cases hA : g.aTaken = true
    · simp only [if_pos hA]
      exact deg_sumTo g.R (fun idx z => x.AV idx * eqIdx g.t (fun s => XOf z (g.cb0 + s)) idx) fun idx _ =>
        (deg_eqIdx g.cb0 g.t idx h).const_mul (x.AV idx)
    · simp only [if_neg hA]
      exact DegLE.const _ 1

theorem le_endOf : ∀ (gs : List WsGrp) (cb : ℕ), cb ≤ endOf gs cb
  | [], _ => Nat.le_refl _
  | g :: gs, cb => Nat.le_trans (Nat.le_add_right cb g.t) (le_endOf gs (cb + g.t))

theorem deg_groupsCols : ∀ (gs : List WsGrp) (xs : List (Fac K)) (cb : ℕ), chainB gs cb = true → endOf gs cb ≤ k →
    DegLE (bnd k cb (endOf gs cb)) (fun z : Fin k → K => groupsCols gs xs (XOf z))
  | [], xs, cb, _, _ => by simpa [groupsCols] using DegLE.const (bnd k cb (endOf [] cb)) (1 : K)
  | g :: gs, [], cb, _, _ => by simpa [groupsCols] using DegLE.const (bnd k cb (endOf (g :: gs) cb)) (1 : K)
  | g :: gs, x :: xs, cb, hc, he => by
    simp only [chainB, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨h0, hc⟩ := hc
    have he' : endOf gs (cb + g.t) ≤ k := he
    have hm := le_endOf gs (cb + g.t)
    have h1 := deg_facCols (K := K) (k := k) g x (by omega)
    rw [h0] at h1
    have h2 := deg_groupsCols gs xs (cb + g.t) hc he'
    exact (h1.mul h2).mono fun i => bnd_add cb (cb + g.t) (endOf gs (cb + g.t)) i (by omega) hm

/-- **A claim's factor on the columns is linear in each variable**, at a unit that is in order. -/
theorem deg_colFac (u : WsUnit) (fs : List (Fac K)) (hc : chainB u.g 0 = true) (he : endOf u.g 0 = u.ncb) (hk : u.ncb ≤ k) :
    DegLE (fun _ => 1) (fun z : Fin k → K => colFac k u fs (XOf z)) := by
  unfold colFac
  have h1 := deg_groupsCols (K := K) (k := k) u.g fs 0 hc (by omega)
  rw [he] at h1
  have h2 := deg_prodTo (K := K) (k := k) u.ncb (k - u.ncb) (fun i z => 1 - XOf z (u.ncb + i)) fun i hi =>
    (DegLE.const _ 1).sub (deg_X (u.ncb + i) (by omega))
  exact (h1.mul h2).mono fun i =>
    (bnd_add 0 u.ncb (u.ncb + (k - u.ncb)) i (by omega) (by omega)).trans (bnd_le_one _ _ i)

/-- **A claim's coefficient on a cell has degree at most 2 in each variable.** -/
theorem deg_coef (lay : WsLay) (ui : ℕ) (fs : List (Fac K)) (row col : ℕ) (hk : lay.lk = k)
    (ok : ∀ u, lay.U[ui]? = some u → unitOK lay u = true) :
    DegLE (fun _ => 2) (fun z : Fin k → K => coef lay ui fs (XOf z) row col) := by
  subst hk
  unfold coef
  cases hu : lay.U[ui]? with
  | none => exact DegLE.const _ 0
  | some u =>
    have h := ok u hu
    simp only [unitOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hc, he⟩, hn⟩, _⟩ := h
    show DegLE (fun _ => 2) (fun z : Fin lay.lk → K => if u.off ≤ row ∧ row < u.off + u.rows then
      colFac lay.lk u fs (XOf z) * (gammaAt u fs (row - u.off) * eqIdx lay.lk (XOf z) col) else 0)
    by_cases hr : u.off ≤ row ∧ row < u.off + u.rows
    · simp only [if_pos hr]
      have h2 : DegLE (fun _ => 1) (fun z : Fin lay.lk → K => eqIdx lay.lk (XOf z) col) := by
        have h3 := deg_eqIdx (K := K) (k := lay.lk) 0 lay.lk col (by omega)
        simp only [Nat.zero_add] at h3
        exact h3.mono fun i => bnd_le_one _ _ i
      exact (deg_colFac u fs hc he hn).mul (h2.const_mul (gammaAt u fs (row - u.off)))
    · simp only [if_neg hr]
      exact DegLE.const _ 0

end Deg

/-! ### the place, the letters, the record -/

/-- **A place of the merge**: the layout of W, the number of claims, each claim's unit; each named unit is there and in order. Public data alone. -/
structure Place where
  lay : WsLay
  n : ℕ
  ui : Fin n → ℕ
  ok : ∀ a, ∃ u, lay.U[ui a]? = some u ∧ unitOK lay u = true

/-- A cell of W: the numbers of its row and of its column. -/
abbrev Place.Cell (P : Place) : Type := Fin P.lay.m0 × Fin (2 ^ P.lay.lk)

/-- What the merge reads of the state in front: for each claim its factors, the factor under its mask entry, the scalar that was sent. -/
structure In (E : Type) (n : ℕ) where
  fs : Fin n → List (Fac E)
  be : Fin n → E
  sh : Fin n → E

section Record
variable {E : Type} [Field E] [Fintype E]

/-- The letters. See the head. -/
structure Letters (E : Type) [Field E] [Fintype E] (P : Place) where
  Jm : Type
  [finJm : Fintype Jm]
  St : Type
  rd : St → In E P.n
  nm : Fin P.n → Jm
  wAt : Cb.PIdx (Cb.ldPartFmt E P.lay.lk (fun _ => 2) ++ [Cb.pDummy E 1]) → Jm
  cAt : Jm
  Rd : St → (P.Cell ⊕ Jm → E) → Prop

attribute [instance] Letters.finJm

/-- **A claim's summand**: the sum over all cells of W of the coefficient times the cell's entry. ui: the claim's unit; fs: its factors; w: the entries of W. -/
def summand (P : Place) (ui : ℕ) (fs : List (Fac E)) (w : P.Cell → E) (z : Fin P.lay.lk → E) : E :=
  ∑ rc : P.Cell, coef P.lay ui fs (XOf z) rc.1.val rc.2.val * w rc

omit [Fintype E] in
/-- **The summand has degree at most 2 in each variable**, at every unit that is in order. -/
theorem deg_summand (P : Place) (ui : ℕ) (fs : List (Fac E)) (w : P.Cell → E)
    (ok : ∀ u, P.lay.U[ui]? = some u → unitOK P.lay u = true) :
    DegLE (fun _ : Fin P.lay.lk => 2) (summand P ui fs w) :=
  DegLE.sum Finset.univ fun rc _ => (deg_coef P.lay ui fs rc.1.val rc.2.val rfl ok).mul_const (w rc)

theorem Place.ok' (P : Place) (a : Fin P.n) : ∀ u, P.lay.U[P.ui a]? = some u → unitOK P.lay u = true := by
  intro u hu
  obtain ⟨u', h1, h2⟩ := P.ok a
  rw [h1] at hu
  cases hu
  exact h2

/-- **THE RECORD AT A PLACE.** -/
def G (P : Place) (T : Letters E P) : Cb.Pv.Lay.WeightsL E where
  J := P.Cell ⊕ T.Jm
  k := P.lay.lk
  n := P.n
  St := T.St
  fa := fun a st m z => summand P (P.ui a) ((T.rd st).fs a) (fun rc => m (.inl rc)) z
  deg := fun a st m => deg_summand P (P.ui a) ((T.rd st).fs a) (fun rc => m (.inl rc)) (P.ok' a)
  nm := fun a => .inr (T.nm a)
  be := fun a st => (T.rd st).be a
  sh := fun a st => (T.rd st).sh a
  wAt := fun q => .inr (T.wAt q)
  cAt := .inr T.cAt
  Rd := T.Rd

/-- deg, as a statement of its own. -/
theorem G_deg (P : Place) (T : Letters E P) (a : Fin P.n) (st : T.St) (m : P.Cell ⊕ T.Jm → E) :
    DegLE (fun _ : Fin P.lay.lk => 2) ((G P T).fa a st m) := (G P T).deg a st m

/-- The record's numbers are the place's. -/
theorem G_k (P : Place) (T : Letters E P) : (G P T).k = P.lay.lk := rfl
theorem G_n (P : Place) (T : Letters E P) : (G P T).n = P.n := rfl

/-- The merge's target behind the draw b: the sent scalars under the powers of b, from the power 0 on. -/
theorem G_tg (P : Place) (T : Letters E P) (st : T.St) (b : E) :
    (G P T).L.tg (st, b) = ∑ a : Fin P.n, b ^ (a : ℕ) * (T.rd st).sh a := rfl

/-- At a place with one claim (the head's) the target is the one sent scalar. -/
theorem G_tg_one (P : Place) (T : Letters E P) (st : T.St) (b : E) (h : P.n = 1) :
    (G P T).L.tg (st, b) = (T.rd st).sh ⟨0, by omega⟩ := by
  rw [G_tg, Fintype.sum_eq_single (⟨0, by omega⟩ : Fin P.n)]
  · simp
  · intro a ha
    exact absurd (Fin.ext (by have := a.isLt; show a.val = 0; omega)) ha

/-- The merge's summand behind the draw b, as one sum over the cells of W. -/
theorem G_f (P : Place) (T : Letters E P) (st : T.St) (b : E) (m : P.Cell ⊕ T.Jm → E) (z : Fin P.lay.lk → E) :
    (G P T).L.f (st, b) m z =
      ∑ rc : P.Cell, (∑ a : Fin P.n, b ^ (a : ℕ) * coef P.lay (P.ui a) ((T.rd st).fs a) (XOf z) rc.1.val rc.2.val) * m (.inl rc) := by
  show ∑ a : Fin P.n, b ^ (a : ℕ) * summand P (P.ui a) ((T.rd st).fs a) (fun rc => m (.inl rc)) z = _
  unfold summand
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun rc _ => Finset.sum_congr rfl fun a _ => (mul_assoc _ _ _).symm

/-- The summand, written out. That it is not the map 0 is NOT proved; Tie.lean ties it to the plain coefficients, Prog.lean to the program's functions. -/
theorem G_fa (P : Place) (T : Letters E P) (a : Fin P.n) (st : T.St) (m : P.Cell ⊕ T.Jm → E) (z : Fin P.lay.lk → E) :
    (G P T).fa a st m z = ∑ rc : P.Cell, coef P.lay (P.ui a) ((T.rd st).fs a) (XOf z) rc.1.val rc.2.val * m (.inl rc) := rfl

end Record

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.deg_summand
#print axioms VerifiableInference.Desc.First.K11Caller.G
#print axioms VerifiableInference.Desc.First.K11Caller.G_deg
#print axioms VerifiableInference.Desc.First.K11Caller.G_f
#print axioms VerifiableInference.Desc.First.K11Caller.G_tg_one
#print axioms VerifiableInference.Desc.First.K11Caller.deg_coef
