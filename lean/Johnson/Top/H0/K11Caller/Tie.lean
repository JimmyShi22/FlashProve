-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Tie.lean: THE SMALL LAW THAT TIES THE TYPED SUMMAND TO THE PLAIN COEFFICIENTS, UNDER EVERY READING.

Coef.lean's text is generic in 0, 1, +, -, *. A map that takes these five to these five takes the text's value to the text's value (map_coef). A reading (OnBytes.Model.Reading) is such a
map from the program's field type. So: where the state's factors are the readings of a claim's factors as the program holds them, and the point is the reading of the program's point,
    the typed summand = the sum over the cells of W of (the reading of the plain coefficient coefE) * (the cell's entry)        (G_fa_reads);
    the proved block's second output claim, the row on the end value, is the like equation with the claims under the powers of the batching element                 (G_EV_reads).
Limits: that coefE is what the PROGRAM computes is not said in this file: proved in Prog.lean. Nothing on the state's reading: it is a premise here.

-/
import Johnson.Top.H0.K11Caller.Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes.Model (WsGrp WsUnit WsLay WsFac WsClaim Reading)
open Finset

section Map
variable {A B : Type} [Zero A] [One A] [Add A] [Sub A] [Mul A] [Zero B] [One B] [Add B] [Sub B] [Mul B]

/-- A map that takes 0, 1, sums, differences and products to the like. -/
structure Keeps (φ : A → B) : Prop where
  zero : φ 0 = 0
  one : φ 1 = 1
  add : ∀ a b, φ (a + b) = φ a + φ b
  sub : ∀ a b, φ (a - b) = φ a - φ b
  mul : ∀ a b, φ (a * b) = φ a * φ b

/-- A factor, read entry by entry. -/
def Fac.map (φ : A → B) (x : Fac A) : Fac B := ⟨fun i => φ (x.HV i), fun i => φ (x.pt i), fun i => φ (x.AV i)⟩

variable {φ : A → B} (h : Keeps φ)
include h

theorem map_prodTo : ∀ (n : ℕ) (f : ℕ → A), φ (prodTo n f) = prodTo n fun i => φ (f i)
  | 0, _ => h.one
  | n + 1, f => by simp only [prodTo, h.mul, map_prodTo n f]

theorem map_sumTo : ∀ (n : ℕ) (f : ℕ → A), φ (sumTo n f) = sumTo n fun i => φ (f i)
  | 0, _ => h.zero
  | n + 1, f => by simp only [sumTo, h.add, map_sumTo n f]

theorem map_eq1 (p x : A) : φ (eq1 p x) = eq1 (φ p) (φ x) := by
  simp only [eq1, h.add, h.mul, h.sub, h.one]

theorem map_pick (b : Bool) (x : A) : φ (pick b x) = pick b (φ x) := by
  cases b <;> simp [pick, h.sub, h.one]

theorem map_eqIdx (t : ℕ) (X : ℕ → A) (idx : ℕ) : φ (eqIdx t X idx) = eqIdx t (fun s => φ (X s)) idx := by
  unfold eqIdx
  split
  · simp only [map_prodTo h, map_pick h]
  · exact h.zero

theorem map_c256 : φ (c256 : A) = c256 := by
  simp only [c256, h.mul, h.add, h.one]

theorem map_facCols (g : WsGrp) (x : Fac A) (X : ℕ → A) : φ (facCols g x X) = facCols g (x.map φ) fun b => φ (X b) := by
  unfold facCols
  split
  · simp only [map_prodTo h, map_eq1 h, Fac.map]
  · split
    · simp only [map_sumTo h, h.mul, map_eqIdx h, Fac.map]
    · exact h.one

theorem map_groupsCols : ∀ (gs : List WsGrp) (xs : List (Fac A)) (X : ℕ → A),
    φ (groupsCols gs xs X) = groupsCols gs (xs.map (Fac.map φ)) fun b => φ (X b)
  | [], _, _ => by simpa [groupsCols] using h.one
  | _ :: _, [], _ => by simpa [groupsCols] using h.one
  | g :: gs, x :: xs, X => by
    simp only [groupsCols, List.map_cons, h.mul, map_facCols h, map_groupsCols gs xs X]

theorem map_colFac (lk : ℕ) (u : WsUnit) (fs : List (Fac A)) (X : ℕ → A) :
    φ (colFac lk u fs X) = colFac lk u (fs.map (Fac.map φ)) fun b => φ (X b) := by
  simp only [colFac, h.mul, map_groupsCols h, map_prodTo h, h.sub, h.one]

theorem map_facRows (g : WsGrp) (x : Fac A) (j : ℕ) : φ (facRows g x j) = facRows g (x.map φ) j := by
  unfold facRows
  split
  · simp only [h.mul, map_prodTo h, map_pick h, Fac.map]
  · split
    · exact h.one
    · rfl

theorem map_gammaGo (dig : ℕ → A) : ∀ (gs : List WsGrp) (xs : List (Fac A)) (r : ℕ),
    φ (gammaGo dig gs xs r) = gammaGo (fun l => φ (dig l)) gs (xs.map (Fac.map φ)) r
  | [], _, _ => by simp [gammaGo]
  | _ :: _, [], _ => by simp [gammaGo]
  | g :: gs, x :: xs, r => by
    simp only [gammaGo, List.map_cons, h.mul, map_facRows h, map_gammaGo dig gs xs]

theorem map_digit (nlw l : ℕ) : φ (digit nlw l : A) = digit nlw l := by
  unfold digit
  split
  · simp only [map_prodTo h, map_c256 h]
  · exact h.zero

theorem map_gammaAt (u : WsUnit) (fs : List (Fac A)) (r : ℕ) : φ (gammaAt u fs r) = gammaAt u (fs.map (Fac.map φ)) r := by
  simp only [gammaAt, map_gammaGo h, map_digit h]

/-- **The text's value is taken to the text's value.** -/
theorem map_coef (lay : WsLay) (ui : ℕ) (fs : List (Fac A)) (X : ℕ → A) (row col : ℕ) :
    φ (coef lay ui fs X row col) = coef lay ui (fs.map (Fac.map φ)) (fun b => φ (X b)) row col := by
  unfold coef
  split
  · exact h.zero
  · split
    · simp only [h.mul, map_colFac h, map_gammaAt h, map_eqIdx h]
    · exact h.zero

end Map

section Read
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A reading keeps the five. -/
theorem keeps : Keeps ρ.val := ⟨ρ.zero, ρ.one, ρ.add, ρ.sub, ρ.mul⟩

/-- A claim's factors as the program holds them, read. -/
def facsOf (c : WsClaim) : List (Fac K) := c.f.map fun x => (Fac.ofWs x).map ρ.val

/-- The program's point, read. -/
def pointOf (k : ℕ) (rm : Array OnBytes.E) : Fin k → K := fun i => ρ.val (rm.getD i.val OnBytes.zeroE)

theorem colX_val (k : ℕ) (rm : Array OnBytes.E) (hk : 0 < k) (b : ℕ) : ρ.val (colX k rm b) = XOf (pointOf ρ k rm) b := by
  unfold colX XOf ptOf pointOf
  rw [dif_pos (by omega)]

/-- **The plain coefficient, read, is the text at the read factors and the read point.** -/
theorem coefE_val (lay : WsLay) (c : WsClaim) (rm : Array OnBytes.E) (hk : 0 < lay.lk) (row col : ℕ) :
    ρ.val (coefE lay c rm row col) = coef lay c.ui (facsOf ρ c) (XOf (pointOf ρ lay.lk rm)) row col := by
  unfold coefE
  rw [map_coef (keeps ρ)]
  simp only [colX_val ρ lay.lk rm hk, facsOf, List.map_map]
  rfl

end Read

section AtG
variable {E : Type} [Field E] [Fintype E] (ρ : Reading E)

/-- **THE TIE.** Where the state's factors of claim a are the readings of the program's claim c, on the place's unit, the typed summand at the read point is the sum over the cells of W of
the read plain coefficient times the cell's entry. -/
theorem G_fa_reads (P : Place) (T : Letters E P) (a : Fin P.n) (st : T.St) (m : P.Cell ⊕ T.Jm → E) (c : WsClaim) (rm : Array OnBytes.E)
    (hk : 0 < P.lay.lk) (hu : c.ui = P.ui a) (hf : (T.rd st).fs a = facsOf ρ c) :
    (G P T).fa a st m (pointOf ρ P.lay.lk rm) = ∑ rc : P.Cell, ρ.val (coefE P.lay c rm rc.1.val rc.2.val) * m (.inl rc) := by
  show summand P (P.ui a) ((T.rd st).fs a) (fun rc => m (.inl rc)) (pointOf ρ P.lay.lk rm) = _
  unfold summand
  refine Finset.sum_congr rfl fun rc _ => ?_
  rw [coefE_val ρ P.lay c rm hk, hu, hf]

/-- **WHAT THE PROVED BLOCK's SECOND OUTPUT CLAIM SAYS AT THIS RECORD**: the row on the end value (MergeL.EV: f(point) + (a mask entry) * beta = the end value) is the equation
    the sum over the cells of W of (the sum over the claims of b^a * the read plain coefficient) * (the cell's entry) + (the entry cAt) * beta = the end value,
where the state's factors are the readings of the program's claims and the output's point is the reading of the program's point. b: the batching element in the output's state. -/
theorem G_EV_reads (P : Place) (T : Letters E P) (o : (G P T).L.T.par.Out) (m : P.Cell ⊕ T.Jm → E) (cl : Fin P.n → WsClaim) (rm : Array OnBytes.E)
    (hk : 0 < P.lay.lk) (hu : ∀ a, (cl a).ui = P.ui a) (hf : ∀ a, (T.rd o.st.1).fs a = facsOf ρ (cl a))
    (hp : (G P T).L.oPt o = pointOf ρ P.lay.lk rm) :
    (G P T).L.EV o m ↔
      ∑ rc : P.Cell, (∑ a : Fin P.n, o.st.2 ^ (a : ℕ) * ρ.val (coefE P.lay (cl a) rm rc.1.val rc.2.val)) * m (.inl rc) +
        m (.inr T.cAt) * (G P T).L.oBe o = o.vals () := by
  unfold Cb.Pv.Lay.MergeL.EV
  rw [hp, show (G P T).L.f o.st m (pointOf ρ P.lay.lk rm) = _ from G_f P T o.st.1 o.st.2 m _]
  simp only [coefE_val ρ P.lay _ rm hk, hu, hf]
  exact Iff.rfl

end AtG

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.map_coef
#print axioms VerifiableInference.Desc.First.K11Caller.coefE_val
#print axioms VerifiableInference.Desc.First.K11Caller.G_fa_reads
#print axioms VerifiableInference.Desc.First.K11Caller.G_EV_reads
