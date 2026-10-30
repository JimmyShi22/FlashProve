-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/SigC.lean: the inner product of the two long vectors is the sum of the
panels' shares: the library with itself.

Inst/Model/FF/Objects.lean lays the panels of the batched inner-product sumcheck one after the
other in two long vectors SA and SB over 2^lamS places: a panel p takes the stretch of 2^wid places
from offP p on, and its entry at (row, column) stands at place offP p + row 2^wcol + column
(Pan.at). The same file defines a panel's share, the sum over its rows and columns of the product
of its two sides under its weights, and the sums Sig0 and Sig1 of the shares of the early and of
the late panels. This file shows that the sum over all places of SA times SB is Sig0 + rJ Sig1.

Every statement here compares objects of the library with objects of the library. The file imports
no file of OnBytes/.

Main definitions: before, inStretch, atPlace, cellProd. Main theorems: sa_sb; pans_nodup (no panel
stands twice in the list); before_irrefl, before_trans, before_total (the order in which offP
places the panels); off_step, pans_apart (no two panels share a place); off_inside (every panel
ends within the 2^lamS places); sum_atPlace (the sum over the places of one panel is the sum over
its rows and columns); sum_apart, sum_om.

There is no hypothesis: sa_sb holds for all sizes D, every record r of values that the panels read,
all weights, tables, points and every rJ. That a panel's first place is a multiple of its number of
places is not needed here; it is shown in Cb/Pv/Lay/At/PanPlace.lean (off_dvd).

What is not claimed. Nothing is said of what the shares are worth (for the early panels see
Cb/Pv/Lay/End/Sig0.lean), of the sumcheck that reduces the inner product to a point, or of
what a verifier's acceptance shows. The program does not import this file.


-/
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Sig

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim LW Pan Rd pans offP panTotal lamS SA SB Sig0 Sig1 wc call)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A sum over places of a function that lives on the stretch from a on, of length n. -/
theorem sum_stretch {a n N : ℕ} (h : a + n ≤ N) (f : ℕ → K) :
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

/-- A double sum of terms that vanish from row n and from column m on. -/
theorem sum_corner {n N m M : ℕ} (hn : n ≤ N) (hm : m ≤ M) (F : ℕ → ℕ → K) :
    ∑ a ∈ range N, ∑ b ∈ range M, (if a < n ∧ b < m then F a b else 0) =
      ∑ a ∈ range n, ∑ b ∈ range m, F a b := by
  rw [← sum_subset (range_subset_range.mpr hn)]
  · refine sum_congr rfl fun a ha => ?_
    rw [← sum_subset (range_subset_range.mpr hm)]
    · exact sum_congr rfl fun b hb => if_pos ⟨mem_range.mp ha, mem_range.mp hb⟩
    · intro b _ hb
      exact if_neg fun hc => hb (mem_range.mpr hc.2)
  · intro a _ ha
    exact sum_eq_zero fun b _ => if_neg fun hc => ha (mem_range.mpr hc.1)

/-- A sum over a list of zeros. -/
theorem listSum_zero {α : Type} (f : α → K) : ∀ l : List α, (∀ x ∈ l, f x = 0) →
    (l.map f).sum = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, List.sum_cons, h x List.mem_cons_self,
      listSum_zero f l fun y hy => h y (List.mem_cons_of_mem _ hy), add_zero]

/-- A member's share of a sum of numbers is at most the sum. -/
theorem le_listSum {α : Type} (f : α → ℕ) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum
  | [], _, h => by cases h
  | y :: l, x, h => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | h'
    · rw [e]
      exact Nat.le_add_right _ _
    · exact Nat.le_trans (le_listSum f l x h') (Nat.le_add_left _ _)

/-- Two families of functions on places, each member living on a stretch of its own, where no two
members of the list share a place: the sum over the places of the product of the two sums over the
list is the sum over the list of the sums of the products. -/
theorem sum_apart {α : Type} (N : ℕ) (a b : α → ℕ → K) (win : α → ℕ → Prop)
    (ha : ∀ p y, ¬ win p y → a p y = 0) (hb : ∀ p y, ¬ win p y → b p y = 0) :
    ∀ l : List α, l.Pairwise (fun p q => ∀ y, ¬ (win p y ∧ win q y)) →
      ∑ y ∈ range N, (l.map fun p => a p y).sum * (l.map fun p => b p y).sum =
        (l.map fun p => ∑ y ∈ range N, a p y * b p y).sum
  | [], _ => by simp
  | p :: l, hp => by
    rw [List.pairwise_cons] at hp
    have e : ∀ y, ((p :: l).map fun p => a p y).sum * ((p :: l).map fun p => b p y).sum =
        a p y * b p y + (l.map fun p => a p y).sum * (l.map fun p => b p y).sum := by
      intro y
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      by_cases hw : win p y
      · have hz : ∀ q ∈ l, ¬ win q y := fun q hq hc => hp.1 q hq y ⟨hw, hc⟩
        rw [listSum_zero (fun q => a q y) l fun q hq => ha q y (hz q hq),
          listSum_zero (fun q => b q y) l fun q hq => hb q y (hz q hq)]
        ring
      · rw [ha p y hw, hb p y hw]
        ring
    simp only [e]
    rw [Finset.sum_add_distrib, sum_apart N a b win ha hb l hp.2, List.map_cons, List.sum_cons]

/-! ## The places of the panels -/

section Places

variable (D : Dim)

/-- The panel q is placed before the panel p: it has more bits, or as many and stands earlier in the
list. The words of offP. -/
def before (q p : Pan) : Prop :=
  p.wid D < q.wid D ∨ (q.wid D = p.wid D ∧ (pans D).idxOf q < (pans D).idxOf p)

instance (q p : Pan) : Decidable (before D q p) := by
  unfold before
  infer_instance

/-- offP in these words. -/
theorem offP_eq (p : Pan) :
    offP D p = ((pans D).map fun q => if before D q p then 2 ^ q.wid D else 0).sum := rfl

/-- No panel is placed before itself. -/
theorem before_irrefl (p : Pan) : ¬ before D p p := by
  unfold before
  omega

/-- The order is transitive. -/
theorem before_trans {r q p : Pan} (h1 : before D r q) (h2 : before D q p) : before D r p := by
  unfold before at *
  omega

/-- Of two different panels, one of them in the list, one is placed before the other. -/
theorem before_total {q p : Pan} (hq : q ∈ pans D) (hne : q ≠ p) :
    before D q p ∨ before D p q := by
  have hi : (pans D).idxOf q ≠ (pans D).idxOf p := fun e => hne ((List.idxOf_inj hq).mp e)
  unfold before
  omega

/-- A panel that is placed before another ends where the other begins, or earlier. -/
theorem off_step {q p : Pan} (hq : q ∈ pans D) (h : before D q p) :
    offP D q + 2 ^ q.wid D ≤ offP D p := by
  have h1 : 2 ^ q.wid D ≤ ((pans D).map fun r => if r = q then 2 ^ r.wid D else 0).sum := by
    have e : (if q = q then 2 ^ q.wid D else 0) ≤ _ :=
      le_listSum (fun r => if r = q then 2 ^ r.wid D else 0) (pans D) q hq
    rwa [if_pos rfl] at e
  have h2 : ((pans D).map fun r => (if before D r q then 2 ^ r.wid D else 0) +
      (if r = q then 2 ^ r.wid D else 0)).sum ≤
      ((pans D).map fun r => if before D r p then 2 ^ r.wid D else 0).sum := by
    refine List.sum_le_sum fun r _ => ?_
    by_cases e : r = q
    · subst e
      rw [if_neg (before_irrefl D r), if_pos rfl, if_pos h, Nat.zero_add]
    · rw [if_neg e, Nat.add_zero]
      by_cases hb : before D r q
      · rw [if_pos hb, if_pos (before_trans D hb h)]
      · rw [if_neg hb]
        exact Nat.zero_le _
  rw [List.sum_map_add] at h2
  rw [offP_eq, offP_eq]
  omega

/-- Every panel of the list ends within the places of all panels. -/
theorem off_inside {p : Pan} (hp : p ∈ pans D) : offP D p + 2 ^ p.wid D ≤ 2 ^ lamS D := by
  have h1 : 2 ^ p.wid D ≤ ((pans D).map fun r => if r = p then 2 ^ r.wid D else 0).sum := by
    have e : (if p = p then 2 ^ p.wid D else 0) ≤ _ :=
      le_listSum (fun r => if r = p then 2 ^ r.wid D else 0) (pans D) p hp
    rwa [if_pos rfl] at e
  have h2 : ((pans D).map fun r => (if before D r p then 2 ^ r.wid D else 0) +
      (if r = p then 2 ^ r.wid D else 0)).sum ≤ ((pans D).map fun r => 2 ^ r.wid D).sum := by
    refine List.sum_le_sum fun r _ => ?_
    by_cases e : r = p
    · subst e
      rw [if_neg (before_irrefl D r), if_pos rfl, Nat.zero_add]
    · rw [if_neg e, Nat.add_zero]
      split_ifs
      · exact Nat.le_refl _
      · exact Nat.zero_le _
  rw [List.sum_map_add] at h2
  have h3 : panTotal D ≤ 2 ^ lamS D := Nat.le_pow_clog (by decide) _
  have h4 : panTotal D = ((pans D).map fun r => 2 ^ r.wid D).sum := rfl
  rw [offP_eq]
  omega

/-- The list of panels has no panel twice. -/
theorem pans_nodup : (pans D).Nodup := by
  have iG : Function.Injective Pan.Gr := fun a b h => Pan.Gr.inj h
  have iU : Function.Injective Pan.Ur := fun a b h => Pan.Ur.inj h
  have iD : Function.Injective Pan.Dr := fun a b h => Pan.Dr.inj h
  simp [pans, List.nodup_append, List.nodup_map_iff iG, List.nodup_map_iff iU,
    List.nodup_map_iff iD, List.nodup_range]
  refine ⟨fun a _ b hb e => ?_, fun a _ b hb e => ?_⟩ <;> subst e <;> simp at hb

/-- The place y lies in the stretch of the panel p. -/
def inStretch (p : Pan) (y : ℕ) : Prop := offP D p ≤ y ∧ y < offP D p + 2 ^ p.wid D

instance (p : Pan) (y : ℕ) : Decidable (inStretch D p y) := by
  unfold inStretch
  infer_instance

/-- No two panels of the list share a place. -/
theorem pans_apart :
    (pans D).Pairwise fun p q => ∀ y, ¬ (inStretch D p y ∧ inStretch D q y) := by
  refine (pans_nodup D).pairwise_of_forall_ne fun p hp q hq hne y hy => ?_
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hy
  rcases before_total D hp hne with h | h
  · have := off_step D hp h
    omega
  · have := off_step D hq h
    omega

end Places

/-! ## One panel -/

section One

variable (D : Dim)

/-- What a function of (row, column) is worth at the place y of the long vectors, for the panel p: 0
if the place is no entry of the panel. The words of SA and SB. -/
def atPlace (p : Pan) (F : ℕ → ℕ → K) (y : ℕ) : K :=
  match p.at D y with
  | some (ρ, ι) => F ρ ι
  | none => 0

/-- atPlace, with the test of Pan.at written out. -/
theorem atPlace_eq (p : Pan) (F : ℕ → ℕ → K) (y : ℕ) :
    atPlace D p F y = if inStretch D p y then
      (if (y - offP D p) / 2 ^ p.wcol D < p.nr D ∧ (y - offP D p) % 2 ^ p.wcol D < p.nc D then
        F ((y - offP D p) / 2 ^ p.wcol D) ((y - offP D p) % 2 ^ p.wcol D) else 0) else 0 := by
  unfold atPlace Pan.at inStretch
  by_cases h1 : offP D p ≤ y ∧ y < offP D p + 2 ^ p.wid D
  · by_cases h2 : (y - offP D p) / 2 ^ p.wcol D < p.nr D ∧
        (y - offP D p) % 2 ^ p.wcol D < p.nc D
    · rw [if_pos ⟨h1.1, h1.2, h2.1, h2.2⟩, if_pos h1, if_pos h2]
    · rw [if_neg fun hc => h2 ⟨hc.2.2.1, hc.2.2.2⟩, if_pos h1, if_neg h2]
  · rw [if_neg fun hc => h1 ⟨hc.1, hc.2.1⟩, if_neg h1]

/-- Outside the panel's stretch it is 0. -/
theorem atPlace_out (p : Pan) (F : ℕ → ℕ → K) (y : ℕ) (h : ¬ inStretch D p y) :
    atPlace D p F y = 0 := by
  rw [atPlace_eq, if_neg h]

/-- The product of two functions of (row, column) at place t of the panel's stretch: 0 if the place
is no entry of the panel. -/
def cellProd (p : Pan) (F G : ℕ → ℕ → K) (t : ℕ) : K :=
  if t / 2 ^ p.wcol D < p.nr D ∧ t % 2 ^ p.wcol D < p.nc D then
    F (t / 2 ^ p.wcol D) (t % 2 ^ p.wcol D) * G (t / 2 ^ p.wcol D) (t % 2 ^ p.wcol D) else 0

/-- The product of two functions at a place of the long vectors. -/
theorem atPlace_mul (p : Pan) (F G : ℕ → ℕ → K) (y : ℕ) :
    atPlace D p F y * atPlace D p G y =
      if offP D p ≤ y ∧ y < offP D p + 2 ^ p.wid D then cellProd D p F G (y - offP D p)
      else 0 := by
  rw [atPlace_eq, atPlace_eq]
  unfold inStretch cellProd
  by_cases h1 : offP D p ≤ y ∧ y < offP D p + 2 ^ p.wid D
  · rw [if_pos h1, if_pos h1, if_pos h1]
    by_cases h2 : (y - offP D p) / 2 ^ p.wcol D < p.nr D ∧
        (y - offP D p) % 2 ^ p.wcol D < p.nc D
    · rw [if_pos h2, if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_neg h2, zero_mul]
  · rw [if_neg h1, if_neg h1, if_neg h1, zero_mul]

/-- The sum over the places of the product of two such functions is the sum over the panel's rows
and columns. -/
theorem sum_atPlace {p : Pan} {N : ℕ} (hN : offP D p + 2 ^ p.wid D ≤ N) (F G : ℕ → ℕ → K) :
    ∑ y ∈ range N, atPlace D p F y * atPlace D p G y =
      ∑ ρ ∈ range (p.nr D), ∑ ι ∈ range (p.nc D), F ρ ι * G ρ ι := by
  have hC : 0 < 2 ^ p.wcol D := Nat.two_pow_pos _
  have hr : p.nr D ≤ 2 ^ Nat.clog 2 (p.nr D) := Nat.le_pow_clog (by decide) _
  have hc : p.nc D ≤ 2 ^ p.wcol D := Nat.le_pow_clog (by decide) _
  have hw : p.wid D = Nat.clog 2 (p.nr D) + p.wcol D := rfl
  simp only [atPlace_mul]
  rw [sum_stretch hN (cellProd D p F G), hw, pow_add, Alg.sum_range_mul_add,
    ← sum_corner hr hc fun ρ ι => F ρ ι * G ρ ι]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b hb => ?_
  have hb' : b < 2 ^ p.wcol D := mem_range.mp hb
  have e1 : (a * 2 ^ p.wcol D + b) / 2 ^ p.wcol D = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hC, Nat.div_eq_of_lt hb', Nat.add_zero]
  have e2 : (a * 2 ^ p.wcol D + b) % 2 ^ p.wcol D = b := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
  unfold cellProd
  rw [e1, e2]

end One

/-! ## All panels -/

section All

variable [scl : Scl] (D : Dim) (r : Rd K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)
  (rJ : K)

omit scl in
/-- A sum over a list of panels under the weights om: the early panels, plus rJ times the late
ones. -/
theorem sum_om (f : Pan → K) : ∀ l : List Pan,
    (l.map fun p => p.om rJ * f p).sum =
      ((l.filter fun p => !p.late).map f).sum + rJ * ((l.filter fun p => p.late).map f).sum
  | [] => by simp
  | p :: l => by
    rw [List.map_cons, List.sum_cons, sum_om f l]
    unfold Pan.om
    cases h : p.late with
    | true =>
      rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_pos (by simp [h]),
        List.map_cons, List.sum_cons, if_pos rfl]
      ring
    | false =>
      rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_neg (by simp [h]),
        List.map_cons, List.sum_cons, if_neg (by decide)]
      ring

/-- The inner product of the two long vectors is the sum of the panels' shares: the early panels'
shares, plus rJ times the late panels'. For every record r of values that the panels read, and all
weights, tables and points. -/
theorem sa_sb :
    ∑ y ∈ range (2 ^ lamS D), SA D r z rJ y * SB D r tb L0 w z zh y =
      Sig0 D r tb L0 w z zh + rJ * Sig1 D r tb L0 w z zh := by
  have eA : ∀ y, SA D r z rJ y = ((pans D).map fun p => atPlace D p
      (fun ρ ι => p.om rJ * wc D z (call p.fam) * p.wt D z ρ * p.A D r ρ ι) y).sum := by
    intro y
    unfold SA
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    unfold atPlace
    generalize p.at D y = o
    rcases o with _ | ⟨ρ, ι⟩ <;> rfl
  have eB : ∀ y, SB D r tb L0 w z zh y =
      ((pans D).map fun p => atPlace D p (fun ρ ι => p.B D r tb L0 w z zh ρ ι) y).sum := by
    intro y
    unfold SB
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    unfold atPlace
    generalize p.at D y = o
    rcases o with _ | ⟨ρ, ι⟩ <;> rfl
  simp only [eA, eB]
  rw [sum_apart (2 ^ lamS D) _ _ (inStretch D) (fun p y h => atPlace_out D p _ y h)
    (fun p y h => atPlace_out D p _ y h) (pans D) (pans_apart D)]
  unfold Sig0 Sig1
  rw [← sum_om rJ (fun p => p.share D r tb L0 w z zh) (pans D)]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  rw [sum_atPlace D (off_inside D hp)]
  unfold Pan.share
  simp only [mul_sum]
  exact sum_congr rfl fun ρ _ => sum_congr rfl fun ι _ => by ring

end All

#print axioms pans_nodup
#print axioms pans_apart
#print axioms off_inside
#print axioms sum_atPlace
#print axioms sa_sb

end Cb.Pv.Lay.End.Sig
