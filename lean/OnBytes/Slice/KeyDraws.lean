-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyDraws.lean: three rounds of a lookup in which the prover sends nothing, as steps,
with their soundness.

A lookup (OnBytes/Iop/Lkp.lean: run) has, beside its sumchecks and the rounds between the levels of
its trees, rounds in which the verifier only draws. This file has three of them.
 One draws alpha. The two sides of the lookup's identity are polynomials in alpha: the product of
 alpha minus a key over all keys, and the product of alpha minus a row of the table, each row with
 its multiplicity.
 One draws a point r, and the claims on the roots of the planes of bits become one claim on the top
 level of the table's tree (joinPlanes).
 One draws a point zeta, and "every bit is 0 or 1" becomes one sum claim: the extension of the table
 bit^2 - bit vanishes at zeta.
A fourth, which draws theta before alpha where several functions share a lookup, is not in this
file.

Each is a step of one round (OnBytes/Slice/KeyExitStep.lean: drawStep, sem_draw): the claim after
the round is "the claim before it holds, or the drawn value is bad". This file gives the bad values
and their counts.
 alpha: the library's Alg.Lookup.BadAlpha and count_badAlpha_le (Alg/Lookup.lean): the number of
 keys less one.
 r and zeta: a multilinear extension of a table that is not 0 on the cube vanishes at no more than
 n |E|^(n - 1) points: the library's Alg.count_mle_zero_le and count_mle_zero_of_injective
 (Alg/Mle.lean).

Main definitions: PscF.eqWeight, PscF.joinOne, PscF.joinPlanes (the program's text over the field,
the loop's step under a name), PscF.gap, CubeZero, VecEl, PlanesGood.

Main theorems: PscF.ext_eq_mle, cnt_ext_zero, cnt_treeMap_zero, PscF.eqWeight_eq,
cnt_eqWeight_zero, PscF.joinPlanes_holds, sem_alpha, sem_join, sem_zero.

Not claimed. That the products at alpha are what the tie's sumchecks claim, that the multiplicities
are read off bits, or that the sum claim after zeta is the next sumcheck's. That the program's run
on a view is these steps' next state.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyTreeMaps
import OnBytes.Slice.KeyPlaces
import Alg.Lookup

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-! ## The extension of a table vanishes at few points -/

namespace PscF

/-- The extension by recursion is the library's multilinear extension. -/
theorem ext_eq_mle : ∀ (n : ℕ) (t : List GE → GE) (z : Fin n → GE),
    ext n t (List.ofFn z) = Alg.mle (fun b => t (List.ofFn (Alg.corner b))) z
  | 0, t, z => by
    simp [ext, Alg.mle, Alg.eqk]
  | n + 1, t, z => by
    have hz : z = Fin.cons (z 0) fun i => z i.succ := (Fin.cons_self_tail z).symm
    rw [List.ofFn_succ]
    show (1 - z 0) * ext n (fun q => t (0 :: q)) (List.ofFn fun i => z i.succ) +
      z 0 * ext n (fun q => t (1 :: q)) (List.ofFn fun i => z i.succ) = _
    rw [ext_eq_mle n, ext_eq_mle n]
    conv_rhs => rw [hz, Alg.mle_cons]
    have h0 : ∀ b : Fin n → Bool, List.ofFn (Alg.corner (K := GE) (Fin.cons false b)) =
        0 :: List.ofFn (Alg.corner b) := fun b => by
      rw [List.ofFn_succ]
      simp [Alg.corner]
      rfl
    have h1 : ∀ b : Fin n → Bool, List.ofFn (Alg.corner (K := GE) (Fin.cons true b)) =
        1 :: List.ofFn (Alg.corner b) := fun b => by
      rw [List.ofFn_succ]
      simp [Alg.corner]
      rfl
    simp only [h0, h1]

end PscF

/-- The table t is 0 on the cube of n variables. -/
def CubeZero (n : ℕ) (t : List GE → GE) : Prop :=
  ∀ b : Fin n → Bool, t (List.ofFn (Alg.corner b)) = 0

/-- The extension of a table that is not 0 on the cube vanishes at no more than n |E|^(n - 1)
points. -/
theorem cnt_ext_zero (n : ℕ) (t : List GE → GE) (h : ¬ CubeZero n t) :
    cnt (fun z : Fin n → GE => PscF.ext n t (List.ofFn z) = 0) ≤
      n * Fintype.card GE ^ (n - 1) := by
  have hu : (fun b : Fin n → Bool => t (List.ofFn (Alg.corner b))) ≠ 0 := fun h0 =>
    h fun b => congrFun h0 b
  have h1 := Alg.count_mle_zero_le _ hu
  rw [Fintype.card_fin] at h1
  exact le_trans (le_of_eq (cnt_congr fun z => by rw [PscF.ext_eq_mle])) h1

/-- A reversed list of n elements. -/
theorem reverse_ofFn {n : ℕ} (z : Fin n → GE) :
    (List.ofFn z).reverse = List.ofFn fun i => z i.rev := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
  congr 1
  refine Fin.ext ?_
  simp only [List.length_ofFn, Fin.val_rev]
  omega

/-- The same for the extension at the point by variable. -/
theorem cnt_treeMap_zero (n : ℕ) (t : List GE → GE) (h : ¬ CubeZero n t) :
    cnt (fun z : Fin n → GE => treeMap n t (List.ofFn z) = 0) ≤ n * Fintype.card GE ^ (n - 1) := by
  have h1 := cnt_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl GE))
    fun z : Fin n → GE => PscF.ext n t (List.ofFn z) = 0
  refine le_trans (le_of_eq (Eq.trans (cnt_congr fun z => ?_) h1)) (cnt_ext_zero n t h)
  unfold treeMap
  rw [reverse_ofFn]
  rfl

/-! ## The equality weights by numbers -/

namespace PscF

/-- eqWeight z j r is r times the product, over the coordinates x of the point z, of x if the
matching bit of j is 1 and of 1 - x if it is 0. The first coordinate goes with the lowest bit. -/
def eqWeight : List GE → ℕ → GE → GE
  | [], _, r => r
  | x :: xs, j, r => eqWeight xs (j / 2) (r * (if j % 2 == 1 then x else 1 - x))

/-- The weight by numbers is the library's equality polynomial at the vertex with the number's
digits. -/
theorem eqWeight_eq : ∀ (n : ℕ) (z : Fin n → GE) (j : ℕ) (r : GE),
    eqWeight (List.ofFn z) j r = r * Alg.eqk z (vtx n j)
  | 0, z, j, r => by simp [eqWeight, Alg.eqk]
  | n + 1, z, j, r => by
    rw [List.ofFn_succ]
    show eqWeight (List.ofFn fun i => z i.succ) (j / 2)
      (r * (if j % 2 == 1 then z 0 else 1 - z 0)) = _
    rw [eqWeight_eq n]
    unfold Alg.eqk
    rw [Fin.prod_univ_succ]
    have h0 : vtx (n + 1) j 0 = (j % 2 == 1) := by
      show j.testBit 0 = _
      rw [Nat.testBit_zero]
      rfl
    have h1 : ∀ i : Fin n, vtx (n + 1) j i.succ = vtx n (j / 2) i := fun i => by
      show j.testBit (i.val + 1) = (j / 2).testBit i.val
      rw [Nat.testBit_succ]
    simp only [h0, h1]
    ring

end PscF

/-- A sum over a list of numbers from 0 on. -/
theorem sum_map_range (f : ℕ → GE) : ∀ n, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]
    simp

/-- A combination of numbers that are not all 0, under the equality weights at a point, vanishes
at no more than n |E|^(n - 1) points. -/
theorem cnt_eqWeight_zero (n : ℕ) (d : ℕ → GE) (h : ∃ j, j < 2 ^ n ∧ d j ≠ 0) :
    cnt (fun z : Fin n → GE =>
      ((List.range (2 ^ n)).map fun j => PscF.eqWeight (List.ofFn z) j 1 * d j).sum = 0) ≤
      n * Fintype.card GE ^ (n - 1) := by
  obtain ⟨j0, hj0, hd0⟩ := h
  have hd : (fun j : Fin (2 ^ n) => d j.val) ≠ 0 := fun h0 => hd0 (congrFun h0 ⟨j0, hj0⟩)
  have h1 := Alg.count_mle_zero_of_injective (K := GE) (fun j : Fin (2 ^ n) => vtx n j.val)
    (fun a b hab => Fin.ext (vtx_inj a.isLt b.isLt hab)) _ hd
  rw [Fintype.card_fin] at h1
  refine le_trans (le_of_eq (cnt_congr fun z => ?_)) h1
  rw [sum_map_range, Finset.sum_range]
  simp only [PscF.eqWeight_eq, one_mul]

/-! ## The claims on the planes' roots become one -/

namespace PscF

/-- One step of the loop of joinPlanes: plane j joins the claim c. -/
def joinOne (r : List GE) (onPlane : List PointClaim) (c : PointClaim) (j : ℕ) : PointClaim :=
  let weight := eqWeight r j 1
  match onPlane[j]? with
  | some p =>
    { c with
      masks := c.masks ++ scaleForm weight p.masks
      value := c.value + weight * p.value }
  | none => { c with value := c.value + weight }

/-- The claims on the planes' roots as one claim on the top level of the table's tree, at the
point r. A plane that is not real has the root 1. -/
def joinPlanes (mu : ℕ) (r : List GE) (onPlane : List PointClaim) : PointClaim :=
  (List.range (2 ^ mu)).foldl (joinOne r onPlane) ⟨r, [], 0⟩

/-- By how much the claim on plane j fails: the root plus the value of the claim's mask form less
the claim's value. For a plane without a claim: the root less 1. -/
def gap (W : World) (root : ℕ → GE) (onPlane : List PointClaim) (j : ℕ) : GE :=
  match onPlane[j]? with
  | some p => root j + W.form p.masks - p.value
  | none => root j - 1

/-- What one step of the loop does to a claim. -/
theorem joinOne_spec (W : World) (root : ℕ → GE) (r : List GE) (onPlane : List PointClaim)
    (c : PointClaim) (j : ℕ) : (joinOne r onPlane c j).point = c.point ∧
      W.form (joinOne r onPlane c j).masks - (joinOne r onPlane c j).value =
        W.form c.masks - c.value + eqWeight r j 1 * (gap W root onPlane j - root j) := by
  unfold joinOne gap
  cases onPlane[j]? with
  | none =>
    refine ⟨rfl, ?_⟩
    simp only []
    ring
  | some p =>
    refine ⟨rfl, ?_⟩
    simp only []
    rw [World.form_append, World.form_scale]
    ring

/-- What the loop of joinPlanes does to a claim. -/
theorem joinLoop (W : World) (root : ℕ → GE) (r : List GE) (onPlane : List PointClaim) :
    ∀ (l : List ℕ) (c : PointClaim), (l.foldl (joinOne r onPlane) c).point = c.point ∧
      W.form (l.foldl (joinOne r onPlane) c).masks - (l.foldl (joinOne r onPlane) c).value =
        W.form c.masks - c.value +
          (l.map fun j => eqWeight r j 1 * (gap W root onPlane j - root j)).sum
  | [], c => by simp
  | j :: l, c => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    obtain ⟨h1, h2⟩ := joinLoop W root r onPlane l (joinOne r onPlane c j)
    obtain ⟨h3, h4⟩ := joinOne_spec W root r onPlane c j
    rw [h1, h2, h3, h4]
    exact ⟨rfl, by ring⟩

/-- The joined claim holds if and only if the claims' gaps, under the equality weights at r, add
up to 0. Top: the map of the top level, which at r is the roots under the equality weights. -/
theorem joinPlanes_holds (W : World) (root : ℕ → GE) (mu : ℕ) (r : List GE)
    (onPlane : List PointClaim) (Top : List GE → GE)
    (hTop : Top r = ((List.range (2 ^ mu)).map fun j => eqWeight r j 1 * root j).sum) :
    (joinPlanes mu r onPlane).Holds W Top ↔
      ((List.range (2 ^ mu)).map fun j => eqWeight r j 1 * gap W root onPlane j).sum = 0 := by
  obtain ⟨h1, h2⟩ := joinLoop W root r onPlane (List.range (2 ^ mu)) ⟨r, [], 0⟩
  have h3 : ((List.range (2 ^ mu)).map fun j =>
      eqWeight r j 1 * (gap W root onPlane j - root j)).sum =
      ((List.range (2 ^ mu)).map fun j => eqWeight r j 1 * gap W root onPlane j).sum -
        ((List.range (2 ^ mu)).map fun j => eqWeight r j 1 * root j).sum := by
    rw [sum_map_range, sum_map_range, sum_map_range, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => mul_sub _ _ _
  rw [h3, ← hTop] at h2
  have h4 : W.form (joinPlanes mu r onPlane).masks - (joinPlanes mu r onPlane).value =
      W.form [] - 0 +
        (((List.range (2 ^ mu)).map fun j => eqWeight r j 1 * gap W root onPlane j).sum - Top r) :=
    h2
  have h5 : (joinPlanes mu r onPlane).point = r := h1
  unfold PointClaim.Holds
  rw [h5]
  rw [World.form_nil] at h4
  constructor
  · intro h
    linear_combination h - h4
  · intro h
    linear_combination h + h4

end PscF

/-! ## The three steps -/

/-- The written round d draws n elements, read by gVec, and its positions have at most 64 bits. -/
structure VecEl (n : ℕ) (d : PQ.RD) : Prop where
  inj : Function.Injective (gVec n (Fmt.dsOf d.entry d.kind))
  logN : d.entry.logN ≤ 64

/-- A round that draws n elements and no position. -/
theorem SendsDraws.vecEl {d : PQ.RD} {ns n a : ℕ} (h : SendsDraws d ns n 0 a) : VecEl n d :=
  ⟨h.gVec_inj, h.logN⟩

section
variable {X : Type} (d : PQ.RD)

/-- The round of alpha. key, tb, t0, pub, m: the keys, the table's rows, the padding row, how
often it is taken, and the multiplicities, at a state. If some key is in no row of the table, then
after the round, but for the counted verifier messages, alpha is not bad. -/
theorem sem_alpha {ι τ : Type} [Fintype ι] [Fintype τ] (hd : OneEl d) (key : X → ι → GE)
    (tb : X → τ → GE) (t0 : X → τ) (pub : X → ℕ) (m : X → τ → ℕ) :
    (drawStep (X := X) d (Fintype.card ι - 1) (gOne _)).Sem (fun x => ∀ i, ∃ t, key x i = tb x t)
      fun p => (∀ i, ∃ t, key p.1 i = tb p.1 t) ∨
        Alg.Lookup.BadAlpha (key p.1) (tb p.1) (t0 p.1) (pub p.1) (m p.1) p.2 :=
  sem_draw d (gOne _) hd.inj hd.logN _ (fun x => ∀ i, ∃ t, key x i = tb x t)
    (fun x => Alg.Lookup.BadAlpha (key x) (tb x) (t0 x) (pub x) (m x))
    fun x _ => Alg.Lookup.count_badAlpha_le (key x) (tb x) (t0 x) (pub x) (m x)

/-- All claims on the planes' roots hold, and a plane without a claim has the root 1. -/
def PlanesGood (W : PscF.World) (root : ℕ → GE) (mu : ℕ) (onPlane : List PscF.PointClaim) : Prop :=
  ∀ j, j < 2 ^ mu → PscF.gap W root onPlane j = 0

/-- The round of r. If a claim on a plane's root is false, then after the round, but for the
counted verifier messages, the joined claim is false of the top level's map. -/
theorem sem_join (mu : ℕ) (hd : VecEl mu d) (W : PscF.World) (root : ℕ → GE)
    (onPlane : X → List PscF.PointClaim) (Top : List GE → GE)
    (hTop : ∀ r : Fin mu → GE, Top (List.ofFn r) =
      ((List.range (2 ^ mu)).map fun j => PscF.eqWeight (List.ofFn r) j 1 * root j).sum) :
    (drawStep (X := X) d (mu * Fintype.card GE ^ (mu - 1)) (gVec mu _)).Sem
      (fun x => PlanesGood W root mu (onPlane x))
      fun p => PlanesGood W root mu (onPlane p.1) ∨
        (PscF.joinPlanes mu (List.ofFn p.2) (onPlane p.1)).Holds W Top :=
  sem_draw d (gVec mu _) hd.inj hd.logN _ (fun x => PlanesGood W root mu (onPlane x))
    (fun x r => (PscF.joinPlanes mu (List.ofFn r) (onPlane x)).Holds W Top) fun x hx => by
      refine le_trans (le_of_eq (cnt_congr fun r =>
        PscF.joinPlanes_holds W root mu (List.ofFn r) (onPlane x) Top (hTop r)))
        (cnt_eqWeight_zero mu _ ?_)
      by_contra hcon
      exact hx fun j hj => not_not.1 fun hne => hcon ⟨j, hj, hne⟩

/-- The round of zeta. u: a table, at a state. If the table is not 0 on the cube, then after the
round, but for the counted verifier messages, its extension does not vanish at zeta. -/
theorem sem_zero (n : ℕ) (hd : VecEl n d) (u : X → List GE → GE) :
    (drawStep (X := X) d (n * Fintype.card GE ^ (n - 1)) (gVec n _)).Sem
      (fun x => CubeZero n (u x))
      fun p => CubeZero n (u p.1) ∨ treeMap n (u p.1) (List.ofFn p.2) = 0 :=
  sem_draw d (gVec n _) hd.inj hd.logN _ (fun x => CubeZero n (u x))
    (fun x z => treeMap n (u x) (List.ofFn z) = 0) fun x hx => cnt_treeMap_zero n (u x) hx

end

end OnBytes.Slice
