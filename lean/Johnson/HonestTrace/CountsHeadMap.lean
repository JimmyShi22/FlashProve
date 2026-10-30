-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsHeadMap.lean

A homomorphism of fields, applied to a reading of the output head's cells, does not move the planes'
matrix bH of Johnson/HonestTrace/CountsHead.lean.

bH P cell depends on the field K of the reading cell : NameH → K: a place that is not padding is
counted at the first row below 2^(k_c) of its call's table whose value equals its key, and the
comparison is made in K. This file shows that the head's key vectors (Ends.H.kvH,
OnBytes/Tie/Pv/Lookup/Ends/H.lean) commute with a ring homomorphism φ : K →+* K' of fields. The
tables' rows are casts of natural numbers, which φ keeps. Such a map is injective, so no comparison
changes.

Main theorems. φ is a ring homomorphism between two fields; P and cell are arbitrary.
* "HeadMap.kvH_map": φ (Ends.H.kvH P cell q i) = Ends.H.kvH P (fun a => φ (cell a)) q i, for all q
  and i.
* "hitsH_map": if both fields have decidable equality, hitsH P (fun a => φ (cell a)) = hitsH P cell.
* "bH_map": so bH P (fun a => φ (cell a)) r c = bH P cell r c, for all r and c.

The steps stand in the namespace HeadMap: one theorem for each of limbs, nrm, xs, dig, digs, wH, lg,
ind, real, iw, midK, lowK, affH and gamH of Ends/H.lean; the other terms of which a key is made
unfold to these.

Limits. No premise is asked: neither that Head.layout returns nor that a key lies in its table. The
fields K and K' are arbitrary; an example is a field inside an extension of it.

Not claimed: that kvH is what a verifier reads; that a prover's committed cells are any of these
readings; anything on soundness or zero knowledge.

-/
import Johnson.HonestTrace.CountsHead

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model
open OnBytes.Ends.H

namespace HeadMap

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

/-- φ of a fold that adds c a * g a over a list, from b, is the fold that adds φ (c a) * φ (g a),
from φ b. -/
theorem sum_hom (c g : ℕ → K) : ∀ (l : List ℕ) (b : K),
    φ (l.foldl (fun s a => s + c a * g a) b) =
      l.foldl (fun s a => s + φ (c a) * φ (g a)) (φ b)
  | [], _ => rfl
  | a :: l, b => by
    rw [List.foldl_cons, List.foldl_cons, sum_hom c g l, map_add, map_mul]

/-- φ of a fold that adds c a * g a over a list, from 0, is the fold that adds φ (c a) * φ (g a),
from 0. -/
theorem sum_hom0 (c g : ℕ → K) (l : List ℕ) :
    φ (l.foldl (fun s a => s + c a * g a) 0) = l.foldl (fun s a => s + φ (c a) * φ (g a)) 0 := by
  rw [sum_hom, map_zero]

variable (P : PubH) (cell : NameH → K)

/-- φ commutes with Ends.H.limbs: φ of its value at cell is its value at the reading fun a => φ
(cell a). -/
theorem limbs_map (n off J x t : ℕ) :
    φ (limbs P cell n off J x t) = limbs P (fun a => φ (cell a)) n off J x t := by
  unfold limbs
  rw [sum_hom0]
  simp only [map_pow, map_ofNat]
  rfl

/-- φ commutes with Ends.H.nrm: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem nrm_map (k t : ℕ) : φ (nrm P cell k t) = nrm P (fun a => φ (cell a)) k t := by
  unfold nrm
  simp only [map_add, map_mul, map_ofNat]
  rfl

/-- φ commutes with Ends.H.xs: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem xs_map (k t : ℕ) : φ (xs P cell k t) = xs P (fun a => φ (cell a)) k t := by
  unfold xs
  rw [sum_hom0]
  simp only [map_pow, map_ofNat]
  rfl

/-- φ commutes with Ends.H.dig: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem dig_map (idx t : ℕ) : φ (dig P cell idx t) = dig P (fun a => φ (cell a)) idx t := by
  unfold dig
  simp only [map_add, map_ofNat]
  rfl

/-- φ commutes with Ends.H.digs: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem digs_map (first n t : ℕ) :
    φ (digs P cell first n t) = digs P (fun a => φ (cell a)) first n t := by
  unfold digs
  rw [sum_hom0]
  simp only [map_pow, map_ofNat, dig_map]

/-- φ commutes with Ends.H.wH: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem wH_map (k v : ℕ) : φ (wH P cell k v) = wH P (fun a => φ (cell a)) k v := by
  unfold wH
  dsimp only
  rw [sum_hom0]
  simp only [map_pow, map_ofNat]

/-- φ commutes with Ends.H.lg: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem lg_map (v t : ℕ) : φ (lg P cell v t) = lg P (fun a => φ (cell a)) v t := by
  unfold lg
  rw [sum_hom0]
  simp only [nrm_map, wH_map]

/-- φ (Ends.H.ind b) = Ends.H.ind b: the values are 0 and 1. -/
theorem ind_map (b : Bool) : φ (ind b) = ind b := by
  unfold ind
  split_ifs <;> simp

/-- φ (Ends.H.real P v t) = Ends.H.real P v t: it reads no cell. -/
theorem real_map (v t : ℕ) : φ (real P v t) = real P v t := ind_map φ _

/-- φ (Ends.H.iw P) = Ends.H.iw P: the inverse of a power of 2, in each field. -/
theorem iw_map : φ (iw P) = iw P := by
  unfold iw
  simp only [map_inv₀, map_pow, map_ofNat]

/-- φ commutes with Ends.H.midK: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem midK_map (v t : ℕ) : φ (midK P cell v t) = midK P (fun a => φ (cell a)) v t := by
  unfold midK d1
  simp only [map_add, map_mul, map_ofNat, limbs_map, real_map]

/-- φ commutes with Ends.H.lowK: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem lowK_map (v t : ℕ) : φ (lowK P cell v t) = lowK P (fun a => φ (cell a)) v t := by
  unfold lowK d2
  simp only [map_add, map_mul, map_ofNat, limbs_map, real_map]

/-- φ commutes with Ends.H.affH: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem affH_map (sn : String) (x t : ℕ) :
    φ (affH P cell sn x t) = affH P (fun a => φ (cell a)) sn x t := by
  unfold affH
  split_ifs <;>
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_zero, aw, ra, ex,
      costC, costB, limbs_map, nrm_map, dig_map, digs_map, ind_map, real_map, iw_map, midK_map,
      lowK_map]

/-- φ commutes with Ends.H.gamH: φ of its value at cell is its value at the reading fun a => φ (cell
a). -/
theorem gamH_map (sn : String) (x t : ℕ) :
    φ (gamH P cell sn x t) = gamH P (fun a => φ (cell a)) sn x t := by
  unfold gamH
  split_ifs <;>
    simp only [map_sub, map_mul, map_zero, recip, digs_map, xs_map, lg_map, real_map, iw_map]

/-- **The head's keys commute with a homomorphism of fields.** For all q and i: φ (Ends.H.kvH P cell
q i) = Ends.H.kvH P (fun a => φ (cell a)) q i. -/
theorem kvH_map (q i : ℕ) : φ (kvH P cell q i) = kvH P (fun a => φ (cell a)) q i := by
  unfold kvH kvOf
  cases colH P.L q (i / P.h.T) with
  | none => exact map_natCast φ _
  | some a =>
    obtain ⟨sn, x⟩ := a
    show φ (segH P cell sn x (i % P.h.T)) = segH P (fun a => φ (cell a)) sn x (i % P.h.T)
    unfold segH
    rw [map_add, affH_map, gamH_map]

end HeadMap

section
variable {K K' : Type} [Field K] [Field K'] [DecidableEq K] [DecidableEq K'] (φ : K →+* K')

/-- For a ring homomorphism φ between fields with decidable equality: hitsH at the reading fun a =>
φ (cell a) is hitsH at cell. -/
theorem hitsH_map (P : PubH) (cell : NameH → K) :
    hitsH P (fun a => φ (cell a)) = hitsH P cell := by
  have e := hitsOf_map φ φ.injective P.L.fs (tabOf K P.L.fs) (kvH P cell) (padH P.h P.L)
  have e1 : (fun c t => φ (tabOf K P.L.fs c t)) = tabOf K' P.L.fs := by
    funext c t
    exact map_natCast φ _
  have e2 : (fun c i => φ (kvH P cell c i)) = kvH P (fun a => φ (cell a)) := by
    funext c i
    exact HeadMap.kvH_map φ P cell c i
  rw [e1, e2] at e
  exact e

/-- **A homomorphism of fields does not move bH.** For a ring homomorphism φ between fields with
decidable equality, and all r and c: bH P (fun a => φ (cell a)) r c = bH P cell r c. -/
theorem bH_map (P : PubH) (cell : NameH → K) (r c : ℕ) :
    bH P (fun a => φ (cell a)) r c = bH P cell r c := by
  unfold bH
  rw [hitsH_map]

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.HeadMap.sum_hom
#print axioms OnBytes.HonestTrace.HeadMap.sum_hom0
#print axioms OnBytes.HonestTrace.HeadMap.limbs_map
#print axioms OnBytes.HonestTrace.HeadMap.nrm_map
#print axioms OnBytes.HonestTrace.HeadMap.xs_map
#print axioms OnBytes.HonestTrace.HeadMap.dig_map
#print axioms OnBytes.HonestTrace.HeadMap.digs_map
#print axioms OnBytes.HonestTrace.HeadMap.wH_map
#print axioms OnBytes.HonestTrace.HeadMap.lg_map
#print axioms OnBytes.HonestTrace.HeadMap.ind_map
#print axioms OnBytes.HonestTrace.HeadMap.real_map
#print axioms OnBytes.HonestTrace.HeadMap.iw_map
#print axioms OnBytes.HonestTrace.HeadMap.midK_map
#print axioms OnBytes.HonestTrace.HeadMap.lowK_map
#print axioms OnBytes.HonestTrace.HeadMap.affH_map
#print axioms OnBytes.HonestTrace.HeadMap.gamH_map
#print axioms OnBytes.HonestTrace.HeadMap.kvH_map
#print axioms OnBytes.HonestTrace.hitsH_map
#print axioms OnBytes.HonestTrace.bH_map
