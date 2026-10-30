-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/ReqRefNeed.lean: how many masks a sumcheck on a family needs, bounded by numbers that survive
gluing.

Generic lemmas on data (no model, no protocol). A family (`Fam`, Cb/Req/ReqSpec.lean) is a sum of
terms over numbered atoms; gluing (`Fam.glue`, Cb/Req/ReqGlue.lean) joins a list of families, the
members, into one.

Why: f.need is the number of masks of a sumcheck on a family f (Cb/Req/ReqSumFmt.lean). Where one
vector under a code is to hold them, f.need is a length of that code; a code with all properties
exists for lengths in a range only, so f.need has to be bounded for the families in use: the glued
families of a partition (Cb/Req/ReqGlue.lean). Which families are glued into one is decided
classically; so the bound must not depend on it.

Main names:
  `need_le`: f.need ≤ f.v (f.deg + 1) + sz f, if the terms name atoms below f.na. `opn_le`,
    `rel_le`: the numbers of factor rows (nc + nAux) and product rows (nAux + 1) that the sumcheck
    records are at most sz f, sz f + 1; `opn_le` under the same hypothesis.
  `sz_to`, `sz_mask`, `sz_pub`, `sz_add`, `sz_glue`: gluing puts atoms and terms side by side: sz
    (Fam.glue pad L) = the sum of the sizes of the members.

Limits: this file says nothing on the sums among the atoms of a glued family (their own sumchecks).
It says nothing on any number of the model.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqNumsGlueProofs
import Cb.Req.ReqSumFmtProofs
import Cb.Req.ReqGlueProofsSeg

set_option autoImplicit false

namespace Cm.Ref
open Cb Cb.Req

/-- the number of atoms in all terms together -/
def tl (as : List (List ℕ)) : ℕ := (as.map List.length).sum

/-- The size of a family: its atoms, and the atoms in all its terms. -/
def sz {X E : Type} (f : Fam X E) : ℕ := f.na + tl f.lists

theorem mulUp_len : ∀ (r : List ℕ) (o cur : ℕ), (mulUp o cur r).length ≤ r.length
  | [], _, _ => Nat.le_refl _
  | [_], _, _ => Nat.zero_le _
  | _ :: b :: r, o, _ => Nat.succ_le_succ (mulUp_len (b :: r) (o + 1) o)

theorem termAux_len (o : ℕ) : ∀ as : List ℕ, (termAux o as).length ≤ as.length
  | [] => Nat.le_refl _
  | a :: r => Nat.le_succ_of_le (mulUp_len r o a)

theorem auxAll_len : ∀ (as : List (List ℕ)) (o : ℕ), (auxAll o as).length ≤ tl as
  | [], _ => Nat.le_refl _
  | a :: ts, o => by
    show (termAux o a ++ auxAll (o + (termAux o a).length) ts).length ≤ a.length + tl ts
    rw [List.length_append]
    exact Nat.add_le_add (termAux_len o a) (auxAll_len ts _)

section
variable {X E : Type}

theorem nAux_le (f : Fam X E) : f.nAux ≤ tl f.lists := auxAll_len _ _

/-- the number of factor rows that a sumcheck on f records -/
theorem opn_le (f : Fam X E) (h : ∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) :
    f.nc + f.nAux ≤ sz f := by
  rw [Cb.Req.nc_eq X E f h]
  exact Nat.add_le_add_left (nAux_le f) _

/-- the number of product rows -/
theorem rel_le (f : Fam X E) : f.nAux + 1 ≤ sz f + 1 :=
  Nat.succ_le_succ (le_trans (nAux_le f) (Nat.le_add_left _ _))

/-- The number of masks of a sumcheck. -/
theorem need_le (f : Fam X E) (h : ∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) :
    f.need ≤ f.v * (f.deg + 1) + sz f :=
  Nat.add_le_add_left (le_trans (Nat.count_le _) (opn_le f h)) _

/-! ## Gluing -/

theorem sz_to (f : Fam X E) (N : ℕ) : sz (f.to N) = sz f := by
  unfold sz Fam.lists Fam.to
  simp only [List.map_map]
  rfl

theorem sz_mask [Mul E] (c : X → ℕ → E) (f : Fam X E) : sz (f.mask c) = sz f := by
  unfold sz Fam.lists Fam.mask
  simp only [List.map_map]
  rfl

theorem sz_pub [Zero E] (v : ℕ) (c : X → ℕ → E) : sz (Fam.pub v c) = 0 := rfl

theorem sz_add (f g : Fam X E) : sz (f.add g) = sz f + sz g := by
  unfold sz tl Fam.lists Fam.add
  simp only [List.map_append, List.map_map, List.sum_append]
  have e : (List.map
        (List.length ∘ Term.atoms ∘
          fun t : Term X E => (⟨t.coef, t.atoms.map (· + f.na)⟩ : Term X E)) g.terms) =
      List.map (List.length ∘ Term.atoms) g.terms :=
    List.map_congr_left fun t _ => List.length_map _
  rw [e]
  omega

theorem sz_glueFrom [Zero E] [One E] [Mul E] (N V : ℕ) :
    ∀ (L : List (Fam X E)) (i : ℕ), sz (glueFrom N V i L) = (L.map sz).sum
  | [], _ => rfl
  | f :: L, i => by
    show sz (Fam.add (Fam.mask _ (f.to N)) (glueFrom N V (i + 1) L)) = sz f + (L.map sz).sum
    rw [sz_add, sz_mask, sz_to, sz_glueFrom N V L (i + 1)]

/-- The size of a glued family is the sum of the sizes of its members. -/
theorem sz_glue [Zero E] [One E] [Mul E] (pad : E) (L : List (Fam X E)) :
    sz (Fam.glue pad L) = (L.map sz).sum := by
  unfold Fam.glue
  rw [sz_add, sz_pub, sz_glueFrom, Nat.zero_add]

end

end Cm.Ref
