-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevLam.lean: at the library's own sumcheck the errors and the numbers of values of
the key sides and of the table's tree, read by the library's readers `Err.toList` and
`Shape.chalList`, are their shares of the list `Lam`.

  `isL_chain`   blocks in a chain. `lev_isL`, `tree_isL`: a level; the levels 0 .. n of any tree
                with
                orders: `tree q g (n + 1)`. The order does not occur in the list.
  `sides_isL`   m key sides: the parts' trees in a row.
  `Dat.keys_isL`, `Dat.table_isL`  `IsL` of the two blocks at `lamKeys`, `lamTable`.
Conditions: 1 ≤ m and 1 ≤ v i (i < m) for the keys; 1 ≤ d for the table. q is the field's number of
elements.
Not claimed: anything on the scalars sent; anything at another letter than the library's sumcheck.
`tree_fmt`: after E3Last.
Not claimed: anything on completeness or hiding.

-/
import Cb.Pv.KeyLookup.LevFit
import Cb.Pv.KeyLookup.AsmErr
import Cb.Ld.LdLkpAsmErrProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob

theorem isL_chain {Ex : ExtSpec} (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (f : ℕ → List
    LRow)
    (h : ∀ l, IsL (b l) (f l)) : ∀ n, IsL (BkK.chain X b n) ((List.range (n + 1)).flatMap f)
  | 0 => by
    have h0 := h 0
    simpa [BkK.chain, List.range_succ] using h0
  | n + 1 => by
    have h1 := isL_seq (isL_chain X b f h n) (h (n + 1))
    rw [List.range_succ (n := n + 1), List.flatMap_append]
    simpa [BkK.chain] using h1

theorem psc_c (q k : ℕ) : (psc q (List.replicate k 3) (some (2, 2))).map (·.c) = pscErrs k 2 2 := by
  simp [psc, pscErrs]

theorem psc_n (q k : ℕ) : (psc q (List.replicate k 3) (some (2, 2))).map (·.n) = pscVals q k := by
  simp [psc, pscVals]

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

theorem lev_isL (D : TreeP E) (l : ℕ) :
    IsL (levK D (PscLtK.lib E Ex) l)
      (psc (Fintype.card E) (List.replicate (D.g + l) 3) (some (2, 2)) ++ [⟨.line, 0, Fintype.card
          E, 1⟩]) := by
  have h := ll_psc (D.lv l).T (D.g + l) 2 (tree_fmt D l).1 Ex Unit
  rw [(tree_fmt D l).2] at h
  refine isL_seq (a := (PscLtK.lib E Ex).full (D.lv l).T.par) (b := lineK Ex D l) ⟨?_, ?_⟩ ⟨rfl,
      rfl⟩
  · rw [psc_c]; exact h.1
  · rw [psc_n]; exact h.2

theorem tree_isL (D : TreeP E) (n : ℕ) :
    IsL (treeK D (PscLtK.lib E Ex) n) (tree (Fintype.card E) D.g (n + 1)) :=
  isL_chain _ _ _ (lev_isL D) n

variable {B : KeyBase E}

theorem sides_isL : ∀ (ps : List (KeyPart B)) (p : KeyPart B) (X : Type) (pr : X → B.X0),
    IsL (sidesK (PscLtK.lib E Ex) p ps X pr)
      ((p :: ps).flatMap fun r => tree (Fintype.card E) 0 (r.v' + 1))
  | [], p, X, pr => by
    have h : IsL (p.sideK X pr (PscLtK.lib E Ex)) (tree (Fintype.card E) 0 (p.v' + 1)) :=
      isL_preM _ (tree_isL (p.tree X pr) p.v')
    simpa [sidesK] using h
  | r :: ps, p, X, pr => by
    have h : IsL (p.sideK X pr (PscLtK.lib E Ex)) (tree (Fintype.card E) 0 (p.v' + 1)) :=
      isL_preM _ (tree_isL (p.tree X pr) p.v')
    have h2 := isL_seq h (sides_isL ps r (p.SideSt X pr) (p.prN X pr))
    rw [List.flatMap_cons]
    exact h2

namespace Dat
variable (A : Dat E) (L : LevPl A)

theorem parts_bits (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    (A.part L 0 :: A.tailP L).map (fun r => r.v' + 1) = A.parts := by
  refine List.ext_getElem (by rw [List.length_map, A.parts_len L hm]; rfl) fun i h1 h2 => ?_
  have hi : i < A.m := h2
  rw [List.getElem_map, A.parts_get L i]
  show A.v i - 1 + 1 = _
  rw [Nat.sub_add_cancel (hv i hi)]
  exact List.getD_eq_getElem _ _ h2

theorem keys_isL (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    IsL (A.keysK L (PscLtK.lib E Ex)) (lamKeys (Fintype.card E) A.toPub) := by
  have h := sides_isL (Ex := Ex) (B := A.kb) (A.tailP L) (A.part L 0) A.XS id
  have e : (A.part L 0 :: A.tailP L).flatMap (fun r => tree (Fintype.card E) 0 (r.v' + 1)) =
      lamKeys (Fintype.card E) A.toPub := by
    unfold lamKeys
    rw [← A.parts_bits L hm hv, List.flatMap_map]
  rw [e] at h
  exact isL_postM (A.backK L) h

theorem table_isL (hd : 1 ≤ A.d) :
    IsL (A.tableK L (PscLtK.lib E Ex)) (lamTable (Fintype.card E) A.toPub) := by
  have h : IsL ((A.tabT L).segK (PscLtK.lib E Ex)) (tree (Fintype.card E) A.mu (A.d - 1 + 1)) :=
    isL_preM _ (tree_isL (A.tabT L).tree (A.d - 1))
  rw [Nat.sub_add_cancel hd] at h
  exact isL_postM (A.backT L) h

end Dat
end
end Lk6

#print axioms Lk6.Dat.keys_isL
#print axioms Lk6.Dat.table_isL
