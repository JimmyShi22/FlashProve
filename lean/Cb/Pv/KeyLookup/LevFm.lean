-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LevFm.lean: the formats of the rounds of the key sides and of the table's tree are
the formats `rowFm` along their shares of the list `Lam`.

Main names:
  `Lev.fmLev_lam`, `Lev.fmT_lam`, `Lev.fmSides_lam`   a level of k variables; the levels 0 .. n of a
                  tree; m key sides.
  `Dat.keysFm_lam`, `Dat.tableFm_lam`   `A.keysFm L` and `Lev.fmT A.mu (A.d - 1)` are `lamKeys`,
                  `lamTable` under `rowFm`, for every q.
Limits: 1 ≤ m and 1 ≤ v i (i < m); 1 ≤ d.

-/
import Cb.Pv.KeyLookup.LevRunD
import Cb.Pv.KeyLookup.LevSent
import Cb.Pv.KeyLookup.LamFm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace Lev
open Flat

theorem fmLev_lam (S : Pub) (q k : ℕ) : fmLev k = (levRows q k).map (rowFm S) := by
  simp [fmLev, fmSum, levRows, psc, rowFm, LRow.short, rowDraws, Function.comp_def]
  rfl

theorem fmT_lam (S : Pub) (q g : ℕ) : ∀ n, fmT g n = (tree q g (n + 1)).map (rowFm S)
  | 0 => by
    rw [tree_is]
    simpa [fmT, List.range_succ] using fmLev_lam S q (g + 0)
  | n + 1 => by
    rw [tree_is, List.range_succ, List.flatMap_append, List.map_append, ← tree_is, ← fmT_lam S q g
        n]
    simpa [fmT] using fmLev_lam S q (g + (n + 1))

variable {E : Type} [Field E] [Fintype E] {B : KeyBase E}

theorem fmSides_lam (S : Pub) (q : ℕ) : ∀ (ps : List (KeyPart B)) (p : KeyPart B),
    fmSides p ps = ((p :: ps).flatMap fun r => tree q 0 (r.v' + 1)).map (rowFm S)
  | [], p => by
    simpa [fmSides] using fmT_lam S q 0 p.v'
  | r :: ps, p => by
    rw [List.flatMap_cons, List.map_append, ← fmSides_lam S q ps r, ← fmT_lam S q 0 p.v']
    rfl

end Lev

namespace Dat
open Flat Lev
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (L : LevPl A)

theorem keysFm_lam (q : ℕ) (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) :
    A.keysFm L = (lamKeys q A.toPub).map (rowFm A.toPub) := by
  have e : (A.part L 0 :: A.tailP L).flatMap (fun r => tree q 0 (r.v' + 1)) =
      lamKeys q A.toPub := by
    unfold lamKeys
    rw [← A.parts_bits L hm hv, List.flatMap_map]
  rw [← e]
  exact fmSides_lam (B := A.kb) A.toPub q (A.tailP L) (A.part L 0)

theorem tableFm_lam (q : ℕ) (hd : 1 ≤ A.d) :
    fmT A.mu (A.d - 1) = (lamTable q A.toPub).map (rowFm A.toPub) := by
  have h := fmT_lam A.toPub q A.mu (A.d - 1)
  rw [Nat.sub_add_cancel hd] at h
  exact h

end Dat
end Lk6

#print axioms Lk6.Dat.keysFm_lam
#print axioms Lk6.Dat.tableFm_lam
