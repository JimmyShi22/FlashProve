-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/HeadPartsFm.lean: the formats of the rounds of the lookup's head and of its parts'
steps are their shares of the list of rounds, read in short form.

Statements and proofs: two lines of the bundle RunD.IsLam of Cb/Pv/KeyLookup/LamFm.lean. The formats
are those of Cb/Pv/KeyLookup/TieRun.lean (the draw; the tie's steps 0, .., pl - 2) and of
Cb/Pv/KeyLookup/PartsRun.lean (m - 1 steps); rowFm S reads a row of the list of
Cb/Pv/KeyLookup/Lam.lean as a format: its scalars in short form, its kind's number of drawn
elements, whether the draw must not be 0.

Main names:
  head_fm q S: ⟨0, 1, false⟩ :: TieR.fmT (S.pl - 2) = (lamHead q S).map (rowFm S).
  parts_fm q S: Parts.fmK (S.m - 1) = (lamParts q S).map (rowFm S).

Limits: no premise. Nothing on a plan of rounds outside this library.

-/
import Cb.Pv.KeyLookup.LamFm
import Cb.Pv.KeyLookup.TieRun
import Cb.Pv.KeyLookup.PartsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Flat

theorem TieR.fmT_lam (S : Pub) (q c : ℕ) : ∀ n,
    (⟨0, 1, false⟩ : Fm) :: TieR.fmT n =
      ([(⟨.lkp, 0, q, c⟩ : LRow)] ++ psc q [] (some (3, 3)) ++
        (List.range n).flatMap fun _ => psc q [] (some (3, 2))).map (rowFm S)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, List.map_append,
      ← TieR.fmT_lam S q c n]
    rfl

theorem head_fm (q : ℕ) (S : Pub) :
    (⟨0, 1, false⟩ : Fm) :: TieR.fmT (S.pl - 2) = (lamHead q S).map (rowFm S) :=
  TieR.fmT_lam S q (S.allKeys - 1) (S.pl - 2)

theorem Parts.fmK_row (S : Pub) (q : ℕ) : ∀ k, Parts.fmK k = (lamSteps q k).map (rowFm S)
  | 0 => rfl
  | k + 1 => by
    rw [lamSteps_succ, List.map_append, ← Parts.fmK_row S q k]
    rfl

theorem parts_fm (q : ℕ) (S : Pub) : Parts.fmK (S.m - 1) = (lamParts q S).map (rowFm S) :=
  Parts.fmK_row S q (S.m - 1)

end Lk6

#print axioms Lk6.head_fm
#print axioms Lk6.parts_fm
