-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LamRunFm.lean: the formats of the lookup's rounds, as Cb/Pv/KeyLookup/LamRun.lean
has them, are
those of the list of Cb/Pv/KeyLookup/Lam.lean; so «a flat transcript fits» speaks of that list's
columns.

It imports Cb/Pv/KeyLookup/LamRun.lean, Cb/Pv/KeyLookup/LamFm.lean and the eight stretches' own
lines (HeadPartsFm, LevFm, CloseFm); no file of the port.

Under 1 ≤ m, 1 ≤ v i for all i < m, and 1 ≤ d (three clauses of `Pub.Adm`; public numbers):
  `runD_isLam`   each stretch's formats are `rowFm` along its share of the list, for every q.
  `runD_fm`      `(A.runD P).fm = lamFm A.toPub`.
  `lamS_runsL`   `Flat.Runs (A.lamS P Ex) (lamFm A.toPub) (A.lamRun P)`: the statement of
                 Cb/Pv/KeyLookup/LamRun.lean with the list's formats in the place of the stretches'
                 own.
What «fits» reads of the list: a row's kind and its column `sent` in short form, and nothing else;
the number of elements drawn comes by kind from the table `rowDraws` of Cb/Pv/KeyLookup/LamFm.lean.
It reads neither the column n nor the column c.
Not claimed: anything on the port's plan (a file that is not in this library ties `lamFm` to what
is tested against it).

-/
import Cb.Pv.KeyLookup.LamRun
import Cb.Pv.KeyLookup.LamFm
import Cb.Pv.KeyLookup.HeadPartsFm
import Cb.Pv.KeyLookup.LevFm
import Cb.Pv.KeyLookup.CloseFm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Flat

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] (A : Dat E) (P : Pl A)

theorem runD_isLam (q : ℕ) (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) (hd : 1 ≤ A.d) :
    (A.runD P).IsLam q where
  head  := head_fm q A.toPub
  parts := parts_fm q A.toPub
  join  := A.join_fm q
  keys  := A.keysFm_lam P.lev q hm hv
  table := A.tableFm_lam q hd
  clo   := A.clo_fm q
  zero  := A.zero_fm q
  bits  := A.bits_fm q

theorem runD_fm (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i) (hd : 1 ≤ A.d) :
    (A.runD P).fm = lamFm A.toPub :=
  (A.runD P).fm_isLam 0 (runD_isLam A P 0 hm hv hd)

/-- The lookup's output is the one function of the flat view, at the list's formats. -/
noncomputable def lamS_runsL (Ex : Iop.ExtSpec) (hm : 1 ≤ A.m) (hv : ∀ i < A.m, 1 ≤ A.v i)
    (hd : 1 ≤ A.d) : Flat.Runs (A.lamS P Ex) (lamFm A.toPub) (A.lamRun P) :=
  (lamS_runs A P Ex).fmEq (runD_fm A P hm hv hd)

end Lk6

#print axioms Lk6.runD_isLam
#print axioms Lk6.runD_fm
#print axioms Lk6.lamS_runsL
