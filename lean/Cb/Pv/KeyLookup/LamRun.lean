-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LamRun.lean: what the verifier of the lookup at the short sumcheck puts out, as ONE
plain
function of the flat transcript, for all transcripts.

A typed transcript is read flat: round by round the scalars sent and the elements drawn
(Cb/Pv/KeyLookup/Flat.lean). This file joins the eight stretches' statements of that kind.

It imports the library's side alone (no file of the port): Cb/Pv/KeyLookup/Lam1Short.lean,
Cb/Pv/KeyLookup/AsmRuns.lean and the stretches' files TieRun, PartsRun, LevRunD, CloseRun.

  `A.runD P`     the eight stretches' formats and plain functions, side by side.
  `A.lamRun P`   THE ONE FUNCTION, from the caller's state and a flat transcript to what is left:
                 the
                 state, a claim (point, mask form, target) for each part, and the rows as linear
                 forms
                 with targets. It is a definition for which Lean makes code.
  `lamS_runs`    `Flat.Runs (A.lamS P Ex) (A.runD P).fm (A.lamRun P)`: readers of the shape's
                 rounds, with
                 the formats `(A.runD P).fm`, such that typed transcripts and flat lists that fit
                 are
                 one-to-one.
  `lamS_out`     for all st y τ: (A.lamS P Ex).R.out st y τ = some (A.lamRun P st (view τ)).
  `lamS_spells`  for every flat list f that fits there is a typed transcript whose view is f, and at
                 it
                 the verifier puts out `A.lamRun P st f`.
Under: a decidable equality on the field, beside what the library asks of it. No condition on
numbers.
Not claimed here: that the formats are those of the list of Cb/Pv/KeyLookup/Lam.lean (that is
Cb/Pv/KeyLookup/LamRunFm.lean); that the function is the port's; anything on an honest side.

-/
import Cb.Pv.KeyLookup.Lam1Short
import Cb.Pv.KeyLookup.AsmRuns
import Cb.Pv.KeyLookup.TieRun
import Cb.Pv.KeyLookup.PartsRun
import Cb.Pv.KeyLookup.LevRunD
import Cb.Pv.KeyLookup.CloseRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn Flat

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]

/-- The eight stretches' formats and plain functions. -/
def Dat.runD (A : Dat E) (P : Pl A) : RunD A where
  fHead  := ⟨0, 1, false⟩ :: TieR.fmT (A.pl - 2)
  fParts := Parts.fmK (A.m - 1)
  fJoin  := [⟨0, A.mu, false⟩]
  fKeys  := A.keysFm P.lev
  fTable := Lev.fmT A.mu (A.d - 1)
  fClo   := A.fmClo
  fZero  := [⟨0, A.mu + A.d, false⟩]
  fBits  := A.fmBits
  rHead  := A.headRun P.tie (A.pl - 2)
  rParts := A.partsRun P.wP P.cP
  rJoin  := A.joinRun
  rKeys  := A.keysRun P.lev
  rTable := A.tableRun P.lev
  rClo   := A.closeRun P.cl
  rZero  := A.zeroRun
  rBits  := A.bitsRun P.cl

/-- THE ONE FUNCTION. -/
def Dat.lamRun (A : Dat E) (P : Pl A) : A.St → List (RV E) → A.Out := (A.runD P).run

/-- Each stretch's output is its plain function of the flat view. -/
noncomputable def bks_runs_short (A : Dat E) (P : Pl A) (Ex : ExtSpec) :
    (A.bks P (SK₀ E Ex)).Runs (A.runD P) where
  head  := headK_runs A P.tie Ex (A.pl - 2)
  parts := partsXK_runs A P.wP P.cP Ex
  join  := A.joinK_runs Ex
  keys  := A.keys_runs P.lev
  table := A.table_runs P.lev
  clo   := A.closeK_runs P.cl Ex
  zero  := A.zeroK_runs Ex
  bits  := A.bitsK_runs P.cl Ex

/-- The lookup's output is the one function of the flat view. -/
noncomputable def lamS_runs (A : Dat E) (P : Pl A) (Ex : ExtSpec) :
    Flat.Runs (A.lamS P Ex) (A.runD P).fm (A.lamRun P) :=
  (A.bks P (SK₀ E Ex)).lam1_runs (A.runD P) (bks_runs_short A P Ex)

theorem lamS_out (A : Dat E) (P : Pl A) (Ex : ExtSpec) (st : A.St) (y : Ex.Str)
    (τ : Tr (A.lamS P Ex).R.shape) :
    (A.lamS P Ex).R.out st y τ = some (A.lamRun P st ((lamS_runs A P Ex).rd.view τ)) :=
  (lamS_runs A P Ex).out st y τ

theorem lamS_spells (A : Dat E) (P : Pl A) (Ex : ExtSpec) (f : List (RV E))
    (hf : fitsAll (A.runD P).fm f = true) :
    (lamS_runs A P Ex).rd.view ((lamS_runs A P Ex).rd.mk f) = f ∧
      ∀ st y, (A.lamS P Ex).R.out st y ((lamS_runs A P Ex).rd.mk f) = some (A.lamRun P st f) :=
  (lamS_runs A P Ex).spells f hf

end Lk6

#print axioms Lk6.lamS_runs
#print axioms Lk6.lamS_out
#print axioms Lk6.lamS_spells
