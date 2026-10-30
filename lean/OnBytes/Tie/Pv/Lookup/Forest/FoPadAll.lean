-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean.
Every run of the byte-level lookup routine on a view that returns hands on the flat function's end
values.

The statements are those of OnBytes/Tie/Pv/Lookup/Forest/FoRds.lean and
OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean; here they are proved.

* `hcOut2R`: the record's shape is made of the lookup's calls by the byte-level verifier's own
  routines; the state of the sub-proof is left as `PadLeft` says; and there is a list l of calls of
  the channel's routines that leads from the context before the run to the context after it
  (`Evs l c c'`), is a row of rounds whose sizes are those of `Fo.planF`, and at which, read as
  plain data, the record holds `endsOf`. That the run made these very calls is not said. On a view
  all such rows of rounds read as the same plain data (`rds_took`,
  OnBytes/Tie/Pv/Lookup/Forest/FoRds.lean; `took_unique`, OnBytes/Tie/Pv/Lookup/Forest/FoSz.lean).
* `hcOut2V`: the same over the rounds that the run takes off the view. `hcOut2`: with these rounds
given.
All three hold for every reading ρ of the byte-level field in a commutative ring. `endsOf` is taken
at the record's shape, at the first free slot before the run, and at every lm: lm is no argument of
the routine.

Under: the arrays under the slots have their sizes before the run (`Sized F`); the run starts on a
view
with no message open (`Clean c`). Both are hypotheses on the caller.

Does not say: that the routine returns; anything on a dry run; anything on the four claims that the
callers
make of the record later.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadHeard
import OnBytes.Tie.Pv.Lookup.Forest.FoPadLeft
import OnBytes.Tie.Pv.Lookup.Forest.FoPadShape
import OnBytes.Tie.Pv.Lookup.Forest.FoSzPad

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

theorem hcOut2R : HCout2R := by
  intro K _ ρ calls pub lid lm F F' c c' g hr hF hc
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' c c' g hr
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (ask_ok P.ask)
  obtain ⟨l, scs, ptT, lvK, lvT, rowsK, rowsT, evK, evT, D, R⟩ := pad_read ρ P hF hc lm H
  have hH := pad_heard ρ R H
  have e : 1 + (5 + (M.h pub).d + (M.h pub).d) = 1 + 2 * (M.h pub).d + 5 := by omega
  have hLeft : PadLeft (M.h pub) F F' g :=
    pad_left P _ _
      ((R.f4 ▸ R.tieSt).trans ((⟨R.keys.same, R.keys.filled, R.keys.out⟩ :
        Stretch M.F5 M.F6 _).trans ⟨R.table.same, R.table.filled, R.table.out⟩))
      (e ▸ R.r5.stretch)
      ((R.f4 ▸ R.tieLater).trans (R.keys.later.trans (R.table.later.trans R.r5.later)))
      R.r5.sized R.r5.lvFirst
  rw [hg]
  refine ⟨hg ▸ pad_shapeOf P, hLeft, l, R.evs, R.rds, pad_sizes_any ρ P hc R.rds R.evs, ?_⟩
  rw [P.heard, P.fork]
  exact hH

theorem hcOut2V : HCout2V := hcOut2V_of hcOut2R

theorem hcOut2 : HCout2 := hcOut2_of hcOut2V

end Fo
