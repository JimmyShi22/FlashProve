-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoPadAll.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  hcOut2R, hcOut2V, hcOut2
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  PadLeft, Stretch, shape_ok
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.FoSzPad
import Johnson.Top.H.FlPort.FoR5Run
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun
import Johnson.Top.H.FlPort.FoDraws
import Johnson.Top.H.FlPort.FoPadCut
import Johnson.Top.H.FlPort.FoSz
import Johnson.Top.H.FlPort.FoPadLeft
import Johnson.Top.H.FlPort.PscRounds
import Johnson.Top.H.FlPort.FoPadHeard
import Johnson.Top.H.FlPort.FoWalks
import Johnson.Top.H.FlPort.FoDescent
import Johnson.Top.H.FlPort.FoPadFlat
import Johnson.Top.H.FlPort.FoR5At
import Johnson.Top.H.FlPort.FoR5
import Johnson.Top.H.FlPort.FoTieNums
import Johnson.Top.H.FlPort.FoTieEnd
import Johnson.Top.H.FlPort.FoTieAll
import Johnson.Top.H.FlPort.FoTieInv
import Johnson.Top.H.FlPort.FoHead
import Johnson.Top.H.FlPort.FoLevelLaw
import Johnson.Top.H.FlPort.FoPadShape
import Johnson.Top.H.FlPort.FoWalksAt

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

theorem hcOut2R : HCout2R := by
  intro K _ ρ calls pub lid lm F F' c c' g hr hF hc
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' c c' g hr
  have hg : g.shape = M.h pub := pad_shape P
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
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


end Fo.Tp
