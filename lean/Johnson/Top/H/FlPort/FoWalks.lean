-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoWalks.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoWalks.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  keys_walk, table_walk
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FormIs, Sized, ledF, leds_key, leds_tab, ordK, ordT
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
import OnBytes.Tie.Pv.Lookup.Forest.FoWalks
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun
import Johnson.Top.H.FlPort.FoDescent
import Johnson.Top.H.FlPort.FoLevelLaw

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The key side. jLK: the lookup's first slot. -/
theorem keys_walk (h : FoNums.Sh) (hd : 10 ≤ h.dT) (jLK : ℕ) (s s' : Forest.Descent)
    (F G : Fork) (c c' : Tape) (tg : K) (inc : List (Pl × K))
    (hrun : ((List.range h.v).foldlM
      (fun (s : Forest.Descent) mu =>
        lkLevel s mu
          (if mu + 1 = h.v then Forest.orderForestRange mu h.rK else orderDefault mu)) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hn : F.next = jLK + (FoNums.S h).fKey 0) (hr : s.rho = #[])
    (hF : FormIs ρ F s.form tg inc) :
    ∃ ev lv rows, Walked ρ (FoNums.ordK h) (fun l => ledF jLK ((FoNums.S h).pKeyC l)) 0 h.v 0 s s'
      F G c c' [] tg inc ev lv rows :=
  keys_descent ρ (levelLaw ρ) h hd _ s s' F G c c' tg inc hrun hS hr hF (hn ▸ leds_key h jLK)

/-- The table side. pt: the point that joins the planes' roots, by coordinate. -/
theorem table_walk (h : FoNums.Sh) (jLK : ℕ) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape)
    (pt : List K) (tg : K) (inc : List (Pl × K))
    (hrun : ((List.range h.d).foldlM
      (fun (s : Forest.Descent) l => lkLevel s (5 + l) (orderDefault (5 + l))) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hn : F.next = jLK + (FoNums.S h).fTab 0) (hl : pt.length = 5)
    (hr : rdA ρ s.rho = pt.reverse) (hF : FormIs ρ F s.form tg inc) :
    ∃ ev lv rows, Walked ρ FoNums.ordT (fun l => ledF jLK ((FoNums.S h).pTabC l)) 5 h.d 0 s s'
      F G c c' pt tg inc ev lv rows :=
  table_descent ρ (levelLaw ρ) h _ s s' F G c c' pt tg inc hrun hS hl hr hF (hn ▸ leds_tab h jLK)

end

end Fo.Tp
