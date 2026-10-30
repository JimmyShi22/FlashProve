-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoWalks.lean: the two walks down a product tree in the byte-level
verifier's lookup routine are the
flat function's levels: with no hypothesis on a level, and at the flat function's own places.

OnBytes/Tie/Pv/Lookup/Forest/FoDescent.lean puts the levels together under the hypothesis LevelLaw,
for any places of the masks
that meet LedsFrom. Here LevelLaw is levelLaw (OnBytes/Tie/Pv/Lookup/Forest/FoLevelLaw.lean), and
the places are those of the
flat function at a forest (numsF's ledK and ledT), which meet LedsFrom from the key side's and the
table side's first slot on (leds_key, leds_tab).

 - keys_walk: the fold over the key levels, as Forest.pad writes it, from a state whose next free
   slot is the key side's first.
 - table_walk: the fold over the table's levels, from a state whose next free slot is the table
   side's first.
Further premises of both: the fold returns; the state fits (Sized); the start form is compared
(FormIs). Of keys_walk: 10 ≤ dT, and the point at the start is empty. Of table_walk: the point at
the start, read, is a point of 5 coordinates reversed.
What they hand on is the record Walked (OnBytes/Tie/Pv/Lookup/Forest/FoDescent.lean).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoDescent
import OnBytes.Tie.Pv.Lookup.Forest.FoLevelLaw

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The key side. jLK: the lookup's first slot. -/
theorem keys_walk (h : FoNums.Sh) (hd : 10 ≤ h.dT) (jLK : ℕ) (s s' : Forest.Descent)
    (F G : Fork) (c c' : Ctx) (tg : K) (inc : List (Pl × K))
    (hrun : ((List.range h.v).foldlM
      (fun (s : Forest.Descent) mu =>
        Forest.level s mu
          (if mu + 1 = h.v then Forest.orderForestRange mu h.rK else orderDefault mu)) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hn : F.next = jLK + (FoNums.S h).fKey 0) (hr : s.rho = #[])
    (hF : FormIs ρ F s.form tg inc) :
    ∃ ev lv rows, Walked ρ (FoNums.ordK h) (fun l => ledF jLK ((FoNums.S h).pKeyC l)) 0 h.v 0 s s'
      F G c c' [] tg inc ev lv rows :=
  keys_descent ρ (levelLaw ρ) h hd _ s s' F G c c' tg inc hrun hS hr hF (hn ▸ leds_key h jLK)

/-- The table side. pt: the point that joins the planes' roots, by coordinate. -/
theorem table_walk (h : FoNums.Sh) (jLK : ℕ) (s s' : Forest.Descent) (F G : Fork) (c c' : Ctx)
    (pt : List K) (tg : K) (inc : List (Pl × K))
    (hrun : ((List.range h.d).foldlM
      (fun (s : Forest.Descent) l => Forest.level s (5 + l) (orderDefault (5 + l))) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hn : F.next = jLK + (FoNums.S h).fTab 0) (hl : pt.length = 5)
    (hr : rdA ρ s.rho = pt.reverse) (hF : FormIs ρ F s.form tg inc) :
    ∃ ev lv rows, Walked ρ FoNums.ordT (fun l => ledF jLK ((FoNums.S h).pTabC l)) 5 h.d 0 s s'
      F G c c' pt tg inc ev lv rows :=
  table_descent ρ (levelLaw ρ) h _ s s' F G c c' pt tg inc hrun hS hl hr hF (hn ▸ leds_tab h jLK)

end
end Fo
