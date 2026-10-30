-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoWalksAt.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoWalksAt.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  Walked.flat0, Walked.rows0, Walked.rho0, Walked.form0, Walked.next, keys_next, table_next
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FormIs, RowIs, flEv, keys_slots, table_slots, walkSlots, zero_fun
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
import OnBytes.Tie.Pv.Lookup.Forest.FoWalksAt
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoPscForm
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun
import Johnson.Top.H.FlPort.FoWalks
import Johnson.Top.H.FlPort.FoDescent
import Johnson.Top.H.FlPort.FoLevelLaw

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] {ρ : Reading K} {o : ℕ → List ℕ} {led : ℕ → Led Pl} {g n : ℕ}
  {s s' : Forest.Descent} {F G : Fork} {c c' : Tape} {pt : List K} {tg : K} {inc : List (Pl × K)}
  {ev : List Ev} {lv : List (Sc K × K)} {rows : List Aff}

theorem Walked.flat0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows)
    (rest : Rounds K) :
    lvGo o n 0 tg pt (flEv ρ ev ++ rest) =
      (lv, tgTop tg lv.reverse, pntTop o pt lv.reverse, rest) := by
  have h := W.flat rest
  rwa [zero_fun o] at h

theorem Walked.rows0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    List.Forall₂ (RowIs ρ G) rows (lvRowsR led g inc lv.reverse).reverse := by
  have h := W.rowsAre
  rwa [zero_fun led] at h

theorem Walked.rho0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    rdA ρ s'.rho = (pntTop o pt lv.reverse).reverse := by
  have h := W.rho
  rwa [zero_fun o] at h

theorem Walked.form0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    FormIs ρ G s'.form (tgTop tg lv.reverse) (incTop led inc lv.reverse) := by
  have h := W.form
  rwa [zero_fun led] at h

theorem Walked.next (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    G.next = F.next + walkSlots g n 0 := W.same.next

end

section
variable {K : Type} [CommRing K] {ρ : Reading K} {o : ℕ → List ℕ} {led : ℕ → Led Pl}
  {s s' : Forest.Descent} {F G : Fork} {c c' : Tape} {pt : List K} {tg : K} {inc : List (Pl × K)}
  {ev : List Ev} {lv : List (Sc K × K)} {rows : List Aff}

/-- Behind the key side the table side's first slot is free. -/
theorem keys_next (h : FoNums.Sh) (jLK : ℕ)
    (W : Walked ρ o led 0 h.v 0 s s' F G c c' pt tg inc ev lv rows)
    (hn : F.next = jLK + (FoNums.S h).fKey 0) : G.next = jLK + (FoNums.S h).fTab 0 := by
  rw [W.next, hn, keys_slots h, Nat.add_assoc]

/-- Behind the table side the first slot of the sumcheck over the leaves is free. -/
theorem table_next (h : FoNums.Sh) (jLK : ℕ)
    (W : Walked ρ o led 5 h.d 0 s s' F G c c' pt tg inc ev lv rows)
    (hn : F.next = jLK + (FoNums.S h).fTab 0) : G.next = jLK + (FoNums.S h).fEnd := by
  rw [W.next, hn, table_slots h, Nat.add_assoc]

end

end Fo.Tp
