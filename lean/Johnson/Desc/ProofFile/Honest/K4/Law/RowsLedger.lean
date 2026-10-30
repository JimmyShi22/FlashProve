-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RowsLedger.lean: CONDITIONAL on a return of the verifier's
function `hearFl` (OnBytes/Desc/First/K4/, "the hearing"). A LAW ON THE VERIFIER's TEXT: the honest
prover is not in it.

What is here. What the ledger holds, behind a return of the hearing of the layers' own rounds
(sub-protocol K4), under the slots of the norms' row products and of the sum that the token sumcheck
on them claims; and which powers batch them. A definition of a proposition, a number, and four
statements with their proofs: calls of the library's `own_ledG` (Johnson/Road/K4/OwnLedgersG.lean),
`hideRun_shown`, `hideRun_factor`, `tsc_cl_factor` (OnBytes/Desc/First/K4/ShownUnder.lean,
FactorUnder.lean), `tsc_cl_shown` (Johnson/Road/K4/OwnLedgers.lean), `tsc_fills`
(Johnson/Road/K4/Slots/Fills.lean), `hideRun_ok` (OnBytes/Tie/Pv/Psc/PscFork.lean), `later_fo`
(OnBytes/Desc/First/K4/TermsShown.lean), `Grows.later` (OnBytes/Desc/First/FlGrows.lean),
`Fo.Later.trans` (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean), `drop_drop'`
(OnBytes/Desc/First/K4/NormsTape.lean).

  `Under G j x f`   slot j of the ledger G is filled; it shows x; its factor is f
  `Under.later`   a later ledger holds the same under a filled slot ("later" is
      `OnBytes.PscRun.Later` here; in `tsc_cl_filled` it is the library's `Fo.Later`, which asks
      less: `later_fo`, OnBytes/Desc/First/K4/TermsShown.lean, leads from the first to the second)
  `rowsRound P g`   the number, in K4's stretch of rounds, from 0, of the round that sends the row
      products; the next round is the first of the token sumcheck on them
  `tcP_drop`   the library's name for the tape from that round on
  `tsc_cl_filled`   the claimed sum's slot is filled in every later ledger
  `hear_rows_under`   under the slot of row product number i: entry i of what that round sent, the
      factor 1; under the slot of the claimed sum: the first word that the next round sent, the
      factor 1; the powers are those of the element that the first of the two rounds sampled

Not shown here. ONE WAY, FROM A RETURN, from a ledger whose arrays have their sizes: that the
hearing returns is not shown. WORDS ALONE: what the ledger shows under a slot is the word as it was
sent; nothing on the hidden value behind it. Nothing on any other slot (Law/SlotsUnder.lean has the
others that are sent with an entry of the mask row). Free of the honest side's frame: no part, no
coin, no thread. It imports four files of the library and no other. Nothing on soundness, on
completeness or on any other property.

Kin. `tcP_drop` IS AN INSTANCE OF THE LIBRARY's `tcP_dropG` (Johnson/Road/K4/SlotsOfLedFirst.lean:
the same equation at every number n0 in the place of `k0 g`), typed again here with the same proof:
that file is not imported: by a walk over import lines it would add some 300 modules to this file's
1,200. The library's own `tcP_drop` (Johnson/Road/K4/SlotsOfLed.lean; another namespace) is the case
n0 = 1. Law/PtsHear.lean (no part of the library yet) has the like at every value of the library's
structure `Ks` and every number (`ks_tcP`); it stands higher than this file. That the slots of
`hear_rows_under`'s first two clauses are filled is also said by two fields (sPv, tVCl) of the
library's `Fills7` (`hear_fills`, Johnson/Road/K4/Slots/HearFills.lean), which is not imported here.
Sought: by statement, to the letter and up to the bound letters, and by short name, among the
theorems of the library and of files that are no part of it yet, as they lay with the writer; by the
names that the proofs unfold, in OnBytes/Desc/First/K4, OnBytes/Desc/First/P1, OnBytes/Tie/Pv/Psc,
Johnson/Road/K4, Johnson/Desc/K4 and Johnson/Desc/ProofFile/Honest. Not sought: a twin of the two
definitions in other letters.
No property is claimed.
-/
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.OwnLedgers
import OnBytes.Desc.First.K4.FactorUnder
import Johnson.Road.K4.Slots.Fills

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.K.Kc (Tape)
open OnBytes.Model (Fork ledNS ledNP ledNO powers)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized Filled Later hideRun_ok)
open OnBytes.Desc.First.K4 (hearFl hear engFl k0 drop_drop' hideRun_shown hideRun_factor
  tsc_cl_factor later_fo hear_calls hearNorms_tape covers)
open OnBytes.Desc.First.P1 (sentOf drawnOf tapeEps tapeCl Ks tscIn_heard levelIn_heard)
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Road.K4 (own_ledG ksOf tsc_cl_shown)

/-- **Under slot j of the ledger G lie the shown word x and the factor f, and the slot is filled.**
-/
structure Under (G : Fork) (j : Nat) (x f : E) : Prop where
  filled : Filled G j
  shown : G.vp.getD j zeroE = x
  factor : G.mf.getD j zeroE = f

/-- A later ledger holds the same under a filled slot. -/
theorem Under.later {G H : Fork} {j : Nat} {x f : E} (h : Under G j x f) (hL : Later G H) :
    Under H j x f :=
  ⟨(hL.keep j h.filled).1, (hL.keep j h.filled).2.1.trans h.shown,
    (hL.keep j h.filled).2.2.trans h.factor⟩

/-- The number, in K4's stretch, from 0, of the round that sends the row products. -/
def rowsRound (P : Pub) (g : Nat) : Nat := k0 g + P.rd.muV + 6

/-- The library's name for the tape from that round on. -/
theorem tcP_drop (P : Pub) (hp : HPlan2) (g : Nat) (t : Tape) :
    (ksOf P hp).tcP (t.drop (k0 g)) = t.drop (rowsRound P g) := by
  have T0 : (t.drop (k0 g)).drop 1 = t.drop (k0 g + 1) := drop_drop' (k0 g) 1 t
  have T1 : (ksOf P hp).tc1 (t.drop (k0 g)) = t.drop (k0 g + 2) := by
    unfold Ks.tc1
    rw [T0, drop_drop']
  unfold Ks.tcP
  rw [T1, drop_drop', drop_drop']
  congr 1
  show k0 g + 2 + (P.rd.muV + 3) + 1 = k0 g + P.rd.muV + 6
  omega

/-- The slot of the sum that a token sumcheck claims is filled in every later ledger: the library's
`tsc_fills` and one step to the later ledger. -/
theorem tsc_cl_filled {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape}
    {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : OnBytes.K.Kc.Fl.tscIn P lt n dY F t = some (o, G, u)) (Hl : Fork) (hL : Fo.Later G Hl) :
    Filled Hl o.sCl :=
  (hL.keep _ (OnBytes.Desc.First.K4.Slots.tsc_fills hF h).2.2.1).1

/-- **What lies under the slots of the row products and of their claimed batch.** -/
theorem hear_rows_under {P : Pub} {hp : HPlan2} {g : Nat} {fo : OnBytes.Model.Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own} (hF : Sized F)
    (h : hearFl P hp g fo F t = some (o, G, u)) :
    (∀ i, i < ledNP P.y.h.xl * P.y.NI →
      Under G (o.H.sPv + i) ((sentOf (t.drop (rowsRound P g))).getD i zeroE) oneE) ∧
    Under G o.H.tV.sCl (tapeCl (t.drop (rowsRound P g + 1))) oneE ∧
    o.H.omV = powers (tapeEps (t.drop (rowsRound P g))) (ledNP P.y.h.xl * P.y.NI) := by
  have h' : hear engFl P hp g fo F t = some (o, G, u) := h
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hF h'
  obtain ⟨vP, hvl, hvs, hrun⟩ := L.runP
  obtain ⟨v2, c2⟩ := L.c2
  have hF7 : Sized ({ F7 with next := F7.next + ledNP P.y.h.xl * P.y.NI } : Fork) := L.s7
  have l8 : Fo.Later F8 G := (later_fo (Grows.later c2)).trans L.g1
  have TP := tcP_drop P hp g t
  have T2 : ((ksOf P hp).tcP (t.drop (k0 g))).drop 1 = t.drop (rowsRound P g + 1) := by
    rw [TP, drop_drop']
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hi' : i < vP.size := by
      rw [hvs]
      exact hi
    obtain ⟨_, _, hin, _⟩ := hideRun_ok _ F8 F7.next vP oneE hF7 hrun
    rw [L.kSPv, L.sPv]
    refine ⟨(l8.keep _ (hin i hi').2.2.1).1, ?_, hideRun_factor hF7 hrun l8 i hi'⟩
    rw [← TP]
    exact hideRun_shown hF7 hrun hvl l8 i hi'
  · rw [L.kTV]
    refine ⟨tsc_cl_filled L.s8 c2 G L.g1, ?_, tsc_cl_factor L.s8 c2 G L.g1⟩
    rw [← T2]
    exact tsc_cl_shown L.s8 c2 G L.g1
  · rw [L.kOmV, L.omV, TP]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.Under
#print axioms ProofFile.Honest.K4.Under.later
#print axioms ProofFile.Honest.K4.rowsRound
#print axioms ProofFile.Honest.K4.tcP_drop
#print axioms ProofFile.Honest.K4.tsc_cl_filled
#print axioms ProofFile.Honest.K4.hear_rows_under
