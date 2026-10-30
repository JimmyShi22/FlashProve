-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/EndSlots.lean: the typed claim on an end value holds exactly if the map at the
point is what the end value's slot is worth in the world of the state behind the sumcheck's
messages.

`plain_end_slot` (OnBytes/Tie/Pv/Att/TiesFull.lean) says that of a bare element. Here the element is
the worth of the slot sEnd + (the number of the end value) in the world of a state in which the end
values lie under the slots from sEnd on with the factor beta (`Filled`,
OnBytes/Tie/Pv/Psc/Run/PscHide.lean), as `scd_tie_full` and `sc3_tie_full` give it for the state F2.

Main names:
  `plain_end_world`: for the parameters of a plain sumcheck, a numbering num of the end values below
    the number of values v, the end values read under their names, and entries m whose entry at the
    place cAt a is the mask entry of the slot sEnd + num a: the typed claim on end value a
    (`PscPar.EHolds` of `plainOut`) holds exactly if the map a at the output's point is what the
    slot sEnd + num a is worth.
  `scd_end_world`, `sc3_end_world`: the same at the two kinds of attention, with `scdNum` and
    `sc3Num`.

Limits: the world is that of the state F2, behind the receipt of the messages. That a later state
keeps these slots is not said here. That the entries' places cAt are the slots' mask entries is a
premise on the choice of cAt.
-/
import OnBytes.Tie.Pv.Att.TiesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open Johnson.L5.Layers Cb.Pv.Att

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

theorem plain_end_world (T : PlainSc K) (st : T.St) (target mu eps : E) (rs : List (List E × E))
    (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (v : List E) (num : T.A → ℕ)
    (hnum : ∀ a, num a < v.length) (F0 F2 : Fork) (sEnd : ℕ) (hF : Filled F0 F2 sEnd v beta)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : T.J → K)
    (hm : ∀ a, m (T.cAt a) = mask (sEnd + num a)) (a : T.A) :
    T.our.par.EHolds
        (plainOut ρ T st target mu eps rs sentY beta hβ fun a => ρ.val (v.getD (num a) zeroE)) m a ↔
      T.map st m a (ldPartIni T.nv T.deg (pDummy K T.DY)
          (plainOut ρ T st target mu eps rs sentY beta hβ
            fun a => ρ.val (v.getD (num a) zeroE)).pt) =
        (F2.worldOf ρ mask entry).slot (sEnd + num a) :=
  plain_end_slot ρ T st target mu eps rs sentY beta hβ _ m a _
    (by rw [hF.world ρ mask entry (num a) (hnum a), hm a])

theorem scd_end_world {s : ScdSize} (T : Cb.Pv.Att.Scd K s) (st : T.St) (target mu eps : E)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (v : List E)
    (hv : v.length = s.Lam + s.pairs * s.lt) (F0 F2 : Fork) (sEnd : ℕ)
    (hF : Filled F0 F2 sEnd v beta) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : T.J → K)
    (hm : ∀ a, m (T.cAt a) = mask (sEnd + scdNum s a)) (a : s.A) :
    T.plain.our.par.EHolds
        (plainOut ρ T.plain st target mu eps rs sentY beta hβ (scdVals ρ s v)) m a ↔
      T.map st m a (ldPartIni s.k s.deg (pDummy K (s.lt + 1))
          (plainOut ρ T.plain st target mu eps rs sentY beta hβ (scdVals ρ s v)).pt) =
        (F2.worldOf ρ mask entry).slot (sEnd + scdNum s a) :=
  plain_end_world ρ T.plain st target mu eps rs sentY beta hβ v (scdNum s)
    (fun a => by rw [hv]; exact scdNum_lt s a) F0 F2 sEnd hF mask entry m hm a

theorem sc3_end_world (T : Cb.Pv.Att.Sc3 K) (st : T.St) (target mu eps : E)
    (rs : List (List E × E)) (sentY : List E) (beta : E) (hβ : ρ.val beta ≠ 0) (v : List E)
    (hv : v.length = 2 * T.nb) (F0 F2 : Fork) (sEnd : ℕ) (hF : Filled F0 F2 sEnd v beta)
    (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K) (m : T.J → K)
    (hm : ∀ a, m (T.cAt a) = mask (sEnd + sc3Num a)) (a : Fin T.nb × Bool) :
    T.plain.our.par.EHolds
        (plainOut ρ T.plain st target mu eps rs sentY beta hβ (sc3Vals ρ T.nb v)) m a ↔
      T.map st m a (ldPartIni T.nv (fun _ => 3) (pDummy K 2)
          (plainOut ρ T.plain st target mu eps rs sentY beta hβ (sc3Vals ρ T.nb v)).pt) =
        (F2.worldOf ρ mask entry).slot (sEnd + sc3Num a) :=
  plain_end_world ρ T.plain st target mu eps rs sentY beta hβ v sc3Num
    (fun a => by rw [hv]; exact sc3Num_lt a) F0 F2 sEnd hF mask entry m hm a

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.plain_end_world
#print axioms OnBytes.Tie.Pv.Att.scd_end_world
#print axioms OnBytes.Tie.Pv.Att.sc3_end_world
