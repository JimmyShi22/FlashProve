-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LocRead.lean: the written round of "LOC" read as one typed draw of a list of
locations, by the library's own maps of written rounds (OnBytes/Flat/CarrySForms.lean: RMap.pos).

  posMaps d a t    the written round d is read as one typed draw of t positions below 2 ^ a.
  posMaps_ok       it is as the library asks where d draws t positions below 2 ^ a and no element.
  poss_shown       the positions that the block reads as drawn off the round shown are the list that
                   the map reads.
  posMaps_pass     the test of work that the map asks is the stretch's.

What is not claimed. That the written round draws so (SendsDraws) is a premise. Nothing on the
columns that are read at the drawn positions. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.ZetaRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (noDigest)
open Iop.IOR (drawRound)

/-- The written round d, read as one typed draw of t positions below 2 ^ a. -/
def posMaps (d : RDT) (a t : Nat) : Maps [d] [drawRound (Fin t → Fin (2 ^ a))] :=
  .step (RMap.pos (fun _ => ((), ())) a t id) .nil

/-- It is as the library asks. -/
theorem posMaps_ok {d : RDT} {ns t a : Nat} (h : SendsDraws (toRD d) ns 0 t a) :
    (posMaps d a t).OK :=
  ⟨RMap.pos_ok _ h Function.injective_id, trivial⟩

/-- **The positions that the block reads as drawn are the list that the map reads.** -/
theorem poss_shown {d : RDT} {ns t a : Nat} (h : SendsDraws (toRD d) ns 0 t a)
    (m : (wT d).Msg) (c : (wT d).Chal) :
    (noDigest (shownAt d m c)).drawn.poss =
      List.ofFn fun i => (gPos a t _ (valsOf (toRD d) c) i).val := by
  have he : (noDigest (shownAt d m c)).drawn.poss = (rvOf (toRD d) (msgRD d m) c).poss := rfl
  have hl : (rvOf (toRD d) (msgRD d m) c).poss.length = t := by
    rw [rvOf_poss, possV_length, h.poss]
  rw [he]
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn]
  rw [h.gPos_val (msgRD d m) c ⟨i, by simpa using h2⟩, List.getD_eq_getElem _ _ h1]

/-- The test of work that the map asks is the stretch's. -/
theorem posMaps_pass (d : RDT) (a t : Nat) (τ : Tr (uLT (ckP .two) [d])) :
    (posMaps d a t).pass τ = passT (ckP .two) [d] (rhoT (ckP .two) [d] τ) := by
  obtain ⟨m, c, τ'⟩ := τ
  rfl

end Desc.K14.Law
