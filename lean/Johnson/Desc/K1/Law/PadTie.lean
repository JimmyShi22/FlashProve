-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PadTie.lean: one quantity by two roads, tied: the places that the statement's
page records as a message's pad are the places at which the kind's sample rows have their pads.

Main names: pad_places, wr_pad.
The kind's rows count a row's places by 2 ^ logEll, the statement's page by the code's length: the
two agree where every code's length is a power of two.
A pure function of the verifier program is named: Send.pad.

What is not claimed. Nothing without that premise. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.Sound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-- **The recorded pad is the rows' pad.** -/
theorem pad_places (codes : Codes) (s : OracleShape) (hl : codes.lengthsOk = true)
    (hs : Blk.shapeOk codes s = true) (hp : (Msg.of codes s).padFits = true) :
    Send.pad codes s = some ((Msg.of codes s).pads.map fun x =>
      { part := (Msg.of codes s).padPart, index := x.2.1, answer := x.1,
        basis := thetaE x.2.2 }) := by
  have hcl : ∀ n, clog n = ceilLog2 n := fun _ => rfl
  simp only [Codes.lengthsOk, Bool.and_eq_true] at hl
  simp only [Blk.shapeOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  simp only [Msg.padFits, Msg.of, Msg.e, decide_eq_true_eq] at hp
  by_cases hz : s.maskRows = 0
  · have hm : s.code < codes.base.size := by
      rcases hs.1.1.2 with h | h
      · omega
      · exact h
    have hmr : 0 < s.mainRows := by omega
    have e := pow_logEll codes.base s.code hm hl.1
    simp only [hz, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, if_false, e] at hp
    have hnot : ¬ (codes.base.getD s.code default).ell <
        (if (s.mainDeg == 3) = true then 1 else 3) * s.answers := Nat.not_lt.2 hp
    unfold Send.pad Send.cube Msg.pads
    simp only [Msg.pad_eq, List.map_map, List.map_flatMap, Msg.padIdx, Msg.padRows, Msg.padLen,
      Msg.padPart, Msg.e, Msg.of, hz, hmr, hcl, e, Nat.lt_irrefl, decide_false, decide_true,
      bne_self_eq_false, Bool.false_or, Bool.false_eq_true, if_false, if_true, hnot,
      Function.comp_def]
  · have hm : s.maskCode < codes.mask.size := by
      rcases hs.1.2 with h | h
      · exact absurd h hz
      · exact h
    have hz' : 0 < s.maskRows := Nat.pos_of_ne_zero hz
    have hb : (s.maskRows != 0) = true := by simpa using hz
    have e := pow_logEll codes.mask s.maskCode hm hl.2
    simp only [hb, Bool.true_or, if_true, e, Nat.one_mul] at hp
    have hnot : ¬ (codes.mask.getD s.maskCode default).ell < 1 * s.answers := by omega
    unfold Send.pad Send.cube Msg.pads
    simp only [Msg.pad_eq, List.map_map, List.map_flatMap, Msg.padIdx, Msg.padRows, Msg.padLen,
      Msg.padPart, Msg.e, Msg.of, hz', hb, hcl, e, decide_true, Bool.true_or, if_true, hnot,
      if_false, Function.comp_def]

/-- The pad that the sending writes into a sampled message's record. -/
theorem wr_pad (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (hl : codes.lengthsOk = true) (hs : Blk.shapeOk codes s = true)
    (hp : (Msg.of codes s).padFits = true) (h0 : s.answers ≠ 0) :
    (wr codes seeds o s ys).pad =
      (Msg.of codes s).pads.map fun x => ((Msg.of codes s).padPart, x.2.1) := by
  simp [wr, h0, pad_places codes s hl hs hp, List.map_map, Function.comp_def]

end VerifiableInference.Desc.K1
