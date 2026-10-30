-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawParted.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS OWN TEXT AND THE TEXT
THAT SAYS YES TO ALL, PARTED BY A NUMBER; AND THE ROUND'S PRICE AT EVERY NUMBER OF COMBINATIONS.

Johnson/Desc/First/K8/LawYes.lean shows, at the toy member of the letters: the text that says yes to
all has the plain form at no error below the round's whole number of written verifier messages. That
the kind's own text's error there is below that number is shown here.
  `hear_price_tau`: GENERAL: at every number tau of combinations the proved block's count, at the
    kind's declared round, is a share of at most 2 ^ -tau of the round's written verifier messages
    (`below_of_entriesOnly`, Johnson/Flat/NoRoomSmall.lean). At tau = 128 it is `hear_price`
    (Johnson/Desc/First/K8/LawPrice.lean).
  `toyErr_lt`: so the toy's error (one combination: a half) is below the round's number of written
    verifier messages.
  `toy_keepsW`: the kind's own text has the plain form at the toy's error.
  `toy_parted`: BETWEEN THE SAME BOUNDARIES, AT THE SAME ERROR, the text that says yes to all has it
    not.
Statements and proofs. Limits: a toy, but for `hear_price_tau`. A prover's message m of the round is
an argument.

-/
import Johnson.Desc.First.K8.LawYes
import Johnson.Desc.First.K8.LawPrice

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Desc.First.K8

open Iop Prob Cb.Pv.Tail OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Tail KObj KObj.TailRow
  VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Number

/-- **At every number of combinations**: the proved block's count is a share of at most 2 ^ -tau of
the round's written verifier messages. -/
theorem hear_price_tau {p : Par} {s : Size} (hf : Fits p s) :
    RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ s.tau) :=
  below_of_entriesOnly ⟨onlyTrits hf, rfl, Nat.zero_le _⟩ _ _
    ((VerifiableInference.Number.le_inv_pow_iff _ _ s.tau).2
      (by rw [card_dr]; exact Nat.div_mul_le_self _ _))

/-- The toy's error is below the round's number of written verifier messages. -/
theorem toyErr_lt : toyErr < Nat.card (roundT (Run.ckP .two) (rdt toyPar)).up.Chal := by
  have h1 := (VerifiableInference.Number.le_inv_pow_iff _ _ _).1 (hear_price_tau toyFitsOn)
  have h2 : 0 < Fintype.card (wRound (rd toyPar)).Chal := Fintype.card_pos
  have h3 : toyErr * 2 ^ 1 ≤ Fintype.card (wRound (rd toyPar)).Chal := h1
  rw [Nat.card_eq_fintype_card]
  have h4 : Fintype.card (roundT (Run.ckP .two) (rdt toyPar)).up.Chal =
      Fintype.card (wRound (rd toyPar)).Chal := rfl
  rw [h4]
  omega

/-- The kind's own text has the plain form at the toy's error. -/
theorem toy_keepsW (base : ℕ) :
    (piece (Cl := Unit) (W := (KTailRngOn.src toyOn).W) (F := toyFrame) toySeatP toyPar base
        toyErr).ior.red.KeepsW
      (toyReads base toyErr).onA (toyReads base toyErr).onB (toyReads base toyErr).relA
      (toyReads base toyErr).relB
      (piece (Cl := Unit) (W := (KTailRngOn.src toyOn).W) (F := toyFrame) toySeatP toyPar base
        toyErr).err :=
  hear_keepsW (toyReads base toyErr) toyFitsOn toyOn_mem (Nat.le_refl _)

/-- **The two texts are parted by a number**: between the same boundaries, at the same error, the
kind's own text has the plain form and the text that says yes to all has it not. -/
theorem toy_parted (base : ℕ) (y : toyFrame.E.Str)
    (m : (roundT (Run.ckP .two) (rdt toyPar)).up.Msg) :
    ¬ (toyYesPiece base toyErr).ior.red.KeepsW
      (toyReads base toyErr).onA (toyReads base toyErr).onB (toyReads base toyErr).relA
      (toyReads base toyErr).relB (toyYesPiece base toyErr).err :=
  toyYes_not_keeps base toyErr y m toyErr_lt

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.hear_price_tau
#print axioms VerifiableInference.Desc.First.K8.toyErr_lt
#print axioms VerifiableInference.Desc.First.K8.toy_keepsW
#print axioms VerifiableInference.Desc.First.K8.toy_parted
