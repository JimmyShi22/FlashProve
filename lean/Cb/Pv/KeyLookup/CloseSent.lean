-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseSent.lean: how many scalars the prover's message in the clear has in each round
of the join point, the closing, the zero point and the test of the bits, as a number of values,
q^sent: the column `sent` of the list of rounds (Cb/Pv/KeyLookup/Lam.lean; `plainList`, `IsS`:
Cb/Pv/KeyLookup/AsmErr.lean). q := the number of elements of E.

It imports Join.lean, Bits.lean, AsmErr.lean and Cb/Pv/KeyLookup/Short0.lean; no file of the port.

  `Clo.plain_p`, `Clo.plain_s`   for any list of variables' formats: the message of the round of a
                  variable of degree n has q^(n + 1) values at the library's sumcheck, q^n at the
                  short one.
  `join_isS f`, `zero_isS f`   the message in the clear has one value (sent = 0). Stated for every
                  map f on rows that leaves such a row's `sent` at 0 (condition hf); the identity
                  and `LRow.short` (Lam.lean) do.
  `clo_isS_lib`, `bits_isS_lib`       at the library's verifier, with f the identity.
  `clo_isS_short`, `bits_isS_short`   at `SK₀`, with f := `LRow.short`. The closing sends 1 scalar,
                  then 2 for each variable of a row and 1 for each of a plane. The test of the bits
                  sends 1, then 2 for each variable, 2 for the further variable, and 1 value.

-/
import Cb.Pv.KeyLookup.Join
import Cb.Pv.KeyLookup.Bits
import Cb.Pv.KeyLookup.AsmErr
import Cb.Pv.KeyLookup.Short0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Johnson.L5.Layers

namespace Clo
variable {E : Type} [Field E] [Fintype E]

theorem card_vec (n : ℕ) : Nat.card (Fin n → E) = Fintype.card E ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem plain_p (l : List (PFmt E)) :
    plainList (pRounds l) = l.map fun f => Fintype.card E ^ (f.n + 1) := by
  unfold plainList
  rw [List.map_map]
  exact List.map_congr_left fun f _ => card_vec (f.n + 1)

theorem plain_s (l : List (PFmt E)) :
    plainList (sRounds l) = l.map fun f => Fintype.card E ^ f.n := by
  unfold plainList
  rw [List.map_map]
  exact List.map_congr_left fun f _ => card_vec f.n

theorem card_one : Nat.card E = Fintype.card E ^ 1 := by
  rw [Nat.card_eq_fintype_card, pow_one]

theorem card_unitVec : Nat.card (Unit → E) = Fintype.card E ^ 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_unit]

end Clo

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A) (Ex : ExtSpec)

theorem join_isS (f : LRow → LRow) (hf : ∀ n c, (f ⟨.join, 0, n, c⟩).sent = 0) :
    IsS (Fintype.card E) (A.joinK Ex) ((lamJoin (Fintype.card E) A.toPub).map f) := by
  show [Nat.card Unit] = [Fintype.card E ^ (f ⟨.join, 0, _, _⟩).sent]
  rw [hf]
  simp

theorem zero_isS (f : LRow → LRow) (hf : ∀ n c, (f ⟨.zero, 0, n, c⟩).sent = 0) :
    IsS (Fintype.card E) (A.zeroK Ex) ((lamZero (Fintype.card E) A.toPub).map f) := by
  show [Nat.card Unit] = [Fintype.card E ^ (f ⟨.zero, 0, _, _⟩).sent]
  rw [hf]
  simp

theorem en_degs :
    ((A.En P).par.fmt.map fun f => f.n) = List.replicate A.d 2 ++ List.replicate A.mu 1 :=
  (mix_degs E _ _).trans (dgEnd_rev A.mu A.d)

theorem clo_isS_lib :
    IsS (Fintype.card E) (A.closeK P (PscLtK.lib E Ex))
      ((lamClo (Fintype.card E) A.toPub).map id) := by
  show Nat.card E :: plainList (pRounds (A.En P).par.fmt) = _
  have h : ((A.En P).par.fmt.map fun f => Fintype.card E ^ (f.n + 1)) =
      ((A.En P).par.fmt.map fun f => f.n).map fun n => Fintype.card E ^ (n + 1) := by
    rw [List.map_map]
    rfl
  rw [Clo.plain_p, h, A.en_degs P, Clo.card_one]
  simp [lamClo, psc]

theorem clo_isS_short :
    IsS (Fintype.card E) (A.closeK P (SK₀ E Ex))
      ((lamClo (Fintype.card E) A.toPub).map LRow.short) := by
  show Nat.card E :: plainList (sRounds (A.En P).par.fmt) = _
  have h : ((A.En P).par.fmt.map fun f => Fintype.card E ^ f.n) =
      ((A.En P).par.fmt.map fun f => f.n).map fun n => Fintype.card E ^ n := by
    rw [List.map_map]
    rfl
  rw [Clo.plain_s, h, A.en_degs P, Clo.card_one]
  simp [lamClo, psc, LRow.short]

theorem bits_isS_lib :
    IsS (Fintype.card E) (A.bitsK P (PscLtK.lib E Ex))
      ((lamBits (Fintype.card E) A.toPub).map id) := by
  show plainList (pRound0 E :: (pRounds (A.BT P).par.fmt ++ [pRoundV E Unit])) = _
  show Nat.card E :: plainList (pRounds (A.BT P).par.fmt ++ [pRoundV E Unit]) = _
  have h : plainList (pRounds (A.BT P).par.fmt ++ [pRoundV E Unit]) =
      plainList (pRounds (A.BT P).par.fmt) ++ [Nat.card (Unit → E)] := by
    unfold plainList
    rw [List.map_append]
    rfl
  have hf : (A.BT P).par.fmt = List.replicate (A.mu + A.d) (pfCube E 2) ++ [pDummy E 2] := rfl
  rw [h, Clo.plain_p, hf, Clo.card_one, Clo.card_unitVec]
  simp [lamBits, psc, pDummy]

theorem bits_isS_short :
    IsS (Fintype.card E) (A.bitsK P (SK₀ E Ex))
      ((lamBits (Fintype.card E) A.toPub).map LRow.short) := by
  show Nat.card E :: plainList (sRounds (A.BT P).par.fmt ++ [pRoundV E Unit]) = _
  have h : plainList (sRounds (A.BT P).par.fmt ++ [pRoundV E Unit]) =
      plainList (sRounds (A.BT P).par.fmt) ++ [Nat.card (Unit → E)] := by
    unfold plainList
    rw [List.map_append]
    rfl
  have hf : (A.BT P).par.fmt = List.replicate (A.mu + A.d) (pfCube E 2) ++ [pDummy E 2] := rfl
  rw [h, Clo.plain_s, hf, Clo.card_one, Clo.card_unitVec]
  simp [lamBits, psc, pDummy, LRow.short]

end Dat
end Lk6

#print axioms Lk6.Dat.join_isS
#print axioms Lk6.Dat.zero_isS
#print axioms Lk6.Dat.clo_isS_lib
#print axioms Lk6.Dat.clo_isS_short
#print axioms Lk6.Dat.bits_isS_lib
#print axioms Lk6.Dat.bits_isS_short
