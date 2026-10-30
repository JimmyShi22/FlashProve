-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyAt15Seat.lean: THEOREMS. **Public premises of the law at the key file's proximity test on its first chain (row 1.15; field r1_15), in that law's own letters, from the equations that hold in the goals' scope.**
WORDS. Key.descriptionFromSource X N P: the key file's IOP as written in Lean; a block: a sub-protocol; what the verifier carries between two sub-protocols: the verifier's state; ρ · y in SeedIs: a sent message's own out-of-domain (OOD) seed and answer.
OBJECT: the premises hlog · told · hseed · horc · hnum of law_15 (Johnson/RunOne/Law/K12Law15At.lean), at its i₁ := ⟨1, by decide⟩: the lookups' own message, at the seat (1, 0). USER: that theorem. LETTERS: X N P · D' · a.
  aOf_mul          by the kernel: the depth of the code of the shape shMul is 22
  seat_15_scope    hlog ∧ told: what the IOP tells of tree 1: it is told, and its log-length is that depth
  seed_15_scope    hseed at every state reached behind fifteen sub-protocols: the state holds the sending kind's row of message 1
  orc_15 | num_15  horc | hnum: the tables' plan numbers message 1 as 1, both ways
What is not claimed. That scope's equations hold. law_15's other premises. Nothing on soundness.

-/
import Johnson.RunOne.KeyPinwReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyLetters
open Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open OnBytes.Maker
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey shIdx shMul)
open Lk6.AtPlan (keyFull)
open LPFD (Hist₁)

theorem aOf_mul : aOf csKey shMul = 22 := by decide +kernel

/-- **hlog ∧ told at the seat (1, 0).** -/
theorem seat_15_scope (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) :
    (∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix (⟨1, by decide⟩ : Fin six.length)).1 = some o → o.logLength = aOf csKey (six.get (⟨1, by decide⟩ : Fin six.length)).1) ∧
      ((Fk X N P).oracleAt (seatAt six numSix atSix (⟨1, by decide⟩ : Fin six.length)).1).isSome = true := by
  have h := (nums_front X N P (hc.trans codes_full) hi hr).2
  obtain ⟨o, ho, hn⟩ := Option.map_eq_some_iff.1 h
  have hl : o.logLength = 22 := congrArg (·.1) hn
  refine ⟨fun o' ho' => ?_, ?_⟩
  · have e : o' = o := Option.some.inj (ho'.symm.trans ho)
    rw [e, hl]
    exact aOf_mul.symm
  · show ((Key.descriptionFromSource X N P).oracleAt 1).isSome = true
    rw [ho]
    rfl

/-- **hseed at every state reached behind fifteen sub-protocols.** -/
theorem seed_15_scope (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (D' : WholeD) :
    ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D' 15 a → ∃ ρ y, K1.SeedIs csKey (six.get (⟨1, by decide⟩ : Fin six.length)).1 a.2.d.st 1 ρ y :=
  fun a h => Johnson.RunOne.KeyMsg.msg_seedIs_at (cs := csKey) (sh := shMul) (hc.trans codes_full) (by rw [hr]; exact msg_shape_full') _
    (Johnson.RunOne.KeyMsg.cond_msg_plan hp hc hr) (by decide) D' 13 a h

theorem orc_15 (X : Key.Source) : (KeyRows1.plan₁ (oneAt X)).orc 1 = some 1 := by
  have h := orc_noSix (oneAt X) (⟨1, by decide⟩ : Fin six.length) (by decide)
  rw [noSix_eq (oneAt X) (⟨1, by decide⟩ : Fin six.length) (by decide)] at h
  simpa using h

theorem num_15 (X : Key.Source) : (KeyRows1.plan₁ (oneAt X)).num 1 = some 1 := rfl

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.aOf_mul
#print axioms Johnson.RunOne.KeyLetters.seat_15_scope
#print axioms Johnson.RunOne.KeyLetters.seed_15_scope
#print axioms Johnson.RunOne.KeyLetters.orc_15
#print axioms Johnson.RunOne.KeyLetters.num_15
