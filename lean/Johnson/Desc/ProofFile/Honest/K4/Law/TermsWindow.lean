-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsWindow.lean: CONDITIONAL.

What is here. Two premises of TermsLed.lean's and TermsTop.lean's statements on the second token
sumcheck's form, had from the hearing's return: the laying of the sumcheck's own slots behind its
rounds returns; and the reading of the inverse of its first challenge, times that challenge's, is 1.

  `led_window`   **the laying returns**: it is the hearing's own step
  `led_hinv`   **the inverse's reading**

Limits. The hearing's return is a premise, opened in the fields of `LedG`
(Johnson/Road/K4/OwnLedgersG.lean). For the second statement besides: THE FIRST CHALLENGE's THREE
WORDS LIE BELOW THE PRIME (`okE`): the library shows that this cannot be dropped
(`coinZero_not_enough`, Johnson/Meaning/HKTHear.lean) and has it of the first word that the first
round of a tape of small words has sampled (`small_eps`, Johnson/Road/K4/OwnCoin.lean); that this
challenge is such a word is not said here. At the reading `Reading.gl`.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsHear
import Johnson.Road.K4.OwnCoin
import Johnson.Road.Rows.LayerEnds34Ref
import OnBytes.Desc.First.K4.HearCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE invE okE)
open OnBytes.Model (Reading Fork Level Tsc Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG gl_ne_of_word)
open OnBytes.Road.Rows (gl_inv)
open OnBytes.Desc.First.P1 (tscIn_heard pscRow_spec)
open OnBytes.Desc.First.K4 (hearNorms_tape hearTerms_calls k0)
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **The laying of the second token sumcheck's own slots behind its rounds returns**: the hearing
does it itself, from the ledger G1' behind the sumcheck's rounds to G2. -/
theorem led_window
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    G1'.hideRun tT.p.first (Array.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) =
      some G2 := by
  obtain ⟨u1, hN, hT⟩ := L.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    a18, a19⟩ := hearNorms_tape hN
  have l2 : (H1.PV.toList.take Q.P.y.h.lt).length = Q.P.y.h.lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard a18).1
  have c3 := L.c3
  rw [at_s2] at c3
  have hu1 : u1 = t.drop (k4StartAt Q 2) := by
    have a19' : u1 = t.drop (k0 Q.g + Q.P.rd.muV + 7 +
      ((H1.PV.toList.take Q.P.y.h.lt).length + 3)) := a19
    rw [a19', l2]
    congr 1
    simp only [k4StartAt]
    omega
  obtain ⟨tT2, Ga, ua, row, p', b1, _, b3, _⟩ := hearTerms_calls hT
  rw [hu1] at b1
  have e := Option.some.inj (b1.symm.trans c3)
  have e1 : tT2 = tT := congrArg Prod.fst e
  have e2 : Ga = G1' := congrArg (fun x => x.2.1) e
  have hw := (pscRow_spec b3).2.2
  rw [e1, e2] at hw
  exact hw

/-- **The reading of the inverse of the second token sumcheck's first challenge, times that
challenge's, is 1**, where the challenge's words lie below the prime. -/
theorem led_hinv
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (hok : okE tT.p.eps = true) :
    Reading.gl.val (invE tT.p.eps) * Reading.gl.val tT.p.eps = 1 := by
  rw [gl_inv]
  exact inv_mul_cancel₀ (gl_ne_of_word hok L.eps)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.led_window
#print axioms ProofFile.Honest.K4.led_hinv
