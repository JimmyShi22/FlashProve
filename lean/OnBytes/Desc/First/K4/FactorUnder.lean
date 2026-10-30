-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/FactorUnder.lean: THE FACTOR THAT EVERY LATER LEDGER HOLDS UNDER A SLOT IS THE
ONE WITH WHICH THE VALUE WAS LAID. Three statements with their proofs. The twin, for the array of
factors mf, of OnBytes/Desc/First/K4/ShownUnder.lean, which treats the array of shown values vp.

  `hideRun_factor`: a run of values laid with the factor f: every later ledger holds f under each
    of its slots.
  `tsc_cl_factor`: the claimed sum that a token sumcheck was sent is laid with the factor 1.
  `stack_factor`: the batched sumcheck's end values are laid with the challenge of the round in the
    further variable, `(stackY lamS t).2.2`.

Limits. One direction: from a return, from a ledger with arrays of the right sizes. Words alone:
what a factor is for is not said.
-/
import OnBytes.Desc.First.K4.ShownUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.P1 (tscIn_heard)

/-- The factor with which a run of values was laid is held by every later ledger. -/
theorem hideRun_factor {F G H : Fork} {first : Nat} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) (hL : Fo.Later G H) (i : Nat) (hi : i < v.size) :
    H.mf.getD (first + i) zeroE = f := by
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first v f hF h
  have k := hin i hi
  rw [(hL.keep (first + i) k.2.2.1).2.2, k.2.2.2.2]

/-- **A token sumcheck's claimed sum is laid with the factor 1.** -/
theorem tsc_cl_factor {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : Sized F) (h : Fl.tscIn P lt n dY F t = some (o, G, u)) (Hl : Fork)
    (hL : Fo.Later G Hl) : Hl.mf.getD o.sCl zeroE = oneE := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hsCl, _, _, v, G0, hG0, _, _, _, _, hG⟩ := tscIn_heard h
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  obtain ⟨_, hS0, _, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork) := hS0
  have l2 : Fo.Later G0
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) :=
    ⟨by show G0.next ≤ G0.next + 1 + 2 * (P.toList.take lt).length + dY + n; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  have l3 := Fo.hideRun_later hS0' hG
  have q := hideRun_factor hF' hG0 ((l2.trans l3).trans hL) 0 Nat.zero_lt_one
  rw [Nat.add_zero] at q
  rw [hsCl, q]

/-- **The batched sumcheck's end values are laid with the further variable's challenge.** -/
theorem stack_factor {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (hF : Sized F) (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    ∀ Hl : Fork, Fo.Later G Hl → ∀ i, i < 2 + (1 + P.y.LamM) + NCLp →
      Hl.mf.getD (S.sA0 + i) zeroE = (stackY lamS t).2.2 := by
  obtain ⟨_, _, _, _, _, vals, G1, _, hs, hG1, hG⟩ := stack_heard h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } :
      Fork) := hF
  obtain ⟨_, hS1, _, _⟩ := hideRun_ok _ G1 _ _ _ hF' hG1
  have l2 := Fo.hideRun_later hS1 hG
  intro Hl hL i hi
  exact hideRun_factor hF' hG1 (l2.trans hL) i (by rw [hs]; exact hi)

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hideRun_factor
#print axioms OnBytes.Desc.First.K4.tsc_cl_factor
#print axioms OnBytes.Desc.First.K4.stack_factor
