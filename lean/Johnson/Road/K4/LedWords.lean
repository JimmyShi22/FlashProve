-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LedWords.lean: the two public constants of each norm, as the verifier's claims on
the norms' ledgers have them (epsOf, twoM), read as the library's: the clauses eps and two of
LedDict (Johnson/Road/K4/LedPort.lean) and of SlotTies (Johnson/Road/K4/FrontDictOf.lean), from the
record NormWords (Johnson/Road/FormsKeysIdnW.lean).

  `eps_of_words`, `two_of_words`: the two clauses. They are two steps inside the proof of
    ledger_line, said on their own.
normWords_sclOf gives NormWords under the table of scales that sclOf makes of the
verifier's scale file; normWords_of_hear (Johnson/Road/K4/NormWordsOfHear.lean) at a hearing.
Limits. NormWords and how numerals are read are premises. Identities on public numbers: nothing on a
draw, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysIdnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env twoM epsOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim npOf)

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K} {v : Env} {D : Dim}

/-- The clause eps. -/
theorem eps_of_words (hρ : Numerals ρ) (N : NormWords v D) :
    ∀ i, i < D.nNu → ρ.val (epsOf v.y i) = ((npOf D i).eps : K) := by
  intro i hi
  unfold epsOf
  rw [hρ.ofNat, ← N.eps i hi]
  norm_cast

/-- The clause two. -/
theorem two_of_words (hρ : Numerals ρ) (N : NormWords v D) (W : World K) :
    ∀ i, i < D.nNu → (twoM v i).value ρ W = 2 ^ ((npOf D i).M + 1) := by
  intro i hi
  unfold twoM
  rw [Aff.value_ofConst, hρ.pw, N.M i hi]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.eps_of_words
#print axioms OnBytes.Road.K4.two_of_words
