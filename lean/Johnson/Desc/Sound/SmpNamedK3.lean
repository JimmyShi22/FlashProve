-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SmpNamedK3.lean: THE LOOKUP's TWO READERS OF SAMPLES, NAMED: THEY ARE THE TABLE's
READER AT THE LOOKUP's OWN LISTS AND SEATS. Definitions and theorems, proved.

The laws of the kind "lookup" take, for each place x, a reader of the samples of x's list of
messages: of the calls' list (`sigListCalls`, signature `attSg`,
Johnson/Desc/First/Look/K3CallerAtt.lean) and of the digits' list (`digList`, signature `digSg`,
K3Caller.lean). Both were letters.
  `smpCalls seats D rad seat x s i`, `smpDigits …`: `smp1At` (SmpNamed.lean) at D's codes, the
    record's statement, the list's entry number i, and the seat that seat gives link x.link's
    message number i (false: the calls; true: the digits).
  `smpCalls_same`, `smpDigits_same` (proved): two records with one statement have the same samples.
  `smpCalls_is`, `smpDigits_is` (proved, by the make): each IS `smpNamed D.codes seats` at the
    sending made of that list and these seats.
Limits. seats, rad and seat are letters. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Desc.First.Look.K3Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open Johnson.Pack
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (Sent sigListCalls digList attSg digSg)

/-- The calls' reader. -/
def smpCalls (seats : List (ℕ × ℕ)) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) (x : First.Look.Place) (s : S)
    (i : Fin (sigListCalls D rad x.link).length) : Option ((attSg x D rad).om i).Smp :=
  smp1At D.codes seats s.st ((sigListCalls D rad x.link).get i) (seat x.link false i.1)

/-- The digits' reader. -/
def smpDigits (seats : List (ℕ × ℕ)) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) (x : First.Look.Place) (s : S)
    (i : Fin (digList x D rad).length) : Option ((digSg x D rad).om i).Smp :=
  smp1At D.codes seats s.st ((digList x D rad).get i) (seat x.link true i.1)

theorem smpCalls_same (seats : List (ℕ × ℕ)) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) (x : First.Look.Place) (s s' : S) (h : s'.st = s.st) :
    smpCalls seats D rad seat x s' = smpCalls seats D rad seat x s := by
  funext i
  unfold smpCalls
  rw [h]

theorem smpDigits_same (seats : List (ℕ × ℕ)) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) (x : First.Look.Place) (s s' : S) (h : s'.st = s.st) :
    smpDigits seats D rad seat x s' = smpDigits seats D rad seat x s := by
  funext i
  unfold smpDigits
  rw [h]

/-- **The calls' reader is the table's**, at the sending made of the calls' list and its seats. -/
theorem smpCalls_is {P : Type} (seats : List (ℕ × ℕ)) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) (x : First.Look.Place) (z : P) (s : S)
    (i : Fin (sigListCalls D rad x.link).length) :
    smpCalls seats D rad seat x s i =
      smpNamed D.codes seats (z, s) ⟨sigListCalls D rad x.link, fun k => seat x.link false k.1⟩ i :=
  rfl

theorem smpDigits_is {P : Type} (seats : List (ℕ × ℕ)) (D : Sent) (rad : OnBytes.OracleShape → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) (x : First.Look.Place) (z : P) (s : S)
    (i : Fin (digList x D rad).length) :
    smpDigits seats D rad seat x s i =
      smpNamed D.codes seats (z, s) ⟨digList x D rad, fun k => seat x.link true k.1⟩ i :=
  rfl

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.smpCalls_same
#print axioms VerifiableInference.Desc.Sound.smpDigits_same
#print axioms VerifiableInference.Desc.Sound.smpCalls_is
#print axioms VerifiableInference.Desc.Sound.smpDigits_is
