-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsK2.lean: K2.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM LooksK2.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksK2
import Johnson.Desc.First.Link.Law.LooksFrame
import Johnson.Desc.First.Link.Law.SlotsFrame
import Johnson.Top.H0.Tw.K2C.ForkKept
import Johnson.Top.H0.Tw.K2C.HeadLedger
import Johnson.Top.H0.Tw.K2C.HeadNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2

theorem k2_keepsS (nsOf : ℕ → ℕ × ℕ) {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {s' : S}
    (h : decideWith snd p s rs gs = .ok s') : KeepsSlots nsOf s s' :=
  keeps_sameS nsOf (fork_kept h) (by rw [k2_link_kept h])

/-- **K2: the code switch.** -/
theorem k2_stepsS (nsOf : ℕ → ℕ × ℕ) (p : P2) :
    (codeSwitchKind p : Block S Unit).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  exact k2_keepsS nsOf (show decideWith _ p s rs gs = .ok s' from h)

end VerifiableInference.Desc.LinkJoin
