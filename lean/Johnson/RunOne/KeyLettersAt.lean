-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyLettersAt.lean. AT THE READINGS' MEMBER (KeyOneReading.lean: BaseSt: the sample off the message's own record, by its number): WHAT PinsStay ASKS OF THE LETTER sm, AND WHERE IT IS THEN FREE.
  SmGroups        sm does not read a message's list «groups» (which a joining turns). Beside SmReads (the ledger).
  smAt_congr      PROVED: statements with one codes and one record at o give one sample at o
  pinsStay_h₂     PROVED: two records of the shared chain over one handed state, with one codes, whose messages' samples are alike at the plan's three numbers: PinsStay at every list. FOR ROWS WITHOUT A SENDING (2.3 · 2.6 · 2.8 …).
Nothing on soundness.
-/
import Johnson.RunOne.KeyOneReading
import Johnson.Desc.Key.KeyLetters

set_option autoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.Key

variable {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec)

/-- The letter sm does not read a message's list of the groups that it belongs to. -/
def BaseSt.SmGroups : Prop := ∀ (c : Codes) (o : Nat) (x : OnBytes.Oracle) g, T.sm c o { x with groups := g } = T.sm c o x

theorem smAt_congr (St St' : Statement) (o : Nat) (hc : St'.codes = St.codes) (ho : (St'.oracles[o]?).bind (T.sm St.codes o) = (St.oracles[o]?).bind (T.sm St.codes o)) :
    T.smAt St' o = T.smAt St o := by
  unfold BaseSt.smAt
  rw [hc]
  exact ho

/-- **The shared chain, where no message comes.** -/
theorem pinsStay_h₂ (at_ : Where) (l : List Nat) (z : P₂) (d d' : St₂) (h : ∀ o, T.smAt d'.st o = T.smAt d.st o) : PinsStay T.h₂ at_ l (z, d) (z, d') :=
  ⟨fun k _ => by
    simp only [BaseSt.h₂]
    split
    · rfl
    · cases orc₂ (T.arr (at_ k).1 (at_ k).2) with
      | none => rfl
      | some o => exact h o, rfl⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.smAt_congr
#print axioms Johnson.RunOne.KeyRows23.pinsStay_h₂
