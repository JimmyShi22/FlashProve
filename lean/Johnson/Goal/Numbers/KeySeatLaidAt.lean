-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/KeySeatLaidAt.lean: THE KEY FILE's HALF OF THE NAMED PREMISE `SeatLaid` IS PAID
BY THE KEY FILE's PIECE (`KeySeatLaid`, Johnson/Goal/Numbers/PlanWrittenMore.lean), at every o: and
so, in scope, THE LAID DATA ARE THE WRITTEN DATA.

Main names.
  descOrAt o d Z: the description that the key file's piece is laid of, at the public files Z: what
    `descAt X Z.lay fixedDigest` returns at the X that `publicOfO o` returns; d where either
    refuses.
  laidYes o Z: the two in a row, `publicOfO o` and then `Key.keyDataAndDecisionAtFixedDigest`, return a value.
  keySeatLaid_of_laidFixed: KeySeatLaid (descOrAt o d) (laidYes o), at every o and d.
  keyWrittenAt_of_laidFixed: KeyWrittenAt (descOrAt o d) (laidYes o).
  laid_data_written: in scope, where the two in a row return (D, r): D = writtenKFull.

Limits. d is a letter: it is read nowhere under the yes. Scope is not spent by the first; the second
and third spend it through `seat_in_scope_key`. That the yes holds at any files is not shown here.
"AT EVERY o" IS WORTH "AT EVERY o AT WHICH THE PUBLIC PART IS ACCEPTED". In scope `publicOfO o`
returns only at an o whose digests of the four public tables are the format's: scope fixes these
words as plain numbers, and Johnson/Desc/Ok/PlanWritten/PublicAt.lean holds o's own digests against
them. At every other o a law here that has the yes among its premises holds of nothing.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.PinnedAtO
import Johnson.Goal.Numbers.PlanWrittenMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes VerifiableInference.Desc

/-- The description that the key file's piece is laid of, at the public files Z. -/
def descOrAt (o : Nat → ByteArray → ByteArray) (d : FileDescription Key.Xi) (Z : VerifierAndGoals.PublicFiles) :
    FileDescription Key.Xi :=
  match (publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.descAt X Z.lay Key.fixedDigest with
  | .ok F => F
  | .error _ => d

/-- The key file's piece is laid at the public files Z. -/
def laidYes (o : Nat → ByteArray → ByteArray) (Z : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ D r, ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) = .ok (D, r)

/-- Under the yes: what `descOrAt` is. -/
theorem descOrAt_of_laid {o : Nat → ByteArray → ByteArray} (d : FileDescription Key.Xi) {Z : VerifierAndGoals.PublicFiles}
    {D : Maker.WholeD} {r : Key.KeyRun}
    (h : ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) =
      .ok (D, r)) :
    seatPinnedKey Z.pol (descOrAt o d Z) = true ∧ (descOrAt o d Z).data "key file" = .ok D ∧
      r = ((descOrAt o d Z).pull Key.keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨X, F, hX, hF, hp, hd, hr⟩ := Key.laid_bind_seat h
  have e : descOrAt o d Z = F := by
    unfold descOrAt
    rw [hX]
    show (match Key.descAt X Z.lay Key.fixedDigest with | .ok F => F | .error _ => d) = F
    rw [hF]
  rw [e]
  exact ⟨hp, hd, hr⟩

/-- **The key file's half of `SeatLaid` is paid by the key file's piece.** -/
theorem keySeatLaid_of_laidFixed (o : Nat → ByteArray → ByteArray) (d : FileDescription Key.Xi) :
    KeySeatLaid (descOrAt o d) (laidYes o) :=
  fun _ _ ⟨_, _, h⟩ => (descOrAt_of_laid d h).1

/-- So the description is made at the written plan values. -/
theorem keyWrittenAt_of_laidFixed (o : Nat → ByteArray → ByteArray) (d : FileDescription Key.Xi) :
    KeyWrittenAt (descOrAt o d) (laidYes o) :=
  keyWrittenAt_of_seat (keySeatLaid_of_laidFixed o d)

/-- **In scope the laid data are the written data.** -/
theorem laid_data_written {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles} {D : Maker.WholeD}
    {r : Key.KeyRun} (hZ : VerifierAndGoals.InScope Z = true)
    (h : ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) =
      .ok (D, r)) : D = Johnson.G.writtenKFull := by
  obtain ⟨X, F, -, -, -, -, -⟩ := Key.laid_bind_seat h
  have h1 := keyWrittenAt_of_laidFixed o F Z hZ ⟨D, r, h⟩
  exact Except.ok.inj ((descOrAt_of_laid F h).2.1.symm.trans h1)

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.keySeatLaid_of_laidFixed
#print axioms VerifiableInference.PlanWritten.keyWrittenAt_of_laidFixed
#print axioms VerifiableInference.PlanWritten.laid_data_written
