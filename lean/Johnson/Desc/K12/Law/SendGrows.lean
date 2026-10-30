-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/SendGrows.lean: a sending on the plain ground only grows the statement.

Source: these two lemmas are not K12's files' own. They are copied from lines 21 to 74 of the file
K14Grows.lean, which is not in this library and was written with the plain ground and `Grows`
(Johnson/Desc/Grows.lean, Johnson/Desc/GrowsGround.lean). One name differs from that text: the
namespace, which is `Desc.Plain` in this library. They stand here because
Johnson/Desc/K12/Law/GrowsK.lean calls the second. `obind_ok` (a bind of options that gives a value)
is the library's: Johnson/Desc/K14/Keeps.lean.



  `sampleLoop_grows`: message by message, each is admitted.
  `sendP_grows`: where `sendP groundG` returns a state, its statement has grown out of the one
    handed in.
Limits: `Grows` says nothing on rows, pads or ledgers. No soundness is claimed, and nothing is said
on hiding.

-/
import Johnson.Desc.Ground.Calls
import Johnson.Desc.GrowsGround
import Johnson.Desc.K14.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Plain
open OnBytes OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-- Message by message: each is admitted. -/
theorem sampleLoop_grows (p : GPar) (codes : Codes) (seeds : List SampleSeed)
    (l : List (Nat × OracleShape)) : ∀ (ys : List E) (d : DState L) (y : DState L × List E),
    sampleLoop groundG p codes seeds l ys d = some y → Grows d.st y.1.st := by
  induction l with
  | nil =>
    intro ys d y h
    simp only [sampleLoop, Option.some.injEq] at h
    subst h
    exact Grows.refl _
  | cons a l ih =>
    intro ys d y h
    obtain ⟨o, s⟩ := a
    cases hr : rowsFor codes s o seeds (List.range s.answers) ys #[] with
    | none => simp [sampleLoop, hr] at h
    | some x =>
      obtain ⟨rows, ys'⟩ := x
      cases ha : (groundG (L := L)).admit p d o rows with
      | none => simp [sampleLoop, hr, ha] at h
      | some d₁ =>
        simp only [sampleLoop, hr, ha] at h
        exact (admitP_grows d d₁ o rows ha).trans (ih _ _ _ h)

/-- A sending: the messages are received; those with answers are admitted. -/
theorem sendP_grows (p : GPar) (own : Bool) (d : DState L) (sent : Array OracleNotice)
    (r₁ r₂ : Fmt.RoundView) (y : Array Nat × List E × List E × Nat × DState L)
    (h : sendP groundG p own d sent r₁ r₂ = some y) : Grows d.st y.2.2.2.2.st := by
  unfold sendP at h
  obtain ⟨⟨ids, d₁⟩, h1, h⟩ := obind_ok h
  dsimp only at h
  obtain ⟨shapes, _, h⟩ := obind_ok h
  obtain ⟨seeds, _, h⟩ := obind_ok h
  obtain ⟨an, _, h⟩ := obind_ok h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := obind_ok h
    dsimp only at h
    split at h
    · cases h
      exact (recvP_grows p.firstTree d d₁ sent ids h1).trans (sampleLoop_grows _ _ _ _ _ _ _ h2)
    · cases h
  · cases h

end Desc.Plain
