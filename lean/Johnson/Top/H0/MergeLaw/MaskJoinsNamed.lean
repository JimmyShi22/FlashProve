-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskJoinsNamed.lean: three theorems of MaskJoins.lean with their conclusion
under its own name, `MaskSeatAt` (Johnson/Desc/Kinds/Law/MaskRowsOne.lean). Three theorems, each one
call.

Main names:
  `maskSeatAt_of_test`: an accept of `maskAtB own xs R s` with xs ∈ N.sent 24 0 and arr xs.1 xs.2 =
    n gives `MaskSeatAt arr N n R s`. (Not to be mistaken for maskSeatAt_of_tests,
    Johnson/Desc/Kinds/Law/MaskSeatOfTests.lean [not in this library], which goes from seven tests.)
  `maskSeatAt_reached`: the same at the unmarked states in front of a sub-protocol that meet Rch k
    and the table's condition.
  `maskSeatAt_of_front`: the same from `MergeFront` at these states, at the member's seat.

Limits. MaskJoins.lean's. That the condition written out there is the body of `MaskSeatAt` is held
here by Lean: the three proofs are that file's theorems, taken as they stand. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskJoins
import Johnson.Desc.Kinds.Law.MaskRowsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds.Head.Law (MaskSeatAt)

/-- The state holds the mask row's seat, from an accept of the test. -/
theorem maskSeatAt_of_test (arr : ℕ → ℕ → ℕ) (N : Numbers) {own : List (ℕ × ℕ)} {xs : ℕ × ℕ}
    {R n : ℕ} {s : S} (h : maskAtB own xs R s = true) (hs : xs ∈ N.sent 24 0)
    (hn : arr xs.1 xs.2 = n) : MaskSeatAt arr N n R s :=
  maskSeat_of_test arr N h hs hn

/-- The same at the states in front of a sub-protocol. -/
theorem maskSeatAt_reached {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (arr : ℕ → ℕ → ℕ) (N : Numbers) (own : List (ℕ × ℕ)) (xs : ℕ × ℕ)
    (R n : ℕ) (hs : xs ∈ N.sent 24 0) (hn : arr xs.1 xs.2 = n)
    (hmask : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → a.1.failed = none → maskAtB own xs R a.1 = true) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MaskSeatAt arr N n R a.1 :=
  maskSeat_reached Rch Nn Mg links ps k arr N own xs R n hs hn hmask

/-- The same from `MergeFront` at these states. -/
theorem maskSeatAt_of_front {Pp W : Type} {Fr : Sound.Frame}
    (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop) (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart)
    (ps : List Place) (k : ℕ) (arr : ℕ → ℕ → ℕ) (N : Numbers) (own : List (ℕ × ℕ))
    (xM : Sound.Mem) (R ni n : ℕ) (hs : Sound.seatOf xM ∈ N.sent 24 0)
    (hn : arr (Sound.seatOf xM).1 (Sound.seatOf xM).2 = n)
    (hFr : ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MergeFront own xM R ni a.1) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) k a →
      Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none → MaskSeatAt arr N n R a.1 :=
  maskSeat_of_front Rch Nn Mg links ps k arr N own xM R ni n hs hn hFr

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeatAt_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeatAt_reached
#print axioms VerifiableInference.Desc.First.MergeLaw.maskSeatAt_of_front
