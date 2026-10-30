-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkAsksWork.lean: where the written link over letters accepts, the test of work of
every written round of its chain has passed.

The reduction of a whole file (`reductionOfWholeFile`) is the key file's and the proof file's protocol. The
entry file's protocol is no such reduction: it is
a link. `linkProtocolOfRoundData` (OnBytes/Flat/LinkSib.lean) is the written link over letters: a kit C, rounds' data
ds, a depth a, stored openings xs, a decision dec. Its verifier asks `passSL` at its one chain in
front of the decision (`skeletonOverBothExternalStrings`, OnBytes/TypedOracleCompiler/Run/PlanQX.lean). Here that is said, and written out
round by round. One definition, statements and proofs.

Main names (namespace `OnBytes.Flat.Work`):
  `workTestsL C ds τ`: for each written round of the chain, in order: its data, and whether its
    test of work passes at the transcript τ (`GChal.pass`, Iop/Grind.lean: every bit of work in the
    round's typed verifier message is 0; so a round without a bit of work passes).
  `passSL_iff`: `passSL` at the chain says yes exactly where every entry of `workTestsL` does.
  `link_passes`: where `linkProtocolOfRoundData C ds a xs dec` accepts, `passSL` holds at its chain.
  `link_asks_work`: and so every entry of `workTestsL` says yes.
Limits: the statements are on the typed protocol `linkProtocolOfRoundData` at a typed transcript, at every decision
dec. The bits are bits of a typed verifier message: no hash function, no bytes and no nonce occur.
That a verifier on files is that protocol compiled, that its yes gives such a transcript, and that
an entry file's protocol in use is `linkProtocolOfRoundData` at some letters is not said here. At the empty list of
rounds nothing is said. That ds are the rounds which a plan declares is not said. Nothing on
soundness or on counts.

-/
import OnBytes.Flat.LinkSib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat.Work
open Iop TypedOracleCompiler.Run.PQ
open _root_.Run.PQ (View SgX CK XO)

/-- For each written round: its data, and whether its test of work passes. -/
def workTestsL (C : CK) : (ds : List RD) → Iop.Tr (uL C ds) → List (RD × Bool)
  | [], _ => []
  | d :: ds, (_, c, τ) => (d, GChal.pass (b := d.entry.work) c) :: workTestsL C ds τ

/-- The chain's test of work, round by round. -/
theorem passSL_iff (C : CK) : ∀ (ds : List RD) (τ : Iop.Tr (uL C ds)),
    passSL C ds (rhoSL C ds τ) = true ↔ ∀ x ∈ workTestsL C ds τ, x.2 = true
  | [], _ => ⟨fun _ _ hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | d :: ds, (_, c, τ) => by
    show (GChal.pass (b := d.entry.work) c && passSL C ds (rhoSL C ds τ)) = true ↔
      ∀ x ∈ (d, GChal.pass (b := d.entry.work) c) :: workTestsL C ds τ, x.2 = true
    rw [Bool.and_eq_true_iff, passSL_iff C ds τ, List.forall_mem_cons]

variable {Y : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : Y → View → Bool) (x : Y)
  (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : Tr (linkProtocolOfRoundData C ds a xs dec).shape)

/-- Where the written link accepts, its chain's test of work has passed. -/
theorem link_passes (h : (linkProtocolOfRoundData C ds a xs dec).accept x y τ = true) :
    passSL C ds (rhoSL C ds τ.2.2) = true := by
  have h' : (passSL C ds (rhoSL C ds τ.2.2) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ.2.2)) &&
      symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ.2.2)) y &&
      dec x (viewX C ds a xs y τ.2.2)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1.1.1

/-- Where the written link accepts, every written round's test of work has passed. -/
theorem link_asks_work (h : (linkProtocolOfRoundData C ds a xs dec).accept x y τ = true) :
    ∀ r ∈ workTestsL C ds τ.2.2, r.2 = true :=
  (passSL_iff C ds τ.2.2).1 (link_passes C ds a xs dec x y τ h)

end OnBytes.Flat.Work

#print axioms OnBytes.Flat.Work.passSL_iff
#print axioms OnBytes.Flat.Work.link_passes
#print axioms OnBytes.Flat.Work.link_asks_work
