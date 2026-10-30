-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/StopsNone.lean: kind K14: no part of the kind's sides of the
honest prover in the shared chain has a test that can stop it.

A part of the honest prover (Part, Honest/Frame.lean) carries two tests, "bad" and "hid". A test
that returns "some message" stops the part. This file proves that both tests of every part of the
kind's sides return "none" at all arguments. The sides are the kind's own (proverSidesOfSharedRounds,
Honest/K14/Parts.lean: three, or four where the shape splits) and the two sendings' (proverSidesOfSharedSendings,
Honest/K14/Sendings.lean): five or six in all.

  lift_stops_none         a part both of whose tests return none at all arguments keeps that when it
                          is placed in a wider input and state by Part.lift
  halves_stops_none       at the kind's own sides, at any public data
  sendHalves_stops_none   at the two sendings' sides, at any public data
  six_stops_none          at the two lists joined
  sixOf_stops_none        at whatever list sixOf (Honest/K14/Six.lean) returns

The conclusion is AtPublicFiles.Stops.NoStop at the list, with AtPublicFiles.Stops.Quiet written out (E2E/NoStop.lean,
which this file does not import): the clause on "bad" first, and the arguments in that file's order.

Why it holds. The parts are quietPart and scalarsPart (Honest/ForKinds.lean) and sendingPart
(Honest/K14/Sendings.lean), each placed by Part.lift. Part.lift keeps the first test, and its second
test is the part's own at what the reader "see" returns. The first test of all three parts is
written "none", and so is the second test of the first two.

Who uses it. The four statements on the kind's sides are general in the types of the index, of the
committer's random values, of the key and of the sides' own state, so they also serve a caller who
reads these sides through other readers; lift_stops_none is for a caller who places them once more.

Limits.
  * On the second test the statements say no more than the type does. In the shared chain the second
    test's first argument has the type Empty, so that clause holds of any part; and the frame never
    asks that test there (Face.sees, Honest/Frame.lean). The content is the clause on the first
    test.
  * A part that never stops can still return an error from a move. Nothing is said on what a part
    sends or on how a run ends.
  * Nothing is said of a side of another kind in the shared chain (its two proximity tests).
  * The kind's member in the second chain is not treated: no part is written for it.
  * The sendings have another text, as calls of the shared sending's part
    (Honest/K14/SendingsVia.lean). It is another term, and nothing is said of it here.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.Six

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)

/-- Placing a part by Part.lift keeps "both tests return none at all arguments". -/
theorem lift_stops_none {V V' W W' X Y : Type} (see : V → V') (wit : W → W') (get : X → Y)
    (set : X → Y → X) {p : Part V' W' Y}
    (h : (∀ f d, p.bad f d = none) ∧ ∀ u f d, p.hid u f d = none) :
    (∀ f d, (p.lift see wit get set).bad f d = none) ∧
      ∀ u f d, (p.lift see wit get set).hid u f d = none :=
  ⟨h.1, fun u => h.2 (see u)⟩

variable {W₀ Rc Ky X : Type}

/-- Both tests of each part of the kind's own sides return none at all arguments. -/
theorem halves_stops_none (A : Data) (weights : W₀ → Weights) :
    ∀ g ∈ (proverSidesOfSharedRounds A weights : List (Placed Empty (Common W₀ Rc Ky) X)), ∀ p ∈ g.parts,
      (∀ f d, p.bad f d = none) ∧ ∀ u f d, p.hid u f d = none := by
  intro g hg p hp
  change g ∈ [⟨place 1, [_]⟩, ⟨place 4, [_]⟩, ⟨place 7, [_]⟩] ++
    (if A.S.sharedSplitNeeded then [⟨place 8, [_]⟩] else []) at hg
  rcases List.mem_append.1 hg with h3 | h4
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl | rfl <;>
      (obtain rfl : p = _ := List.mem_singleton.1 hp
       exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩)
  · by_cases c : A.S.sharedSplitNeeded = true
    · rw [if_pos c] at h4
      obtain rfl : g = _ := List.mem_singleton.1 h4
      obtain rfl : p = _ := List.mem_singleton.1 hp
      exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · rw [if_neg c] at h4
      cases h4

/-- Both tests of the part of either sending's side return none at all arguments. The second clause
holds by the type: there is nothing to hand the second test. -/
theorem sendHalves_stops_none (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ∀ g ∈ (proverSidesOfSharedSendings A weights rand : List (Placed Empty (Common W₀ Rc Ky) X)), ∀ p ∈ g.parts,
      (∀ f d, p.bad f d = none) ∧ ∀ u f d, p.hid u f d = none := by
  intro g hg p hp
  change g ∈ [⟨sendPlace 2, [_]⟩, ⟨sendPlace 5, [_]⟩] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    (obtain rfl : p = _ := List.mem_singleton.1 hp
     exact ⟨fun _ _ => rfl, fun u _ _ => u.elim⟩)

/-- The two lists joined. -/
theorem six_stops_none (A : Data) (B : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ∀ g ∈ (proverSidesOfSharedRounds A weights ++ proverSidesOfSharedSendings B weights rand :
        List (Placed Empty (Common W₀ Rc Ky) X)), ∀ p ∈ g.parts,
      (∀ f d, p.bad f d = none) ∧ ∀ u f d, p.hid u f d = none :=
  fun g hg => (List.mem_append.1 hg).elim (halves_stops_none A weights g)
    (sendHalves_stops_none B weights rand g)

/-- **Whatever list sixOf returns.** It returns the two lists joined, or an error. -/
theorem sixOf_stops_none {S Cl : Type} (P : Desc.K14.P14) (bs : List (Block S Cl))
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    {hs : List (Placed Empty (Common W₀ Rc Ky) X)} (e : sixOf P bs weights rand = .ok hs) :
    ∀ g ∈ hs, ∀ p ∈ g.parts,
      (∀ f d, p.bad f d = none) ∧ ∀ u f d, p.hid u f d = none := by
  unfold sixOf at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact six_stops_none _ _ _ _

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.lift_stops_none
#print axioms ProofFile.Honest.K14.halves_stops_none
#print axioms ProofFile.Honest.K14.sendHalves_stops_none
#print axioms ProofFile.Honest.K14.six_stops_none
#print axioms ProofFile.Honest.K14.sixOf_stops_none
