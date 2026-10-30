-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/FirstOpensUp.lean: THE PREMISE `up` OF `firstOpens_at_last`
(Johnson/Desc/K12/Coin/FirstOpensAtLast.lean), CUT INTO WHAT IT RESTS ON: along D.ts the places
(sending chain; number there) rise strictly, FROM THREE FACTS ON THE RECORD's BOOK.
  `ts_rise`        D.ts rises strictly: PAID: it is a `Fmt.listOf` (`made_of`, `Fmt.listOf_incr`)
  `plOf_omega`, `plOf_other`   `plOf` at Omega's tree's place, and at every other
  `up_of_numbers`  **a rising list of places of a book, Omega's tree's place last among them, each
                   other tree's number its place: the places `plOf` rise strictly**
  `up_at`          **the premise `up`**, from these three facts at the record's book
THE THREE, NONE PAID HERE. `hω`: Omega has a place in the book, in the tree at zω. `last`: no place of
D.ts lies behind zω (a law in other files on K14's second part: Omega's place is the old number of
trees). `num`: at every other place z of D.ts the tree's number is z: THAT A TREE's NUMBER IN THE BOOK
IS ITS PLACE IN ITS CHAIN's ORDER OF SENDING, for a chain that counts from 0 (a law in other files
on a book that is numbered; that the first chain's book is so along the walk is nobody's yet).
Limits. A rule under letters. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.FirstOpensSets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Plain)

/-- D.ts rises strictly. -/
theorem ts_rise {π : P12} {t : T12} {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group}
    {Ly : GroupLayout} {D : Plain} (hF : Fixes π t a rest G0 Ly D) : D.ts.Pairwise (· < ·) := by
  rw [(H2K.First.made_of _ _ _ _ _ (hF.2.2.2 { group := 0 })).ts]
  exact Fmt.listOf_incr _

theorem plOf_omega {B : TreeBook} {ω zω : ℕ} (hω : (B.place[ω]?).map (·.1) = some zω) :
    (plOf B ω zω).1 = 1 := by
  unfold plOf
  rw [hω]
  simp

theorem plOf_other {B : TreeBook} {ω zω z : ℕ} (hω : (B.place[ω]?).map (·.1) = some zω)
    (hz : z ≠ zω) : plOf B ω z = (0, ((B.trees[z]?).map (·.number)).getD 0) := by
  unfold plOf
  rw [hω, if_neg (fun e => hz (Option.some.inj e).symm)]

/-- **The places rise.** -/
theorem up_of_numbers (B : TreeBook) (ω zω : ℕ) (hω : (B.place[ω]?).map (·.1) = some zω)
    (ts : List ℕ) (hts : ts.Pairwise (· < ·)) (last : ∀ z ∈ ts, z ≤ zω)
    (num : ∀ z ∈ ts, z ≠ zω → ((B.trees[z]?).map (·.number)).getD 0 = z) :
    (ts.map (plOf B ω)).Pairwise Before := by
  refine List.pairwise_map.2 (hts.imp_of_mem fun {z z'} hz hz' hlt => ?_)
  have h1 : z ≠ zω := by
    have := last z' hz'
    omega
  rw [before_iff, plOf_other hω h1, num z hz h1]
  by_cases h2 : z' = zω
  · subst h2
    exact Or.inl (by rw [plOf_omega hω]; exact Nat.zero_lt_one)
  · rw [plOf_other hω h2, num z' hz' h2]
    exact Or.inr ⟨rfl, hlt⟩

/-- **The premise `up`.** -/
theorem up_at (π : P12) (t : T12) (ω zω : ℕ) (hω : (t.book.place[ω]?).map (·.1) = some zω)
    (last : ∀ s rest G0 Ly D, Fixes π t s rest G0 Ly D → ∀ z ∈ D.ts, z ≤ zω)
    (num : ∀ s rest G0 Ly D, Fixes π t s rest G0 Ly D → ∀ z ∈ D.ts, z ≠ zω →
      ((t.book.trees[z]?).map (·.number)).getD 0 = z) :
    ∀ s rest G0 Ly D, Fixes π t s rest G0 Ly D →
      (D.ts.map (plOf t.book ω)).Pairwise Before :=
  fun s rest G0 Ly D hF =>
    up_of_numbers t.book ω zω hω D.ts (ts_rise hF) (last s rest G0 Ly D hF) (num s rest G0 Ly D hF)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.ts_rise
#print axioms VerifiableInference.Desc.K12.Coin.up_of_numbers
#print axioms VerifiableInference.Desc.K12.Coin.up_at
