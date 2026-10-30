-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/FirstOpensOf.lean: THE PROMISE `FirstOpens` OF THE PROXIMITY TEST's LAW
(Johnson/Desc/K12/Coin/Sheet.lean) AT A PLACE ON THE LAST CHAIN OF A DESCRIPTION, FROM THREE
NAMED PREMISES: one call of `firstOpens_round` (Johnson/Desc/Sound/FirstOpensOfSets.lean).

What is paid here. That the plain data's openings are one declared round's (`cut_of_ok`, from the
block's own test on the plan; `made_of`); that this round is a round of the block (`cut_mem`), so of
the description's last chain where the block is seated there (`seated`); that its openings' places
rise strictly (the description's tests on the plan: `F.treeSharingOk`); that a taken tree's number is below
F.t₁ + F.t₂ (`F.data`'s yes).
  `cut_mem`        a round of the first switch's cut is a round of the block
  `firstOpens_of`  **FirstOpens π (numAt F.t₁ F.t₂ 2) (fun z => wholeNo F.t₁ F.t₂ (pl z)) base t**
THE NAMED PREMISES. `taken`: every opening of the first switch's cut is of a tree that is taken over (a
fact on the place's numbers). `up`: along D.ts the places pl z rise strictly (a fact on the book's
make). `sets`: the openings' places and the places pl z, z in D.ts, are the same as sets (from the
last chain's test on taken sources, and the seat's way in).
Limits. The three premises are not paid; that they hold together at the release's plan and a record
that runs has not been tested. pl is a letter, fixed for all records: that pl z is the place of the
tree at z in the record's book is inside `up` and `sets`. Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.Law.FirstCutLaw
import Johnson.Desc.K12.Law.FirstOkLaw
import Johnson.Desc.Sound.FirstOpensOfSets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK (cutS laidS laidOf)

/-- A round of the first switch's cut is a round of the block. -/
theorem cut_mem (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (k : ℕ)
    (d : Fmt.DeclaredRound) (hd : d ∈ cutS (laidS π) k) :
    d ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds := by
  rw [H2K.Sw.k12_rounds _ _ hp]
  unfold cutS laidS at hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
  exact List.mem_map.2
    ⟨x, List.mem_of_mem_drop (List.mem_of_mem_drop (List.mem_of_mem_take hx)), rfl⟩

/-- **The promise, at a place on the last chain.** -/
theorem firstOpens_of {Xi : Type} {F : FileDescription Xi} {file : String} {D₀ : WholeD}
    (h : F.data file = .ok D₀) (hk : F.treeSharingOk = true) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (seated : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, r ∈ F.roundsDeclaredByBlocks.2.2)
    (pl : ℕ → ℕ × ℕ) (base : ℕ) (hb : F.t₁ + F.t₂ ≤ base) (t : T12)
    (taken : ∀ a rest, π.nums.stages = a :: rest →
      ∀ o ∈ H2K.First.opensOf π a.k, ∃ c n, o.2 = .taken c n)
    (up : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D → (D.ts.map pl).Pairwise Before)
    (sets : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D →
      ∀ x, x ∈ (D.opens.map fun o => BookPlan.treePlace 2 o.2) ↔ x ∈ D.ts.map pl) :
    FirstOpens π (VerifiableInference.Desc.numAt F.t₁ F.t₂ 2)
      (fun z => Three.wholeNo F.t₁ F.t₂ (pl z)) base t := by
  intro a rest G0 Ly D hF
  have hs := hF.1
  have hD := hF.2.2.2 { group := 0 }
  have hO : D.opens = H2K.First.opensOf π a.k := (H2K.First.made_of _ _ _ _ _ hD).opens
  obtain ⟨dS, dC, hc, -, -, -, -, hC⟩ :=
    H2K.First.cut_of_ok π a rest hs (H2K.JointK.cut_of_planOk π hp)
  have hm : dC ∈ F.roundsDeclaredByBlocks.2.2 := seated dC (cut_mem π hp a.k dC (by rw [hc]; simp))
  have key := firstOpens_round h hk dC hm D.ts pl (up a rest G0 Ly D hF)
    (by rw [hC]; exact taken a rest hs)
    (by rw [hC, ← hO]; exact sets a rest G0 Ly D hF) base hb
  rw [hC, ← hO] at key
  exact key

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.cut_mem
#print axioms VerifiableInference.Desc.K12.Coin.firstOpens_of
