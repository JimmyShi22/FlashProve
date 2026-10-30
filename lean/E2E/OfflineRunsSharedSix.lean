-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsSharedSix.lean: "every run returns" (Owed.runs,
Johnson/Desc/ProofFile/Honest/Owed.lean): WHAT ONE SUB-PROTOCOL OWES, BlockPlays
(E2E/OfflineRunsForm.lean: from a state of a given form, at challenges that its rounds can draw,
where nothing of it stops and the book has lent: play returns), AT THE SIX MEMBERS OF A SHARED CHAIN
AT WHICH THE LINEAR CLAIM (kind K14) HAS A HALF: the members 1, 2, 4, 5, 7, 8 of any list that
begins with the chain's front sub-protocol and the eight that the library makes of a plan P (FlatOf,
Johnson/Desc/K14/Honest/FlatForm.lean, with hb). General in the plan, the book, the list of halves
and THE FORM Pre: NOTHING OF THE FORM IS SPENT: the kind's six rows play at every stand.

  blockPlays_quiet | _split | _send   at one sub-protocol, from the kind's laws loc_moved,
                                      split_moved (Johnson/Desc/ProofFile/Honest/K14/Debts.lean),
                                      send_moved
                  (…/K14/SendingsPlay.lean)
  blockPlays_six  **at the six members**

What is not claimed. That any description's shared list has that form, or that a prover's list holds
the six halves. The members 0, 3 and 6, which have no half, and the members behind the eighth. That
a run returns. Nothing on completeness, soundness or hiding.
Terms. A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import E2E.OfflineRunsForm
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.K14.PaidAt
import Johnson.Desc.ProofFile.Honest.K14.Kit
import Johnson.Desc.K14.Honest.FlatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest (FlatOf Like)

variable {S Cl W₀ Rc Ky X : Type} {Bk : ProverCoinCounts}

/-- A member at which the kind sends nothing: "LIN point", "LOC", "LIN zeta". -/
theorem blockPlays_quiet (chain : Nat) (A : Data) (weights : W₀ → Weights) (b : Block S Cl)
    (d : Fmt.DeclaredRound) (hr : b.rounds = [d]) (ho : b.oracles = [[]]) (hd : d.items = [])
    (hop : d.opens = []) {hs : List (Placed Empty (Common W₀ Rc Ky) X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftK14 A weights quietPart] })
    (Pre : Mid (Common W₀ Rc Ky) X → Prop) :
    BlockPlays (Face.shared : Face Empty (Common W₀ Rc Ky) Ky) Bk chain hs b Pre := by
  intro k m ds l _ hfit _ hl
  obtain ⟨x, -, hp, -⟩ := loc_moved A weights b d hr ho hd hop hf hl m ds hfit
  exact ⟨_, hp⟩

/-- "SPLIT". -/
theorem blockPlays_split (chain : Nat) (A : Data) (weights : W₀ → Weights) (b : Block S Cl)
    (d : Fmt.DeclaredRound) (hr : b.rounds = [d]) (ho : b.oracles = [[]]) (hd : d.items = [.e])
    (hop : d.opens = []) (hst : d.stored = []) {hs : List (Placed Empty (Common W₀ Rc Ky) X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftK14 A weights (splitPart A)] })
    (Pre : Mid (Common W₀ Rc Ky) X → Prop) :
    BlockPlays (Face.shared : Face Empty (Common W₀ Rc Ky) Ky) Bk chain hs b Pre := by
  intro k m ds l _ hfit _ hl
  obtain ⟨x, c, -, -, hp, -⟩ := split_moved A weights b d hr ho hd hop hst hf hl m ds hfit
  exact ⟨_, hp⟩

/-- A sending. -/
theorem blockPlays_send {W : Type} (chain : Nat) (J : SendJob) (wit : W → Ask) (b : Block S Cl)
    (D : SendDeclared b J) {φ : Face Empty W Ky} {hs : List (Placed Empty W X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftSend wit (sendingPart J)] })
    (Pre : Mid W X → Prop) : BlockPlays φ Bk chain hs b Pre := by
  intro k m ds l _ hfit _ hl
  obtain ⟨d₀, d₁, os, hr, ho, f₀, f₁, o₀, s₀, o₁, s₁⟩ := D.rounds
  obtain ⟨x₀, x₁, c, -, -, hp, -⟩ :=
    send_moved J wit b d₀ d₁ os hr ho f₀ f₁ o₀ s₀ o₁ s₁ hf hl m ds hfit
  exact ⟨_, hp⟩

/-- **BlockPlays at the members 1, 2, 4, 5, 7, 8.** F, hb: the list begins with the front
sub-protocol and the plan's eight. hS, hA: the shape splits, at the plan and at the data. nd, hin:
the list of halves has no place twice, and holds the kind's four own halves at the data A and its
two sendings' halves at ⟨P, at'⟩. Pre: any form, one for each member. -/
theorem blockPlays_six {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (A : Data) (at' : Nat)
    (hS : P.S.sharedSplitNeeded = true) (hA : A.S.sharedSplitNeeded = true)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    {hs : List (Placed Empty (Common W₀ Rc Ky) X)} (nd : (hs.map (·.place)).Nodup)
    (hin : ∀ g ∈ (proverSidesOfSharedRounds A weights ++ proverSidesOfSharedSendings ⟨P, at'⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ hs)
    (chain : Nat) (Pre : Nat → Mid (Common W₀ Rc Ky) X → Prop) :
    ∀ j, j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 → ∀ b, xs[j]? = some b →
      BlockPlays (Face.shared : Face Empty (Common W₀ Rc Ky) Ky) Bk chain hs b (Pre j) := by
  obtain ⟨c0, c1, c2, r1, o1, r4, o4, r7, o7⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨c3, r8, o8⟩ := declares_split P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
  obtain ⟨p1, p4, p7, p8⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨dU, pU, dO, pO⟩ := send_declares P at' b1 b2 b3 b4 b5 b6 b7 b8 hb
  rw [halves_eq, sendHalves_eq, if_pos hA] at hin
  have found : ∀ g : Placed Empty (Common W₀ Rc Ky) X, g ∈ hs →
      (hs.find? fun h => h.place == g.place) = some g := fun g hg => find_of_mem hs g nd hg
  intro j hj b hx
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · have l := F.at1 hx
    refine blockPlays_quiet chain A weights b _ (l.rounds.trans r1) (l.oracles.trans o1) c0 rfl ?_ _
    rw [l.place.trans p1]
    exact found ⟨place 1, [liftK14 A weights quietPart]⟩ (hin _ (by simp))
  · have l := F.at2 hx
    refine blockPlays_send chain _ (witOf P weights rand) b
      (sendDeclared_like l.rounds l.oracles dU) ?_ _
    rw [l.place.trans pU]
    exact found ⟨sendPlace 2, [liftSend (witOf P weights rand) (sendingPart (jobU ⟨P, at'⟩))]⟩
      (hin _ (List.mem_append_right _ List.mem_cons_self))
  · have l := F.at4 hx
    refine blockPlays_quiet chain A weights b _ (l.rounds.trans r4) (l.oracles.trans o4) c1 rfl ?_ _
    rw [l.place.trans p4]
    exact found ⟨place 4, [liftK14 A weights quietPart]⟩ (hin _ (by simp))
  · have l := F.at5 hx
    refine blockPlays_send chain _ (witOf P weights rand) b
      (sendDeclared_like l.rounds l.oracles dO) ?_ _
    rw [l.place.trans pO]
    exact found ⟨sendPlace 5, [liftSend (witOf P weights rand) (sendingPart (jobOmega ⟨P, at'⟩))]⟩
      (hin _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · have l := F.at7 hx
    refine blockPlays_quiet chain A weights b _ (l.rounds.trans r7) (l.oracles.trans o7) c2 rfl ?_ _
    rw [l.place.trans p7]
    exact found ⟨place 7, [liftK14 A weights quietPart]⟩ (hin _ (by simp))
  · have l := F.at8 hx
    refine blockPlays_split chain A weights b _ (l.rounds.trans r8) (l.oracles.trans o8) c3 rfl rfl
      ?_ _
    rw [l.place.trans p8]
    exact found ⟨place 8, [liftK14 A weights (splitPart A)]⟩ (hin _ (by simp))

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.blockPlays_quiet
#print axioms AtPublicFiles.OfflineRows.blockPlays_split
#print axioms AtPublicFiles.OfflineRows.blockPlays_send
#print axioms AtPublicFiles.OfflineRows.blockPlays_six
