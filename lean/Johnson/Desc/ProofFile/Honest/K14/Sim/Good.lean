-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/Good.lean: K14's SIX ROWS IN THE FRAME's SLOT, AT THE PROOF FILE's IOP AS WRITTEN IN
LEAN: under the library's head (`P5J.AtMgA`), at one book and one order of places, each of the six rows has a side off the
description's shared list, and `Good` holds of it as one term. Joins of laws that stand in this folder; no new argument over a
distribution.

  `good_sending`   `Good` at a sending's row, AT A := False, from `rowsServe_at_shared`, where the two owners' tests accept
  `good_own`       `Good` at one of the four own rows, AT A := False, from `good_rows`, where the book passes `noneSpent`
  `OwnClear`       the book passes `noneSpent` at the four own places
  `simData`, `simPub`   the public data at which the frame's filling lays the halves: "LIN point" is round 0, "LIN zeta" round 6
  `simRows_places`   under the head the list has its six rows, at the places 1, 4, 7, 8, 2, 5
  `six_good`       **at every row of the six: a side, and `Good`**
  `simLettered`, `six_goodAt`   the row with its letters, and the form that the frame's rule takes

Limits. AT A := False `plays` AND `acc` ARE MET FOR NOTHING: fits, exact and fresh alone say something here; the frame's rule
reads these three alone. ON THE BOOK: premises here; Honest/K14/Sim/AtPure.lean pays them at the
book that `onlineProverFromPublicFiles` returns. WHAT A PART SHOWS IS NOT ALL THAT A RUN SHOWS OF ITS MESSAGES AND COINS: the proximity tests behind
these parts are handed these coins: that is their own slot's work, and nothing here says it holds. `exact` at "SPLIT" takes its
coin as uniform: the owner's sentence at "send o_omega" is `fresh`. No property of the protocol is claimed: nothing on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sim.Rows
import Johnson.Desc.ProofFile.Honest.K14.GoodSeated
import Johnson.Desc.ProofFile.Honest.K14.RowsAtShared
import Johnson.Desc.ProofFile.Honest.K14.PlanAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (St chainOf)
open Desc.K14.Honest (flatOf_carried)
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Ky X : Type}

/-- The public data at which the halves are laid. -/
def simData (Zp : ProofFile.Pub) (Np : H2U.Places4) : Data :=
  { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 }

/-- The sendings' public data. -/
def simPub (Zp : ProofFile.Pub) (Np : H2U.Places4) : SendPub := ⟨qAt Zp Np, 0⟩

/-- The book passes `noneSpent` at the four own places. -/
def OwnClear (Bk : ProverCoinCounts) : Prop :=
  noneSpent Bk ⟨place 1, 0⟩ = true ∧ noneSpent Bk ⟨place 4, 0⟩ = true ∧
    noneSpent Bk ⟨place 7, 0⟩ = true ∧ noneSpent Bk ⟨place 8, 0⟩ = true

/-- **The six rows stand at six places**, under the head: so the statements "at every row" below are not said of an empty list. -/
theorem simRows_places (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    ((simRows (simData Zp Np) (simPub Zp Np) weights rand :
        List (Unlettered Empty (Common W₀ Rc Ky) X Ky)).map (·.place)) =
      [place 1, place 4, place 7, place 8, sendPlace 2, sendPlace 5] := by
  unfold simRows
  rw [List.map_append, ownRows_four _ weights (sendings_at_head h).2.1]
  rfl

/-- **`Good` at a sending's row, at A := False**, where the two owners' tests accept. -/
theorem good_sending (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place)
    (okU : (maskOwner (simPub Zp Np)).ok Bk ord ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner (simPub Zp Np)).ok Bk ord ⟨sendPlace 5, 0⟩ = true)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Ky)
    (hr : r ∈ sendingRows (simPub Zp Np) weights rand)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X Ky)
    (hσ : Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    Good pre .shared σ Bk ord 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On r.bud := by
  obtain ⟨f1, f2, f3⟩ := (rowsServe_at_shared h X W₀ Rc Ky weights rand fs Bk ord r hr).2 σ hσ
  exact { fits := f1, plays := fun _ _ _ _ _ h => h.elim, acc := fun _ _ _ _ _ h => h.elim
          exact := fun u hu ca m front ds asks o s _ d b e t => f2 u hu ca m front ds asks o s d b e t
          fresh := f3 okU okO }

/-- **A side and `Good` at one of the four own rows, at A := False**, at a book that passes `noneSpent` there. -/
theorem good_own (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights)
    (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place) (hB : OwnClear Bk)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Ky)
    (hr : r ∈ (ownRows (simData Zp Np) weights : List (Unlettered Empty (Common W₀ Rc Ky) X Ky)))
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∃ σ, Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ ∧
      Good pre .shared σ Bk ord 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On r.bud := by
  obtain ⟨sentU, layO, hP⟩ := plan2_at_head h
  obtain ⟨B⟩ := hP.eight
  have F := flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6
    B.b7 B.b8 (tests Np) last B.made
  obtain ⟨i, hi, hp⟩ := place_of_row _ weights r hr
  have hN : noneSpent Bk { place := r.place, part := 0 } = true := by
    rw [hp]
    obtain ⟨a, b, c, e⟩ := hB
    rcases hi with rfl | rfl | rfl | rfl
    · exact a
    · exact b
    · exact c
    · exact e
  rw [shared_flat_at]
  obtain ⟨σ, hσ⟩ := seated_some F B.made i hi r.row fs
  rw [← hp] at hσ
  exact ⟨σ, hσ, good_rows F B.made _ rfl weights r hr fs σ hσ .shared Bk ord 1 0 pre hN⟩

/-- **At every row of the six: a side off the description's shared list, and `Good` as one term, at A := False.** -/
theorem six_good (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place)
    (hB : OwnClear Bk)
    (okU : (maskOwner (simPub Zp Np)).ok Bk ord ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner (simPub Zp Np)).ok Bk ord ⟨sendPlace 5, 0⟩ = true)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Ky)
    (hr : r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∃ σ, Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ ∧
      Good pre .shared σ Bk ord 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On r.bud := by
  rcases List.mem_append.1 hr with h' | h'
  · exact good_own h weights fs Bk ord hB r h' pre
  · obtain ⟨-, hs⟩ := rowsServe_at_shared h X W₀ Rc Ky weights rand fs Bk ord r h'
    have hany := (rowsServe_at_shared h X W₀ Rc Ky weights rand fs Bk ord r h').1
    cases hσ : Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs with
    | none =>
      exfalso
      unfold Side.seated at hσ
      obtain ⟨b, hb, hp⟩ := List.any_eq_true.1 hany
      rw [Option.map_eq_none_iff, List.find?_eq_none] at hσ
      exact hσ b hb hp
    | some σ => exact ⟨σ, rfl, good_sending h weights rand fs Bk ord okU okO r h' σ hσ pre⟩

/-- The row with its letters: A and B False. -/
def simLettered (Bk : ProverCoinCounts) (r : Unlettered Empty (Common W₀ Rc Ky) X Ky) :
    Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X Ky :=
  { place := r.place, row := r.row, A := fun _ _ _ _ => False, B := fun _ _ _ _ => False
    On := r.On, bud := r.bud }

/-- **The form that the frame's rule takes**, at every row of the six. -/
theorem six_goodAt (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place)
    (hB : OwnClear Bk)
    (okU : (maskOwner (simPub Zp Np)).ok Bk ord ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner (simPub Zp Np)).ok Bk ord ⟨sendPlace 5, 0⟩ = true)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Ky)
    (hr : r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand)
    (earlier : List (Nat × Nat × List Fmt.DeclaredRound)) :
    (simLettered Bk r).goodAt earlier .shared (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder ord 1 0 fs := by
  intro σ hσ
  obtain ⟨σ', h1, h2⟩ := six_good h weights rand fs Bk ord hB okU okO r hr _
  have e : σ' = σ := Option.some.inj (h1.symm.trans hσ)
  subst e
  exact h2

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.simRows_places
#print axioms ProofFile.Honest.K14.good_sending
#print axioms ProofFile.Honest.K14.good_own
#print axioms ProofFile.Honest.K14.six_good
#print axioms ProofFile.Honest.K14.six_goodAt
