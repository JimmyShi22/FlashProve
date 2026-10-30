-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameYes.lean: **THE GAME OF THE PROXIMITY TEST WITHOUT THE PROMISE ON THE
BATCHED ROWS**: `PayRec` leaves the promise wherever a yes of the block's own step holds the test
`combineAt` at the record in front. Statements and proofs.

  `StepComb π`: a yes of `Block.step` of the proximity test's block, the record's group and its
    layout give `combineAt` at the statement behind the test's beginning, the layout in front and
    the rows that the test takes in. IT IS THE STATEMENT OF `comb_of_step`
    (Johnson/Desc/K12/Law/Step8.lean, the kind's own law's side) TO THE LETTER, at one π.
    That theorem holds only because the block's parts ask guard (c);
    here it is a premise.
  `leads_drop_yes`: for every reduction: a clause of the promise that the rest of the promise and a
    yes together give may be dropped.
  `yes_payRec`: under `StepComb π`: where a piece of that block with nothing put back says yes,
    `PayRec π` holds of the record in front.
  `GameAtY`, `GameAtYO`: the game's form (Game.lean) with the record's count of roots and
    `FirstOpens` | `FirstOpensOwn` alone in the promise.
  `gameY_of_game`, `gameYO_of_game`: under `StepComb π`, at a piece of that block: Game.lean's form
    gives this one.
Limits: those of Game.lean. NO SOUNDNESS IS CLAIMED. `StepComb` is a premise here.

-/
import Johnson.Desc.K12.Coin.Game

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayRec)

/-- A yes of the block's step holds `combineAt` at the record in front. -/
def StepComb (π : P12) : Prop :=
  ∀ (t0 tE : T12) (F n : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    (proximityTestKind guardedProximityTestParts π : Block T12 Unit).step F t0 rs cols = .ok (tE, n) →
    ∀ (G0 : Group) (Ly : GroupLayout), t0.st.groups[t0.g]? = some G0 →
      t0.st.layout t0.g = some Ly →
      Means.combineAt (begun t0.st t0.g G0) t0.g ⟨Ly, runRows t0.st G0⟩ = true

/-- A clause of the promise that the rest of the promise and a yes together give may be dropped. -/
theorem leads_drop_yes {A B : Type} {K : Reduction A B} {on P : A → Prop} {Q : A → B → Prop}
    {ε : Err K.shape} (h : K.Leads (fun a => on a ∧ P a) Q ε)
    (hP : ∀ a τ b, on a → K.out a τ = some b → P a) : K.Leads on Q ε := by
  intro a ha
  by_cases hy : ∃ τ b, K.out a τ = some b
  · obtain ⟨τ, b, hb⟩ := hy
    exact h a ⟨ha, hP a τ b ha hb⟩
  · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hy

/-- Where a piece of the block says yes, the batched rows lie within the group. -/
theorem yes_payRec {W : Type} (F : Frame) (π : P12) (hS : StepComb π)
    (p : Piece (ckP .two) F T12 Unit W) (hb : p.b = proximityTestKind guardedProximityTestParts π) (h0 : p.back = [])
    (x : T12 × F.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds)) (b : T12 × F.E.Str)
    (h : p.ior.red.out x τ = some b) : PayRec π x.1 := by
  intro a rest G0 Ly D hf
  obtain ⟨_, k, hst, _⟩ := yes_step p h0 x τ b h
  rw [hb] at hst
  exact hS x.1 b.1 _ k _ _ hst G0 Ly hf.2.1 hf.2.2.1

/-- The game's form, first arm, without the promise on the batched rows. -/
def GameAtY {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W) : Prop :=
  p.ior.red.Leads (fun x => x.1.roots = n ∧ FirstOpens π num no base x.1)
    (fun x _ => QN π (NTuple F π no rad rd) x) p.err

/-- The second arm's. -/
def GameAtYO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W) : Prop :=
  p.ior.red.Leads (fun x => x.1.roots = n ∧ FirstOpensOwn π num no base x.1)
    (fun x _ => QN π (NTuple F π no rad rd) x) p.err

theorem gameY_of_game {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W)
    (hS : StepComb π) (hb : p.b = proximityTestKind guardedProximityTestParts π) (h0 : p.back = [])
    (h : GameAt F π num no rad rd base n p) : GameAtY F π num no rad rd base n p :=
  leads_drop_yes (P := fun x => PayRec π x.1)
    (Reduction.Leads.conseq h (fun _ hx => ⟨hx.1.1, hx.1.2, hx.2⟩) (fun _ _ _ _ _ q => q))
    (fun x τ b _ hy => yes_payRec F π hS p hb h0 x τ b hy)

theorem gameYO_of_game {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base n : ℕ) (p : Piece (ckP .two) F T12 Unit W)
    (hS : StepComb π) (hb : p.b = proximityTestKind guardedProximityTestParts π) (h0 : p.back = [])
    (h : GameAtO F π num no rad rd base n p) : GameAtYO F π num no rad rd base n p :=
  leads_drop_yes (P := fun x => PayRec π x.1)
    (Reduction.Leads.conseq h (fun _ hx => ⟨hx.1.1, hx.1.2, hx.2⟩) (fun _ _ _ _ _ q => q))
    (fun x τ b _ hy => yes_payRec F π hS p hb h0 x τ b hy)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.leads_drop_yes
#print axioms VerifiableInference.Desc.K12.Coin.yes_payRec
#print axioms VerifiableInference.Desc.K12.Coin.gameY_of_game
#print axioms VerifiableInference.Desc.K12.Coin.gameYO_of_game
