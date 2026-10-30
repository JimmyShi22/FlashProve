-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/DenseAtOwn.lean: every row that the last chain's test takes in is
dense (`DenseRow`, OnBytes/Slice/BlkProxDense.lean), from what the two earlier chains hand over and the
first member's yes: the premise `denseRows` of `ShapeAsksD` (K12/PlanBDense.lean) at that test.

  `dense_of_members`   the rows that a test on a group takes in are dense, where the open rows are in
                 order and the sample rows of the group's members are plain. `runRows_denseOf`
                 (Johnson/AtFull/Shape/TakenRowsDense.lean) with the second premise asked of the members
                 alone: the whole statement is more than a test takes in
  `ord_takeOver`, `ord_second`   the taking-over of Omega and the block "K14, second part" keep the
                 open rows in order: the relation `OrdStays` (Johnson/AtFull/Shape/OpenRowsOrder.lean)
                 goes along the ground's functions (`groundKeeps_ord`), and the new row (Dot) passes
                 `addRowP`'s own test
  `dense_at_own`   the statement: behind the first member's yes, behind a block that changes no
                 state, at the own group

Why the second premise is narrower than the library's. Behind the first chain's own test the statement
holds messages of that test, and nothing yet says that their sample rows are plain. The test at the last
chain reads three members' sample rows alone: the index masks' message, W, Omega.

Limits.
- hP IS A PREMISE: the members' sample rows. W's and the index masks' are laid on the first chain in
  front of its test (`samplesPlain_upto_354`); that they stay to that chain's end, and that Omega's are
  plain at the shared chain, is not shown here.
- hO at the state that the chain's start returns is a premise: `openOrd_reached` has it at the first
  chain's end, and the start lays that statement: the last step is not typed here.
- Of a statement's shape: nothing on a value. Nothing on a run.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.AtFull.Shape.TakenRowsDense
import Johnson.Desc.Third.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open OnBytes.Slice.ProxRun (DenseRow denseRow_of_plain)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut takeOver batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (takeOver_inv k14Second_inv)
open Johnson.AtFull.Shape (OpenOrd OrdStays groundKeeps_ord denseRow_of_rowOrd)
open Desc.Plain (DState)

/-- **Every row that a test on a group takes in is dense**, where the open rows are in order and the
sample rows of the group's members are plain. -/
theorem dense_of_members {T : Statement} (hO : OpenOrd T) {g : ℕ} {G : Group}
    (hG : T.groups[g]? = some G)
    (hP : ∀ o ∈ G.members.toList, ∀ x : OnBytes.Oracle, T.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, PlainRow r) :
    ∀ r ∈ (runRows T G).toList, DenseRow r := by
  have key : ∀ (l : List ℕ) (acc : Array OnBytes.Row), (∀ o ∈ l, o ∈ G.members.toList) →
      (∀ r ∈ acc.toList, DenseRow r) →
      ∀ r ∈ (l.foldl (fun a o => a ++ ((T.oracles[o]?).map (·.sampleRows)).getD #[]) acc).toList,
        DenseRow r := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons o l ih =>
      intro acc hl hacc
      refine ih _ (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) fun r hr => ?_
      rw [Array.toList_append, List.mem_append] at hr
      rcases hr with hr | hr
      · exact hacc r hr
      · cases hx : T.oracles[o]? with
        | none =>
          rw [hx] at hr
          cases hr
        | some x =>
          rw [hx] at hr
          exact denseRow_of_plain (hP o (hl o List.mem_cons_self) x hx r hr)
  intro r hr
  unfold runRows at hr
  rw [Array.toList_append, Array.toList_append, List.mem_append, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · rw [Array.toList_filter] at hr
    exact denseRow_of_rowOrd (hO g G hG r (List.mem_filter.1 hr).1)
  · rw [← Array.foldl_toList] at hr
    exact key _ _ (fun _ h => h) (fun _ h => by cases h) r hr
  · rw [Array.toList_filter] at hr
    exact denseRow_of_rowOrd (hO g G hG r (List.mem_filter.1 hr).1)

/-- The taking-over of Omega keeps the open rows in order. -/
theorem ord_takeOver (S : Params.LinShape) (own : ℕ) (o : SharedOut)
    (d : DState VerifiableInference.Desc.Third.Loc₃) (r : ℕ × DState VerifiableInference.Desc.Third.Loc₃)
    (h : takeOver S own o d = .ok r) : OrdStays d.st r.2.st := by
  obtain ⟨_, _, _, a, d₁, _, _, _, ha, _, h1, h2⟩ := takeOver_inv S own o d r h
  exact groundKeeps_ord.trans (groundKeeps_ord.trans
    (groundKeeps_ord.adopt _ _ _ _ _ ha) (groundKeeps_ord.elsewhere _ _ _ _ _ h1))
    (groundKeeps_ord.join _ _ _ _ _ h2)

/-- **The block "K14, second part" keeps the open rows in order.** -/
theorem ord_second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    OrdStays s.st s'.st := by
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  exact groundKeeps_ord.trans (ord_takeOver _ _ _ _ _ ha)
    (groundKeeps_ord.addRow _ _ _ _ hb)

/-- **At the own group, behind the first member's yes**: a state s₀ whose open rows are in order, s its
step, s' what a block that changes no state hands on. -/
theorem dense_at_own {Cl : Type} (p : P₁₄) (s₀ s : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s)
    (hO : OpenOrd s₀.st) {G : Group} (hG : s.st.groups[s.loc.own]? = some G)
    (hP : ∀ o ∈ G.members.toList, ∀ x : OnBytes.Oracle, s.st.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, PlainRow r) :
    ∀ r ∈ (runRows s.st G).toList, DenseRow r :=
  dense_of_members (ord_second p s₀ s rs gs h hO) hG hP

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.dense_of_members
#print axioms ProofFile.Honest.K12.AtFile.ord_takeOver
#print axioms ProofFile.Honest.K12.AtFile.ord_second
#print axioms ProofFile.Honest.K12.AtFile.dense_at_own
