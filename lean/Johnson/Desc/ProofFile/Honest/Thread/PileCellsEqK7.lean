-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PileCellsEqK7.lean: the item `pile` of the first chain's
invariant passes over K9's "the one equation" in each of the 25 segments and, under one hypothesis,
over the sub-protocol of the kind K7. Both change the statement, so `ridesPastAt_pile`
(RowPileRides.lean) does not apply. `ridesPastAt_pile_older` (PileForward.lean) asks five things. Two
hold wherever the invariant holds (`head_pileMasks`, RowPileForwardKinds.lean; `head_index`,
HeadFences.lean). The three others are read off the clauses of `keeps` here. No definition.

  1  `eqKeeps_pile`   on two states, under K9's clause at "the one equation": the pending rows and
     the list of commitment trees are the same, and the statement after the step extends the one
     before it
  2  `k7KeepsAt_pile`   on two states, under K7's clause: the list of commitment trees is the same,
     and the statement after the step extends the one before it
  3  `pile_cell_eq`   **the cell at "the one equation"**, at the numbers `14 * l + IM.nAt l + 4`
  4  `pile_cell_k7`   the cell at a place of the kind K7, under `hrows`

`eqKeeps_pile` has three of the five conclusions of `eqKeeps_five` (WoEq.lean), without that lemma's
hypothesis `OwnNotIndex`, which serves another of its conclusions.

What `pile_cell_k7` leaves as a hypothesis.
  * `hrows`: `keeps` at that sub-protocol gives `s'.rows = s.rows`. K7's clause does not give it.
    The clause ends in `keepsOpened` (Law/NoHouse/OpenedKeeps.lean), which says that `out.pending`
    is the same and says nothing of the field `here` after the step, and `S.rows` reads `here`.
    `keepsOpenedR` (OpenedKeepsR.lean) is `keepsOpened` with that equation added.

Limits.
  * Nothing shows that a clause of `keeps` holds at any step.
  * Items 3 and 4: full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PinKeptCells
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Desc.ProofFile.Honest.Thread.Numbers358
import Johnson.Desc.First.Link.Law.FifthTieEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K2 (headFrontQ_rest)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.LinkJoin (door_both part_reads tri_blind rb_putLink rb_putFork
  door_link rows_set)
open ProofFile.Honest.K9 (EqKeeps k9KeepsAt)
open OnBytes.Means (Extends)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 and 2 On two states -/

/-- After "the one equation". -/
theorem eqKeeps_pile {s s' : S} (k : EqKeeps s s') :
    s'.rows = s.rows ∧ Extends s.st s'.st ∧ s'.book = s.book := by
  obtain ⟨a, o, ha, hdoor, rfl⟩ := k.laid
  obtain ⟨hL, hst⟩ := part_reads s a ha
  obtain ⟨e1, -⟩ := door_both tri_blind _ _ _ _ _ _ hdoor
  rw [hst] at e1
  have hb := ((rb_putLink s a.L o.L hL
    (by rw [door_link _ _ _ _ _ _ hdoor])).trans
    (rb_putFork _ o.F)).book
  refine ⟨rows_set s _, ⟨e1.1, fun j x hx => ?_⟩, hb⟩
  have e := e1.2 j
  rw [hx] at e
  obtain ⟨x', h1, h2⟩ := Option.map_eq_some_iff.1 e
  exact ⟨x', h1, congrArg (·.1) h2⟩

/-- After K7's sub-protocol. -/
theorem k7KeepsAt_pile {G : ProofFile.Ground} {p : Place} {s s' : S} (k : K7KeepsAt G p s s') :
    Extends s.st s'.st ∧ s'.book = s.book := by
  refine ⟨?_, ?_⟩
  · rw [k.2.st]
    exact ⟨rfl, fun _ x hx => ⟨x, hx, rfl⟩⟩
  · obtain ⟨m, ⟨-, t, ht, o, x, -, -, -, -, rfl⟩, h2⟩ := k.2
    exact (keepsOpened_book h2).trans (headFrontQ_rest ht).1

/-! ## 3 and 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The cell of `pile` at "the one equation" of segment `l`.** -/
theorem pile_cell_eq (hf9 : f KindName.K9 = k9KeepsAt cF Zp) {l : Nat} (hl : l < 25) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread
      (14 * l + IM.nAt l + 4) Item.pile := by
  have hn : IM.nAt l = 7 ∨ IM.nAt l = 9 := by
    by_cases h24 : l = 24
    · subst h24
      exact Or.inr nAt_head
    · exact Or.inl (nAt_lt (by omega))
  have hlen : cF.blocksInOrder.length = 358 := head_len h
  refine ridesPastAt_pile_older h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    fun k s mm E s' hA hK => ?_
  obtain ⟨e1, e2, e3⟩ := eqKeeps_pile
    (head_keeps_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf9 hl s s' hK)
  refine ⟨e1, head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w (by omega) hA,
    head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hA
      (open_pinI (by omega) (by omega)), e2, fun o _ => ?_⟩
  rw [e3]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- The cell of `pile` at a place of the kind K7, if `keeps` there leaves the pending rows. -/
theorem pile_cell_k7 {G : ProofFile.Ground} (hf7 : f KindName.K7 = K7KeepsAt G) {b : Nat} {p : Place}
    (hb : b < 358) (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K7)
    (hrows : ∀ s s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps b s s' →
      s'.rows = s.rows) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread b
      Item.pile := by
  have e338 : b = 338 := k7_number_of hb hp hk
  have hlen : cF.blocksInOrder.length = 358 := head_len h
  refine ridesPastAt_pile_older h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
    fun k s mm E s' hA hK => ?_
  obtain ⟨e2, e3⟩ := k7KeepsAt_pile (G := G) (p := p)
    (head_hk h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hp hk (K := K7KeepsAt G p)
      (fun s s' hc => by
        rw [hf7] at hc
        exact hc) s s' hK)
  refine ⟨hrows s s' hK,
    head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w (by omega) hA,
    head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hA
      (open_pinI (by omega) (by omega)), e2, fun o _ => ?_⟩
  rw [e3]
  exact ⟨rfl, fun _ _ => rfl⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.eqKeeps_pile
#print axioms ProofFile.Honest.FirstThread.k7KeepsAt_pile
#print axioms ProofFile.Honest.FirstThread.pile_cell_eq
#print axioms ProofFile.Honest.FirstThread.pile_cell_k7
