-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K13/GoodRows.lean: kind K13, the members' batching: the kind's
simulator, as the rows of `k13SLot` (RowsLot.lean of this folder), meets the conditions `fits`,
`exact` and `fresh` of `Good` (Honest/Side.lean) at the proof file's own description and at the book
of coins that the frame's maker returns there. The only hypotheses: the library's head h
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), and that the book is one that `bookWhole`
(Honest/BookWhole.lean) returns at the head's description, or the book of what `onlineProverFromPublicFiles`
(Honest/AtPure.lean) returns at the head's files. No test on the book is left as a hypothesis.
Statements with their proofs; no definition. At the full size and at the hash `OnBytes.secondHashFunction`
alone.

  `k13_good_rows`   **at each row of `k13SLot`**: `Side.seated` returns a side, its sub-protocol is
     number 355 of the first chain's flat list, and every side that it returns meets `Good`
  `k13_seat`   the row's place is a sub-protocol's: the rule's hypothesis `seat₁` at the row
  `k13_hand`   the same in the form of the hypothesis `hand₁` of the frame's rule for a file
     (`file_owed_rows`, Honest/Thread/Rows.lean), at any threads
  `k13_good_rows_atPure`   `k13_good_rows` at the book of what `onlineProverFromPublicFiles` returns at the head's files,
     at any filling
  `k13_onFromS`, `k13_bud_at`   the kind's `On` and `bud` ask nothing, so the rule's hypotheses on
     them (`OnFromS`, Honest/Thread/OnSaid.lean; the clause of `BudDebts`, Honest/Law/OwedRule.lean)
     hold at a row laid from `k13SLot`

What this pays. The frame's rule reads of a row's author a term of `Good` at any A and B, and takes
`fits`, `exact` and `fresh` from it. So `k13_hand` is the kind's share of the rule's hypothesis
`hand₁`, `k13_seat` of `seat₁`, and `k13_onFromS` and `k13_bud_at` give its shares of the hypotheses
on `On` and `bud`. The field `good` of `Owed` (Honest/Owed.lean) asks `plays` and `acc` at the row's
own A and B too; only at rows whose A and B are struck (`file_owed_rows_mute`,
Honest/Thread/RowsMute.lean) is `k13_hand` all that `good` asks at this row.

On meeting the hypotheses. h holds at all public files in the goals' scope that are read and pass
the library's test `protocolDataWellFormed` (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that `bookWhole` returns
under h is not shown here.

Limits.
  * A and B are False in every term of `Good` here: `plays` and `acc` hold vacuously. Nothing is
    said about a run, about the verifier's acceptance or about any state. The fields `runs` and
    `owed` of `Owed` ask, at this kind's place, the conditions on the thread (`OwesS`, `SaidNext`):
    not shown here.
  * `exact` is the borrower's half, and `fresh` at the kind's own parts compares no coin (the heads
    of Exact.lean and Fields.lean of this folder). That the block which part 1 borrows is still
    uniform when it is spent is the condition `fresh` at the part that owns these coins in the book,
    at part 1's address: not shown here. Without it these statements say nothing about hiding. Which
    entry of the book that block is, and who owns it: AtFullSide/K13/EntryAtBook.lean.
  * The test `Sides.owns` (Honest/Law/Rule/Session.lean), a hypothesis of `rule_views`
    (Honest/Law/Rule/Row.lean), asks that this owner has a list of parts among the sides: not shown
    here.
  * The reader of the index and the filler of the pile are parameters. That the lot which a given
    filling lays at this place is `k13SLot`'s is not shown here; AtFill.lean of this folder shows it
    at one filling.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.K13.FieldsAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Place Chain)
open P5J (AtMgA TS)
open ProofFile.Honest.K14 (atPure_book_at_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-! ## 1 `Good` at the rows of `k13SLot` -/

include h in
/-- **The kind's simulator as a value of `SLot`: `fits`, `exact` and `fresh` at each of its rows**,
at the first chain's own flat list and a book that `bookWhole` returns at the head's description,
under h alone. The first part says that the second is not met for want of a side: one is returned,
at the sub-protocol number 355. A and B are False: see the head for what the term pays and what it
does not. -/
theorem k13_good_rows {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 M = .ok Bk)
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (G : ProofFile.Ground)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Pb) (ord : List Place)
    (chain firstTree : Nat) (fs : List (Fall TS)) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zp G,
      (∃ σ, Side.seated cF.blocksInOrder r.place r.row fs = some σ ∧ cF.blocksInOrder[355]? = some σ.block) ∧
        ∀ σ, Side.seated cF.blocksInOrder r.place r.row fs = some σ →
          Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
            r.bud := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact ⟨k13_side_at h weights (pile Zp G) fs, fun σ hσ =>
    k13_good_at_head h hW pre weights (pile Zp G) φ hσ ord chain firstTree⟩

include h in
/-- The row's place is a sub-protocol's: the rule's hypothesis `seat₁` at the row. -/
theorem k13_seat (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst)
    (G : ProofFile.Ground) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zp G,
      cF.blocksInOrder.any (fun b => b.place == r.place) = true := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  obtain ⟨σ, h1, -⟩ :=
    k13_side_at (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) h weights (pile Zp G) []
  exact List.any_eq_true.2 ⟨σ.block, sideSeated_mem h1, beq_iff_eq.2 (sideSeated_place h1)⟩

include h in
/-- **The same in the form of the rule's hypothesis on a row's author** (`hand₁` of
`file_owed_rows`, Honest/Thread/Rows.lean): at the row as laid at any threads T and any Sd. -/
theorem k13_hand {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 M = .ok Bk)
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (G : ProofFile.Ground)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Pb) (ord : List Place)
    (chain firstTree : Nat) (fs : List (Fall TS))
    (T : Local W₀ Rc ProofFile.Inst Tr →
      Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb)
    (Sd : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zp G,
      ∀ σ, (r.lay T Sd cF.blocksInOrder).side cF.blocksInOrder fs = some σ →
        ∃ A' B', Good pre φ σ Bk ord chain firstTree A' B' (r.lay T Sd cF.blocksInOrder).On
          (r.lay T Sd cF.blocksInOrder).bud :=
  fun r hr => hand_of_seated r T Sd cF.blocksInOrder fun σ hσ =>
    ⟨_, _, (k13_good_rows h hW weights pile G pre φ ord chain firstTree fs r hr).2 σ hσ⟩

include h in
/-- **`k13_good_rows` at the book of what `onlineProverFromPublicFiles` returns at the head's files**, at any filling P.
-/
theorem k13_good_rows_atPure {W₁ Rc₁ Tr₁ X₀ X₁ : Type} {P : OnlineProverParts W₁ Rc₁ Tr₁ X₀ X₁}
    {A : OnlineProverWithDescription W₁ Rc₁ Tr₁ X₀ X₁}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (G : ProofFile.Ground)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Pb) (ord : List Place)
    (chain firstTree : Nat) (fs : List (Fall TS)) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zp G,
      (∃ σ, Side.seated cF.blocksInOrder r.place r.row fs = some σ ∧ cF.blocksInOrder[355]? = some σ.block) ∧
        ∀ σ, Side.seated cF.blocksInOrder r.place r.row fs = some σ →
          Good pre φ σ A.B ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
            r.bud :=
  k13_good_rows h (atPure_book_at_head h hA) weights pile G pre φ ord chain firstTree fs

/-! ## 2 `On` and `bud` -/

/-- The rule's hypothesis on `On` (`OnFromS`) at a row of `k13SLot` as laid: the kind's `On` asks
nothing. At any thread T', any Said, border number and depths. -/
theorem k13_onFromS {Bk' : ProverCoinCounts}
    (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst) (Zq : ProofFile.Pub)
    (G : ProofFile.Ground) {S Cl : Type}
    (T' : Thread Bk' S Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb)
    (Said : Nat → Coins Bk' → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (T : Local W₀ Rc ProofFile.Inst Tr →
      Thread Bk' S Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X Pb)
    (Sd : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins Bk' → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (bs : List (Block S Cl)) (b : Nat) (len : Nat → Nat → Nat) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zq G,
      OnFromS T' Said (r.lay T Sd bs) b len := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial

/-- The kind's `bud` at a row of `k13SLot`: it holds at every number, all challenges and all lists
of positions, so the clause of `BudDebts` at such a row holds. -/
theorem k13_bud_at (weights : W₀ → Weights) (pile : ProofFile.Pub → ProofFile.Ground → PileOf ProofFile.Inst)
    (Zq : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ r ∈ (k13SLot (Rc := Rc) (Tr := Tr) (X := X) (Pb := Pb) weights pile).rows Zq G,
      ∀ n ds asks, r.bud n ds asks := by
  intro r hr
  obtain rfl := List.mem_singleton.1 hr
  exact fun _ _ _ => trivial

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_good_rows
#print axioms ProofFile.Honest.K13.k13_seat
#print axioms ProofFile.Honest.K13.k13_hand
#print axioms ProofFile.Honest.K13.k13_good_rows_atPure
#print axioms ProofFile.Honest.K13.k13_onFromS
#print axioms ProofFile.Honest.K13.k13_bud_at
