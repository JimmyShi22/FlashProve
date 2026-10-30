-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K5.lean: THE ROUNDS THAT THE BLOCKS OF K5's LOT DECLARE (H2K5.lotN,
Johnson/Desc/ProofFile/Lot/K5.lean: an attention segment's own rounds), WRITTEN OUT OF THE TWO
VALUES THAT THEY READ. General in the public part Z and the ground G. Definitions, statements and
proofs. Nothing is evaluated here.

Why. That the proof file's description declares the written rounds (F.roundsDeclaredByBlocks) is to be shown out of
the blocks' own rounds, lot by lot. By report (not held here) a block's skeleton holds how
many rounds it has, not the rounds. This file is K5's lot's row for the rounds themselves.

What the texts say. attentionKind (Johnson/Desc/First/Att/K5AttentionKind.lean) lays rounds := rounds p, and rounds p reads
p.own and p.work alone: not link, piece or before. k5AtN (Johnson/Desc/First/Att/SeatN.lean) lays
own := a.own at W.A[g]? = some a, and as work the policy's work at a round that draws field
elements. k5AtN and k5OwnN turn the block's own test alone. lotN's field own is empty.

  k5RoundsOf work own   the rounds, of these two values.
  k5Work W   the policy's work at a round of the request's scope that draws field elements, off the
      public part. Not K5's alone: another kind's lot lays the same expression.
  rounds_reads_two   rounds p is k5RoundsOf p.work p.own.
  k5RoundsOf_no_rows   of own the field rows is not read.
  k5AtN_rounds   a block that k5AtN returns has the rounds of its group's plan's own.
  **k5_second_row**   the lot's blocks' rounds, block by block: no premise. A SEGMENT WHOSE GROUP
      HAS NO PLAN GIVES NO ENTRY: the list can be shorter than the list of attention segments.
  **k5_second_row_list**   where every attention segment's group has a plan whose own, with the
      public part's work, gives the one list R: so many copies of R as there are attention segments.
  k5_second_row_written   the same from one value own at every group and the work w. "Written" is in
      w and own alone: the count and the list are no literals. It asks the whole record own, rows
      too, which is more than the rounds read. That records alike but for rows suffice is one step
      from k5_second_row_list and k5RoundsOf_no_rows; no theorem here takes it.

Limits. No public files are named: that hw, hA or hR hold anywhere is not said, nor how many
attention segments there are. Whether all groups have one own hangs on the public files, not on the
structure. That k5RoundsOf w own is a stretch of the declared rounds is not said.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Lot.K5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First

/-- K5's block's rounds, of the two values that they read. -/
def k5RoundsOf (work : Nat) (own : Params.AttentionRounds) : List Fmt.DeclaredRound :=
  Att.P.rounds { link := 0, piece := 0, work := work, own := own, before := [] }

/-- The policy's work at a round of the request's scope that draws field elements, off the public
part. -/
def k5Work (W : Verify.Public) : Nat := (Params.settingOf W.P.frame).workOf .field .request

/-- The rounds read the work and the planner's record of these rounds alone. -/
theorem rounds_reads_two (p : Att.P.Par) : Att.P.rounds p = k5RoundsOf p.work p.own := rfl

/-- Of own the field rows is not read. -/
theorem k5RoundsOf_no_rows (w : Nat) (x : Params.AttentionRounds) (r : Nat) :
    k5RoundsOf w { x with rows := r } = k5RoundsOf w x := rfl

/-- A block that k5AtN returns has the rounds of its group's plan's own. -/
theorem k5AtN_rounds {W : Verify.Public} {l g : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) :
    ∃ a, W.A[g]? = some a ∧ b.rounds = k5RoundsOf (k5Work W) a.own := by
  unfold Att.P.k5AtN at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨p, hp, rfl⟩

/-- **K5's lot's blocks' rounds, block by block.** -/
theorem k5_second_row (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((H2K5.lotN Z).blocks G).map (·.rounds) =
      (H2K5.k5Places G).filterMap fun x =>
        (G.W.A[x.2.2]?).map fun a => k5RoundsOf (k5Work G.W) a.own := by
  have e : (H2K5.lotN Z).blocks G = H2K5.k5OwnN Z G := rfl
  rw [e]
  unfold H2K5.k5OwnN
  rw [List.map_filterMap]
  refine congrArg (fun f => List.filterMap f (H2K5.k5Places G)) (funext fun x => ?_)
  unfold Att.P.k5AtN
  cases G.W.A[x.2.2]? <;> rfl

/-- **The same, where every attention segment's group's plan gives the one list R.** -/
theorem k5_second_row_list (Z : ProofFile.Pub) (G : ProofFile.Ground) {R : List Fmt.DeclaredRound}
    (hR : ∀ x ∈ H2K5.k5Places G,
      ∃ a, G.W.A[x.2.2]? = some a ∧ k5RoundsOf (k5Work G.W) a.own = R) :
    ((H2K5.lotN Z).blocks G).map (·.rounds) = List.replicate (H2K5.k5Places G).length R := by
  rw [k5_second_row]
  generalize H2K5.k5Places G = l at hR ⊢
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨a, ha, ho⟩ := hR x (List.mem_cons_self ..)
    have hx : (fun x : Nat × String × Nat =>
        (G.W.A[x.2.2]?).map fun a => k5RoundsOf (k5Work G.W) a.own) x = some R := by
      show (G.W.A[x.2.2]?).map (fun a => k5RoundsOf (k5Work G.W) a.own) = some R
      rw [ha, ← ho]
      rfl
    rw [List.filterMap_cons_some (f := fun x : Nat × String × Nat =>
        (G.W.A[x.2.2]?).map fun a => k5RoundsOf (k5Work G.W) a.own) (a := x) hx,
      List.length_cons, List.replicate_succ, ih fun y hy => hR y (List.mem_cons_of_mem _ hy)]

/-- The same from one value own at every attention segment's group, and the work w. -/
theorem k5_second_row_written (Z : ProofFile.Pub) (G : ProofFile.Ground) {w : Nat}
    {own : Params.AttentionRounds} (hw : k5Work G.W = w)
    (hA : ∀ x ∈ H2K5.k5Places G, ∃ a, G.W.A[x.2.2]? = some a ∧ a.own = own) :
    ((H2K5.lotN Z).blocks G).map (·.rounds) =
      List.replicate (H2K5.k5Places G).length (k5RoundsOf w own) :=
  k5_second_row_list Z G fun x hx => by
    obtain ⟨a, ha, ho⟩ := hA x hx
    exact ⟨a, ha, by rw [hw, ho]⟩

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.rounds_reads_two
#print axioms Johnson.AtFull.Rounds.k5RoundsOf_no_rows
#print axioms Johnson.AtFull.Rounds.k5AtN_rounds
#print axioms Johnson.AtFull.Rounds.k5_second_row
#print axioms Johnson.AtFull.Rounds.k5_second_row_list
#print axioms Johnson.AtFull.Rounds.k5_second_row_written
