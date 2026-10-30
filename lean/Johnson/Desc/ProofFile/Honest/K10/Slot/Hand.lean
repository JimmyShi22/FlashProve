-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Slot/Hand.lean: the closing of a segment (K10): AT THE 25 WRITTEN PLACES, what the rule
asks at the laid row (`closing_hand`, Honest/K10/RowsOfClosings.lean) with its premise on the seated side paid: from
`PlanAlike WP F`, the whole book's return and `F.placesOk`.

  `close_no_seed`    the kind's rounds hold no round "SEND seed"
  `seated_mem`       a seated side's block is of the list
  `written_side`     at such a place every seated side of the row has one member, fits, and no entry spends its coins
  **`written_hand`**  so the laid row at such a place meets `Good`, at its own On and bud
  `closing_on`, `closing_on_always`, `closing_bud`   the row's share of the rule's hypotheses on On and bud (`file_owed_rows`, `BudDebts`): both
      ask nothing here, at every stand: so the closing's On leans on no kind's `plays`

Limits. THE SPENDER's HALF: `Good` here is at letters of `closing_hand`'s, A := B := False inside it. That `bookWhole`
returns, `F.placesOk` and `PlanAlike WP F` are premises. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Slot.Written
import Johnson.Desc.ProofFile.Honest.K10.RowsOfClosings
import Johnson.Desc.ProofFile.Honest.BookOwners
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Slot
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par entries)
open P2Law.ProofPlan (WP)

/-- The kind's rounds hold no round "SEND seed". -/
theorem close_no_seed (P : Par) : ∀ r ∈ (closeRounds P).map (·.1), r.entry.name ≠ "SEND seed" := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  unfold entries at he
  rcases List.mem_cons.1 he with rfl | he
  · show ("BAT" : String) ≠ "SEND seed"
    decide
  rcases List.mem_cons.1 he with rfl | he
  · show ("FOLD epsilon" : String) ≠ "SEND seed"
    decide
  rw [List.eq_of_mem_replicate he]
  show ("FOLD round" : String) ≠ "SEND seed"
  decide

/-- A seated side's block is of the list. -/
theorem seated_mem {S Cl V W X Pb : Type} {bs : List (Block S Cl)} {a : Place}
    {row : List (Part V W X × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W X Pb}
    (h : Side.seated bs a row fs = some σ) : σ.block ∈ bs := by
  obtain ⟨blk, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  exact List.mem_of_find?_eq_some hf

section
variable {Xf : Type} {F : FileDescription Xf} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {Bk : ProverCoinCounts}
  {V W Y Pb : Type}

/-- **At a written place every seated side of the row** has one member, fits, and no entry spends a coin of its part. -/
theorem written_side (hF : PlanAlike WP F) (hk : bookWhole F p0 p1 p2 M = .ok Bk)
    (hp : F.placesOk = true) (J : CloseJob W) (hQ : J.pub.par ∈ writtenClosings) (fs : List (Fall F.S₁))
    (σ : Side F.S₁ F.Cl V W Y Pb)
    (hσ : Side.seated F.first.blocksInOrder (closePlace J.pub.par) (closingPairs J) fs = some σ) :
    σ.members = [closeAt true J] ∧ σ.fits = true ∧ ∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = [] := by
  have h : CloseSeated σ J := closeSeated_of_seated hσ (written_rounds hF hQ) (written_plan hQ)
  refine ⟨slot_members h, slot_fits h, fun q => ?_⟩
  refine bookWhole_spent_nil hk hp (seated_mem hσ) (fun r hr => ?_) 0 q
  rw [h.rounds] at hr
  exact close_no_seed _ r hr

end

section
variable {W₀ Rc Xi Tr X Xf : Type} {F : FileDescription Xf} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
  {Bk : ProverCoinCounts}

/-- **At a written place the laid row meets `Good`.** -/
theorem written_hand (hF : PlanAlike WP F) (hk : bookWhole F p0 p1 p2 M = .ok Bk)
    (hp : F.placesOk = true) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (ord : List Place) (chain firstTree : Nat)
    (fs : List (Fall F.S₁)) (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) (hQ : Q ∈ writtenClosings)
    (T : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Sd : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    ∀ σ, ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
      ∃ A' B', Good pre φ σ Bk ord chain firstTree A' B'
        ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd F.first.blocksInOrder).On
        ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd F.first.blocksInOrder).bud :=
  closing_hand pre φ ord chain firstTree F.first.blocksInOrder fs readers rows stAt Z G Q T Sd (written_plan hQ)
    fun σ h => written_side hF hk hp (closingJob readers rows stAt Z G Q) hQ fs σ h

/-- **K10's share of the rule's hypothesis on On**: the row's condition asks nothing. -/
theorem closing_on {S Cl : Type} (T₀ : Local W₀ Rc Xi Tr → Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (Sd : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (bs : List (Block S Cl)) (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) (b : Nat) (len : Nat → Nat → Nat) :
    OnFromS T Said ((closingRow (X := X) readers rows stAt Z G Q).lay T₀ Sd bs) b len := by
  intro σ _ u _ k m E ca front _ _ _ hf
  exact Bool.noConfusion hf

/-- **The row's On holds at every member, carried value, stand and front**: the form that an `OnAtRun` clause takes. -/
theorem closing_on_always {S Cl : Type} (T₀ : Local W₀ Rc Xi Tr → Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Sd : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (bs : List (Block S Cl)) (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) :
    ∀ u ca m front, ((closingRow (X := X) readers rows stAt Z G Q).lay T₀ Sd bs).On u ca m front := by
  intro u ca m front hf
  exact Bool.noConfusion hf

/-- **K10's share of the hypothesis on bud**: the row's bound asks nothing. -/
theorem closing_bud {S Cl : Type} (T₀ : Local W₀ Rc Xi Tr → Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Sd : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (bs : List (Block S Cl)) (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) (n : Nat) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    ((closingRow (X := X) readers rows stAt Z G Q).lay T₀ Sd bs).bud n ds asks := trivial

end

end ProofFile.Honest.K10.Slot

#print axioms ProofFile.Honest.K10.Slot.closing_on
#print axioms ProofFile.Honest.K10.Slot.closing_on_always
#print axioms ProofFile.Honest.K10.Slot.closing_bud
#print axioms ProofFile.Honest.K10.Slot.close_no_seed
#print axioms ProofFile.Honest.K10.Slot.seated_mem
#print axioms ProofFile.Honest.K10.Slot.written_side
#print axioms ProofFile.Honest.K10.Slot.written_hand
