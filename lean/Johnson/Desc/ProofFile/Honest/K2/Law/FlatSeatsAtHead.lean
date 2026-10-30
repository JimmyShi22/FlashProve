-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FlatSeatsAtHead.lean: NUMBERS OF A PUBLIC PLAN: UNDER THE
LIBRARY's HEAD AND THE OPENING THE SEATS THAT THE FIRST CHAIN's FLAT LIST DECLARES (`flatSeats`,
Honest/Thread/JoinFit.lean, of other authors) ARE JUST THE SEATS OF THE PLAN's LIST OF THE FIRST
CHAIN (`P5J.At.seats`, Johnson/P5J/LettersAt.lean). The one half is the field whole of `JoinFit` at
that list of seats. A guest in this folder: no term of the kind occurs. One definition with code;
closed facts by Lean's kernel, one of them a control; statements with their proofs.

  `flatSeatsOf`     `flatSeats`'s text over what the blocks tell, block by block
  `flatMap_told`    what a list of blocks tells, laid flat
  `flatSeats_told`  `flatSeats` bs is that, at the blocks' own tellings
  `flatSeatsW`      BY LEAN's KERNEL, at the written tellings (`toldFull`,
                    Johnson/Top/H0/K2Ties/ToldAt.lean) and the written seats (`P5T.psFull`): 199
                    seats are declared, no two are one, each stands in the plan's list; the plan's
                    list has 199, and each of them is declared. A CONTROL: with the plan's last seat
                    struck the first test says no
  `flatSeats_at_head`, `planSeats_at_head`   under the head (and, for the first, the opening) the
                    flat list's seats and the plan's list are the written ones
  `whole_at_head`   THE FIELD whole: every seat that the flat list declares stands in the plan's
                    list
  `declared_at_head`   the converse: every seat of the plan's list is declared

By: `toldOf_of_cut` (ToldAt.lean) · `tests_at_head` (Johnson/Desc/K2/Honest/Returns/UnderHead.lean)
· `P5J.AtMg.seats` (Johnson/P5T/CoreAtMg.lean).

NEAR, of other authors: `declared_head` (AtFullSide/K1/DeclaredSeatsAtHead.lean; not imported): the
sentence of `whole_at_head` under the head alone, without the opening: whoever wants the field whole
calls that one.

Limits. TREES' AND TENANTS' NUMBERS ALONE: no lot, coin, input or run occurs. The first chain alone.
The head and the opening are premises. The full size; the format's second hash function. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.P5T.CoreAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Oracle)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Ties (toldFull toldOf_of_cut)
open VerifiableInference.Desc.K2.Honest.Returns (tests_at_head)
open ProofFile.Honest.FirstThread (flatSeats)
open P5T (psFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- `flatSeats`'s text over what the blocks tell, block by block. -/
def flatSeatsOf (told : List (List Oracle)) : List (Nat × Nat) :=
  told.flatten.zipIdx.flatMap fun o => (List.range o.1.tenants.length).map fun t => (o.2, t)

/-- What a list of blocks tells, laid flat. NEAR: `told_flat` (ReadStated.lean of this folder; not
imported: it stands over files that this one does not want): the same equation, read the other way.
-/
theorem flatMap_told {St Cl : Type} (bs : List (Block St Cl)) :
    (bs.flatMap fun blk => blk.oracles.flatMap id) =
      (bs.map fun x => x.oracles.flatten).flatten := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ih, List.flatMap_id]

/-- **`flatSeats` is that text at the blocks' own tellings.** -/
theorem flatSeats_told {Cl : Type} (bs : List (Block S Cl)) :
    flatSeats bs = flatSeatsOf (bs.map fun x => x.oracles.flatten) := by
  unfold flatSeats flatSeatsOf
  rw [flatMap_told]

set_option maxRecDepth 1000000 in
/-- **At the written tellings and the written seats**; a control that says no. -/
theorem flatSeatsW :
    (flatSeatsOf toldFull).length = 199 ∧ (flatSeatsOf toldFull).Nodup ∧
      ((flatSeatsOf toldFull).all fun s => (psFull.map fun p => (p.j, p.t)).contains s) = true ∧
      psFull.length = 199 ∧
      ((psFull.map fun p => (p.j, p.t)).all fun s => (flatSeatsOf toldFull).contains s) = true ∧
      ((flatSeatsOf toldFull).all fun s =>
        (psFull.dropLast.map fun p => (p.j, p.t)).contains s) = false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- Under the head and the opening the flat list's seats are the written ones. -/
theorem flatSeats_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : flatSeats cF.blocksInOrder = flatSeatsOf toldFull := by
  rw [flatSeats_told]
  exact congrArg flatSeatsOf (toldOf_of_cut (tests_at_head h O).2.1)

/-- Under the head the plan's list of the first chain's seats is the written one. -/
theorem planSeats_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF) :
    P5J.At.seats Zp = psFull.map fun p => (p.j, p.t) := by
  unfold P5J.At.seats P5J.At.pseats
  rw [h.seats]

/-- **THE FIELD whole OF `JoinFit` AT THE PLAN's LIST: every seat that the flat list declares stands
in it.** -/
theorem whole_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : ∀ s ∈ flatSeats cF.blocksInOrder, s ∈ P5J.At.seats Zp := by
  intro s hs
  rw [flatSeats_at_head h O] at hs
  rw [planSeats_at_head h]
  exact List.contains_iff_mem.1 (List.all_eq_true.1 flatSeatsW.2.2.1 s hs)

/-- **The converse: every seat of the plan's list is declared.** -/
theorem declared_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : ∀ s ∈ P5J.At.seats Zp, s ∈ flatSeats cF.blocksInOrder := by
  intro s hs
  rw [planSeats_at_head h] at hs
  rw [flatSeats_at_head h O]
  exact List.contains_iff_mem.1 (List.all_eq_true.1 flatSeatsW.2.2.2.2.1 s hs)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.flatSeatsOf
#print axioms ProofFile.Honest.K2.Law.flatMap_told
#print axioms ProofFile.Honest.K2.Law.flatSeats_told
#print axioms ProofFile.Honest.K2.Law.flatSeatsW
#print axioms ProofFile.Honest.K2.Law.flatSeats_at_head
#print axioms ProofFile.Honest.K2.Law.planSeats_at_head
#print axioms ProofFile.Honest.K2.Law.whole_at_head
#print axioms ProofFile.Honest.K2.Law.declared_at_head
