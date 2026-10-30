-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/SeedStateAtK10.lean: THE SIX PREMISES ON THE VERIFIER's STATE OF
  seed_field (Johnson/LPFE1R/SeedAtSeat.lean: the sendings' invariant K1.SeedIs at every member of a
  written list), IN FRONT OF K10's PLACE OF EVERY LINK l < 25, FROM THE ONE HEAD (P5J.AtMgA) AT o :=
  OnBytes.secondHashFunction AND WHAT IS AT HAND WHERE K10's LAW SPENDS IT: the table's promise at ixK10 l,
  "reached" there, no mark. A joining.


THE NAMES.
sampled_is: the tenants whose pin is open are read off the plan's seats alone: sampledIn at the
  table's numbers is sampledIn at numbersOf of the plan's seats.
heldK10B, held_k10_all: a closed fact at the written seats of the full size, by Lean's kernel: at
  each l < 25 the seat of every place of the l-th written list is among the tenants whose pin is
  open at ixK10 l.
ix_le: ixK10 l ≤ 353 at l < 25.
seed_state: **the head · l < 25 · the promise at ixK10 l · reached there · no mark ⊢ the six**: (1)
  reached under "below", within the part in front · (2) the state's codes are At.cs Zp · (3) bookAt
  at the table's numbers and the place At.ps[ixK10 l]? · (4) atFirstSeats Ld at every Ld that
  laidAtCodes returns · (5) atFirstShapes at msgsOfChain · (6) smpHeld at the seat of every place of
  the l-th written list.

WHENCE. (1) is the first half of "reached"; 353 is Meaning.Carry.front_len. (2)
  recAll_all. (3) and (6) stand in the promise itself; the meaning's "held" is smpHeld by
  definition. (4) and (5) seatsCarried_field and msgShapes_field
  (Johnson/IMR/SeatsField.lean), their test on the sendings by hB_paid off the door's row
  madeRow.
Limits. The promise is a premise. NO MEMBER. THAT heldK10B CAN SAY FALSE IS SHOWN BY NO LINE HERE:
  negative lines are left to other files. At l = 0: the six-list, not the five-list. The full size
  alone. At OnBytes.secondHashFunction alone. It leans on the door's issue 2. A raised limit stands in this
  file (maxRecDepth 100000). Nothing on soundness.
-/
import Johnson.LPFE1R.SeedAtSeat
import Johnson.LPFE1R.SeedPublicFull
import Johnson.LPFK10R.SitsAll
import Johnson.IMR.SeatsField
import Johnson.IMR.EndFiveMade
import Johnson.IMR.AtReach
import Johnson.IMR.RootsWhole
import Johnson.ToldDescR.SmpWalkOpen
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.P5J.NAtReaders
import Johnson.P5T.FenceAtMg
import Johnson.P5T.CoreAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.P2Notices
open OnBytes OnBytes.Slice
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit)
open VerifiableInference.Desc (Chain smpHeld)
open VerifiableInference.Desc.First (bookAt sampledIn samplesHeld openSets start)
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (laidAtCodes msgsOfChain atFirstSeats atFirstShapes)
open _root_.Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (frontOf)
open LPFK10 (ixK10)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The tenants whose pin is open are read off the plan's seats alone. -/
theorem sampled_is (O : List First.Item) :
    sampledIn (At.N Zp cF) O = sampledIn (P5T.numbersOf (At.pseats Zp)) O := rfl

/-- The test at the written seats: every place's seat is among the tenants whose pin is open. -/
def heldK10B : Bool :=
  (List.range 25).all fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      (sampledIn (P5T.numbersOf P5T.psFull)
        ((openSets fullLinks At.ps (start fullLinks))[ixK10 l]?.getD [])).contains
        (seatK10 (linksFullLit.getD l []) P5T.psFull l i)

/-- **It accepts**: by Lean's kernel. -/
theorem held_k10_all : heldK10B = true := by decide +kernel

theorem ix_le {l : ℕ} (hl : l < 25) : ixK10 l ≤ 353 := by
  have k : ∀ l ∈ List.range 25, ixK10 l ≤ 353 := by decide
  exact k l (List.mem_range.2 hl)

/-- **THE SIX PREMISES ON THE STATE, IN FRONT OF K10's PLACE OF EVERY LINK.** -/
theorem seed_state (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    {a : (ProofFile.InstPub × TS) ×
      (Frame.E (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)).Str}
    (ha : onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) a)
    (hr : h.toAtMg.rch (ixK10 l) a) (hm : ¬ a.1.2.failed ≠ none) :
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (ixK10 l) (a.1.1, a.1.2) ∧
      ixK10 l ≤ (frontOf cF).length ∧
      a.1.2.st.codes = At.cs Zp ∧
      bookAt (At.N Zp cF) At.ps[ixK10 l]? a.1.2 = true ∧
      (∀ Ld, laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld →
        atFirstSeats Ld a.1.2 = true) ∧
      atFirstShapes (msgsOfChain Zp.made.proof.1) a.1.2 = true ∧
      ∀ i : Fin (linksFullLit.getD l []).length,
        smpHeld a.1.2.st a.1.2.book (seatK10 (linksFullLit.getD l []) (At.pseats Zp) l i).1
          (seatK10 (linksFullLit.getD l []) (At.pseats Zp) l i).2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hu : a.1.2.failed = none := not_not.1 hm
  have hp := ToldDesc.open_planOk O h.laid.planOk
  have e : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (ixK10 l) (a.1.1, a.1.2) := hr.1
  have e' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (ixK10 l) (a.1.1, a.1.2) := reach_raw e
  have hB := Meaning.K2.hB_paid h.scope h.laid.planOk h.toAtMg.pins.1 Bs base _ _ O
  have hRch : ∀ k (b : ProofFile.InstPub × TS), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k b → ∃ rs cols r q,
      foldBlocks 0 (cF.blocksInOrder.take k) (ProofFile.startS Zp b.1) rs cols = .ok (b.2, r, q) := by
    intro k b hb
    obtain ⟨-, rs, cols, f⟩ := hb.fold
    exact ⟨rs, cols, [], [], f⟩
  obtain ⟨-, hq⟩ := ha
  rcases hq with hf | ⟨hb, hs, -⟩
  · exact absurd hf hm
  · simp only [Bool.and_eq_true] at hb
    refine ⟨e, ?_, (Meaning.K2.recAll_all h.scope h.reads O hp e' hu).codes, hb.2, ?_, ?_, ?_⟩
    · rw [Meaning.Carry.front_len h.scope h.reads O]
      exact ix_le hl
    · intro Ld hLd
      exact IM.seatsCarried_field h.scope h.reads O (fun k b => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k b)
        (fun b => b) hRch h.laid.planOk hB hLd (ixK10 l) (a.1.1, a.1.2) e' hu
    · exact IM.msgShapes_field h.scope h.reads O (fun k b => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k b)
        (fun b => b) hRch h.laid.planOk hB (ixK10 l) (a.1.1, a.1.2) e' hu
    · intro i
      have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
      have k := List.all_eq_true.1 (List.all_eq_true.1 held_k10_all l (List.mem_range.2 hl)) i
        (List.mem_finRange i)
      have hx : seatK10 (linksFullLit.getD l []) (At.pseats Zp) l i ∈ sampledIn (At.N Zp cF)
          ((openSets fullLinks At.ps (start fullLinks))[ixK10 l]?.getD []) := by
        rw [sampled_is, e1]
        exact List.contains_iff_mem.1 k
      unfold samplesHeld at hs
      exact List.all_eq_true.1 hs _ hx

end VerifiableInference.Desc.P2Notices

#print axioms VerifiableInference.Desc.P2Notices.sampled_is
#print axioms VerifiableInference.Desc.P2Notices.held_k10_all
#print axioms VerifiableInference.Desc.P2Notices.ix_le
#print axioms VerifiableInference.Desc.P2Notices.seed_state
