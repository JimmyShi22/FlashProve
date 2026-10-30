-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SLotRows.lean: UNDER THE LIBRARY's HEAD (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): Good (Honest/Side.lean) AT EVERY ROW OF THE LOT k5SLot
(Honest/K5/Law/SLot5.lean) AT THE DESCRIPTION's OWN PUBLIC PART AND GROUND: the seat's two facts
that k5_good_seated_head asks hold at whatever the lot's maker of seats yields there. Statements
with their proofs.

  row_of_lot     a row of the lot is r5 at a seat that seatAtK yields at one of the ground's places
  seat_facts     CONDITIONAL: what seatAtK yields at (l, nm, g) bears the segment's number l and the
                 shape and numbers of the ground's plan of group g
  k5_good_rows   **Good at the side that Side.seated makes of each row of the lot**, at whatever
                 falls and every pre

THE PREMISES THAT STAY, BY NAME. h: the head: A HYPOTHESIS · G is the ground that the description's
maker makes of the public part · hk: no entry of the book names a part of a place of the kind K5 as
owner.

WHAT IT SAYS, AND WHAT NOT. THE LOT MAY HAVE FEWER THAN TWELVE ROWS, OR NONE: WHERE seatAtK YIELDS
NOTHING (the ground has no plan of the group; the table of steps lacks the place's first step; one
of the three tests on the public data fails, and the third hangs on the letter keyOf) THERE IS NO
ROW AND NOTHING IS SAID. THAT IT YIELDS IS NOT SHOWN IN THIS FILE: at a keyOf of wrong lengths every
row falls away in silence and k5_good_rows holds of the empty list. Under the head the third test's
yes gives the other two, and seatAtK yields (seatAt_returns_at_head,
Honest/K5/Law/SeatReturns.lean).
The lot has its twelve rows under the head, hG and KeysFitAll (rows_twelve,
Honest/K5/Law/SLotTwelve.lean). At the reader keyOfK3 KeysFitAll's clause is had under the head and
hG, group by group (keysFit_K3, Honest/K5/Law/KeysFitK3.lean). No file of this library joins the
two. NONE OF THE THREE FILES IS IMPORTED HERE.
At a row
that is there Side.seated makes a side (seated_head, Honest/K5/Law/GoodHead.lean). What Good says:
see the heads of Honest/K5/Law/GoodPaid.lean and GoodHead.lean: AT A := B := THE EMPTY SENTENCE
(False); fresh IS EMPTY; exact IS THE SPENDER's HALF ALONE, one part at a time.

Limits. The rows are asked at the blank ground, as the frame asks them. The library's full size
alone. No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SLot5
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatedAt
import Johnson.Desc.First.Att.Row.K5RowSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place)
open P5J (AtMgA TS)

variable {W₀ Rc Xi Tr X Pb : Type}

/-- A row of the lot is r5 at a seat that the maker yields at one of the ground's places. -/
theorem row_of_lot {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)} {Zp : Pub} {G : Ground}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) :
    ∃ y ∈ H2K5.k5Places G, ∃ Y, seatAtK keyOf Zp G y.1 y.2.1 y.2.2 = some Y ∧ r = r5 cells Y := by
  obtain ⟨y, hy, e⟩ := List.mem_filterMap.1 hr
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨y, hy, Y, hY, rfl⟩

/-- **What the maker yields bears the segment's number and the plan's shape and numbers.**
CONDITIONAL: it yields. -/
theorem seat_facts {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)} {Zp : Pub}
    {G : Ground} {l : Nat} {nm : String} {g : Nat} {Y : Seat5}
    (hY : seatAtK keyOf Zp G l nm g = some Y) :
    Y.link = l ∧ ∃ A, G.W.A[g]? = some A ∧ Y.P = ⟨A.S, A.own⟩ := by
  obtain ⟨A, base, hA, -, rfl, -, -⟩ := seatAt_spec (seatAtK_spec hY).1
  exact ⟨rfl, A, hA, rfl⟩

/-- **Good at every row of the lot, beside the description's own member, AT A := B := THE EMPTY
SENTENCE (False); fresh IS EMPTY.** BY TYPE IT IS WHAT THE FRAME's RULE TAKES FOR THE FIELD good OF
THE STRUCTURE Owed AT THESE ROWS; BY WEIGHT IT SAYS fits, exact (THE SPENDER's HALF) AND AN EMPTY
fresh, AND NOTHING ON plays OR acc. THE RULE IS file_owed_rows (Honest/Thread/Rows.lean): it
takes such a term through hand_of_house (Honest/Thread/RowsMore.lean), at the pre that it makes and
whatever A and B (this one holds at every pre), and UNDER ITS OTHER PREMISES it makes the field,
which asks Good at other A and B, itself.
THE LOT MAY HAVE FEWER THAN TWELVE ROWS, OR NONE: WHERE seatAtK
YIELDS NOTHING THERE IS NO ROW AND NOTHING IS SAID. CONDITIONAL: see the head. pre is tied to no
description, not to this one either; at each pre this says of exact no more than msForm_paid,
loneForm_paid and quietForm_paid (Honest/K5/Law/GoodPaid.lean).
No move of this kind reads what it is handed as seen (Honest/K5/Law/NoneSeen5.lean, with that file's
limits; what is seen holds the opened columns too: Seen, Honest/Frame.lean). The simulators that
simsOf lays beside the parts (sumSim, quietSim, scalarsSim) read none of the opened columns that the
front holds: a reading of their code, with theorems for parts of it (tells_scalars; tell_toSim). The
rest is a reading of the frame's text: play and shows reach these columns through a move's say
alone; in Good they stand besides only in premises that tie the state to the front or test
positions, and in the fields plays and acc, which are empty here, and in On, which is True here. So,
as a reading, this theorem's statement says the same at every value of the opened columns. -/
theorem k5_good_rows {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E))
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (fs₀ : List (Fall TS))
    (hk : ∀ e ∈ Bk.ahead, e.owner.place.kind ≠ .K5) :
    ∀ r ∈ (k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOf).rows Zp G,
      ∀ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀ →
        Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
          r.On r.bud := by
  intro r hr σ₀ hσ
  obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hl, A, hA, hP⟩ := seat_facts hY
  have ha : (P5J.At.X Zp).A[g]? = some A := by
    rw [← hA, H2K5.Row.ground_W hG]
    rfl
  exact k5_good_seated_head h (List.mem_range.1 hg) ha hl hP pre φ Bk ord chain firstTree fs₀ hσ
    fun e he hc => hk e he (by rw [hc]; rfl)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.row_of_lot
#print axioms ProofFile.Honest.K5.seat_facts
#print axioms ProofFile.Honest.K5.k5_good_rows
