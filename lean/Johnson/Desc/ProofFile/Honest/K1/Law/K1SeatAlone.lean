-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1SeatAlone.lean: THE SHARED "SENDING" (the kind K1): WHO ELSE
SITS AT A SEAT OF OURS: NOBODY: UNDER THE LIBRARY's HEAD: A SEAT OF THE PLAN's LIST (all three
chains') AT THE TREE AND TENANT OF A MESSAGE OF THE OPENING OR OF ONE OF THE FIFTY LATER SENDINGS IS
THAT MESSAGE's: ITS SENDING's NUMBER, ITS PLACE IN THE SENDING, ITS LINK AND MOMENT ARE OURS. PUBLIC
DATA ALONE: plans, the plan's list of seats, numbers. Two theorems; no definition.

  - k1Seat_alone_two: UNDER h (the library's head: A HYPOTHESIS), O, n below the opening's plan's
    number of messages: a member q of the plan's list with (q.j, q.t) our seat has q.send = 0, q.idx
    = n and q.seg = some (0, 0).
  - k1Seat_alone_fifty: the like at each of the fifty (hl : l < 25; d): q.send = 3 * l + momL d,
    q.idx = n, q.seg = some (l, momL d).

For whom. The tie: PadLotsAgree (Honest/Thread/ScriptLots.lean) between our lots of pads and another
sender's bites only at one tree and tenant. A lot of pads that stands at a seat of ANOTHER sending
of the plan's list is at none of our 55 seats. THAT ANOTHER HOUSE's LOTS STAND AT SEATS OF ITS OWN
SENDINGS IS THAT HOUSE's TO SAY: no text of another house's is imported.

The road. Just one seat of the plan's list stands at our seat, with its sending and place (seat_two,
seat_fifty, one_of_filter: K1NumAtHead.lean); its link and moment: segW2, segW50 (K1NumOthers.lean)
through find_two, find_fifty (K1NumApart.lean). No closed fact of its own. Kin in the library:
seatsAllFull_apart (Johnson/P5T/PlanSeatsFull.lean): no tree and tenant stands twice in the written
list.

Limits. 51 PLACES: W's sending is not here. THE FULL SIZE ALONE. Nothing is said of the Script, nor
of any lot. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumOthers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (momL fifty_of)
open P5T (PSeat)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **AT NUMBER 2: WHO SITS AT A SEAT OF THE OPENING's IS THAT MESSAGE's OWN SEAT.** -/
theorem k1Seat_alone_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size) {q : PSeat}
    (hm : q ∈ P5J.At.pseatsAll Zp)
    (e : (q.j, q.t) = seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n) :
    q.send = 0 ∧ q.idx = n ∧ q.seg = some (0, 0) := by
  obtain ⟨p, f, h1, h2, -⟩ := seat_two h O hn
  have hq : q = p := (one_of_filter f).2.2.1 q hm (by
    show (q.j == _ && q.t == _) = true
    rw [← e]
    simp)
  subst hq
  obtain ⟨s, f1, g1⟩ := find_two h O hn
  obtain rfl : q = s := Option.some.inj ((one_of_filter f).2.2.2.symm.trans f1)
  rw [K1.eG_atAll h O (K1.pin1_atAll h)] at hn
  have c := List.all_eq_true.1 segW2 n (List.mem_range.2 hn)
  rw [g1] at c
  exact ⟨h1, h2, eq_of_beq c⟩

/-- **AT EACH OF THE FIFTY: THE LIKE.** -/
theorem k1Seat_alone_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {n : ℕ}
    (hn : n < (K1.parL Zp Bs.G₀ l d).sent.size) {q : PSeat}
    (hm : q ∈ P5J.At.pseatsAll Zp)
    (e : (q.j, q.t) = seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) n) :
    q.send = 3 * l + momL d ∧ q.idx = n ∧ q.seg = some (l, momL d) := by
  obtain ⟨p, f, h1, h2, -⟩ := seat_fifty h O hl d hn
  have hq : q = p := (one_of_filter f).2.2.1 q hm (by
    show (q.j == _ && q.t == _) = true
    rw [← e]
    simp)
  subst hq
  obtain ⟨s, f1, g1⟩ := find_fifty h O hl d hn
  obtain rfl : q = s := Option.some.inj ((one_of_filter f).2.2.2.symm.trans f1)
  rw [parL_written h O l d] at hn
  have c := List.all_eq_true.1 (fifty_of segW50 l hl d) n (List.mem_range.2 hn)
  rw [g1] at c
  exact ⟨h1, h2, eq_of_beq c⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Seat_alone_two
#print axioms ProofFile.Honest.K1.k1Seat_alone_fifty
