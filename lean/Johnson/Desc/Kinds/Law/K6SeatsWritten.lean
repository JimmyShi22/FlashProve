-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6SeatsWritten.lean: THE TEST seatsK6C (Law/K6SeatsTest.lean) ACCEPTS
WHEREVER SIX VALUES OF Z ARE THE WRITTEN ONES AND THREE MORE VALUES ARE AS NAMED. Theorems; two
evaluations by Lean's kernel. On the pattern of Law/HeadViewsSeats.lean.

Why. The test is a function of plain values (Law/K6SeatsView.lean: seatsK6C_view). At the
written values of the codes, the request's shape and layout, the two lists of seats and the proof
file's sendings, Lean's kernel evaluates it: it accepts.

  owsW, placesW, shapesW   the eight labels' owners and names; the listed seats and the shapes of
          the written first chain's oracle messages.
  sorted_written           BY LEAN's KERNEL: the written sendings stand in the order of their
          entries: so sorting leaves them (sentsOf_written, shapes_written). The kernel does not
          evaluate the sorting itself (it is defined by a recursion on a measure).
  **seatsK6V_closed**      BY LEAN's KERNEL: the test at plain values accepts at the written values,
          at 179 and 183 oracle messages in front of the two borders, and at the name (24, "U3").
  seatsK6V_ows             the test at plain values reads the owners below the number of matrices.
  **seatsK6C_of_seats**    so seatsK6C accepts at Z's own values.

WHAT IS LEFT IN FRONT OF IT.
  GIVEN IN THE GOALS' SCOPE BY OTHERS' THEOREMS: W : SeatsWritten Z (seatsWritten_in_scope,
          Goal/Meaning/HeadTestsScope.lean) · hs : Z.made.proof = proofSendsFull (sends_in_scope,
          Goal/Numbers/MadeInScope.lean) · hx : XPart Z.p.X (xPart_in_scope) · h3 (public_third,
          Law/ReadsNamed.lean). These stand under their own premises: another public test
          accepts; the proof file's value is laid.
  GIVEN BY NOTHING YET, THREE VALUES: hb, h0: how many oracle messages the sub-protocols tell in
          front of segment 24's first sending (179) and in front of border 341 (183) · hA: the
          entry number 0 of the built segment 24's list of arrays is (24, "U3").
  hN: the table's numbers' list "sent" at (24, 0) is the seats' own: at the composed meaning's
          closed parameters by the make, BY A READING (two later layers leave that field).
  hL: the listed seats are K12.Door.laidOf at Z's codes and at the first chain's sendings in the
          order of their entries. WHETHER THAT IS THE CLOSED PARAMETER'S OWN TERM IS NOT HELD: its
          author's function (laidAtCodes, Desc/K12/Door/LaidAt.lean) has not been read by us.

No existential quantifier in these statements.
What it does not say. That the three values are so: they were SEEN so in two evaluations at one
stored set of public files. Nothing on any state of the verifier. The full size alone. Nothing on
soundness.
-/
import Johnson.Desc.Kinds.Law.K6SeatsView
import Johnson.Goal.Meaning.HeadTestsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull proofSendsFull)
open P5T (planSeats planSeatsAll numbersOf psFull seatsAllFull)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.FillSent (sentDataOf TreeLook)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (SeatsWritten XPart lettersS)

/-- The eight labels' owners and names. -/
def owsW (a : Nat) : Nat × String :=
  if a = 7 then (22, Meaning.nameOf 7) else (24, Meaning.nameOf a)

/-- A chain's sendings' notices, in the order of their entries. -/
def sentsOf (c : Johnson.G.ChainSends) : List (List OracleNotice) :=
  (c.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent)

/-- The written first chain's sendings' notices, as they are written. -/
def sentsW : List (List OracleNotice) := proofSendsFull.1.sends.map (·.sent)

/-- The listed seats of the written first chain's oracle messages. -/
def placesW : List (Nat × Nat) :=
  ((K12.Door.laidOf proofSizedFull.codes sentsW).map (·.places)).getD []

/-- Their shapes. -/
def shapesW : List OracleShape := K12.Door.msgsOf sentsW

/-- Lean's kernel evaluates it: the written sendings stand in the order of their entries. -/
theorem sorted_written :
    List.Pairwise (fun a b : Johnson.G.Sending => Decidable.decide (a.entry ≤ b.entry) = true)
      proofSendsFull.1.sends := by
  decide +kernel

/-- So sorting leaves them. (The kernel does not evaluate the sorting itself.) -/
theorem sentsOf_written : sentsOf proofSendsFull.1 = sentsW := by
  unfold sentsOf sentsW
  rw [List.mergeSort_of_pairwise sorted_written]

theorem shapes_written : K12.Door.msgsOfChain proofSendsFull.1 = shapesW := by
  unfold K12.Door.msgsOfChain shapesW sentsW
  rw [List.mergeSort_of_pairwise sorted_written]

/-- **Lean's kernel evaluates it.** -/
theorem seatsK6V_closed :
    seatsK6V proofSizedFull.codes layoutFull proofSizedFull.request 8 4 owsW lettersS.arr
      lettersS.num lettersS.sent0 placesW shapesW 179 183 (lettersS.num 24 0) 0
      (some (24, "U3")) = true := by
  decide +kernel

/-- Two tests that agree below n agree on the whole range. -/
theorem all_range_congr {n : Nat} {p q : Nat → Bool} (h : ∀ a, a < n → p a = q a) :
    (List.range n).all p = (List.range n).all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H a ha => (h a (List.mem_range.1 ha)) ▸ H a ha,
    fun H a ha => (h a (List.mem_range.1 ha)).symm ▸ H a ha⟩

/-- The test at plain values reads the owners below the number of matrices alone. -/
theorem seatsK6V_ows (cs : OnBytes.Codes) (lay6 : ReqLayout) (shape : ReqShape) (NM NHf : Nat)
    (ows ows' : Nat → Nat × String) (arr num : Nat → Nat → Nat) (sent0 places : List (Nat × Nat))
    (M : List OracleShape) (base n0 n rb : Nat) (a0 : Option (Nat × String))
    (h : ∀ a, a < NM → ows a = ows' a) :
    seatsK6V cs lay6 shape NM NHf ows arr num sent0 places M base n0 n rb a0 =
      seatsK6V cs lay6 shape NM NHf ows' arr num sent0 places M base n0 n rb a0 := by
  unfold seatsK6V
  congr 2
  refine all_range_congr fun a ha => ?_
  rw [h a ha]

/-- **The test accepts at Z's own values.** -/
theorem seatsK6C_of_seats {Z : ProofFile.Pub} (W : SeatsWritten Z) (hs : Z.made.proof = proofSendsFull)
    (hx : XPart Z.p.X) (h3 : readsOf Z.p.X = 0) (N : Numbers)
    (hN : N.sent 24 0 = (numbersOf (planSeats Z Z.D.1)).sent 24 0) (base : Nat → Nat)
    (trees : Nat → List TreeLook) (hb : base 24 = 179) (n0 : Nat) (h0 : n0 = 183)
    (Lp : K12.Door.Laid) (hL : K12.Door.laidOf Z.first.codes (sentsOf Z.made.proof.1) = some Lp)
    (arrs : Array (Nat × String)) (hA : arrs[0]? = some (24, "U3")) :
    seatsK6C (P5T.arrOf (planSeatsAll Z Z.D)) N Z.p.X Z.first.layout
      (P5T.numOfPlan (planSeatsAll Z Z.D)) (P5T.numOfPlan (planSeatsAll Z Z.D) 24 0) 0
      Z.first.codes Z.first.shape (sentDataOf Z.first.shape base trees) Lp
      (K12.Door.msgsOfChain Z.made.proof.1) arrs n0 = true := by
  have hP : Lp.places = placesW := by
    unfold placesW
    rw [← sentsOf_written, ← W.codes, ← hs, hL]
    rfl
  have hNM : (Meaning.sizesOf Z.p.X 24).NM = 8 := hx.nm
  rw [seatsK6C_view, hNM, hx.nhf, h3, hA, hN, hb, h0, hP, W.codes, W.shape, W.layout, W.seats,
    W.seatsAll, hs, shapes_written]
  have hh : ∀ a, a < 8 → (Meaning.ownerK (Meaning.labAt Z.p.X 24 a),
      Meaning.nameOf (Meaning.ownerA (Meaning.labAt Z.p.X 24 a))) = owsW a :=
    fun a ha => hx.head a ha
  rw [seatsK6V_ows _ _ _ 8 4 _ owsW _ _ _ _ _ _ _ _ _ _ hh]
  exact seatsK6V_closed

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.seatsK6V_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.seatsK6C_of_seats
