-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SLot5.lean: THE ROWS OF THE ATTENTION SEGMENTS' OWN ROUNDS
(kind K5: the label of that sub-protocol in the description) IN THE FORM IN WHICH THE FRAME TAKES A
LOT's ROWS (SLot, Unlettered, Honest/Thread/Rows.lean): each row with its simulators, its On and its
bud; the one equation that ties that lot to the lot of halves (k5LotK, Honest/K5/KeysFit.lean); and
Good at the side that Side.seated makes of such a row. Definitions with code, and statements with
their proofs.

  Row5, r5       a row without letters: the place; the parts, each with the form of a simulator
                 beside it (k5Pairs); On := True; bud := k5Bud
  k5SLot         the lot: a row at every attention segment whose public data fit
  sims_length, r5_half   as many simulators as shapes; the row's half is k5Half
  k5SLot_toHLot  **k5SLot.toHLot = k5LotK**
  k5_good_seated CONDITIONAL: Good at Side.seated's own value, at a list of members bs, at whatever
                 falls and every pre: under K5Block, hx and hk (k5_good_paid,
                 Honest/K5/Law/GoodPaid.lean)
  k5_good_seated_head   CONDITIONAL: the same at the description's own flat list, under the
                 library's head: K5Block and hx are shown there (k5_good_head,
                 Honest/K5/Law/GoodHead.lean)

THE LOT MAY HAVE FEWER THAN TWELVE ROWS, OR NONE: k5SLot has a row only where seatAtK yields (the
ground has a plan of the group; the table of steps has the place's first step; three tests on the
public data, the third of which hangs on the letter keyOf): WHERE IT YIELDS NOTHING THERE IS NO ROW,
WITHOUT A WORD. THAT IT YIELDS AT ANY PLACE IS NOT SHOWN HERE. k5SLot_toHLot holds whatever the
number of rows, at the empty lot too: no distribution occurs in it.

What Good says here, and what not: see the heads of these two files: AT A := B := THE EMPTY SENTENCE
(False); fresh IS EMPTY; exact IS THE SPENDER's HALF ALONE, one part at a time.

Limits. That a row of the lot at the real public part has the seat's two facts of
k5_good_seated_head is not shown here: it is the matter of Honest/K5/Law/SLotRows.lean, under the
library's head, at the blank ground, at the rows that the lot has. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.GoodHead
import Johnson.Desc.ProofFile.Honest.K5.KeysFit
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (shapes)
open P5J (AtMgA TS)

variable {W₀ Rc Xi Tr X Pb : Type}

/-! ## 1 The lot -/

/-- The type of a row without letters at the first chain's own input. -/
abbrev Row5 (W₀ Rc Xi Tr X Pb : Type) : Type :=
  Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb

/-- **A row without letters.** -/
def r5 (cells : Tr → Cells) (Z : Seat5) : Row5 W₀ Rc Xi Tr X Pb :=
  ⟨Z.place, k5Pairs cells Z, fun _ _ _ _ => True, k5Bud⟩

/-- **The lot's rows**: a row at every attention segment whose public data fit. keyOf: the key
points' reader at a segment. -/
def k5SLot (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    SLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb :=
  { name := "K5: the attention segments' own rounds"
    rows := fun Z G => (H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map (r5 cells) }

/-- As many simulators as shapes. -/
theorem sims_length (a : Place) (x : OnBytes.Params.AttentionRounds) :
    (simsOf (Pb := Pb) a x).length = (shapes x).length := by
  unfold simsOf
  rw [List.length_map, List.length_zipIdx]

/-- The row's half is the lot's half. -/
theorem r5_half (cells : Tr → Cells) (Z : Seat5) :
    (r5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells Z).half = k5Half cells Z := by
  have hn : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.length =
      (shapes Z.P.x).length := by
    have e := congrArg List.length (half_cut (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z)
    rw [List.length_map] at e
    rw [e]
    exact List.length_map _
  exact half_of_zip Z.place (k5Half cells Z).parts (simsOf Z.place Z.P.x) _ _
    (by rw [hn, sims_length])

/-- **THE ONE EQUATION: the lot of rows, its simulators, On and bud left off, is the lot of
halves.** No premise. -/
theorem k5SLot_toHLot (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    (k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOf).toHLot =
      k5LotK cells keyOf := by
  unfold SLot.toHLot k5SLot k5LotK
  congr 1
  funext Z G
  rw [List.map_filterMap]
  congr 1
  funext y
  rw [Option.map_map]
  congr 1
  funext Y
  exact r5_half cells Y

/-! ## 2 Good at the side that Side.seated makes -/

/-- **Good at Side.seated's own value, at whatever falls, AT A := B := THE EMPTY SENTENCE (False);
fresh IS EMPTY.** CONDITIONAL: on K5Block at the member that stands there, hx and hk. pre is tied to
no description, not to bs either; at each pre this says of exact no more than msForm_paid,
loneForm_paid and quietForm_paid (Honest/K5/Law/GoodPaid.lean). No move of this kind reads what it
is handed as seen (Honest/K5/Law/NoneSeen5.lean, with that file's limits; what is seen holds the
opened columns too: Seen, Honest/Frame.lean). The simulators that simsOf lays beside the parts
(sumSim, quietSim, scalarsSim) read none of the opened columns that the front holds: a reading of
their code, with theorems for parts of it (tells_scalars; tell_toSim). The rest is a reading of the
frame's text: play and shows reach these columns through a move's say alone; in Good they stand
besides only in premises that tie the state to the front or test positions, and in the fields plays
and acc, which are empty here, and in On, which is True here. So, as a reading, this theorem's
statement says the same at every value of the opened columns. -/
theorem k5_good_seated {S Cl : Type} {cells : Tr → Cells} {Z : Seat5} {p : P.Par}
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (bs : List (Block S Cl)) (fs₀ : List (Fall S))
    {σ₀ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated bs (r5 cells Z : Row5 W₀ Rc Xi Tr X Pb).place
      (r5 cells Z).row fs₀ = some σ₀)
    (hB : K5Block σ₀.block Z p)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z.place) :
    Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (r5 cells Z).On (r5 cells Z : Row5 W₀ Rc Xi Tr X Pb).bud := by
  obtain ⟨b, -, e⟩ := Option.map_eq_some_iff.1 hσ
  subst e
  exact k5_good_paid pre φ Bk ord chain firstTree hB rfl hx hk

/-- **The same beside the description's own member, under the library's head.** BY TYPE IT IS WHAT
THE FRAME's RULE TAKES FOR THE FIELD good OF THE STRUCTURE Owed AT THIS ROW; BY WEIGHT IT SAYS fits,
exact (THE SPENDER's HALF) AND AN EMPTY fresh, AND NOTHING ON plays OR acc. THE RULE IS
file_owed_rows (Honest/Thread/Rows.lean): it takes such a term through hand_of_house
(Honest/Thread/RowsMore.lean), at the pre that it makes and whatever A and B (this one holds at
every pre), and UNDER ITS OTHER PREMISES it makes the field, which asks Good at other A and B,
itself. CONDITIONAL: the head; g
is below 12; a is the plan of group g; the seat's two facts; hk. pre is tied to no description, not
to this one either; at each pre this says of exact no more than msForm_paid, loneForm_paid and
quietForm_paid (Honest/K5/Law/GoodPaid.lean). No move of this kind reads what it is handed as seen
(Honest/K5/Law/NoneSeen5.lean, with that file's limits; what is seen holds the opened columns too:
Seen, Honest/Frame.lean). The simulators that simsOf lays beside the parts (sumSim, quietSim,
scalarsSim) read none of the opened columns that the front holds: a reading of their code, with
theorems for parts of it (tells_scalars; tell_toSim). The rest is a reading of the frame's text:
play and shows reach these columns through a move's say alone; in Good they stand besides only in
premises that tie the state to the front or test positions, and in the fields plays and acc, which
are empty here, and in On, which is True here. So, as a reading, this theorem's statement says the
same at every value of the opened columns. -/
theorem k5_good_seated_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells}
    {Z5 : Seat5} (hl : Z5.link = 2 * g + 1) (hP : Z5.P = ⟨a.S, a.own⟩)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (fs₀ : List (Fall TS))
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder (r5 cells Z5 : Row5 W₀ Rc Xi Tr X Pb).place
      (r5 cells Z5).row fs₀ = some σ₀)
    (hk : ∀ e ∈ Bk.ahead, e.owner.place ≠ Z5.place) :
    Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (r5 cells Z5).On (r5 cells Z5 : Row5 W₀ Rc Xi Tr X Pb).bud :=
  k5_good_head h hg ha hl hP pre φ Bk ord chain firstTree fs₀ hσ hk

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sims_length
#print axioms ProofFile.Honest.K5.r5_half
#print axioms ProofFile.Honest.K5.k5SLot_toHLot
#print axioms ProofFile.Honest.K5.k5_good_seated
#print axioms ProofFile.Honest.K5.k5_good_seated_head
