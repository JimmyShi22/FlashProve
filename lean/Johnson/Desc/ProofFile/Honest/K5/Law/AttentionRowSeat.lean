-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AttentionRowSeat.lean: from a row of the lot of the attention
segments' own rounds (kind K5: the label of that sub-protocol in the description), under the library's
head (P5J.AtMgA), to the public data behind the row, and the equation of the field exact at that row's side.
Statements with their proofs, and one definition.

  noBook           a book without entries; the field exact does not read the book
  exact_at_side    CONDITIONAL: K5Block, the side's row, the test on the shapes: ExactAtOneTable
  side_at_head     CONDITIONAL: the head: the side that Side.seated makes at a segment's place has
                   K5's row and meets K5Block
  seat_at_place, seat_of_row   CONDITIONAL: the head, hG: a row of the lot with a side comes from public
                   data Y, which the lot's maker of seats yields, at which these three premises hold

Limits. Nothing here is about a run. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (shapes)
open P5J (AtMgA TS)

variable {W₀ Rc Xi Tr X S Cl : Type}

/-- A book without entries. -/
def noBook : ProverCoinCounts := ⟨[], [], [], [], []⟩

/-- **The equation of the field exact at a side with K5's row**, at every list of rounds in front.
CONDITIONAL: hB; hr; hx. The book is not read by that field, so none is a premise. -/
theorem exact_at_side {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    {cells : Tr → Cells} {Z : Seat5} {p : P.Par} (hB : K5Block σ.block Z p)
    (hr : σ.row = k5Pairs cells Z)
    (hx : ((shapes Z.P.x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ExactAtOneTable σ (fun _ _ _ _ => True) k5Bud pre :=
  exactAtOneTable_of_good (k5_good_paid pre .own noBook [] 0 0 hB hr hx fun _ he => by simp [noBook] at he)

section Head
variable {Zf : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Pb : Type}

/-- **At a segment's place the side that Side.seated makes has K5's row and meets K5Block.**
CONDITIONAL: the head; g; a; the seat's two facts; hσ. -/
theorem side_at_head (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x) {g : Nat} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells}
    {Z5 : Seat5} (hl : Z5.link = 2 * g + 1) (hP : Z5.P = ⟨a.S, a.own⟩) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder Z5.place (k5Pairs cells Z5) fs₀ = some σ₀) :
    σ₀.row = k5Pairs cells Z5 ∧ K5Block σ₀.block Z5 (parAt Zp g a) := by
  obtain ⟨b, hf, rfl⟩ := Option.map_eq_some_iff.1 hσ
  have hf' : cF.blocksInOrder.find? (fun b => b.place == (⟨1, some (2 * g + 1), 3, .K5⟩ : Place)) =
      some b := by
    rw [← hl]
    exact hf
  exact ⟨rfl, k5Block_head h hg ha (found_is_member h hf') hl hP⟩

/-- **A row of the lot with a side comes from public data that the lot's maker of seats yields at one
of the ground's places, at which the side has K5's row, meets K5Block and passes the test on the
shapes.** CONDITIONAL: the head; hG; hr; hσ. -/
theorem seat_at_place (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) :
    ∃ y ∈ H2K5.k5Places G, ∃ (Y : Seat5) (p : P.Par), seatAtK keyOf Zp G y.1 y.2.1 y.2.2 = some Y ∧
      r = r5 cells Y ∧ σ₀.row = k5Pairs cells Y ∧ K5Block σ₀.block Y p ∧
      ((shapes Y.P.x).all fun s =>
        match s with
        | .sum k => shapeOk k
        | .one _ => true) = true := by
  obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
  have hy₀ := hy
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨hl, a, hA, hP⟩ := seat_facts hY
  have ha : (P5J.At.X Zp).A[g]? = some a := by
    rw [← hA, H2K5.Row.ground_W hG]
    rfl
  have hgl := List.mem_range.1 hg
  obtain ⟨e1, e2⟩ := side_at_head h hgl ha hl hP hσ
  exact ⟨_, hy₀, Y, _, hY, rfl, e1, e2, shapes_head h hgl ha hP⟩

/-- **The same without the place.** CONDITIONAL: the head; hG; hr; hσ. -/
theorem seat_of_row (h : AtMgA OnBytes.secondHashFunction Zf D r₀ Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {cells : Tr → Cells}
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    {r : Row5 W₀ Rc Xi Tr X Pb} (hr : r ∈ (k5SLot cells keyOf).rows Zp G) {fs₀ : List (Fall TS)}
    {σ₀ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
    (hσ : Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) :
    ∃ (Y : Seat5) (p : P.Par), r = r5 cells Y ∧ σ₀.row = k5Pairs cells Y ∧
      K5Block σ₀.block Y p ∧ ((shapes Y.P.x).all fun s =>
        match s with
        | .sum k => shapeOk k
        | .one _ => true) = true := by
  obtain ⟨_, -, Y, p, -, e1, e2, e3, e4⟩ := seat_at_place h hG hr hσ
  exact ⟨Y, p, e1, e2, e3, e4⟩

end Head

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.exact_at_side
#print axioms ProofFile.Honest.K5.side_at_head
#print axioms ProofFile.Honest.K5.seat_at_place
#print axioms ProofFile.Honest.K5.seat_of_row
