-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Row.lean: CONDITIONAL where it says so. NOT a law on a
distribution, and NOT at a description of the protocol: THE SIDE OF THE SUB-PROTOCOL "the output
head's own rounds", UNDER ONE STRUCTURE OF FOUR PREMISES (three on public data; the fourth, on the
side's row, names wit, the prover's reading of its input): its eight members written out, the field
`fits` of `Good` (Honest/Side.lean), the plan's test on shapes: GENERAL IN THE PLACE's PUBLIC
NUMBERS p: proofs, no evaluation.

  1  `HeadSeated σ wit p at_`   THE STRUCTURE: the side's row is `headSided wit p at_`; its block
     stands at the place at_ and has the rounds that the verifier's text declares at p, with no
     oracle message. NOTHING ON THE SIDE's FALL, ON THE BLOCK's NAME, DECISION OR CLAIMS; it does
     not ask that `Side.seated` has laid the side
  2  `sum_moves`, `head_moves`, `head_zip`, `head_laid`, `head_members`, `head_numbers`   the row is
     cut at the eight stretches of Honest/K6/Law/Segs.lean: each member written out
  3  `head_fits`, `head_shaped`   `σ.fits = true`; `σ.block.shaped = true`
  4  `headSeated_of_seated`, `headSeated_of_headSide`, `headSeated_of_k6Seated`   DOORS TO THE
     STRUCTURE: a side seated by `Side.seated` AT WHATEVER FALLS, as the frame's rule seats it; its
     case `headSide`; and the structure of premises at a thread (Honest/K6/Law/Seated.lean)
  5  `headSeatB`, `members_at_of_seatB`, `headSeated_of_seatB`, `kind_meets`   THE SEAT's TEST, WITH
     CODE, on a chain's list, p and the place: where it says yes the first door's premise on the
     list is paid; and that the kind's own block, bare, at every p, has what the test asks

Called. The cut in general: Honest/Small/Cut.lean. `foldl_moves`: Honest/Law/Steps.lean.
`head_plain`: Honest/K6/Law/Rounds.lean. `moves_length`, `scalarsOf_length`:
Honest/SumLaw/Fits.lean.

Limits. THE STRUCTURE IS A PREMISE's FORM: nothing in this file shows that it is met at a
description of the protocol. THE SEAT's TEST HAS BEEN EVALUATED AT NO DESCRIPTION's LIST: at a
made-up list alone (Honest/K6/Law/GoodRowToy.lean, which is not in the library). That the
description's own block at the place, as its makers have wrapped it, has the kind's rounds and no
oracle message: Honest/K6/Law/RowAtMember.lean, and RowAtMg.lean, which is not in the library, under
premises of their own. "Members" in this file: `σ.members`, the frame's `Member`. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.Law.Steps
import Johnson.Desc.ProofFile.Honest.K6.Side
import Johnson.Desc.ProofFile.Honest.K6.Law.Seated
import Johnson.Desc.ProofFile.Honest.K6.Law.Segs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.Kinds
open ProofFile.Honest.Small ProofFile.Honest.SumLaw

variable {S Cl X W₀ Rc Tr : Type}

/-! ## 1 The premises on the side, in one structure -/

/-- **What is taken of the side**: its row is `headSided wit p at_`; its block stands at the place
at_, and has the rounds that the verifier's text declares at the public numbers p, with no oracle
message. NOTHING ON THE BLOCK's DECISION, ITS NAME OR THE SIDE's FALL; that `Side.seated` has laid
the side is not asked. -/
structure HeadSeated (σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) : Prop where
  row : σ.row = headSided wit p at_
  place : σ.block.place = at_
  rounds : σ.block.rounds = p.rounds
  oracles : σ.block.oracles = p.rounds.map fun _ => []

/-! ## 2 The members -/

/-- A masked sumcheck's part has as many moves as its call's shape counts rounds. -/
theorem sum_moves {V : Type} (name endName : String) (J : SumJob HeadAsk Unit) :
    (sumPart (V := V) name endName J).moves.length = (scalarsOf J.shape).length :=
  (moves_length name endName J).trans (scalarsOf_length name endName J).symm

/-- The row's parts have the cut's numbers of moves. No premise. -/
theorem head_moves (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    (headSided (X := X) wit p at_).map (·.1.moves.length) = headCut p := by
  simp only [headSided, headRow, headParts, headSims, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_right, Part.lift, List.length_map, sum_moves]
  show [1, 1, (scalarsOf (pointShape 0 (headLPd p + headLt p) 2)).length, 1, 1,
    (scalarsOf (pointShape 1 (headLt p) 4)).length, (scalarsOf (pointShape 1 (headLt p) 2)).length,
    (scalarsOf (pointShape 1 (headLt p + headLPd p) 2)).length] = _
  simp [scalarsOf_point, headCut]

/-- The declared rounds, each with no oracle message, are the eight stretches as laid, one behind
the other. No premise. -/
theorem head_zip (p : Head.Par) :
    p.rounds.zip (p.rounds.map fun _ => ([] : List Oracle)) =
      ((headSegs p).map (laySeg p)).flatten := by
  rw [zip_map_nil, head_rounds_segs]
  simp only [Head.Par.declare, List.map_flatten, List.map_map]
  rfl

/-- CONDITIONAL. **The eight members, laid out**: in the form in which a proof by cases takes them.
-/
theorem head_laid {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) :
    σ.members = laid (headSided wit p at_) 0 ((headSegs p).map (laySeg p)) := by
  unfold Side.members
  rw [h.row, h.rounds, h.oracles, head_zip]
  refine membersOf_flatten _ _ _ ?_
  rw [head_moves, ← headSegs_cut, List.map_map]
  refine List.map_congr_left fun s _ => ?_
  simp [laySeg, Head.Par.declare]

/-- CONDITIONAL. **The eight members, written out**: number i; the stretch number i; the row's part
and simulator number i. -/
theorem head_members {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) :
    σ.members = (headSided wit p at_).zipIdx.map fun x => ⟨x.2, headSeg p x.2, x.1.1, x.1.2⟩ := by
  rw [head_laid h]
  rfl

/-- CONDITIONAL. The members' numbers are below 8. -/
theorem head_numbers {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) : ∀ u ∈ σ.members, u.number < 8 := by
  intro u hu
  rw [head_laid h] at hu
  simp only [headSided, headRow, headParts, headSims, headSegs, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_right, laid, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-! ## 3 fits; the plan's test on shapes -/

/-- CONDITIONAL. **The field `fits` of `Good`**, for all sizes. -/
theorem head_fits {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) : σ.fits = true := by
  have h1 : σ.row.zipIdx.all (fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) = true := by
    rw [h.row, h.place]
    simp [headSided, headRow, headParts, headSims, quietSim, scalarsSim, sumSim, List.zipIdx_cons]
  have h2 : σ.half.rounds = σ.block.rounds.length := by
    unfold Side.half Placed.rounds
    rw [foldl_moves, List.map_map, h.row, h.rounds, head_rounds_segs]
    have hm := head_moves (X := X) wit p at_
    have hm' : (headSided (X := X) wit p at_).map ((·.moves.length) ∘ (·.1)) = headCut p := hm
    rw [hm', ← headSegs_cut]
    simp [Head.Par.declare, List.length_flatten, Function.comp_def]
  have h3 : σ.block.oracles.length = σ.block.rounds.length := by
    rw [h.oracles, h.rounds, List.length_map]
  unfold Side.fits
  rw [h1, h2, h3]
  simp

/-- CONDITIONAL. The plan's test on shapes follows from the structure. -/
theorem head_shaped {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    (h : HeadSeated σ wit p at_) : σ.block.shaped = true := by
  unfold Block.shaped
  rw [h.oracles, h.rounds, zip_map_nil, List.length_map, beq_self_eq_true, Bool.true_and,
    List.all_eq_true]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
  have h0 := (head_plain p d hd).1
  simp [h0]

/-! ## 4 Doors to the structure -/

/-- CONDITIONAL. **The door to the structure**: a side that is seated as the frame's rule seats it
(`Side.seated`, AT WHATEVER FALLS fs), over a list whose blocks at the place have the declared
rounds and no oracle message. -/
theorem headSeated_of_seated {bs : List (Block S Cl)} {fs : List (Fall S)}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    (h : Side.seated bs at_ (headSided wit p at_) fs = some σ)
    (hb : ∀ b ∈ bs, b.place = at_ → b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => []) :
    HeadSeated σ wit p at_ := by
  unfold Side.seated at h
  obtain ⟨b, hf, rfl⟩ := Option.map_eq_some_iff.1 h
  have hp : b.place = at_ := by simpa using List.find?_some hf
  obtain ⟨hr, ho⟩ := hb b (List.mem_of_find?_eq_some hf) hp
  exact ⟨rfl, hp, hr, ho⟩

/-- **THE SEAT's TEST, WITH CODE**: every block of a chain's list that stands at the place has the
rounds that the verifier's text declares at p, as many lists of oracle messages, and each of these
empty. On public data alone. -/
def headSeatB (bs : List (Block S Cl)) (p : Head.Par) (at_ : Place) : Bool :=
  bs.all fun b => b.place != at_ ||
    (decide (b.rounds = p.rounds) && b.oracles.length == b.rounds.length &&
      b.oracles.all (·.isEmpty))

/-- CONDITIONAL. Where the seat's test says yes: what the door asks of the list. -/
theorem members_at_of_seatB {bs : List (Block S Cl)} {p : Head.Par} {at_ : Place}
    (h : headSeatB bs p at_ = true) :
    ∀ b ∈ bs, b.place = at_ → b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => [] := by
  intro b hb hp
  unfold headSeatB at h
  have h1 := List.all_eq_true.1 h b hb
  simp only [hp, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.all_eq_true, List.isEmpty_iff] at h1
  obtain ⟨⟨hr, hl⟩, he⟩ := h1
  refine ⟨hr, ?_⟩
  rw [← hr]
  refine List.ext_getElem (by rw [List.length_map]; exact hl) fun i h₁ h₂ => ?_
  rw [List.getElem_map]
  exact he _ (List.getElem_mem h₁)

/-- CONDITIONAL. **A door with code**: a side seated at whatever falls over a list at which the
seat's test says yes. -/
theorem headSeated_of_seatB {bs : List (Block S Cl)} {fs : List (Fall S)}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place}
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    (h : Side.seated bs at_ (headSided wit p at_) fs = some σ)
    (hB : headSeatB bs p at_ = true) : HeadSeated σ wit p at_ :=
  headSeated_of_seated h (members_at_of_seatB hB)

/-- **The kind's own block, bare, at every p**, stands at the row's place and has the declared
rounds and no oracle message. By unfolding. No premise. -/
theorem kind_meets {St : Type} (cl : _ → Cl) (L : Head.Seat St) (link piece : Nat)
    (p : Head.Par) :
    (Head.kind cl L link piece p).place = headPlace link piece ∧
      (Head.kind cl L link piece p).rounds = p.rounds ∧
      (Head.kind cl L link piece p).oracles = p.rounds.map fun _ => [] :=
  ⟨rfl, rfl, rfl⟩

/-- CONDITIONAL. Its case at `headSide`. -/
theorem headSeated_of_headSide {bs : List (Block S Cl)} {wit : Local W₀ Rc Inst Tr → HeadAsk}
    {p : Head.Par} {link piece : Nat}
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    (h : headSide bs wit p link piece = some σ)
    (hb : ∀ b ∈ bs, b.place = headPlace link piece →
      b.rounds = p.rounds ∧ b.oracles = p.rounds.map fun _ => []) :
    HeadSeated σ wit p (headPlace link piece) :=
  headSeated_of_seated (fs := []) h hb

/-- CONDITIONAL. **The two structures meet**: where the side's block is the block of which
`K6Seated` (Honest/K6/Law/Seated.lean) speaks, and its row is the head's. -/
theorem headSeated_of_k6Seated {Bk : ProverCoinCounts} {Pb : Type}
    {T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb} {b : Nat}
    {wit : Local W₀ Rc Inst Tr → HeadAsk} {p : Head.Par} {at_ : Place} {blk : Block S Cl}
    (k : K6Seated T b wit p at_ blk)
    {σ : Side S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst}
    (hrow : σ.row = headSided wit p at_) (hblk : σ.block = blk) : HeadSeated σ wit p at_ := by
  subst hblk
  exact ⟨hrow, k.place, k.rounds, k.oracles⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.sum_moves
#print axioms ProofFile.Honest.K6.head_moves
#print axioms ProofFile.Honest.K6.head_zip
#print axioms ProofFile.Honest.K6.head_laid
#print axioms ProofFile.Honest.K6.head_members
#print axioms ProofFile.Honest.K6.head_numbers
#print axioms ProofFile.Honest.K6.head_fits
#print axioms ProofFile.Honest.K6.head_shaped
#print axioms ProofFile.Honest.K6.headSeated_of_seated
#print axioms ProofFile.Honest.K6.members_at_of_seatB
#print axioms ProofFile.Honest.K6.headSeated_of_seatB
#print axioms ProofFile.Honest.K6.kind_meets
#print axioms ProofFile.Honest.K6.headSeated_of_headSide
#print axioms ProofFile.Honest.K6.headSeated_of_k6Seated
