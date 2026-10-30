-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPlaced.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAWS AT THE BLOCK WITH
ANOTHER PLACE OR NAME WRITTEN ON IT.

A maker of a file's description may lay a kind's block with the place's address written anew (`{ b
with place := a }`). The laws of Law.lean, LawView.lean, LawBefore.lean and LawAnswers.lean are
stated of `approximateRangeProofDrawKind seat p` itself. A block's step reads its rounds and its decision alone; the test on
the order reads its rounds and the field `before`. So the laws hold of every block that has these
fields.
  `Like seat p b`: the block b has the kind's rounds, decision, field `before` and tests on the plan
    alone. `like_self`, `like_placed`: so has the kind's own block, and that block with another
    place and name.
  `step_like`: such a block's step is the kind's.
  `hear_law_view_like`: the law at all written transcripts, of such a block.
  `file_before_draw_like`, `file_answers_before_draw_like`: the order, from the file's one test on
    the plan, for a description whose first chain's flat list has such a block in it.
Statements and proofs. Limits: those of the files named. That a given description's flat list has
such a block at a given position is a premise.


-/
import Johnson.Desc.First.K8.LawView
import Johnson.Desc.First.K8.LawAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb.Pv.Tail OnBytes.Maker OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail

/-- The block b has the kind's rounds, decision, field `before` and tests on the plan alone. -/
structure Like {S Cl : Type} (seat : Seat S) (p : Par) (b : Block S Cl) : Prop where
  rounds : b.rounds = (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds
  decide : b.decide = (approximateRangeProofDrawKind (Cl := Cl) seat p).decide
  before : b.before = (approximateRangeProofDrawKind (Cl := Cl) seat p).before
  planOk : b.planOk = (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk

theorem like_self {S Cl : Type} (seat : Seat S) (p : Par) : Like seat p (approximateRangeProofDrawKind (Cl := Cl) seat p) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem like_placed {S Cl : Type} (seat : Seat S) (p : Par) (a : Place) (name : String) :
    Like seat p ({ approximateRangeProofDrawKind (Cl := Cl) seat p with place := a, name := name } : Block S Cl) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Such a block's step is the kind's. -/
theorem step_like {S Cl : Type} {seat : Seat S} {p : Par} {b : Block S Cl} (h : Like seat p b)
    (ft : Nat) (st : S) (rs : List Fmt.RoundView) (cols : List Col) :
    b.step ft st rs cols = (approximateRangeProofDrawKind (Cl := Cl) seat p).step ft st rs cols := by
  unfold Block.step
  rw [h.rounds, h.decide]

/-- **The law at all written transcripts of the round, of such a block.** -/
theorem hear_law_view_like {S Cl : Type} {seat : Seat S} {p : Par} {s : Size} (hf : Fits p s)
    {b : Block S Cl} (h : Like seat p b) (m : (roundT (Run.ckP .two) (rdt p)).up.Msg)
    (c : (roundT (Run.ckP .two) (rdt p)).up.Chal) (ft : Nat) (st st' : S) (n : Nat)
    (cols : List Col) :
    b.step ft st (vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) cols = .ok (st', n) ↔
      (seat.closed st = true ∧ seat.nothingOwed st = true ∧ seat.drawn st = false ∧
        seat.matrices st = p.ks.length ∧ seat.ks st = p.ks ∧ seat.ms st = p.ms ∧
        seat.tau st = p.tau ∧ seat.tabs st = tabs p ∧
        seat.lay st (listOf (matrixOf hf c)) (firstColumns p) = .ok st' ∧ n = 0) := by
  rw [step_like h]
  exact hear_law_view (Cl := Cl) hf seat m c ft st st' n cols

/-- The test on the order reads a block's rounds and its field `before` alone. -/
theorem beforeAt_like {S Cl : Type} {seat : Seat S} {p : Par} {b : Block S Cl} (h : Like seat p b)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) (post : List (Block S Cl)) :
    ∀ (pre : List (Block S Cl)) (from' : Nat),
      beforeAt D O c from' (pre ++ b :: post) = beforeAt D O c from' (pre ++ approximateRangeProofDrawKind seat p :: post)
  | [], from' => by
    simp only [List.nil_append, beforeAt, h.rounds, h.before]
  | a :: pre, from' => by
    simp only [List.cons_append, beforeAt, beforeAt_like h D O c post pre]

section
variable {Xi : Type} (F : FileDescription Xi) {seat : Seat F.S₁} {p : Par} {b : Block F.S₁ F.Cl}
  (h : Like seat p b) (pre post : List (Block F.S₁ F.Cl)) (hflat : F.first.blocksInOrder = pre ++ b :: post)
  (hF : F.planOk = true)

include h hflat hF in
/-- What the file's one test on the plan gives at such a block. -/
theorem file_facts_like :
    beforeAt F.roundsDeclaredByBlocks (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder) 0 0
        (pre ++ approximateRangeProofDrawKind seat p :: post) = true ∧
      (approximateRangeProofDrawKind (Cl := F.Cl) seat p).planOk = true ∧ F.roundsDeclaredByBlocks.1[roundsIn pre]? = some (round p) := by
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hF
  have hbo : F.beforeOk = true := by tauto
  have hbl : blocksOk F.first.blocksInOrder = true := by tauto
  simp only [FileDescription.beforeOk, Bool.and_eq_true] at hbo
  have hb := hbo.1.1
  refine ⟨?_, ?_, ?_⟩
  · rw [← beforeAt_like h, ← hflat]
    exact hb
  · rw [hflat] at hbl
    simp only [blocksOk, List.all_eq_true, Bool.and_eq_true] at hbl
    rw [← h.planOk]
    exact (hbl b (by simp)).1
  · show (F.first.blocksInOrder.flatMap (·.rounds))[roundsIn pre]? = _
    rw [hflat, flatMap_rounds_at, h.rounds]
    rfl

include h hflat hF in
theorem file_before_draw_like (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    ∃ i, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ i < roundsIn pre := by
  obtain ⟨h1, h2, h3⟩ := file_facts_like F h pre post hflat hF
  exact before_draw seat p F.roundsDeclaredByBlocks _ pre post h1 h2 h3 n hn

include h hflat hF in
theorem file_answers_before_draw_like (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn)
    (hs : ((oraclesOf F.first.blocksInOrder)[n]?).any (fun o => o.tenants.any (·.sampled)) = true) :
    ∃ i j r, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ F.roundsDeclaredByBlocks.1[j]? = some r ∧ r.entry.answers ≠ 0 ∧ i < j ∧
      j < roundsIn pre := by
  obtain ⟨h1, h2, h3⟩ := file_facts_like F h pre post hflat hF
  exact answers_before_draw seat p F.roundsDeclaredByBlocks _ pre post h1 h2 h3 n hn hs

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.like_placed
#print axioms VerifiableInference.Desc.First.K8.hear_law_view_like
#print axioms VerifiableInference.Desc.First.K8.file_before_draw_like
#print axioms VerifiableInference.Desc.First.K8.file_answers_before_draw_like
