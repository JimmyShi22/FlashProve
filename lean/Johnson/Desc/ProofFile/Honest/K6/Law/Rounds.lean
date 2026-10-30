-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/Rounds.lean: what the declared rounds of the sub-protocol "the
output head's own rounds" state, held against `headSent`: a list, written here beside the eight
parts of its honest side (`headParts`, Honest/K6/Part.lean), of how many scalars each round of each
part is to send: GENERAL IN THE PLACE's PUBLIC NUMBERS p: proofs, no evaluation, and no premise on
p. One definition with code, and statements with their proofs.

What it is not. Counts and shapes of rounds alone: nothing on any value that is sent, on a
challenge, or on the verifier's decision. NO STATEMENT HERE NAMES `headParts`, A PART OR A MOVE:
that the parts' moves say lists of `headSent`'s lengths is not proved in this file. Nothing is
claimed on soundness, completeness or hiding.

  `headSent`   how many scalars each round of each of the eight parts is to send: a list written
     beside the parts
  `scalarsOf_point`, `sent_sumcheck`, `sent_level`   what a call of the row's shape sends, and what
     the verifier's text's two tables of rounds send, round by round
  `declare_stated`   rounds that are declared of ANY table of the text's rounds state its scalars
  `head_sent`, `head_stated`   **the verifier's table of rounds sends, round by round, what
     `headSent` lists**; so the declared rounds state these scalars, with no oracle message laid
     beside them
  `headSent_cut`, `head_rounds_length`   `headSent`'s numbers of rounds, part by part, are
     `headCut`'s; there are as many declared rounds as `headSent` lists
  `head_reads_nothing`, `head_plain`, `head_unsealed`   no round reads a stored table or opens a
     tree; no entry has a root or an answer, and each message is whole scalars; none is a sealing
     round

Why no premise on p: the norm inside the head is one norm by the text's own instance, so that every
count is a function of the two logarithms alone, on both sides the same terms.

Typed here, and why. No lemma of another file of this tree is called: every proof unfolds the text's
own definitions. The step on how an entry that is made of such a round is cut into items stands by
itself too, as `items_of_round` (Johnson/Desc/Kinds/Law/K06FitsShape.lean), which is not imported
here; its three lines stand here again, inside `declare_stated`, so that this file leans on nothing
beyond the honest side's own text and the masked sumcheck's law.
-/
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Part.MaskedSum (Var)
open ProofFile.Honest.SumLaw

/-- How many scalars each round of each of the eight parts is to send: a list written beside
`headParts`. No statement of this file ties it to the parts' moves. -/
def headSent (p : Head.Par) : List (List Nat) :=
  [[0], [9], scalarsOf (headSquaresJob p).shape, [0], [7], scalarsOf (headProductsJob p).shape,
    scalarsOf (headNormedJob p).shape, scalarsOf (headLogitsJob p).shape]

/-- What a call of the row's shape sends, round by round. -/
theorem scalarsOf_point (lead n ends : Nat) :
    scalarsOf (pointShape lead n ends) = (lead + 1) :: List.replicate n 2 ++ [2, ends] := by
  simp [scalarsOf, pointShape, Var.d]

/-- What the text's masked sumcheck sends, round by round. -/
theorem sent_sumcheck (m ends : Nat) :
    (sumcheck.rounds m ends).map (·.sent) = 2 :: List.replicate m 2 ++ [2, ends] := by
  simp [sumcheck.rounds]

/-- What the text's level sends, round by round. -/
theorem sent_level (m : Nat) :
    (level.rounds m).map (·.sent) = 1 :: List.replicate m 2 ++ [2, 2, 0] := by
  simp [level.rounds]

/-- Rounds that are declared of the text's table of rounds state each round's scalars, and no
oracle message is laid beside them. General in the table. -/
theorem declare_stated (p : Head.Par) (rs : List Round) :
    StatedBy (rs.map (·.sent)) ((p.declare rs).zip ((p.declare rs).map fun _ => [])) := by
  induction rs with
  | nil => exact trivial
  | cons r rs ih =>
    show ({ entry := r.entry p.work } : Fmt.DeclaredRound).items.filter (· != .root) =
        List.replicate r.sent .e ∧ ([] : List Oracle) = [] ∧
      StatedBy (rs.map (·.sent)) ((p.declare rs).zip ((p.declare rs).map fun _ => []))
    refine ⟨?_, rfl, ih⟩
    show (r.entry p.work).cut.filter (· != .root) = _
    unfold Fmt.Entry.cut Round.entry
    simp

/-- The verifier's table of rounds sends, round by round, what `headSent` lists. No premise. -/
theorem head_sent (p : Head.Par) :
    (let _ := p.sizes
     VerifiableInference.Desc.Kinds.Head.rounds).map (·.sent) = (headSent p).flatten := by
  letI := p.sizes
  have hN0 : Norm.lNI = 0 := rfl
  have hN1 : Norm.NI = 1 := rfl
  show (Norm.rounds ++ FinalNorm.rounds ++ sumcheck.rounds (Norm.lt + Norm.lPd) 2).map (·.sent) = _
  show _ = [0] ++ ([9] ++ (scalarsOf (pointShape 0 (Norm.lPd + Norm.lt) 2) ++ ([0] ++ ([7] ++
    (scalarsOf (pointShape 1 Norm.lt 4) ++ (scalarsOf (pointShape 1 Norm.lt 2) ++
      (scalarsOf (pointShape 1 (Norm.lt + Norm.lPd) 2) ++ [])))))))
  simp only [Norm.rounds, FinalNorm.rounds, hN0, hN1, List.map_append, sent_sumcheck, sent_level,
    scalarsOf_point, drawPoint.rounds, sendThenBatch.rounds, List.map_cons, List.map_nil,
    beq_self_eq_true, if_true, Nat.mul_one, Nat.zero_add]
  simp

/-- **The declared rounds state `headSent`'s scalars**, with no oracle message laid beside them. No
premise. -/
theorem head_stated (p : Head.Par) :
    StatedBy (headSent p).flatten (p.rounds.zip (p.rounds.map fun _ => [])) := by
  rw [← head_sent]
  exact declare_stated p _

/-- `headSent`'s numbers of rounds, part by part, are the cut's. No premise. -/
theorem headSent_cut (p : Head.Par) : (headSent p).map (·.length) = headCut p := by
  show [1, 1, (scalarsOf (pointShape 0 (headLPd p + headLt p) 2)).length, 1, 1,
    (scalarsOf (pointShape 1 (headLt p) 4)).length, (scalarsOf (pointShape 1 (headLt p) 2)).length,
    (scalarsOf (pointShape 1 (headLt p + headLPd p) 2)).length] = _
  simp [scalarsOf_point, headCut]

/-- There are as many declared rounds as `headSent` lists. No premise. -/
theorem head_rounds_length (p : Head.Par) : p.rounds.length = (headSent p).flatten.length := by
  rw [← head_sent, List.length_map]
  exact List.length_map _

/-- No declared round reads a stored table or opens a tree. No premise. -/
theorem head_reads_nothing (p : Head.Par) : ∀ r ∈ p.rounds, r.stored = [] ∧ r.opens = [] := by
  intro r hr
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr
  exact ⟨rfl, rfl⟩

/-- No entry has a root or an answer, and each message is whole scalars. No premise. -/
theorem head_plain (p : Head.Par) :
    ∀ d ∈ p.rounds, d.entry.roots = 0 ∧ d.entry.answers = 0 ∧ 24 ∣ d.entry.msg := by
  intro d hd
  obtain ⟨r, _, rfl⟩ := List.mem_map.1 hd
  exact ⟨rfl, rfl, ⟨r.sent, rfl⟩⟩

/-- None of the declared rounds is a sealing round. No premise. -/
theorem head_unsealed (p : Head.Par) :
    ∀ z ∈ p.rounds, Fmt.kindOf z.entry.name ≠ some .sealed := by
  intro z hz
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hz
  letI := p.sizes
  show Fmt.kindOf R.name ≠ some .sealed
  simp only [Head.rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, drawJoin.rounds,
    sendThenBatch.rounds, level.rounds, sumcheck.rounds, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hR
  simp only [or_assoc] at hR
  rcases hR with rfl | rfl | h | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl |
    rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl
  case inr.inr.inl =>
    have hN0 : Norm.lNI = 0 := rfl
    rw [hN0] at h
    simp at h
  all_goals (dsimp only; decide)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.scalarsOf_point
#print axioms ProofFile.Honest.K6.sent_sumcheck
#print axioms ProofFile.Honest.K6.sent_level
#print axioms ProofFile.Honest.K6.declare_stated
#print axioms ProofFile.Honest.K6.head_sent
#print axioms ProofFile.Honest.K6.head_stated
#print axioms ProofFile.Honest.K6.headSent_cut
#print axioms ProofFile.Honest.K6.head_rounds_length
#print axioms ProofFile.Honest.K6.head_reads_nothing
#print axioms ProofFile.Honest.K6.head_plain
#print axioms ProofFile.Honest.K6.head_unsealed
