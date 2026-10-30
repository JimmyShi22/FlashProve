-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawAnswers.lean: "FIXED BEFORE THE DRAW", FROM THE TEST ON THE PLAN: THE
CLAUSE ON SAMPLED MESSAGES.

Johnson/Desc/First/K8/LawBefore.lean draws out of a yes of `beforeAt` (Johnson/Desc/Block.lean) that
a message which a block names in `before` is SENT in front of the block's first draw. `beforeAt`
asks more of a message one of whose tenants is sampled: a round behind the one that sends it, and
likewise in front of the draw, has sample answers in its message. A committed word binds its sender
to one message only together with its sample's answers: so this clause belongs to "fixed". Here it
is drawn out.
  `oraclesOfChain`: what one of the three chains' blocks say of the messages that they send.
  `beforeAt_answers`: GENERAL IN THE BLOCK: for a named message with a sampled tenant there is a
    declared round j with sample answers, strictly behind the round that sends the message and not
    later than the block's first drawing round (own chain).
  `answers_before_draw`: THE KIND'S: for each message that it names, if a tenant is sampled: such a
    round stands strictly behind the sending and STRICTLY in front of the round of the draw.
    `file_answers_before_draw`: the same from the file's one test on the plan.
Statements and proofs. Limits: those of LawBefore.lean. THAT round has answers: whose answers they
are, the test does not ask: a round with the answers of another message's sample passes. Rounds are
those of the declared plan.

-/
import Johnson.Desc.First.K8.LawBefore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- What one of the three chains' blocks say of the messages that they send, by the chain's number
from 1. -/
def oraclesOfChain (O : List Oracle × List Oracle × List Oracle) (c : Nat) : List Oracle :=
  if c == 1 then O.1 else if c == 2 then O.2.1 else O.2.2

/-- **The clause on sampled messages, at any block of the list.** -/
theorem beforeAt_answers (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) :
    ∀ (pre : List (Block S Cl)) (from' : Nat) (b : Block S Cl) (post : List (Block S Cl)),
      beforeAt D O c from' (pre ++ b :: post) = true → ∀ m ∈ b.before,
        ((oraclesOfChain O m.1)[m.2]?).any (fun o => o.tenants.any (·.sampled)) = true →
        ∃ i j r, sendRound (chainOf D m.1) m.2 = some i ∧ (chainOf D m.1)[j]? = some r ∧
            r.entry.answers ≠ 0 ∧ i < j ∧
          j ≤ (if m.1 == c + 1 then from' + roundsIn pre + b.rounds.findIdx drawsAny
            else (chainOf D m.1).length)
  | [], from', b, post, h, m, hm, hs => by
    simp only [List.nil_append, beforeAt, Bool.and_eq_true, List.all_eq_true] at h
    have hm' := h.1 m hm
    unfold oraclesOfChain at hs
    unfold chainOf
    split at hm'
    · exact absurd hm' (by simp)
    · rename_i i hi
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hm'
      rcases hm'.2 with hn | ha
      · rw [hs] at hn
        exact absurd hn (by simp)
      · obtain ⟨x, hx, hc⟩ := List.any_eq_true.1 ha
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
        exact ⟨i, x.2, x.1, hi, List.mem_zipIdx_iff_getElem?.1 hx, hc.1.1, hc.1.2, by simpa
            [roundsIn] using hc.2⟩
  | a :: pre, from', b, post, h, m, hm, hs => by
    simp only [List.cons_append, beforeAt, Bool.and_eq_true] at h
    obtain ⟨i, j, r, h1, h2, h3, h4, h5⟩ := beforeAt_answers D O c pre (from' + a.rounds.length) b
        post h.2 m hm hs
    refine ⟨i, j, r, h1, h2, h3, h4, ?_⟩
    have e : from' + a.rounds.length + roundsIn pre = from' + roundsIn (a :: pre) := by
      simp [roundsIn, Nat.add_assoc]
    rwa [e] at h5

end VerifiableInference.Desc

namespace VerifiableInference.Desc.First.K8

/-- **The kind's**: a round with sample answers stands strictly behind the sending of each named
message that has a sampled tenant, and strictly in front of the round of the draw. -/
theorem answers_before_draw {S Cl : Type} (seat : Seat S) (p : Par)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (pre post : List (Block S Cl))
    (hb : beforeAt D O 0 0 (pre ++ approximateRangeProofDrawKind seat p :: post) = true)
    (hp : (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk = true)
    (hD : D.1[roundsIn pre]? = some (round p)) (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn)
    (hs : (O.1[n]?).any (fun o => o.tenants.any (·.sampled)) = true) :
    ∃ i j r, sendRound D.1 n = some i ∧ D.1[j]? = some r ∧ r.entry.answers ≠ 0 ∧ i < j ∧ j <
        roundsIn pre := by
  have hm : ((1, n) : Nat × Nat) ∈ (approximateRangeProofDrawKind (Cl := Cl) seat p).before := by
    show (1, n) ∈ (p.matsIn ++ p.readsIn).map fun n => (1, n)
    exact List.mem_map.2 ⟨n, hn, rfl⟩
  obtain ⟨i, j, r, h1, h2, h3, h4, h5⟩ :=
    beforeAt_answers D O 0 pre 0 (approximateRangeProofDrawKind seat p) post hb (1, n) hm (by simpa [oraclesOfChain] using
                                 hs)
  rw [first_draw seat p hp] at h5
  have h1' : sendRound D.1 n = some i := by simpa [chainOf] using h1
  have h2' : D.1[j]? = some r := by simpa [chainOf] using h2
  have h5' : j ≤ roundsIn pre := by simpa using h5
  refine ⟨i, j, r, h1', h2', h3, h4, ?_⟩
  rcases Nat.lt_or_ge j (roundsIn pre) with hlt | hge
  · exact hlt
  · have e : j = roundsIn pre := Nat.le_antisymm h5' hge
    rw [e, hD] at h2'
    obtain rfl : round p = r := by simpa using h2'
    exact absurd rfl h3

/-- **From the file's one test on the plan.** -/
theorem file_answers_before_draw {Xi : Type} (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par)
    (pre post : List (Block F.S₁ F.Cl)) (hflat : F.first.blocksInOrder = pre ++ approximateRangeProofDrawKind seat p :: post)
    (hF : F.planOk = true) (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn)
    (hs : ((oraclesOf F.first.blocksInOrder)[n]?).any (fun o => o.tenants.any (·.sampled)) = true) :
    ∃ i j r, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ F.roundsDeclaredByBlocks.1[j]? = some r ∧ r.entry.answers ≠ 0 ∧ i < j ∧
      j < roundsIn pre := by
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hF
  have hbo : F.beforeOk = true := by tauto
  have hbl : blocksOk F.first.blocksInOrder = true := by tauto
  simp only [FileDescription.beforeOk, Bool.and_eq_true] at hbo
  have hb := hbo.1.1
  have hp : (approximateRangeProofDrawKind (Cl := F.Cl) seat p).planOk = true := by
    rw [hflat] at hbl
    simp only [blocksOk, List.all_eq_true, Bool.and_eq_true] at hbl
    exact (hbl (approximateRangeProofDrawKind seat p) (by simp)).1
  have hD : F.roundsDeclaredByBlocks.1[roundsIn pre]? = some (round p) := by
    show (F.first.blocksInOrder.flatMap (·.rounds))[roundsIn pre]? = _
    rw [hflat, flatMap_rounds_at]
    rfl
  have hb' : beforeAt F.roundsDeclaredByBlocks (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf
                        F.second.blocksInOrder) 0 0
      (pre ++ approximateRangeProofDrawKind seat p :: post) = true := by
    rw [← hflat]
    exact hb
  exact answers_before_draw seat p F.roundsDeclaredByBlocks _ pre post hb' hp hD n hn hs

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.file_answers_before_draw
#print axioms VerifiableInference.Desc.beforeAt_answers
#print axioms VerifiableInference.Desc.First.K8.answers_before_draw
