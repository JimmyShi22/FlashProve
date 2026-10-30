-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SendsMore.lean: MORE OF WHAT THE SENDING THAT THE CODE SWITCH CALLS
RETURNS (`sentAt`, Returns/Sends.lean): the roots, the book, the count of answers taken, how many
numbers it hands on. Statements and proofs. NOTHING OF THE SENDING IS PROVED ANEW: two are clauses
of the shared sending's own law (`behind_rest`, Johnson/Prover/Send/Form.lean) that
Returns/Sends.lean does not hand on; the others read the term.

  `sentAt_roots`    the count of roots behind: the count in front and one for each tree that the
                    sending's messages are laid in
  `sentAt_book`     the book behind: the one that the shared sending's receiving lays
  `sentAt_took`     the count of answers taken: the place's answers
  `sentAt_idsSize`  as many numbers as messages
  `sentAt_others`   so: where the sending announces a switch's messages (the carrying message, the
                    kept copies, the others), the numbers behind the first 1 + kept are as many as
                    the others

WHICH PREMISES OF THE LAW ON A SEGMENT's FIRST PLACE (`LinkFits`, Returns/Link.lean) THESE REACH:
`numbers`: `sentAt_others` IS it, at the sending's term · `trees`: `sentAt_roots`, WITH ONE TIE
LEFT: the number of trees is the number of roots that the place's first entry states · `took`:
`sentAt_took`, WITH ONE TIE LEFT: the second round shows at least as many items as the place has
answers.

Limits. The two ties are not shown here. `sentAt_book` says which term the book is: nothing on what
stands in it. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.Sends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open Johnson.Prover.Send (numbers behind_rest)
open _root_.Tw.K2 (switchNotices)

variable (Q : K1.Par) (S : Statement) (B : TreeBook) (roots : Nat) (rS rL : Fmt.RoundView)

theorem sentAt_roots :
    (sentAt Q S B roots rS rL).roots = roots + ((layTrees Q.codes Q.sent).getD {}).shapes.size :=
  (behind_rest Q (frontOfSend S B roots) (K1.seedsOf Q rS)
    (K1.answersIn (K1.cutTo Q rL))).2.2.2.2.2.2.1

theorem sentAt_book :
    (sentAt Q S B roots rS rL).book =
      (K1.recvD Q.gp.firstTree (frontOfSend S B roots) Q.sent
        ((layTrees Q.codes Q.sent).getD {})).book :=
  (behind_rest Q (frontOfSend S B roots) (K1.seedsOf Q rS)
    (K1.answersIn (K1.cutTo Q rL))).2.2.2.2.2.2.2

theorem sentAt_took : (sentAt Q S B roots rS rL).took = Q.answers := rfl

theorem sentAt_idsSize : (sentAt Q S B roots rS rL).ids.size = Q.sent.size := by
  show (numbers Q S.oracles.size).size = _
  unfold numbers
  rw [Array.size_map, Array.size_range]

/-- The numbers behind the carrying message's and the copies' are as many as the others. -/
theorem sentAt_others (T : SwitchTarget) (others : Array OracleNotice)
    (hs : Q.sent = switchNotices T others) :
    ((sentAt Q S B roots rS rL).ids.extract (1 + T.kept.size)
      (sentAt Q S B roots rS rL).ids.size).size = others.size := by
  have h : (sentAt Q S B roots rS rL).ids.size = 1 + T.kept.size + others.size := by
    rw [sentAt_idsSize, hs]
    unfold switchNotices
    simp [Array.size_append]
    omega
  rw [Array.size_extract, h]
  omega

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_roots
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_book
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_idsSize
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_others
#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentAt_took
