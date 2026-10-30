-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeardEntered.lean: THE SMALL LAWS (L1) | (L2) AT THE READING heardA
(HeardAt.lean), AT EVERY RECORD:
(L2) for K6's block as it rides; (L1) for the next token's block under the wrapper
"entered". heardA is a reading of its own, typed to the letter of S.heard (StateHeard.lean): the
two are one by rfl (HeardName.lean: heardA_eq). These laws stand here apart from that name.





-/
import Johnson.Desc.Kinds.Law.HeardAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open VerifiableInference.Desc.First (S)

/-- The same for `blockOf`, the block as it rides. -/
theorem blockOf_leaves_heardA (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) : Leaves heardA b := by
  unfold blockOf at hb
  cases hu : W.H.tl.ix.U.getD 2 none with
  | none => rw [hu] at hb; simp at hb
  | some i =>
    rw [hu] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    exact blockAt_leaves_heardA _ _ _ _

/-- **(L1) at the reading heardA**, at a record inside the head's link that is not yet opened. -/
theorem k7_lays_heardA_at {Cl : Type} (link piece V : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (o : VerifiableInference.Desc.First.HeadOwn)
    (ho : s.here = .head o) (hn : o.opened = false)
    (hd : (Reply.kind (Cl := Cl) k7SeatCopy link piece V).decide s rs gs = .ok s') :
    heardA s' = replyOf rs := by
  have _ := hn
  exact k7_lays_at k7SeatCopy link piece V s s' rs gs (k7SeatCopy_law ho) hd

/-- A wrapper (`Reply.entered`, Johnson/Stored/ReplySeatAt.lean), to the letter: a
block that is let through
inside the head's link alone, while that link is not yet opened. -/
def enteredCopy (b : Block S Unit) : Block S Unit :=
  { b with decide := fun s v g =>
      match s.here with
      | .head o =>
        if o.opened then .error "the next token: the head's link is not yet opened" else b.decide s v g
      | _ => .error "the next token: the head's link is entered" }

/-- **(L1) AS TYPED, at the reading heardA, for the next token's block under that wrapper: at every record.** -/
theorem entered_lays_A (link piece V : Nat) :
    Lays heardA replyOf (enteredCopy (Reply.kind k7SeatCopy link piece V)) := by
  intro s rs gs s' hd
  have hd' : (match s.here with
      | .head o =>
        if o.opened then .error "the next token: the head's link is not yet opened"
        else (Reply.kind (Cl := Unit) k7SeatCopy link piece V).decide s rs gs
      | _ => .error "the next token: the head's link is entered") = Except.ok s' := hd
  cases hh : s.here with
  | head o =>
    rw [hh] at hd'
    dsimp only at hd'
    by_cases ho : o.opened = true
    · rw [if_pos ho] at hd'; cases hd'
    · rw [if_neg ho] at hd'
      exact k7_lays_heardA_at link piece V s s' rs gs o hh (by simpa using ho) hd'
  | between | lay _ | att _ | fin _ | mem _ => rw [hh] at hd'; cases hd'

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_leaves_heardA
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7_lays_heardA_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.entered_lays_A
