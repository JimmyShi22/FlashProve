-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeardAt.lean: OVER State.lean
(the heard reply has ONE HOME, out.reply) and the seats that go with it
(Stored/HeadSeatAt.lean; Stored/ReplySeatAt.lean).
(L2) AT THE FIRST CHAIN's RECORD: the output head's block, as it is seated at State.lean's S
(blockAt, blockOf), leaves s.out.reply, and heardA, which is the same reading.
WHAT THIS FILE HOLDS:

  setHeard_ok       its clause o'.t = o.t (the tables of reads stay).

  blockOf_leaves    Leaves reply b /\ Leaves heardA b.
  heardA            out.reply (First/StateHeard.lean's S.heard, to the letter).


  k7SeatCopy        Reply.seatAt (out.reply): it gives back what was laid AT
                    EVERY RECORD and marks nothing.

  k7_lays_or_marked its first half holds always: k7_lays_seat.
-/
import Johnson.Desc.Kinds.Law.Heard
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open VerifiableInference.Desc.First (S)

theorem out_putFork (s : S) (F : OnBytes.Model.Fork) : (s.putFork F).out = s.out := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

theorem out_mark (s : S) (m : String) : (s.mark m).out = s.out := by
  unfold S.mark
  split <;> rfl

/-- Where putFork? returns it returns what putFork lays. -/
theorem putFork?_ok {s s1 : S} {F : OnBytes.Model.Fork} (h : s.putFork? F = .ok s1) :
    s1 = s.putFork F := by
  unfold S.putFork? at h
  split at h
  · exact ((S.unmarked_ok _ _).mp h).1.symm
  · cases h

variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat)

/-- Where the seat's setHeard returns: the record stands in the head's link, and of that link's own
part only what was heard turns. -/
theorem setHeard_ok {s s2 : S} {H : HeardAll} (e : (seatAt h iU3).setHeard s H = .ok s2) :
    ∃ (o o' : VerifiableInference.Desc.First.HeadOwn), s.here = .head o ∧
      s2 = { s with here := .head o' } ∧ o'.t = o.t ∧ o'.opened = o.opened ∧ o'.F = o.F := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · rename_i o ho
    split at e
    · simp only [Except.ok.injEq] at e
      exact ⟨o, _, ho, e.symm, rfl, rfl, rfl⟩
    · cases e
  · cases e

/-- **(L2) for K6's block at S: it leaves s.out.reply.** -/
theorem blockAt_leaves_reply : Leaves (fun s : S => s.out.reply) (blockAt h iU3 work l) := by
  refine leaves_of_decide_eq (b := kind (fun _ => ()) (seatAt h iU3) l 4 (parOf h work)) rfl
    (k6_leaves _ (seatAt h iU3) l 4 (parOf h work) _ ?_ ?_ ?_)
  · intro s F s1 e
    rw [putFork?_ok (show s.putFork? F = .ok s1 from e), out_putFork]
  · intro s H s2 e
    obtain ⟨o, o', _, rfl, _, _, _⟩ := setHeard_ok h iU3 e
    rfl
  · intro s w; rfl

/-! ## The one reading -/

/-- The heard next token: it has one home. -/
def heardA (s : S) : Option E := s.out.reply

theorem heardA_putFork (s : S) (F : OnBytes.Model.Fork) : heardA (s.putFork F) = heardA s := by
  unfold heardA
  rw [out_putFork]

theorem heardA_mark (s : S) (m : String) : heardA (s.mark m) = heardA s := by
  unfold heardA
  rw [out_mark]

/-- **(L2) for K6's block at S, at the one reading.** -/
theorem blockAt_leaves_heardA : Leaves heardA (blockAt h iU3 work l) :=
  blockAt_leaves_reply h iU3 work l

/-- The same for `blockOf`, the block as it rides. -/
theorem blockOf_leaves (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) : Leaves (fun s : S => s.out.reply) b ∧ Leaves heardA b := by
  unfold blockOf at hb
  cases hu : W.H.tl.ix.U.getD 2 none with
  | none => rw [hu] at hb; simp at hb
  | some i =>
    rw [hu] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    exact ⟨blockAt_leaves_reply _ _ _ _, blockAt_leaves_heardA _ _ _ _⟩

/-! ## (L1) at the seat at which the next token's block rides -/

/-- The seat at which the next token's block rides: Stored/ReplySeatAt.lean's, by name. -/
def k7SeatCopy : Reply.Seat S := Reply.seatAt

/-- The seat gives back what was laid. (Nothing reads the premise.) -/
theorem k7SeatCopy_law {s : S} {o : VerifiableInference.Desc.First.HeadOwn} (_ho : s.here = .head o)
    (x : E) : k7SeatCopy.reply (k7SeatCopy.setReply s x) = some x := rfl

/-- **(L1) at that seat: it lays what it read, at every record.** -/
theorem k7_lays_seat {Cl : Type} (link piece V : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hd : (Reply.kind (Cl := Cl) k7SeatCopy link piece V).decide s rs gs = .ok s') :
    k7SeatCopy.reply s' = replyOf rs :=
  k7_lays_at _ link piece V s s' rs gs (fun _ => rfl) hd

/-- It lays or it marks; by `k7_lays_seat` the first half holds always. -/
theorem k7_lays_or_marked {Cl : Type} (link piece V : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (hd : (Reply.kind (Cl := Cl) k7SeatCopy link piece V).decide s rs gs = .ok s') :
    k7SeatCopy.reply s' = replyOf rs ∨ s'.failed.isSome = true :=
  Or.inl (k7_lays_seat link piece V s s' rs gs hd)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_leaves
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_leaves_heardA
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k7_lays_or_marked
