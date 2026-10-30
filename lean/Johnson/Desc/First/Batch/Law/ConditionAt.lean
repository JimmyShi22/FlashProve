-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ConditionAt.lean (kind K9): THEOREMS: FROM
DECLARED ROUNDS THAT ARE, WRITTEN OUT, A WRITTEN LIST, TO K9's CONDITION AT K9's DECLARED ROUND.
Law/Condition.lean's at_written speaks of a MEMBER of a written list. A description declares rounds
(Fmt.DeclaredRound); writtenOf (Johnson/G/RoundsOfPlan.lean) writes them out; the test seatPinnedProof
(Johnson/Desc/Ok/PlanWritten/Test.lean) says that, written out, they are the full size's written
lists. Here is the step between:
  mem_of_mapM       a list mapped with refusals: each member's image is among what is returned.
  first_of_written  writtenOf file D = .ok R: each declared round d of the first chain is written
                    out (d.round [] = some x), and (x, d.stored) is a member of R.1.
  k9Decl p, k9Decl_round   K9's declared round, as K9's block declares it (Batch/Kind.lean: rounds
                    := [{ entry := entry p }]); written out it is K9's entry, elements drawn,
                    nothing sent, nothing opened.
  drawAlone_rounds, batch_rounds   the rounds of K9's draw, and of the batching that a segment lays
                    (the draw with the adding behind it), are [k9Decl p]: by rfl.
  at_decl           **writtenOf file D = .ok R, R.1 one of the two written lists, k9Decl p ∈ D.1:
                    THEN 1 ≤ p.rows, p.rows - 1 ≤ 2^60, and K9's count at d := p.rows - 1 is at most
                    the cap.**
  at_desc           the same AT A FILE's DESCRIPTION F (Johnson/Desc/Block.lean): F's declared
                    rounds, written out, are R; a block of the first chain's flat list has K9's
                    declared round among its rounds. (FileDescription.roundsDeclaredByBlocks's first part is these blocks'
                    rounds in a row.)
WHAT IT DOES NOT SAY: that writtenOf … F.roundsDeclaredByBlocks returns a written list (the test seatPinnedProof's yes
at the full size's key gives that: seat_yes, Ok/PlanWritten/Seat.lean); that the data of the piece
which a description makes of K9's draw are [k9Round p]; Law/Condition.lean's own limits.

-/
import Johnson.G.RoundsOfPlan
import Johnson.Desc.First.Batch.Law.Condition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Flat OnBytes.Maker
open OnBytes.Params (Rounds)
open Johnson.G Johnson.G.OfPlan
open VerifiableInference.Desc (Block FileDescription)
open _root_.Run (ckP)
open _root_.Iop (Err)

theorem mem_of_mapM {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (R : List β), l.mapM f = .ok R → ∀ a ∈ l, ∃ y ∈ R, f a = .ok y
  | [], _, _, a, ha => by cases ha
  | x :: l, R, h, a, ha => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [hx, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [hx, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨b, List.mem_cons_self, hx⟩
        · obtain ⟨y, hy, hf⟩ := mem_of_mapM f l bs hl a ha
          exact ⟨y, List.mem_cons_of_mem _ hy, hf⟩

/-- Each declared round of the first chain is written out, and stands in the first written list. -/
theorem first_of_written {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) (d : Fmt.DeclaredRound) (hd : d ∈ D.1) :
    ∃ x, d.round [] = some x ∧ (x, d.stored) ∈ R.1 := by
  unfold writtenOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i R1 h1
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨y, hy, hf⟩ := mem_of_mapM _ _ _ h1 d hd
        rw [← Except.ok.inj h]
        cases e : d.round [] with
        | none => simp [e, throw, throwThe, MonadExceptOf.throw] at hf
        | some x =>
          simp only [e, Except.ok.injEq] at hf
          exact ⟨x, rfl, hf ▸ hy⟩

/-- K9's declared round. -/
def k9Decl (p : K9.Where) : Fmt.DeclaredRound := { entry := K9.entry p }

theorem kindOf_sigma : Fmt.kindOf "BAT-sigma" = some .elems := by
  decide +kernel

theorem k9Decl_round (p : K9.Where) :
    (k9Decl p).round [] = some { entry := K9.entry p, kind := .elems } := by
  have hk : Fmt.kindOf (k9Decl p).entry.name = some .elems := kindOf_sigma
  have ho : (k9Decl p).opens = [] := rfl
  have hi : (k9Decl p).items = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, k9Decl, K9.entry]
  unfold Fmt.DeclaredRound.round
  rw [hk, ho, hi]
  simp [k9Decl]

theorem drawAlone_rounds {T Cl : Type} (X : K9.Lens T) (p : K9.Where) :
    (K9.drawAlone (Cl := Cl) X p).rounds = [k9Decl p] := rfl

theorem batch_rounds {T : Type} (X : K9.Lens T) (p : K9.Where)
    (claims : T → Except String (List Claim × T)) : (K9.batch X p claims).rounds = [k9Decl p] :=
  rfl

/-- **From declared rounds that are, written out, a written list.** -/
theorem at_decl {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file D = .ok R) (hR : R.1 = dryProofFull.1 ∨ R.1 = dryProofSmall.1)
    (p : K9.Where) (hp : k9Decl p ∈ D.1) :
    1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 ∧
      Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
        (Err.cap 128 (uLT (ckP .two) [k9Round p])) := by
  obtain ⟨x, hx, hm⟩ := first_of_written h (k9Decl p) hp
  rw [k9Decl_round] at hx
  rw [← Option.some.inj hx] at hm
  refine at_written p (k9Decl p).stored (List.mem_append.2 ?_)
  rcases hR with e | e
  · exact Or.inl (e ▸ hm)
  · exact Or.inr (e ▸ hm)

/-- **At a file's description.** -/
theorem at_desc {Xi : Type} (F : FileDescription Xi) {file : String} {R : Rounds × Rounds × Rounds}
    (h : writtenOf file F.roundsDeclaredByBlocks = .ok R) (hR : R.1 = dryProofFull.1 ∨ R.1 = dryProofSmall.1)
    (b : Block F.S₁ F.Cl) (hb : b ∈ F.first.blocksInOrder) (p : K9.Where) (hp : k9Decl p ∈ b.rounds) :
    1 ≤ p.rows ∧ p.rows - 1 ≤ 2 ^ 60 ∧
      Err.le (allErr (fun _ _ => p.rows - 1) 0 [k9Round p])
        (Err.cap 128 (uLT (ckP .two) [k9Round p])) :=
  at_decl h hR p (List.mem_flatMap.2 ⟨b, hb, hp⟩)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.first_of_written
#print axioms VerifiableInference.Desc.K9L.k9Decl_round
#print axioms VerifiableInference.Desc.K9L.at_decl
#print axioms VerifiableInference.Desc.K9L.at_desc
