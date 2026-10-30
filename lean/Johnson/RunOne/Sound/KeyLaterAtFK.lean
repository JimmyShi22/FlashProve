-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyLaterAtFK.lean: It stands on Johnson/Desc/Key/Desc.lean.
THE KEY FILE'S SHARED AND LAST CHAIN: which block sits at which seat;
and two more seats.

What is said.
  `fk_shared_is`, `fk_second_is`: the two chains are `(sharedChain c P).retype` and
  `(thirdChain c P).retype`.
  `fk_shared_at`: seat 1 + j of the shared chain holds member j of `sharedK`'s back: the kind K14's
    blocks (`blocksOr (p14K c (beforePointK P))`), the two proximity tests, the end. `fk_K14_at`: so
    where `blocks (p14K …) = some bl`, seat 1 + j holds bl's member j.
  `fk_front₂_pass`, `fk_front₂_seat`: SEAT 0 OF THE SHARED CHAIN (its front: a test on the plan
    alone) hands the record on always: FILLED.
  `fk_second_at`: the last chain's four seats: K14's second part; the taken trees' sources; the own
    test; the end.
  `asksTaken`, `fk_taken_pass`, `fk_taken_seat`: SEAT 1 OF THE LAST CHAIN hands the record on just
    where its three clauses hold: FILLED.

Limits. As for the ends' seats (Johnson/RunOne/Sound/KeyEndsAtFK.lean). Nothing on any other block's
law. Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyQuietAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.ChainEnd
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.Key (descriptionFromSource Source Claim)
open VerifiableInference.Desc.Third (S₃ takenSources takenOf opensTaken batchLinearConstraintsSecondPart)
open _root_.Run (ckP)
open _root_.Iop (Err)

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

theorem fk_shared_is : (FK X N P).shared = (Key.sharedChain X.chains P).retype := rfl

theorem fk_second_is : (FK X N P).second = (Key.thirdChain X.chains P).retype := rfl

/-- A block at the key file's type of claims, as the flat list lays it. -/
abbrev atClaim {S : Type} (b : Block S Unit) : Block S Key.Claim := bareB b.retype

/-- **Seat 1 + j of the shared chain holds member j of its back and last block.** -/
theorem fk_shared_at (j : ℕ) :
    (FK X N P).shared.blocksInOrder[1 + j]? =
      ((Key.sharedChain X.chains P).back.map atClaim ++
        [atClaim (Key.sharedChain X.chains P).last])[j]? := by
  have e : ((Key.sharedChain X.chains P).retype (Cl' := Key.Claim)).blocksInOrder =
      [bareB ((Key.sharedChain X.chains P).retype (Cl' := Key.Claim)).first] ++
        ((Key.sharedChain X.chains P).back.map atClaim ++
          [atClaim (Key.sharedChain X.chains P).last]) := by
    show _ :: [] ++ [] ++ ((Key.sharedChain X.chains P).back.map Block.retype).map bareB ++ [_] = _
    rw [List.append_nil, List.map_map]
    rfl
  exact (congrArg (fun c : Chain _ Key.Claim => c.blocksInOrder[1 + j]?) (fk_shared_is X N P )).trans
    ((congrArg (fun l => l[1 + j]?) e).trans (getElem?_append_at _ _ 1 j rfl))

/-- **Where the kind's blocks can be said, seat 1 + j holds the kind's block number j.** -/
theorem fk_K14_at
    (bl : List (Block _root_.Desc.K14.St Unit))
    (hbl : _root_.Desc.K14.blocks (Key.sharedPar X.chains (Key.beforeSharedPoint P)) = some bl) (j : ℕ)
    (b : Block _root_.Desc.K14.St Unit) (hb : bl[j]? = some b) :
    (FK X N P).shared.blocksInOrder[1 + j]? = some (atClaim b) := by
  have hj : j < bl.length := (List.getElem?_eq_some_iff.1 hb).1
  have hback : (Key.sharedChain X.chains P).back = bl ++ Key.sharedTests P := by
    show _root_.Desc.K14.blocksOr _ ++ Key.sharedTests P = _
    unfold _root_.Desc.K14.blocksOr
    rw [hbl]
    rfl
  have hj' : j < ((bl ++ Key.sharedTests P).map (atClaim (S := _root_.Desc.K14.St))).length := by
    rw [List.length_map, List.length_append]
    omega
  rw [fk_shared_at X N P j, hback, List.getElem?_append_left hj', List.getElem?_map,
    List.getElem?_append_left hj, hb]
  rfl

theorem fk_front₂_pass :
    ∃ e, (FK X N P).shared.blocksInOrder[0]? = some e ∧
      ∀ s rs gs s', e.decide s rs gs = .ok s' →
        (∀ c ∈ (fun _ : _root_.Desc.K14.St => ([] : Clauses)) s, c.2 = true) ∧ s' = s := by
  refine ⟨_, (congrArg (fun c : Chain _ Key.Claim => c.blocksInOrder[0]?) (fk_shared_is X N P )).trans rfl,
    fun s rs gs s' h => ?_⟩
  have h' : (Except.ok s : Except String _root_.Desc.K14.St) = .ok s' := h
  exact ⟨fun c hc => (by cases hc), (Except.ok.inj h').symm⟩

/-- **The last chain's four seats.** -/
theorem fk_second_at : ∃ a o e, (FK X N P).second.blocksInOrder =
    [a, atClaim (takenSources (Key.ownTest P)), o, e] :=
  ⟨_, _, _, (congrArg (fun c : Chain _ Key.Claim => c.blocksInOrder) (fk_second_is X N P )).trans rfl⟩

/-- What the block "the taken trees' sources" asks. -/
def asksTaken (own : Block S₃ Unit) (s : S₃) : Clauses :=
  [("every member of the own group, and the mask, has a tree in the book", (takenOf s).isSome),
   ("every such tree is declared as taken from the chain that sent it",
      ((takenOf s).getD []).all fun x => opensTaken own.rounds x.1 x.2),
   ("no other tree is declared as taken",
      (own.rounds.flatMap (·.opens)).all fun o =>
        match o.2 with
        | .own _ => true
        | .taken c n => ((takenOf s).getD []).contains (c, n))]

theorem taken_decide (own : Block S₃ Unit) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h : (takenSources own).decide s rs gs = .ok s') :
    (∀ c ∈ asksTaken own s, c.2 = true) ∧ s' = s := by
  have h' : ((named "every member of the own group, and the mask, has a tree in the book"
      (takenOf s)).bind fun ts =>
      (need "every such tree is declared as taken from the chain that sent it"
        (ts.all fun x => opensTaken own.rounds x.1 x.2)).bind fun _ =>
      (need "no other tree is declared as taken"
        ((own.rounds.flatMap (·.opens)).all fun o =>
          match o.2 with
          | .own _ => true
          | .taken c n => ts.contains (c, n))).bind fun _ =>
      (pure s : Except String S₃)) = .ok s' := h
  unfold asksTaken
  cases ht : takenOf s with
  | none =>
    rw [ht] at h'
    cases h'
  | some ts =>
    rw [ht] at h'
    cases h1 : (ts.all fun x => opensTaken own.rounds x.1 x.2) with
    | false =>
      have h2 : ((need "every such tree is declared as taken from the chain that sent it"
        (ts.all fun x => opensTaken own.rounds x.1 x.2)).bind fun _ =>
        (need "no other tree is declared as taken"
          ((own.rounds.flatMap (·.opens)).all fun o =>
            match o.2 with
            | .own _ => true
            | .taken c n => ts.contains (c, n))).bind fun _ =>
        (pure s : Except String S₃)) = .ok s' := h'
      rw [h1] at h2
      cases h2
    | true =>
      have h2 : ((need "every such tree is declared as taken from the chain that sent it"
        (ts.all fun x => opensTaken own.rounds x.1 x.2)).bind fun _ =>
        (need "no other tree is declared as taken"
          ((own.rounds.flatMap (·.opens)).all fun o =>
            match o.2 with
            | .own _ => true
            | .taken c n => ts.contains (c, n))).bind fun _ =>
        (pure s : Except String S₃)) = .ok s' := h'
      rw [h1] at h2
      cases h3 : ((own.rounds.flatMap (·.opens)).all fun o =>
          match o.2 with
          | .own _ => true
          | .taken c n => ts.contains (c, n)) with
      | false =>
        have h4 : ((need "no other tree is declared as taken"
          ((own.rounds.flatMap (·.opens)).all fun o =>
            match o.2 with
            | .own _ => true
            | .taken c n => ts.contains (c, n))).bind fun _ =>
          (pure s : Except String S₃)) = .ok s' := h2
        rw [h3] at h4
        cases h4
      | true =>
        have h4 : ((need "no other tree is declared as taken"
          ((own.rounds.flatMap (·.opens)).all fun o =>
            match o.2 with
            | .own _ => true
            | .taken c n => ts.contains (c, n))).bind fun _ =>
          (pure s : Except String S₃)) = .ok s' := h2
        rw [h3] at h4
        refine ⟨fun c hc => ?_, (Except.ok.inj h4).symm⟩
        rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h1
        rcases List.mem_cons.1 hc with rfl | hc
        · exact h3
        · cases hc

theorem fk_taken_pass :
    ∃ e, (FK X N P).second.blocksInOrder[1]? = some e ∧
      ∀ s rs gs s', e.decide s rs gs = .ok s' →
        (∀ c ∈ asksTaken (Key.ownTest P) s, c.2 = true) ∧ s' = s := by
  obtain ⟨a, o, e, h⟩ := fk_second_at X N P
  exact ⟨_, (congrArg (fun l => l[1]?) h).trans rfl,
    fun s rs gs s' hd => taken_decide (Key.ownTest P) s s' rs gs hd⟩

variable {F : Frame} {W : Type}

/-- **Seat 0 of the shared chain is filled.** -/
theorem fk_front₂_seat (εs : ℝ≥0∞)
    (A : JointRow (H₂ X N P × (FK X N P).S₂) F)
    (ps : List (Piece (ckP .two) F (H₂ X N P × (FK X N P).S₂) (FK X N P).Cl W))
    (rs : List (JointRow (H₂ X N P × (FK X N P).S₂) F))
    (hbs : ps.map (·.b) =
      ((FK X N P).shared.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (0 + 1) = (keyRowAt A rs 0).passed fun _ => [])
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[0]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (0 + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (0 + 1)).rel) :
    SeatGood εs A ps rs 0 := by
  obtain ⟨e, he, hd⟩ := fk_front₂_pass X N P
  exact seat_of_pass εs A ps rs _ hbs _ e he (fun _ => []) hd hrow hnd hp

/-- **Seat 1 of the last chain is filled.** -/
theorem fk_taken_seat (εs : ℝ≥0∞)
    (A : JointRow (H₃ X N P × (FK X N P).S₃) F)
    (ps : List (Piece (ckP .two) F (H₃ X N P × (FK X N P).S₃) (FK X N P).Cl W))
    (rs : List (JointRow (H₃ X N P × (FK X N P).S₃) F))
    (hbs : ps.map (·.b) =
      ((FK X N P).second.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hrow : keyRowAt A rs (1 + 1) = (keyRowAt A rs 1).passed fun t => asksTaken (Key.ownTest P) t.2)
    (hnd : (F.all.map (·.no)).Nodup)
    (hp : ∀ p, ps[1]? = some p → Err.Below p.err εs ∧
      ReadsBelow p.base (keyRowAt A rs (1 + 1)).on ∧
      ReadsBelow p.base (keyRowAt A rs (1 + 1)).rel) :
    SeatGood εs A ps rs 1 := by
  obtain ⟨e, he, hd⟩ := fk_taken_pass X N P
  exact seat_of_pass εs A ps rs _ hbs _ e he (asksTaken (Key.ownTest P)) hd hrow hnd hp

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.fk_shared_at
#print axioms Johnson.RunOne.Sound.fk_K14_at
#print axioms Johnson.RunOne.Sound.fk_second_at
#print axioms Johnson.RunOne.Sound.taken_decide
#print axioms Johnson.RunOne.Sound.fk_front₂_seat
#print axioms Johnson.RunOne.Sound.fk_taken_seat
#print axioms Johnson.RunOne.Sound.fk_shared_is
#print axioms Johnson.RunOne.Sound.fk_second_is
#print axioms Johnson.RunOne.Sound.fk_front₂_pass
#print axioms Johnson.RunOne.Sound.fk_taken_pass
