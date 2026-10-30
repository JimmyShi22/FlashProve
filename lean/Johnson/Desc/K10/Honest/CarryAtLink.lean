-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/CarryAtLink.lean: the premises of `carryExact_of_close` on the way in, at a link's border, from
facts on the state.

What is proved. `carryExact_of_close` (Johnson/Desc/K10/Honest/CarryOf.lean) asks three things of the way in: that the
library's way in and the front are known, that the front's single rows are the closing's, and that the front's statement
has the shapes of `D.S1 s`. **`carryExact_at_link`** brings all three back, where the code switch stands at a link's
first message (`(ProofFile.pAtK2 Zp n).stands = .link`), to:
  (a) `firstFront` returns at the state as it will be left between the links (`rest a.2`);
  (b) that state's statement is the one that the closing returned, `spent (D.S1 s) D.m`;
  (c) its frame's single rows are the ones that the closing returned.

  `sameShapes_then`   `SameShapes` is transitive
  `sameShapes_spent`  marking a message as spent changes no code and no shape
  `front_keeps`       where `firstFront` returns, its statement has the shapes of the one that it was handed, and its
                   frame has the same single rows
  `door_link`, `front_link`   the library's way in and front at such a place, unfolded
  `rest_st`, `rest_frame`, `live_putRec`   the state as it will be left between the links has the same statement and the
                   live copy's frame; the frame that the lifted closing lays back is read off the live copy
  **`carryExact_behind`**   so (b) and (c) hold at the first chain's state behind the lifted closing
                   (`K9.putRec t ⟨none, …, spent (D.S1 s) D.m⟩`, the record of `close_leaves`, at s := `K9.recOf t`);
                   (a) becomes: `firstFront` returns at that record's statement and frame. w, hw: a letter for the
                   witness's words there, and its equation
  `carryExact_of_door`   the sentence reads of the state what the way in makes of it, and nothing else: so it says the
                   same in front of and behind every step that keeps `doorZ`
  `carryExact_shut`, `carryExact_left`   so in front of and behind "the segment is shut" and the leaving of a link, by
                   the library's `doorZ_shut`, `doorZ_left` (Johnson/Top/H0/K2Caller/CarryOverShut.lean)
  `closing_leaves`    the lifted closing's decision (`K9.closing`) returns just the state of `carryExact_behind`

The library has `rest_frame`, `rest_st`, `front_link`, the second half of `front_keeps` and `live_putRec` under other
names (`Johnson.Desc.First.Walk.Tied.rest_frame`, `frontAt_link`, `firstFront_rows`;
`VerifiableInference.Desc.LinkJoin.rest_st`; `First.Close.recOf_putRec`): not called, to keep this file's imports few.

Limits. (a), (b), (c) and the place's sort are assumptions of `carryExact_at_link`; (a) and the place's sort of
`carryExact_behind`: that a state of a run meets them is not shown here. That the premises can be met together, the
place's sort aside: CarryToy.lean, at one made-up example. `closing_leaves` is on the lifted block's decision: its step
hands the decision the rounds without their digests, and two more wrappers stand around it in the first chain
(AtS.lean): not treated here. The other two sorts of place (the head, the finish) are not treated by
`carryExact_at_link` and `carryExact_behind`: see CarryAtDoor.lean. Not treated: a leaving of a link that also lays a
row (it turns a ledger in the statement, so `doorZ` is not kept; `carryExact_alike`, Exact.lean, is the tool); the step
that enters the head. All premises of `carryExact_of_close` beside the three stay. The words are made at the front's
statement and at the book of the state that the way in returns (`rest a.2`; in `carryExact_behind`: `rest` of the state
behind the closing). That, at the state behind the lifted closing, they are the words at the statement and the book in
front of the closing: `words_front` (CarryWords.lean). Of n the sentence and these theorems read the place's sort alone
(`(ProofFile.pAtK2 Zp n).stands`). No premise ties n to the link or the group of the record s. Where Zp has no switch into
group n + 1, `pAtK2` gives `deadP2` (Johnson/Desc/ProofFile/CarryAt.lean), whose sort is .link: there the theorems at a
link hold too, of a place that is none. Nothing is said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.CarryOf
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Desc.First.Close.Law.LaysLive
import Johnson.Desc.First.Batch.Place
import Johnson.Top.H0.K2Caller.CarryOverShut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.First.K2Caller (doorZ rest)
open VerifiableInference.Desc.First.K2 (SameShapes)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll)
open ProofFile.Honest.K10.Values (keptLen)

/-- `SameShapes` is transitive. -/
theorem sameShapes_then {S S' S'' : Statement} (h : SameShapes S S') (h' : SameShapes S' S'') :
    SameShapes S S'' :=
  ⟨h'.codes.trans h.codes, fun o => (h'.shape o).trans (h.shape o)⟩

/-- Marking a message as spent changes no code and no shape. -/
theorem sameShapes_spent (S : Statement) (id : Nat) : SameShapes S (spent S id) :=
  ⟨rfl, fun o => by
    show ((S.oracles.modify id _)[o]?).map _ = _
    rw [Array.getElem?_modify]
    split
    · cases S.oracles[o]? <;> rfl
    · rfl⟩

/-- Where `firstFront` returns, its statement has the shapes of the one that it was handed, and its frame has the same
single rows. -/
theorem front_keeps {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : _root_.Tw.K2.firstFront S f = .ok x) : SameShapes S x.st ∧ x.f.rows = f.rows := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S f x).1 h
  have e : S' = VerifiableInference.Desc.Ground.withGroup S f.shape.code f.shape.maskCode := by
    have o := a.opened
    unfold _root_.Tw.K2.newGroupG VerifiableInference.Desc.Ground.newGroupP at o
    split at o
    · rename_i g' d hd
      split at hd
      · cases hd
        cases o
        rfl
      · cases hd
    · cases o
  rw [a.out, e]
  exact ⟨⟨rfl, fun _ => rfl⟩, rfl⟩

/-- The library's way in at a link's first message. -/
theorem door_link {Zp : ProofFile.Pub} {n : Nat} (hst : (ProofFile.pAtK2 Zp n).stands = .link) (s : First.S) :
    doorZ Zp n s = some (rest s) := by
  unfold doorZ
  rw [hst]

/-- The front at a link's first message. -/
theorem front_link {Zp : ProofFile.Pub} {n : Nat} (hst : (ProofFile.pAtK2 Zp n).stands = .link) (t : First.S) :
    First.K2.frontAt (ProofFile.pAtK2 Zp n) t = (_root_.Tw.K2.firstFront t.st t.check.frame).toOption := by
  unfold First.K2.frontAt
  rw [hst]

/-- **The exact carry at a link's border.** -/
theorem carryExact_at_link {Q Cells Tok Cl : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat)
    (a : Q × First.S) (y : Strs) (v : Wit Cells Tok MsgT) {fx : _root_.Tw.K2.Front}
    (hst : (ProofFile.pAtK2 Zp n).stands = .link)
    (hF : _root_.Tw.K2.firstFront (rest a.2).st (rest a.2).check.frame = .ok fx)
    {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (hS : (rest a.2).st = spent (D.S1 s) D.m)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll =
      ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList (wordsFirst arr fx.st (rest a.2).book v))
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    (hrows : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      (rest a.2).check.frame.rows = foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR))
    (W : HIdx (sVars GE 2 ((stageB D s).h + (stageB D s).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D s).h + (stageB D s).g)))
    (hP : Pairs (stageB D s) (stageB D s).Z.l W
      (freshB D s (wordsFirst arr fx.st (rest a.2).book v)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 ((stageB D s).h + (stageB D s).g)) W)
    (hR : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      Shows ((stageB D s).h + (stageB D s).g) rR (foldQK (stageB D s) (vecG (stageB D s) row)
        (msgOf (stageB D s) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G)
          (wordsFirst arr fx.st (rest a.2).book v))) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G)
          (wordsFirst arr fx.st (rest a.2).book v)).kept row.kept) γ) γ) :
    carryExact Zp arr n a y v := by
  obtain ⟨k1, k2⟩ := front_keeps hF
  refine carryExact_of_close (Cl := Cl) Zp arr n a y v (door_link hst a.2)
    (by rw [front_link hst, hF]; rfl) H ?_ hlen hs rB rE rR gs hl hsh
    (fun row h => k2.trans (hrows row h)) W γ hP hσ hR
  exact sameShapes_then (sameShapes_spent (D.S1 s) D.m) (hS ▸ k1)

/-! ## At the state that the first chain carries, behind the closing -/

/-- The state as it will be left between the links has the same statement. -/
theorem rest_st (s : First.S) : (rest s).st = s.st := by
  unfold First.K2Caller.rest
  split <;> rfl

/-- Its frame is the live copy's. -/
theorem rest_frame (s : First.S) : (rest s).check.frame = s.live.frame := by
  cases hq : s.here with
  | head a =>
    by_cases ho : a.opened = true <;>
      simp [First.K2Caller.rest, First.S.inLink, First.S.fork?, First.S.live, First.S.link?, hq, ho]
  | _ => simp [First.K2Caller.rest, First.S.inLink, First.S.fork?, First.S.live, First.S.link?, hq]

/-- The frame that the lifted closing lays back is read off the live copy. -/
theorem live_putRec (t : First.S) (r : Rec) : (K9.putRec t r).live.frame = r.frame := by
  show (t.putLive { t.live with frame := r.frame }).live.frame = r.frame
  rw [First.S.live_putLive]

/-- The sentence reads of the state what the way in makes of it, and nothing else. -/
theorem carryExact_of_door {Q Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat)
    (a b : Q × First.S) (y y' : Strs) (v : Wit Cells Tok MsgT) (h : doorZ Zp n a.2 = doorZ Zp n b.2) :
    carryExact Zp arr n a y v ↔ carryExact Zp arr n b y' v := by
  unfold carryExact
  rw [h]

/-- **The exact carry at the state behind the lifted closing**, where the next code switch stands at a link's first
message. t: the first chain's state in front of the closing. -/
theorem carryExact_behind {Q Cells Tok Cl : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat) (z : Q)
    (t : First.S) (y : Strs) (v : Wit Cells Tok MsgT) {fx : _root_.Tw.K2.Front}
    (hst : (ProofFile.pAtK2 Zp n).stands = .link)
    {P : Par} {D : BaseData} (H : CloseBase P (K9.recOf t) D)
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    {row : GroupRow}
    (hrow : Own.batch (D.S1 (K9.recOf t)) (K9.recOf t).frame.group
      ⟨Own.layoutOf (K9.recOf t).st D.G, runRows (K9.recOf t).st D.G⟩ (drawnOf rB) = some row)
    (hF : _root_.Tw.K2.firstFront (spent (D.S1 (K9.recOf t)) D.m) { (K9.recOf t).frame with
      rows := foldOutAt (D.S1 (K9.recOf t)) (D.F (K9.recOf t)) row D.m (rE :: rR), mask := none
      link := (K9.recOf t).frame.link + 1, next := .first } = .ok fx)
    (w : Words GE)
    (hw : w = wordsFirst arr fx.st (rest (K9.putRec t ⟨none, { (K9.recOf t).frame with
      rows := foldOutAt (D.S1 (K9.recOf t)) (D.F (K9.recOf t)) row D.m (rE :: rR), mask := none
      link := (K9.recOf t).frame.link + 1, next := .first },
      spent (D.S1 (K9.recOf t)) D.m⟩)).book v)
    (hlen : 2 ^ (Own.layoutOf (K9.recOf t).st D.G).logEll =
      ((D.S1 (K9.recOf t)).codes.base.getD (K9.recOf t).frame.shape.code default).ell)
    (hs : AllSay rdE (K9.recOf t).st (runRows (K9.recOf t).st D.G).toList w)
    (W : HIdx (sVars GE 2 ((stageB D (K9.recOf t)).h + (stageB D (K9.recOf t)).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D (K9.recOf t)).h + (stageB D (K9.recOf t)).g)))
    (hP : Pairs (stageB D (K9.recOf t)) (stageB D (K9.recOf t)).Z.l W (freshB D (K9.recOf t) w))
    (hσ : readE ((sentOf rE).getD 0 zeroE) =
      hMu (sVars GE 2 ((stageB D (K9.recOf t)).h + (stageB D (K9.recOf t)).g)) W)
    (hR : Shows ((stageB D (K9.recOf t)).h + (stageB D (K9.recOf t)).g) rR
      (foldQK (stageB D (K9.recOf t)) (vecG (stageB D (K9.recOf t)) row)
        (msgOf (stageB D (K9.recOf t))
          (tablesOf (D.S1 (K9.recOf t)) (Own.layoutOf (K9.recOf t).st D.G) w)) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 (K9.recOf t)))
          (tablesOf (D.S1 (K9.recOf t)) (Own.layoutOf (K9.recOf t).st D.G) w).kept row.kept) γ) γ) :
    carryExact Zp arr n (z, K9.putRec t ⟨none, { (K9.recOf t).frame with
      rows := foldOutAt (D.S1 (K9.recOf t)) (D.F (K9.recOf t)) row D.m (rE :: rR), mask := none
      link := (K9.recOf t).frame.link + 1, next := .first },
      spent (D.S1 (K9.recOf t)) D.m⟩) y v := by
  subst hw
  refine carryExact_at_link (Cl := Cl) Zp arr n _ y v hst (fx := fx) ?_ H ?_ hlen hs rB rE rR gs hl hsh
    ?_ W γ hP hσ ?_
  · rw [rest_st, rest_frame, live_putRec]
    exact hF
  · rw [rest_st]
    rfl
  · intro row' h'
    obtain rfl : row = row' := Option.some.inj (hrow.symm.trans h')
    rw [rest_frame, live_putRec]
  · intro row' h'
    obtain rfl : row = row' := Option.some.inj (hrow.symm.trans h')
    exact hR

/-- **The lifted closing's decision returns just that state.** -/
theorem closing_leaves {Cl : Type} {P : Par} {t : First.S} {D : BaseData}
    (H : CloseBase P (K9.recOf t) D) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hl : (rB :: rE :: rR).length = 2 + P.k)
    (hsh : ShapedAll (rB :: rE :: rR)) :
    ∃ row, Own.batch (D.S1 (K9.recOf t)) (K9.recOf t).frame.group
        ⟨Own.layoutOf (K9.recOf t).st D.G, runRows (K9.recOf t).st D.G⟩ (drawnOf rB) = some row ∧
      (K9.closing (Cl := Cl) P).decide t (rB :: rE :: rR) gs = .ok (K9.putRec t ⟨none,
        { (K9.recOf t).frame with
          rows := foldOutAt (D.S1 (K9.recOf t)) (D.F (K9.recOf t)) row D.m (rE :: rR), mask := none
          link := (K9.recOf t).frame.link + 1, next := .first },
        spent (D.S1 (K9.recOf t)) D.m⟩) := by
  obtain ⟨row, hrow, hdec⟩ := ProofFile.Honest.K10.Values.close_leaves (Cl := Cl) H rB rE rR gs hl hsh
  refine ⟨row, hrow, ?_⟩
  show (((First.Close.kind (Cl := Cl)) P).decide (K9.recOf t) (rB :: rE :: rR) gs).map (K9.putRec t) = _
  rw [hdec]
  rfl

/-- The sentence says the same in front of and behind "the segment is shut". -/
theorem carryExact_shut {Q Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat) (z z' : Q)
    {s : First.S} {L : OnBytes.Model.LinkCtx} (hL : s.link? = some L) (y y' : Strs)
    (v : Wit Cells Tok MsgT) :
    carryExact Zp arr n (z, s) y v ↔
      carryExact Zp arr n (z', s.putLink (K9.closed L L.check.frame)) y' v :=
  carryExact_of_door Zp arr n _ _ y y' v (First.K2Caller.doorZ_shut Zp n hL).symm

/-- The sentence says the same in front of and behind the leaving of a link, where a link is open and the live copy's
flag is down; at the head's sort: where the state does not stand in the head. -/
theorem carryExact_left {Q Cells Tok : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat) (z z' : Q)
    {s : First.S} (hi : s.inLink = true) (hf : s.live.inLink = false)
    (hh : (ProofFile.pAtK2 Zp n).stands = .head → ∀ a, s.here ≠ .head a) (y y' : Strs)
    (v : Wit Cells Tok MsgT) :
    carryExact Zp arr n (z, s) y v ↔ carryExact Zp arr n (z', s.leaveLink) y' v :=
  carryExact_of_door Zp arr n _ _ y y' v (First.K2Caller.doorZ_left Zp n hi hf hh).symm

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.closing_leaves
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_shut
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_left
#print axioms ProofFile.Honest.K10.LeftIs.rest_st
#print axioms ProofFile.Honest.K10.LeftIs.rest_frame
#print axioms ProofFile.Honest.K10.LeftIs.live_putRec
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_of_door
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_behind
#print axioms ProofFile.Honest.K10.LeftIs.sameShapes_then
#print axioms ProofFile.Honest.K10.LeftIs.sameShapes_spent
#print axioms ProofFile.Honest.K10.LeftIs.front_keeps
#print axioms ProofFile.Honest.K10.LeftIs.door_link
#print axioms ProofFile.Honest.K10.LeftIs.front_link
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_at_link
