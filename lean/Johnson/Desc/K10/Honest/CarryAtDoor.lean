-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/CarryAtDoor.lean: two premises of `carryExact_of_close` on the way in, at all three sorts of
place, from facts on the state.

What is proved. `carryExact_of_close` (Johnson/Desc/K10/Honest/CarryOf.lean) asks of the way in that the front's single
rows are the closing's and that the front's statement has the shapes of `D.S1 s`. **`carryExact_at_door`** brings both
back, wherever the next code switch stands (a link's first message, the head's link, the finish) and where the library's
way in and the front return, to: the state's statement is the one that the closing returned, `spent (D.S1 s) D.m`; its
live frame's single rows are the ones that the closing returned. **`carryExact_behind_door`**: these two hold at the
first chain's state s₁ behind the lifted closing (t: what the way in returns there).

  `shapes_newGroup`   opening a new group changes no code and no shape
  `finish_keeps`      where `finishFront` returns, its statement has the shapes of the one that it was handed
  `front_st_head`, `front_st_finish`   at the head's link and at the finish the front's statement is that of the state t
                   at which it is made
  **`door_shapes`**    the front's statement has the shapes of the statement of the state s in front of the way in, at
                   all three sorts
  `door_reads`        the library's `DoorReads` (Johnson/Top/H0/Walk/FrameCarryFenceEnds.lean) at all three sorts: what
                   the way in returns has the state's book and number of roots, and its front's single rows are the live
                   frame's

Limits. That the way in and the front return, and, at the head's sort, that the state does not yet stand in the head,
are assumptions: that a state of a run meets them is not shown here. That the premises can be met together:
CarryToy.lean meets those of `carryExact_behind` (CarryAtLink.lean) at one made-up example, the place's sort aside:
.link stays a premise there. Of this file's premises no theorem states it; at the head's and the finish's sort there is
no example. All premises of `carryExact_of_close` beside the two stay. The words are made at the front's statement and
at the book of the state t that the way in returns. That, at the state behind the lifted closing, they are the words at
the statement and the book in front of the closing: `words_front` (CarryWords.lean). Of n the sentence and these
theorems read the place's sort alone (`(ProofFile.pAtK2 Zp n).stands`). No premise ties n to the link or the group of the
record s. Where Zp has no switch into group n + 1, `pAtK2` gives `deadP2` (Johnson/Desc/ProofFile/CarryAt.lean), whose
sort is .link: there the theorems at a link (CarryAtLink.lean) hold too, of a place that is none. Nothing is said on
soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.CarryAtLink
import Johnson.Top.H0.Walk.FrameCarryFenceEnds
import Johnson.Top.H0.Tw.K2C.FrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.LeftIs
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.First.K2 (SameShapes)
open Johnson.Desc.First.Walk.Tied (DoorReads doorReads_link doorReads_head doorReads_finish doorZ_head
  doorZ_finish toOption_some)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase ShapedAll)
open ProofFile.Honest.K10.Values (keptLen)

/-- Opening a new group changes no code and no shape. -/
theorem shapes_newGroup {S S' : Statement} {c m g : Nat}
    (h : _root_.Tw.K2.newGroupG S c m = .ok (S', g)) : SameShapes S S' := by
  rw [(First.K2.newGroupG_is h).1]
  exact ⟨rfl, fun _ => rfl⟩

/-- Where `finishFront` returns, its statement has the shapes of the one that it was handed. -/
theorem finish_keeps {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : _root_.Tw.K2.finishFront S f = .ok x) : SameShapes S x.st := by
  obtain ⟨G, S', g, a⟩ := (_root_.Tw.K2.finishFront_iff S f x).1 h
  rw [a.out]
  exact shapes_newGroup a.opened

/-- At the head's link the front's statement is that of the state t at which it is made. -/
theorem front_st_head {p : First.K2.P2} {t : First.S} {fx : _root_.Tw.K2.Front} (hp : p.stands = .head)
    (hf : First.K2.frontAt p t = some fx) : fx.st = t.st := by
  unfold First.K2.frontAt at hf
  cases hh : t.here with
  | head a =>
    simp only [hp, hh] at hf
    obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    rfl
  | _ => simp [hp, hh] at hf

/-- At the finish the front's statement is that of the state t at which it is made. -/
theorem front_st_finish {p : First.K2.P2} {t : First.S} {fx : _root_.Tw.K2.Front}
    (hp : p.stands = .finish) (hf : First.K2.frontAt p t = some fx) : fx.st = t.st := by
  unfold First.K2.frontAt at hf
  cases hh : t.here with
  | fin a =>
    simp only [hp, hh] at hf
    obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    rfl
  | _ => simp [hp, hh] at hf

/-- **The front's statement has the shapes of the statement of the state s in front of the way in**, at all three sorts
of place. -/
theorem door_shapes {Zp : ProofFile.Pub} {n : Nat} {s t : First.S} {fx : _root_.Tw.K2.Front}
    (hH : (ProofFile.pAtK2 Zp n).stands = .head → ∀ a, s.here ≠ .head a)
    (hd : doorZ Zp n s = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx) :
    SameShapes s.st fx.st := by
  cases hp : (ProofFile.pAtK2 Zp n).stands with
  | link =>
    rw [door_link hp] at hd
    obtain rfl := Option.some.inj hd
    rw [front_link hp] at hf
    have k := (front_keeps (toOption_some hf)).1
    rwa [rest_st] at k
  | head =>
    rw [doorZ_head hp (hH hp)] at hd
    obtain ⟨x, s₁, a, k⟩ := (First.K2.headFrontQ_iff _ _ _).1 (toOption_some hd)
    have e : t.st = x.st := by rw [k.out]
    rw [front_st_head hp hf, e]
    have k' := (front_keeps k.front).1
    rwa [rest_st] at k'
  | finish =>
    rw [doorZ_finish hp] at hd
    obtain ⟨G, x, s₁, a, k⟩ := (First.K2.finishFrontQ_iff _ _).1 (toOption_some hd)
    have e : t.st = x.st := by rw [k.out]
    rw [front_st_finish hp hf, e]
    have k' := finish_keeps k.front
    rwa [rest_st] at k'

/-- The library's `DoorReads`, at all three sorts of place. -/
theorem door_reads {Zp : ProofFile.Pub} {n : Nat} {s t : First.S}
    (hH : (ProofFile.pAtK2 Zp n).stands = .head → ∀ a, s.here ≠ .head a)
    (hd : doorZ Zp n s = some t) : DoorReads (ProofFile.pAtK2 Zp n) s t := by
  cases hp : (ProofFile.pAtK2 Zp n).stands with
  | link => exact doorReads_link hp hd
  | head => exact doorReads_head hp (hH hp) hd
  | finish => exact doorReads_finish hp hd

/-- **The exact carry, wherever the next code switch stands.** -/
theorem carryExact_at_door {Q Cells Tok Cl : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat)
    (a : Q × First.S) (y : Strs) (v : Wit Cells Tok MsgT) {t : First.S} {fx : _root_.Tw.K2.Front}
    (hH : (ProofFile.pAtK2 Zp n).stands = .head → ∀ x, a.2.here ≠ .head x)
    (hd : doorZ Zp n a.2 = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx)
    {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (hS : a.2.st = spent (D.S1 s) D.m)
    (hlen : 2 ^ (Own.layoutOf s.st D.G).logEll =
      ((D.S1 s).codes.base.getD s.frame.shape.code default).ell)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList (wordsFirst arr fx.st t.book v))
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    (hrows : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      a.2.live.frame.rows = foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR))
    (W : HIdx (sVars GE 2 ((stageB D s).h + (stageB D s).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D s).h + (stageB D s).g)))
    (hP : Pairs (stageB D s) (stageB D s).Z.l W (freshB D s (wordsFirst arr fx.st t.book v)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 ((stageB D s).h + (stageB D s).g)) W)
    (hR : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      Shows ((stageB D s).h + (stageB D s).g) rR (foldQK (stageB D s) (vecG (stageB D s) row)
        (msgOf (stageB D s) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G)
          (wordsFirst arr fx.st t.book v))) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G)
          (wordsFirst arr fx.st t.book v)).kept row.kept) γ) γ) :
    carryExact Zp arr n a y v :=
  carryExact_of_close (Cl := Cl) Zp arr n a y v hd hf H
    (sameShapes_then (sameShapes_spent (D.S1 s) D.m) (hS ▸ door_shapes hH hd hf)) hlen hs rB rE rR gs
    hl hsh (fun row h => ((door_reads hH hd).rows fx hf).trans (hrows row h)) W γ hP hσ hR

/-- **The exact carry at the state behind the lifted closing**, wherever the next code switch stands. t₀: the first
chain's state in front of the closing. -/
theorem carryExact_behind_door {Q Cells Tok Cl : Type} (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (n : Nat)
    (z : Q) (t₀ : First.S) (y : Strs) (v : Wit Cells Tok MsgT) {t : First.S}
    {fx : _root_.Tw.K2.Front} {P : Par} {D : BaseData} (H : CloseBase P (K9.recOf t₀) D)
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR))
    {row : GroupRow}
    (hrow : Own.batch (D.S1 (K9.recOf t₀)) (K9.recOf t₀).frame.group
      ⟨Own.layoutOf (K9.recOf t₀).st D.G, runRows (K9.recOf t₀).st D.G⟩ (drawnOf rB) = some row)
    (s₁ : First.S)
    (hs₁ : s₁ = K9.putRec t₀ ⟨none, { (K9.recOf t₀).frame with
      rows := foldOutAt (D.S1 (K9.recOf t₀)) (D.F (K9.recOf t₀)) row D.m (rE :: rR), mask := none
      link := (K9.recOf t₀).frame.link + 1, next := .first },
      spent (D.S1 (K9.recOf t₀)) D.m⟩)
    (hH : (ProofFile.pAtK2 Zp n).stands = .head → ∀ x, s₁.here ≠ .head x)
    (hd : doorZ Zp n s₁ = some t) (hf : First.K2.frontAt (ProofFile.pAtK2 Zp n) t = some fx)
    (hlen : 2 ^ (Own.layoutOf (K9.recOf t₀).st D.G).logEll =
      ((D.S1 (K9.recOf t₀)).codes.base.getD (K9.recOf t₀).frame.shape.code default).ell)
    (hs : AllSay rdE (K9.recOf t₀).st (runRows (K9.recOf t₀).st D.G).toList
      (wordsFirst arr fx.st t.book v))
    (W : HIdx (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)) → GE)
    (γ : HPt (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)))
    (hP : Pairs (stageB D (K9.recOf t₀)) (stageB D (K9.recOf t₀)).Z.l W
      (freshB D (K9.recOf t₀) (wordsFirst arr fx.st t.book v)))
    (hσ : readE ((sentOf rE).getD 0 zeroE) =
      hMu (sVars GE 2 ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g)) W)
    (hR : Shows ((stageB D (K9.recOf t₀)).h + (stageB D (K9.recOf t₀)).g) rR
      (foldQK (stageB D (K9.recOf t₀)) (vecG (stageB D (K9.recOf t₀)) row)
        (msgOf (stageB D (K9.recOf t₀)) (tablesOf (D.S1 (K9.recOf t₀))
          (Own.layoutOf (K9.recOf t₀).st D.G) (wordsFirst arr fx.st t.book v))) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 (K9.recOf t₀))) (tablesOf (D.S1 (K9.recOf t₀))
          (Own.layoutOf (K9.recOf t₀).st D.G) (wordsFirst arr fx.st t.book v)).kept row.kept) γ) γ) :
    carryExact Zp arr n (z, s₁) y v := by
  refine carryExact_at_door (Cl := Cl) Zp arr n (z, s₁) y v hH hd hf H ?_ hlen hs rB rE rR gs hl hsh
    ?_ W γ hP hσ ?_
  · rw [hs₁]
    rfl
  · intro row' h'
    obtain rfl : row = row' := Option.some.inj (hrow.symm.trans h')
    show s₁.live.frame.rows = _
    rw [hs₁, live_putRec]
  · intro row' h'
    obtain rfl : row = row' := Option.some.inj (hrow.symm.trans h')
    exact hR

end ProofFile.Honest.K10.LeftIs

#print axioms ProofFile.Honest.K10.LeftIs.carryExact_behind_door
#print axioms ProofFile.Honest.K10.LeftIs.shapes_newGroup
#print axioms ProofFile.Honest.K10.LeftIs.finish_keeps
#print axioms ProofFile.Honest.K10.LeftIs.front_st_head
#print axioms ProofFile.Honest.K10.LeftIs.front_st_finish
#print axioms ProofFile.Honest.K10.LeftIs.door_shapes
#print axioms ProofFile.Honest.K10.LeftIs.door_reads
#print axioms ProofFile.Honest.K10.LeftIs.carryExact_at_door
