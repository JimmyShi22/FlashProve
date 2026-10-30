-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/AsksWhole.lean: the kind «the code switch»: WHAT THE DECISION's YES ASKS, BOTH
WAYS, AT EACH OF ITS THREE SORTS OF PLACE. NO BLOCK IMPORTS THIS FILE.
K2C/Closed.lean proves, at the outer layers, the direction from a yes to the closed form
(readOld_inv · switchE_inv · link_inv · head_inv · finish_inv). Here stand the converses, and so:
  readOld_iff     the reading of the old rows says (B, left, y)  ⇔  ReadIs …
  switchE_iff     guard, sending and the step behind say (w, roots)  ⇔  SwitchIs …
  link_iff        at a place that stands at a link:   decideWith snd p s rs gs = .ok s'  ⇔  rs =
      [r₁, r₂] and LinkIs …
  head_iff        at the head's link:                 …  ⇔  rs = [r₁, r₂] and HeadIs …
  finish_iff      at the finish:                      …  ⇔  rs = [r₁, r₂] and FinIs …
With K2C/Asks.lean (firstFront_iff · firstBehind_iff · openOne_iff …), K2C/Closed.lean
(locPositions_iff · switchBehind_iff), K2C/Laws.lean, K2C/Yard.lean, K2/TargetAgree.lean,
K2/RowsMadeAgree.lean and K2/RowsCanMeans.lean each test of the running text that we know of stands
in a statement that goes both ways.
TRIED, NOT PROVED: in working copies of the running text, kept out of every tree, one test at a time
was struck, weakened or made stricter, and the law files were built over each copy with no proof
mended. Before this file and Asks.lean were written, seventeen such copies left every law file
green; with them none of the copies that we tried does. A build that fails shows that a proof
breaks, not which statement would be false; and a guard at which a value would lack (a «match» on
nothing) cannot be struck in this way.
WHAT STAYS A NAME: the sending (a letter snd; the block lays sendByL8), the plain ground's adapters,
the walk's firstDue | firstKept, Own.symbolsAt | rowsSymbols | colsStand, the maker of the rows.
No soundness is claimed: this says what the text asks, not that it asks enough.

-/
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut readOld switchBehind switchE firstEW chainFirstEW firstFront
    firstBehind switchGuard switchNotices switchAloneEW headSwitchEW finishSwitchEW)
open Johnson.Desc.First.Walk (firstDue firstKept)

theorem readOld_of {i : SwIn} {pos B left y places cols opened} (k : ReadIs i pos B left y places
    cols opened) :
    readOld i pos = .ok (B, left, y) := by
  unfold readOld
  simp only [k.hPlaces, k.hAll, Bool.not_true, Bool.false_eq_true, if_false, k.hOpen, k.hSymbols,
      k.hLayout]

theorem readOld_iff (i : SwIn) (pos : Positions) (B : TreeBook) (left : List _root_.Tw.K2.Col) (y :
    Array E) :
    readOld i pos = .ok (B, left, y) ↔ ∃ places cols opened, ReadIs i pos B left y places cols
        opened :=
  ⟨readOld_inv, fun ⟨_, _, _, k⟩ => readOld_of k⟩

theorem switchE_of {behind P send s x rS rL cols w roots y} (k : SwitchIs behind P send s x rS rL
    cols w roots y) :
    switchE behind P send s x rS rL cols = .ok (w, roots) := by
  have hs := k.hSend
  rw [k.hSettled] at hs
  have ht : ¬ rL.vals.length < y.took := by have := k.hTook; omega
  have hT : (y.roots != s.roots + P.eSeed.roots) = false := by simp [k.hTrees]
  have hb := k.hBehind
  unfold behindArgs at hb
  unfold switchE
  simp only [bind, Except.bind, pure, Except.pure, k.hSettled, k.hRows, k.hGuard, hs, ht, hT, hb,
      k.hRoots, Bool.not_true,
    Bool.false_eq_true, if_false, bne_self_eq_false]

theorem switchE_iff (behind : SwIn → Except String SwOut) (P : _root_.Tw.K2.Par9) (send :
    _root_.Tw.K2.SendFn) (s : _root_.Tw.K2.S9)
    (x : _root_.Tw.K2.Front) (rS rL : Fmt.RoundView) (cols : List _root_.Tw.K2.Col) (w : SwOut) (roots :
               Nat) :
    switchE behind P send s x rS rL cols = .ok (w, roots) ↔ ∃ y, SwitchIs behind P send s x rS rL
        cols w roots y :=
  ⟨switchE_inv, fun ⟨_, k⟩ => switchE_of k⟩

theorem inRange_two {p : P2} {r₁ r₂ : Fmt.RoundView} (h : ∀ q ∈ r₂.drawn.poss, q < 2 ^ p.logN) : inRange p
    [r₁, r₂] = true := by
  simp [inRange]
  exact h

theorem allTaken_of {p : P2} {gs : List (List (Nat × List UInt64))} {left : List _root_.Tw.K2.Col}
    (h : left = [] ∧ gs.length = p.read.length) : allTaken p gs left = .ok () := by
  unfold allTaken
  simp [h.1, h.2]

theorem rightGroup_of {p : P2} {g : Nat} (h : g = p.grp) : rightGroup p g = .ok () := by
  unfold rightGroup
  simp [h]

theorem link_of {snd p s r₁ r₂ gs s' x w roots S' f mine} (hp : p.stands = .link)
    (k : LinkIs snd p s r₁ r₂ gs s' x w roots S' f mine) : decideWith snd p s [r₁, r₂] gs = .ok s'
        := by
  have hpl : ([] : List E).length = x.plain := by rw [k.hPlain]; rfl
  have h1 : firstEW switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, s.check.frame, [],
      s.noneWaits⟩ [r₁, r₂] (flat p gs) =
      .ok (⟨S', w.book, roots, f, [], (par9 p).eLoc.rows == 0⟩, w.opened) := by
    unfold firstEW
    simp only [bind, Except.bind, pure, Except.pure, k.hFront, k.hSwitch, k.hBehind, hpl,
        bne_self_eq_false, Bool.false_eq_true, if_false]
  have h2 : chainFirstEW switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, s.check, s.noneWaits⟩
      [r₁, r₂] (flat p gs) =
      .ok (⟨S', w.book, roots, firstKept s.check f f.own, (par9 p).eLoc.rows == 0⟩, w.opened) := by
    unfold chainFirstEW
    simp only [k.hDue, Bool.not_true, Bool.false_eq_true, if_false, bind, Except.bind, pure,
        Except.pure, h1]
  unfold decideWith
  simp only [inRange_two k.hRange, Bool.not_true, Bool.false_eq_true, if_false, hp, k.hHere, bind,
      Except.bind, pure, Except.pure, h2,
    allTaken_of k.hTaken]
  have hg : rightGroup p (firstKept s.check f f.own).frame.group = .ok () := rightGroup_of k.hGrp
  simp only [hg, k.hOut, k.hHere]

theorem link_iff (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (rs : List Fmt.RoundView) (gs : List (List
           (Nat × List UInt64))) (s' : S)
    (hp : p.stands = .link) :
    decideWith snd p s rs gs = .ok s' ↔
      ∃ r₁ r₂ x w roots S' f mine, rs = [r₁, r₂] ∧ LinkIs snd p s r₁ r₂ gs s' x w roots S' f mine :=
  ⟨link_inv hp, fun ⟨_, _, _, _, _, _, _, _, e, k⟩ => e ▸ link_of hp k⟩

theorem switchAloneEW_of {behind P send} {s : _root_.Tw.K2.S9S} {x rS rL cols w roots}
    (h : switchE behind P send ⟨s.st, s.book, s.roots, x.f, [], s.settled⟩ x rS rL cols = .ok (w,
        roots)) :
    switchAloneEW behind P send s x [rS, rL] cols = .ok (w.out, ⟨w.st, w.book, roots, P.eLoc.rows ==
        0⟩, w.opened) := by
  unfold switchAloneEW
  simp only [bind, Except.bind, pure, Except.pure, h]

theorem head_of {snd p s r₁ r₂ gs s' a G w roots} (hp : p.stands = .head)
    (k : HeadIs snd p s r₁ r₂ gs s' a G w roots) : decideWith snd p s [r₁, r₂] gs = .ok s' := by
  have h1 : headSwitchEW switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, s.noneWaits⟩
      s.check.frame a.fr [r₁, r₂] (flat p gs) =
      .ok (w.out, ⟨w.st, w.book, roots, (par9 p).eLoc.rows == 0⟩, w.opened) := by
    unfold headSwitchEW
    simp only [k.hGroup]
    exact switchAloneEW_of k.hSwitch
  unfold decideWith
  simp only [inRange_two k.hRange, Bool.not_true, Bool.false_eq_true, if_false, hp, k.hHere, bind,
      Except.bind, pure, Except.pure,
    rightGroup_of k.hGrp, h1, allTaken_of k.hTaken, k.hOut]

theorem head_iff (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (rs : List Fmt.RoundView) (gs : List (List
           (Nat × List UInt64))) (s' : S)
    (hp : p.stands = .head) :
    decideWith snd p s rs gs = .ok s' ↔ ∃ r₁ r₂ a G w roots, rs = [r₁, r₂] ∧ HeadIs snd p s r₁ r₂ gs
        s' a G w roots :=
  ⟨head_inv hp, fun ⟨_, _, _, _, _, _, e, k⟩ => e ▸ head_of hp k⟩

theorem finish_of {snd p s r₁ r₂ gs s' a G w roots} (hp : p.stands = .finish)
    (k : FinIs snd p s r₁ r₂ gs s' a G w roots) : decideWith snd p s [r₁, r₂] gs = .ok s' := by
  have h1 : finishSwitchEW switchBehind (par9 p) snd ⟨s.st, s.book, s.roots, s.noneWaits⟩ a.fr
      G.target [r₁, r₂] (flat p gs) =
      .ok (w.out, ⟨w.st, w.book, roots, (par9 p).eLoc.rows == 0⟩, w.opened) := by
    unfold finishSwitchEW
    exact switchAloneEW_of k.hSwitch
  unfold decideWith
  simp only [inRange_two k.hRange, Bool.not_true, Bool.false_eq_true, if_false, hp, k.hHere, bind,
      Except.bind, pure, Except.pure,
    rightGroup_of k.hGrp, k.hLaid, Option.elim, h1, allTaken_of k.hTaken, k.hOut]

theorem finish_iff (snd : _root_.Tw.K2.SendFn) (p : P2) (s : S) (rs : List Fmt.RoundView) (gs : List (List
           (Nat × List UInt64))) (s' : S)
    (hp : p.stands = .finish) :
    decideWith snd p s rs gs = .ok s' ↔ ∃ r₁ r₂ a G w roots, rs = [r₁, r₂] ∧ FinIs snd p s r₁ r₂ gs
        s' a G w roots :=
  ⟨finish_inv hp, fun ⟨_, _, _, _, _, _, e, k⟩ => e ▸ finish_of hp k⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.readOld_iff
#print axioms VerifiableInference.Desc.First.K2.switchE_iff
#print axioms VerifiableInference.Desc.First.K2.link_iff
#print axioms VerifiableInference.Desc.First.K2.head_iff
#print axioms VerifiableInference.Desc.First.K2.finish_iff
