-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeHear.lean: code switching (K2): hMade, THE PREMISE ON THE MAKINGS OF ITS SHARE
OF e₁ AT «H:2» (sub-protocol number 339; share_hearP | share_hearQ, Johnson/P1K2R/SharesAtE.lean |
SharesScope.lean), GATHERED: all six public items that the place makes, under premises that are
sorted by what they read. NO BLOCK IMPORTS THIS FILE.
  HeadPlan G₀ D   CLOSED ON THE PLAN, at the head's link's letters HP (ProofFile.pureLetters G₀ 24): the
                  plan's number of slots of segment 24 is HP.hp.ns · madeLookB
                  accepts at HP's letters
  hMade_hear      hMade, to the letter, at any further Bools E
  share_hearM     share_hearQ with hMade paid so
WHAT STAYS, BY NAME: HeadPlan · hU, at the fenced states at which the promise's tests in front
hold: the head's own part has nothing heard at either seat
(Tw/K2C/HeadUnheard.lean | HeadUnheardReached.lean are its payers) · hSent: THE TWO ITEMS
"frame.sentIs" AND "ledger.treesAre" at 24: K2's FILES' TO PAY, NOT PAID YET: a named premise
(Where this and lean/THEOREM.md differ, the page
holds.) · the
share's hgrp · fresh · «D» · htok.
LIMITS. A GATHERING. No premise is shown at a value. No soundness is claimed.

-/
import Johnson.P1K2R.MadeAtHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (SwitchDebts HeadFresh frontAt frameAt madeLookB)
open ProofFile (Cl)
open IM (HandsR XK Yes linksW placesW k2P)
open _root_.Tw.K2 (switchNotices)

/-- Closed on the plan, at the head's link's letters. -/
structure HeadPlan (G₀ : ProofFile.Ground) (D : PubData) : Prop where
  hns : ∀ HP, pureLetters G₀ 24 = some HP → D.nsOf 24 = some HP.hp.ns
  hB : ∀ HP, pureLetters G₀ 24 = some HP → madeLookB D.d3 24 3 HP.X.arrayOf 0 HP.hp.ns = true

variable {Q : Type}

theorem hMade_hear {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (Pl : HeadPlan G₀ D)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat}
    (hU : ∀ s, Fk 339 s → XK N linksW placesW E 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    (hSent : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true →
      pubAll D base (.more (some 24) "frame.sentIs") (z, s') = true ∧
        pubAll D base (.more (some 24) "ledger.treesAre") (z, s') = true) :
    ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW E 339 s = true →
      ∀ e ∈ madeAt 24 3 false, pubAll D base e (z, s') = true := by
  intro s s' hf hy hu hu' hx e he
  obtain ⟨⟨g1, g2⟩, g3, g4⟩ :=
    made_hear hlot hpl D base z Pl.hns Pl.hB hy hu hu' hx (hU s hf hx)
  obtain ⟨g5, g6⟩ := hSent s s' hf hy hu hu' hx
  unfold madeAt at he
  simp only [Bool.false_eq_true, if_false, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact g1
  · exact g4
  · exact g3
  · exact g2
  · exact g5
  · exact g6

theorem share_hearM {Fk : Nat → S → Prop} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 })
    {N : Numbers} {ft : Nat} (D₀ : PubData) (base : Pub → Q × S → Bool) (z : Q)
    (Pl : HeadPlan G₀ D₀)
    (hgrp : ∀ P n, prepOf Z G₀ = some P → numsAt P (some 24) = some n → N.groupAt 24 = n.grp)
    (fresh : ∀ s, Fk 339 s → XK N linksW placesW (EP D₀ base z) 339 s = true → HeadFresh s)
    (D : ∀ nm P n (s : S) x W lay, prepOf Z G₀ = some P → numsAt P (some 24) = some n →
      Fk 339 s → XK N linksW placesW (EP D₀ base z) 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      SwitchDebts N 24 placesW[339]? placesW[339 + 1]? s.book.trees.size n.positions
        (1 + x.T.kept.size + x.own.length) x W lay)
    (htok : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      pubAll D₀ base .tokenSmall (z, s) = true → pubAll D₀ base .tokenSmall (z, s') = true)
    (hU : ∀ s, Fk 339 s → XK N linksW placesW (EP D₀ base z) 339 s = true →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    (hSent : ∀ s s', Fk 339 s → Yes ft b' s s' → s.failed = none → s'.failed = none →
      XK N linksW placesW (EP D₀ base z) 339 s = true →
      pubAll D₀ base (.more (some 24) "frame.sentIs") (z, s') = true ∧
        pubAll D₀ base (.more (some 24) "ledger.treesAre") (z, s') = true) :
    HandsR Fk N linksW placesW (EP D₀ base z) ft 339 b' :=
  share_hearQ hlot hpl D₀ base z hgrp fresh D htok
    (hMade_hear hlot hpl D₀ base z Pl hU hSent)

end P1K2

#print axioms P1K2.hMade_hear
#print axioms P1K2.share_hearM
