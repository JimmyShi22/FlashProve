-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/AtWritten.lean: FROM PINS, `Key.rangesNumbers m` AND `Key.laterPlaces m`
RETURN THE WRITTEN VALUES. General in m: the written values stand in the premises and in the ends
alone; nothing is evaluated.

`Johnson.KB8.rangesNumsFull` and `laterPlacesFull` (Johnson/HB/LLHARD/KB8/Written.lean) are the
numbers of a key file's four proximity tests' places at the full size, written out. Most of their
fields are the makers' own expressions at the typed sizes (`Lk6.AtPlan.keyFull`) and the typed
setting (`recordSet`). Four fields of each place were typed by hand there: start, first, free,
firstTree.

IT PAYS NOTHING. Each premise below is a debt: `treesSent`'s returns; that m's sizes and setting are
the typed ones; and one premise for each number or tree that was typed by hand. None is shown at any
m here. The laws cannot make the typed numbers true: they name them.
  `rangesAt_written`: `rangesAt m t₀ i = rangesNumsFull`, from: the two pins; i = 18805; the trees
    that the first opening reads; the roots in front are 2.
  `laterAt_written`: `laterAt m (firstsAt m t₀ t₁) tU tW = laterPlacesFull`, from: the two pins; the
    number of the ranges' stages, which the routine reads at another field of m; of each of the
    three cuts its start, roots and stages; that Omega's cut is there and the typed shape splits; of
    each place the trees that its first opening reads; the first chain sends six trees.
  `omegaCut_eq`: Omega's cut is `H2U.cutOn` at the shared chain's second "BAT".
  `rangesNumbers_written`, `laterPlaces_written`: these joined with OfCuts.lean: the routines return
    the written values. A cut's start, roots and stages are not asked: they follow from
    `H2U.cutOn`'s return (`H2K.Made.cutOn_free`, Johnson/Desc/K12/Law/FreeOfMade.lean;
    `H2K.Sizes.cutOn_stages`, Johnson/Desc/K12/Law/Sizes/IdxAtScope.lean).
Limits. Whether the numbers typed by hand are right is not said: where one is wrong, its premise can
be met by no m at which the routine returns, and the law is idle.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.OfCuts
import Johnson.Desc.K12.Law.Sizes.IdxAtScope
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

/-- **r2's value is the written one**, from the pins and the four fields typed by hand. -/
theorem rangesAt_written (m : Made) (t₀ : List (Sent × Nat)) (i : Nat)
    (hk : m.p.chains.made.sized.key = keyFull)
    (hset : m.p.chains.made.sized.set = recordSet)
    (hi : i = 18805)
    (hfirst : rangesFirst t₀ = [(⟨22, 77, false, 1⟩, .own 1)])
    (hfree : (((plan₀ m).rounds.take i).map (·.roots)).foldl (· + ·) 0 = 2) :
    rangesAt m t₀ i = Johnson.KB8.rangesNumsFull := by
  unfold rangesAt Johnson.KB8.rangesNumsFull
  rw [hfree, hfirst, hk, hset, hi]

/-- **r3's value is the written one**, from the pins and the fields typed by hand. -/
theorem laterAt_written (m : Made) (t₀ t₁ : List (Sent × Nat)) (tU tO tW : H2U.TestCut)
    (hk : m.p.chains.made.sized.key = keyFull)
    (hset : m.p.chains.made.sized.set = recordSet)
    (hr : m.p.chains.key.oneTime.ranges.stages.length = keyFull.ranges.x.stages.length)
    (hUs : tU.start = 8) (hUr : tU.roots = 3) (hUt : tU.stages = keyFull.once.shape.testU)
    (hO : omegaCut m = some tO)
    (hOs : tO.start = 43) (hOr : tO.roots = 7) (hOt : tO.stages = keyFull.once.shape.testOmega)
    (hWs : tW.start = 0) (hWr : tW.roots = 0) (hWt : tW.stages = keyFull.once.shape.testOwn)
    (hfU : foldedFirst keyFull.once.shape t₁ =
      [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)])
    (hsp : keyFull.once.shape.sharedSplitNeeded = true)
    (hfO : ((sharedOpens keyFull.once.shape t₁)[2 + (switchOpens 0 .folded t₁).length]?).map
        (fun x => (x.1.dropLast, 0)) =
      some ([(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)], 0))
    (hfW : ownFirst keyFull.once.shape t₀ t₁ =
      [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 12, false, 5⟩, .taken 0 5),
        (⟨22, 36, false, 1⟩, .taken 1 1)])
    (hn : t₀.length = 6) :
    laterAt m (firstsAt m t₀ t₁) tU tW = Johnson.KB8.laterPlacesFull := by
  have hS : shapeK m = keyFull.once.shape := by
    show m.p.chains.made.sized.key.once.shape = _
    rw [hk]
  have hFO : (firstsAt m t₀ t₁).O =
      some ([(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)], 0) := by
    unfold firstsAt
    dsimp only
    rw [hS, if_pos hsp]
    exact hfO
  unfold laterAt Johnson.KB8.laterPlacesFull
  rw [hO, hFO]
  unfold firstsAt sharedScope H2U.mkPlace Johnson.KB8.scopeShared
  simp only [hS, hk, hset, hr, hUs, hUr, hUt, hOs, hOr, hOt, hWs, hWr, hWt, hfU, hfW, hn]

/-- Omega's cut is `H2U.cutOn` at the shared chain's second "BAT". -/
theorem omegaCut_eq (m : Made) (P₁ : Planned) (j : Nat)
    (hP₁ : m.p.chains.made.key[1]? = some P₁)
    (hb : (H2U.batPlaces (P₁.rounds.map (·.entry)))[1]? = some j) :
    omegaCut m = H2U.cutOn (P₁.rounds.map (·.entry)) 1 j (shapeK m).testOmega := by
  rw [← keyTestCut_eq _ 1 j _ P₁ hP₁]
  simp only [omegaCut, keyBatchRounds, hP₁, Option.map_some, Option.bind_eq_bind,
    Option.bind_some, hb]

/-- **r2 at the written value**: `Key.rangesNumbers m` returns `rangesNumsFull`. -/
theorem rangesNumbers_written (m : Made) (t₀ : List (Sent × Nat)) (pre post : List Fmt.Entry)
    (b : Fmt.Entry)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (hk : m.p.chains.made.sized.key = keyFull)
    (hset : m.p.chains.made.sized.set = recordSet)
    (hs : (plan₀ m).rounds = pre ++ b :: post)
    (hp : noBat pre = true) (hb : b.name = "BAT") (hlen : pre.length = 18805)
    (hg : rangesGuard m 18805 = true)
    (hfirst : rangesFirst t₀ = [(⟨22, 77, false, 1⟩, .own 1)])
    (hfree : (pre.map (·.roots)).foldl (· + ·) 0 = 2) :
    rangesNumbers m = .ok Johnson.KB8.rangesNumsFull := by
  rw [rangesNumbers_of_split m t₀ pre post b h₀ hs hp hb (by rw [hlen]; exact hg),
    rangesAt_written m t₀ pre.length hk hset hlen hfirst
      (by rw [hs, List.take_left]; exact hfree)]

/-- **r3 at the written value**: `Key.laterPlaces m` returns `laterPlacesFull`. -/
theorem laterPlaces_written (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (P₁ P₂ : Planned)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (h₁ : treesSent "key file, shared chain" m.key.2.1 (plan₁ m)
      (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁)
    (h₂ : treesSent "key file, second chain" m.key.2.2 (plan₂ m) [] = .ok t₂)
    (hk : m.p.chains.made.sized.key = keyFull)
    (hset : m.p.chains.made.sized.set = recordSet)
    (hr : m.p.chains.key.oneTime.ranges.stages.length = keyFull.ranges.x.stages.length)
    (hP₁ : m.p.chains.made.key[1]? = some P₁)
    (hbU : (H2U.batPlaces (P₁.rounds.map (·.entry))).head? = some 8)
    (hbO : (H2U.batPlaces (P₁.rounds.map (·.entry)))[1]? = some 43)
    (hU : (H2U.cutOn (P₁.rounds.map (·.entry)) 1 8 keyFull.once.shape.testU).isSome = true)
    (hO : (H2U.cutOn (P₁.rounds.map (·.entry)) 1 43 keyFull.once.shape.testOmega).isSome = true)
    (hrU : (((P₁.rounds.map (·.entry)).take 8).map (·.roots)).foldl (· + ·) 0 = 3)
    (hrO : (((P₁.rounds.map (·.entry)).take 43).map (·.roots)).foldl (· + ·) 0 = 7)
    (hP₂ : m.p.chains.made.key[2]? = some P₂)
    (hbW : (H2U.batPlaces (P₂.rounds.map (·.entry))).head? = some 0)
    (hW : (H2U.cutOn (P₂.rounds.map (·.entry)) 2 0 keyFull.once.shape.testOwn).isSome = true)
    (hfU : foldedFirst keyFull.once.shape t₁ =
      [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)])
    (hsp : keyFull.once.shape.sharedSplitNeeded = true)
    (hfO : ((sharedOpens keyFull.once.shape t₁)[2 + (switchOpens 0 .folded t₁).length]?).map
        (fun x => (x.1.dropLast, 0)) =
      some ([(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)], 0))
    (hfW : ownFirst keyFull.once.shape t₀ t₁ =
      [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 12, false, 5⟩, .taken 0 5),
        (⟨22, 36, false, 1⟩, .taken 1 1)])
    (hn : t₀.length = 6) :
    laterPlaces m = .ok Johnson.KB8.laterPlacesFull := by
  have hS : shapeK m = keyFull.once.shape := by
    show m.p.chains.made.sized.key.once.shape = _
    rw [hk]
  obtain ⟨tU, hU⟩ := Option.isSome_iff_exists.1 hU
  obtain ⟨tO, hO⟩ := Option.isSome_iff_exists.1 hO
  obtain ⟨tW, hW⟩ := Option.isSome_iff_exists.1 hW
  have fU := H2K.Made.cutOn_free _ _ _ _ _ hU
  have fO := H2K.Made.cutOn_free _ _ _ _ _ hO
  have fW := H2K.Made.cutOn_free _ _ _ _ _ hW
  rw [laterPlaces_of_cuts m t₀ t₁ t₂ P₁ P₂ 8 0 tU tW h₀ h₁ h₂ hP₁ hbU (by rw [hS]; exact hU)
      hP₂ hbW (by rw [hS]; exact hW),
    laterAt_written m t₀ t₁ tU tO tW hk hset hr fU.1 (fU.2.trans hrU) (H2K.Sizes.cutOn_stages hU)
      ((omegaCut_eq m P₁ 43 hP₁ hbO).trans (by rw [hS]; exact hO))
      fO.1 (fO.2.trans hrO) (H2K.Sizes.cutOn_stages hO)
      fW.1 fW.2 (H2K.Sizes.cutOn_stages hW) hfU hsp hfO hfW hn]

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rangesAt_written
#print axioms Johnson.AtFull.KeyBack.laterAt_written
#print axioms Johnson.AtFull.KeyBack.omegaCut_eq
#print axioms Johnson.AtFull.KeyBack.rangesNumbers_written
#print axioms Johnson.AtFull.KeyBack.laterPlaces_written
