-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/LaterReturns.lean: WHERE `Key.testFirsts m` AND `Key.laterPlaces m` RETURN,
AND WHAT. General in m: no written value stands here.

IT TAKES A RETURN TO GIVE A RETURN. `Key.testFirsts` (Johnson/Desc/Key/Places.lean) can refuse at
five places: `treesSent` at the key file's three chains, and two looks into the rule's lists. The
two looks cannot refuse, by the rule's text. `Key.laterPlaces` calls it, and can refuse at two more:
the cuts of the test on the folded row's group (U) and of the own test (W). So five premises stay:
  h₀ h₁ h₂ `treesSent` returns at the three chains;
  hU hW `cutAt` (Core.lean) returns at the chains number 1 and 2.
None of the five is shown at any m here. BatLaw.lean takes hU and hW apart further.

  `take_of_some`: the routines' "take it or refuse" returns what an Option holds.
  `foldedFirst S ts`, `sharedOpens_one`: entry number 1 of the rule's list for a shared chain.
  `ownFirst S t₀ t₁`: the head of the rule's list for a key file's second chain. That the list has
    this head is `Johnson.G.OfPlan.secondOpens_head` (Johnson/G/SecondOpensTaken.lean), which is
    called.
  `firstsAt m t₀ t₁`, `testFirsts_eq`, `testFirsts_returns`, `testFirsts_only`: what `Key.testFirsts
    m` returns; that it returns; the way back. The value does not read the second chain's trees.
  `omegaCut m`: the cut of the test on Omega's group: an Option, which refuses nothing.
  `sharedScope m`: the scope of the work at the shared chain's two tests.
  `laterAt m Fs tU tW`, `laterPlaces_eq`, `laterPlaces_returns`, `laterPlaces_only`: the same for
    `Key.laterPlaces m`.
The forms "_eq" take `treesSent`'s returns at the routine's own words for a refusal. The forms
"_returns" take them at every such words, as `TreesK` (Core.lean) gives them. The forms "_only" give
them back at the routine's own words. So the premises of "_eq" ask no more than the routines do.
Limits. No m is shown at which the premises hold. Whether the place O is there is not said: it is
left as the routine's own text in `firstsAt` and `laterAt`. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core
import Johnson.Desc.K12.Law.FreeOfMade
import Johnson.G.SecondOpensTaken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- Where an Option holds a value, the routines' "take it or refuse" returns it. -/
theorem take_of_some {α : Type} {x : Option α} {e : String} {a : α} (h : x = some a) :
    (match x with
      | some v => (pure v : Except String α)
      | none => throw e) = .ok a := by
  subst h
  rfl

/-- The trees that the second round of positions of a shared chain opens. -/
def foldedFirst (S : LinShape) (ts : List (Sent × Nat)) : List Told :=
  (ts.filter fun t => t.1.tag == .foldedRow ||
    (t.1.tag == .omega && (!S.sharedSplitNeeded || t.1.cls == S.sharedSplitLeafClass))).map
      (ownAt 0)

/-- The rule's list for a shared chain has an entry number 1, whatever the trees. -/
theorem sharedOpens_one (S : LinShape) (ts : List (Sent × Nat)) :
    (sharedOpens S ts)[1]? = some (foldedFirst S ts, []) :=
  rfl

/-- The trees that the first round of positions of a key file's second chain opens. -/
def ownFirst (S : LinShape) (t₀ t₁ : List (Sent × Nat)) : List Told :=
  (t₀.filter fun t => t.1.tag == .indexMask).map (takenAt 0) ++
    (t₀.filter fun t => t.1.tag == .w).map (takenAt 0) ++
    (t₁.filter fun t => t.1.tag == .omega && t.1.cls == S.omegaLeafClass).map (takenAt 1)

/-- What `Key.testFirsts m` returns, at the trees of the first and of the shared chain. -/
def firstsAt (m : Made) (t₀ t₁ : List (Sent × Nat)) : TestFirsts :=
  { U := (foldedFirst (shapeK m) t₁, 0)
    O := if (shapeK m).sharedSplitNeeded then
        ((sharedOpens (shapeK m) t₁)[2 + (switchOpens 0 .folded t₁).length]?).map fun x =>
          (x.1.dropLast, 0)
      else none
    W := (ownFirst (shapeK m) t₀ t₁, t₀.length + 1) }

/-- **What `Key.testFirsts m` returns**, from the three steps that can refuse. -/
theorem testFirsts_eq (m : Made) (t₀ t₁ t₂ : List (Sent × Nat))
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (h₁ : treesSent "key file, shared chain" m.key.2.1 (plan₁ m)
      (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁)
    (h₂ : treesSent "key file, second chain" m.key.2.2 (plan₂ m) [] = .ok t₂) :
    testFirsts m = .ok (firstsAt m t₀ t₁) := by
  unfold testFirsts
  dsimp only
  refine bind_of_ok h₀ (bind_of_ok h₁ (bind_of_ok h₂ ?_))
  rw [sharedOpens_one, Johnson.G.OfPlan.secondOpens_head]
  rfl

/-- **`Key.testFirsts m` returns**, where `treesSent` does at the three chains. -/
theorem testFirsts_returns (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (hT : TreesK m t₀ t₁ t₂) :
    ∃ Fs, testFirsts m = .ok Fs :=
  ⟨_, testFirsts_eq m t₀ t₁ t₂ (hT.first _) (hT.shared _) (hT.second _)⟩

/-- **The way back**: a return gives the three returns of `treesSent`, and the value. -/
theorem testFirsts_only (m : Made) (Fs : TestFirsts) (h : testFirsts m = .ok Fs) :
    ∃ t₀ t₁ t₂ : List (Sent × Nat),
      treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀ ∧
      treesSent "key file, shared chain" m.key.2.1 (plan₁ m)
        (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁ ∧
      treesSent "key file, second chain" m.key.2.2 (plan₂ m) [] = .ok t₂ ∧
      Fs = firstsAt m t₀ t₁ := by
  have h' := h
  unfold testFirsts at h'
  dsimp only at h'
  obtain ⟨t₀, h₀, h'⟩ := ok_of_bind h'
  obtain ⟨t₁, h₁, h'⟩ := ok_of_bind h'
  obtain ⟨t₂, h₂, _⟩ := ok_of_bind h'
  refine ⟨t₀, t₁, t₂, h₀, h₁, h₂, ?_⟩
  exact Except.ok.inj (h.symm.trans (testFirsts_eq m t₀ t₁ t₂ h₀ h₁ h₂))

/-- The cut of the test on Omega's group: at the shared chain's second round named "BAT". -/
def omegaCut (m : Made) : Option H2U.TestCut := do
  keyTestCut m.p.chains.made 1 (← (← keyBatchRounds m.p.chains.made 1)[1]?) (shapeK m).testOmega

/-- The scope of the work at the shared chain's two tests. -/
def sharedScope (m : Made) : Scope :=
  if m.p.chains.made.sized.key.once.lines.oneTime then .once else .shared

/-- What `Key.laterPlaces m` returns, at what the first openings read and at the two cuts. -/
def laterAt (m : Made) (Fs : TestFirsts) (tU tW : H2U.TestCut) : LaterPlaces :=
  { U := H2U.mkPlace m.p.chains.made.sized.set.samples 2
      m.p.chains.made.sized.key.once.folded.stages
      ((shapeK m).fold.index.answers + (shapeK m).fold.columns + 1 +
        2 * m.p.chains.made.sized.set.samples)
      (m.p.chains.made.sized.set.workOf .query (sharedScope m)) (!(shapeK m).masksAhead) tU Fs.U 2
      (shapeK m).choice.masksRide
    O := match omegaCut m, Fs.O with
      | some tO, some fO =>
        some (H2U.mkPlace m.p.chains.made.sized.set.samples 2
          m.p.chains.made.sized.key.once.omega.stages (1 + 2 * m.p.chains.made.sized.set.samples)
          (m.p.chains.made.sized.set.workOf .query (sharedScope m)) true tO fO
          (2 + (tU.stages.length - 1)) (shapeK m).choice.masksRide)
      | _, _ => none
    W := H2U.mkPlace m.p.chains.made.sized.set.samples 3 m.p.chains.made.sized.key.once.own.stages
      (2 + 3 * m.p.chains.made.sized.set.samples)
      (m.p.chains.made.sized.set.workOf .query
        (if m.p.chains.made.sized.key.once.lines.oneTime then .once else .request))
      (!(shapeK m).masksAhead) tW Fs.W (m.p.chains.key.oneTime.ranges.stages.length + 1)
      (shapeK m).choice.masksRide }

/-- **What `Key.laterPlaces m` returns**, from the three steps that can refuse. -/
theorem laterPlaces_eq (m : Made) (Fs : TestFirsts) (tU tW : H2U.TestCut)
    (hF : testFirsts m = .ok Fs)
    (hU : cutAt m.p.chains.made 1 (shapeK m).testU = some tU)
    (hW : cutAt m.p.chains.made 2 (shapeK m).testOwn = some tW) :
    laterPlaces m = .ok (laterAt m Fs tU tW) := by
  unfold laterPlaces
  refine bind_of_ok hF ?_
  dsimp only
  refine bind_of_ok (take_of_some hU) (bind_of_ok (take_of_some hW) ?_)
  rfl

/-- **r3: `Key.laterPlaces m` returns**, where `treesSent` does at the three chains and the two cuts
return. -/
theorem laterPlaces_returns (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (tU tW : H2U.TestCut)
    (hT : TreesK m t₀ t₁ t₂)
    (hU : cutAt m.p.chains.made 1 (shapeK m).testU = some tU)
    (hW : cutAt m.p.chains.made 2 (shapeK m).testOwn = some tW) :
    ∃ P, laterPlaces m = .ok P :=
  ⟨_, laterPlaces_eq m _ tU tW
    (testFirsts_eq m t₀ t₁ t₂ (hT.first _) (hT.shared _) (hT.second _)) hU hW⟩

/-- **The way back**: a return gives the five premises, and the value. -/
theorem laterPlaces_only (m : Made) (P : LaterPlaces) (h : laterPlaces m = .ok P) :
    ∃ (t₀ t₁ t₂ : List (Sent × Nat)) (tU tW : H2U.TestCut),
      treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀ ∧
      treesSent "key file, shared chain" m.key.2.1 (plan₁ m)
        (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁ ∧
      treesSent "key file, second chain" m.key.2.2 (plan₂ m) [] = .ok t₂ ∧
      cutAt m.p.chains.made 1 (shapeK m).testU = some tU ∧
      cutAt m.p.chains.made 2 (shapeK m).testOwn = some tW ∧
      P = laterAt m (firstsAt m t₀ t₁) tU tW := by
  have h' := h
  unfold laterPlaces at h'
  obtain ⟨Fs, hF, h'⟩ := ok_of_bind h'
  dsimp only at h'
  obtain ⟨tU, hU, h'⟩ := ok_of_bind h'
  obtain ⟨tW, hW, _⟩ := ok_of_bind h'
  have hU' : cutAt m.p.chains.made 1 (shapeK m).testU = some tU := H2K.Made.get_some hU
  have hW' : cutAt m.p.chains.made 2 (shapeK m).testOwn = some tW := H2K.Made.get_some hW
  obtain ⟨t₀, t₁, t₂, h₀, h₁, h₂, rfl⟩ := testFirsts_only m Fs hF
  refine ⟨t₀, t₁, t₂, tU, tW, h₀, h₁, h₂, hU', hW', ?_⟩
  exact Except.ok.inj (h.symm.trans (laterPlaces_eq m _ tU tW hF hU' hW'))

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.take_of_some
#print axioms Johnson.AtFull.KeyBack.sharedOpens_one
#print axioms Johnson.AtFull.KeyBack.testFirsts_eq
#print axioms Johnson.AtFull.KeyBack.testFirsts_returns
#print axioms Johnson.AtFull.KeyBack.testFirsts_only
#print axioms Johnson.AtFull.KeyBack.laterPlaces_eq
#print axioms Johnson.AtFull.KeyBack.laterPlaces_returns
#print axioms Johnson.AtFull.KeyBack.laterPlaces_only
