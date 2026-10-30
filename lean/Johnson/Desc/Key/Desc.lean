-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Desc.lean: a key file's description: its three chains, their starts, and the tests
on the file. Definitions only, all computable; nothing is proved here.

Main names.
  descriptionFromSource X N P: the description (`FileDescription`, Johnson/Desc/Block.lean).
  sourceOf, descriptionFromPlan: the same from the planner's answer and the sendings.

Limits. The description is general in what it is made of: that X, N and P come of the public files
is the maker's matter (Johnson/Desc/Key/Road.lean). This is the decision's half of a verifier: that
opened columns hang under their roots, and how draws come of a hash function, is not here. Nothing
on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.WantedFirst
import Johnson.Desc.Key.WantedLater
import Johnson.Desc.Key.Chains23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-- **The key file's description.** X: what it is made of; N: the numbers of the ranges' test's
place; P: those of the three later proximity tests' places. The first chain is `firstChain`; the
second (shared) and the third chain are `sharedChain` and `thirdChain`, retyped (`Chain.retype`).
The plans handed in are the declared rounds. The tables of places and of what is owed are other
files' (`wantedFirst`, `owedFirst`: Johnson/Desc/Key/WantedFirst.lean; `wantedShared`,
`wantedSecond`, `owedShared`, `owedSecond`: Johnson/Desc/Key/WantedLater.lean), made of the public
values and importing none of the files that lay the blocks; `wantedOk` and `owedOk` stand beside
`planOk`. The table's depth is the index tree's. The test on the file is `fileClauses` at the
numbers of rounds of these three chains, and `openedInBlocks` at their oracles and rounds. The test
on the instance asks `instanceOk` and `K14.okKey`; `instanceOk` holds the test that every word of
the key is below the prime (`keyWordsBelow`), without which a seed's factor with the words (p, 0,
0), which is 0 in the field, would pass "no seed's factor is 0". The third chain starts from the
first chain's end, whose record must hold the linear claim's first part (its W, own group and mask,
if any, are handed on by name; what is asked of them is `Third.start₃E`'s), and the shared chain's
end, which must have nothing untested; the last test asks `firstEndOk` and `Third.fin₃`. -/
def descriptionFromSource (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) : FileDescription Xi :=
  let Z := X.Y
  let c := X.chains
  let z := c.made.sized.key
  let c₁ := firstChain Z.k.oneTime Z.D.1 Z.told.1 X.set N
  let c₂ : Chain _root_.Desc.K14.St Claim := (sharedChain c P).retype
  let c₃ : Chain VerifiableInference.Desc.Third.S₃ Claim := (thirdChain c P).retype
  let len {σ : Type} (x : Chain σ Claim) : Nat := (x.blocksInOrder.flatMap (·.rounds)).length
  { S₁ := FirstState, S₂ := _root_.Desc.K14.St, S₃ := VerifiableInference.Desc.Third.S₃, Cl := Claim
    plans := Z.D
    wanted := wantedFirst Z.k.oneTime ++ wantedShared Z.k.shared.lin ++ wantedSecond Z.k.shared.lin
    owed := owedFirst Z.k.oneTime ++ owedShared Z.k.oneTime Z.k.shared.lin ++ owedSecond Z.k.oneTime
    tableDepth := Z.k.shared.lin.fold.index.tree.a
    fileOk := (fileClauses X N P (len c₁) (len c₂) (len c₃)).all (·.2) &&
      openedInBlocks
        [VerifiableInference.Desc.oraclesOf c₁.blocksInOrder, VerifiableInference.Desc.oraclesOf c₂.blocksInOrder,
          VerifiableInference.Desc.oraclesOf c₃.blocksInOrder]
        (c₁.blocksInOrder.flatMap (·.rounds), c₂.blocksInOrder.flatMap (·.rounds), c₃.blocksInOrder.flatMap (·.rounds))
    okStart := fun x => instanceOk X.Y.k.shared.lin x &&
        _root_.Desc.K14.okKey (sharedPar c []) x.key
    XiPub := Xi, pub := id
    start₁ := fun _ => chainStart Z.k.oneTime.codes {}
    start₂ := fun x => _root_.Desc.K14.first z.codes x.key
    start₃ := fun _ s₁ s₂ => do
      let f := firstOf s₁
      let l ← named "the first chain's end names no W" s₁.lin
      let e₂ ← named "the shared chain's end: something is untested" (_root_.Desc.K14.ended s₂)
      VerifiableInference.Desc.Third.start₃E z.codes z.once.shape f.1 f.2.1 f.2.2.1 l.w l.own
          l.mask f.2.2.2 (VerifiableInference.Desc.Third.sharedOfEnd e₂)
    first := c₁
    shared := c₂
    second := c₃
    fin := fun _ s₁ _ s₃ => firstEndOk Z.k.oneTime s₁ && VerifiableInference.Desc.Third.fin₃ s₃ }

/-- What the description is made of, out of the planner's answer and the sendings. The setting is
the sized key's; the units of rows are the layout's (`Plan.unitsOfLayout`). -/
def sourceOf (m : Johnson.G.OfPlan.Made) : Except String Source := do
  let D ← Johnson.G.OfPlan.declKOf m
  let z := m.p.chains.made.sized
  let Y : KeySource :=
    ⟨m.p.chains.key, z.key.once.shape, (m.key.1.codes, m.key.2.1.codes, m.key.2.2.codes),
      z.key.once.input, z.key.ranges.x, z.set.samples, D, ← toldOfMade m,
      OnBytes.Plan.unitsOfLayout m.p.X.layers.wsLay⟩
  pure ⟨Y, m.p.chains, z.key.set⟩

/-- **The key file's description**, of the planner's answer and the sendings. It refuses where the
source, or a proximity test's place's numbers, cannot be made. -/
def descriptionFromPlan (m : Johnson.G.OfPlan.Made) : Except String (FileDescription Xi) :=
  match sourceOf m, rangesNumbers m, laterPlaces m with
  | .ok X, .ok N, .ok P => .ok (descriptionFromSource X N P)
  | .error e, _, _ => .error e
  | _, .error e, _ => .error e
  | _, _, .error e => .error e

end VerifiableInference.Desc.Key
