-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/MidW.lean: The state of a run before the part at an address, as `runC`
(Walk.lean) reaches it: beside `midAt` and `midSharedAt` (Frame.lean), which play the rounds by
`play` and hand no columns. Definitions with code. No theorem.

  `midInW`         one chain: `midIn` (Frame.lean) with `walk` in the place of `play`
  `midAtW`         an address of the first or the second chain: the lines of `runC`, up to the chain
                   that holds the address
  `midSharedAtW`   an address of the shared chain

The result is an `Option` inside the `Except`: `none` once the verifier has rejected, since the walk
plays nothing after that.

Limits.
  * Nothing relates these functions to `midAt`, `midSharedAt` or `runC` here. Nothing is proved.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription OpenedColumn)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X W Y : Type}

/-- **The state of a chain's walk before the part at an address**: the rounds before it, walked. An
error at an address that has no round in the list. `ChainProgress.heard` ends in `ChainProgress.settle`: so after
these rounds every sub-protocol whose rounds are all laid has been asked. From a `z` that
`ChainProgress.start` returns at `front`, over that chain's own rounds: at the first part of a sub-protocol
the field `opened` holds `front`, then the columns of the chain's sub-protocols before it, and at a
later part of the same sub-protocol it holds the same (`live_field`, Honest/K12/LiveField.lean;
WalkOpened.lean, Limits). -/
def midInW (L : Lay) (steps : List (Step W Y)) (ds : List Fmt.Drawn) (z : ChainProgress S Cl W Y)
    (a : Addr) : Except Refusal (Option (Mid W Y)) :=
  let n := (steps.takeWhile fun s => s.addr != a).length
  if !steps.any (·.addr == a) then .error ⟨.unfit, "no round of the chain stands at the address"⟩
  else (walk L (steps.take n) (ds.take n) z).map (·.mid)

/-- **The state of a run before the part at an address of the first or the second chain**, as
`runC` reaches it. -/
def midAtW (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) (a : Addr) :
    Except Refusal (Option (Mid (Local W₀ Rc Xi Tr) X)) :=
  let stored := H.storedWords w₀ rc
  (ready F B H w₀ rc x c).bind fun R =>
  (ChainProgress.start ⟨0, 0, stored, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
    (some (F.start₁ (F.pub x))) []).bind fun a₁ =>
  if R.first.any (·.addr == a) then midInW ⟨0, 0, stored, treeOwn⟩ R.first ρ.first a₁ a else
  (walk ⟨0, 0, stored, treeOwn⟩ R.first ρ.first a₁).bind fun z₁ =>
  if !sealQuiet z₁.laid then .error ⟨.unfit, "the sealing round sends or draws something"⟩ else
  (ChainProgress.start ⟨1, 0, stored, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  (walk ⟨1, 0, stored, treeOwn⟩ R.shared ρ.shared a₂).bind fun z₂ =>
  let L₃ : Lay := ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩
  (ChainProgress.start L₃ F.second.blocksInOrder
    (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
    (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)).bind fun a₃ =>
  midInW L₃ R.second ρ.second a₃ a

/-- The like at an address of the shared chain. The first chain is not walked: a state can be
returned also where `runC` has returned an error before this chain. -/
def midSharedAtW (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) (a : Addr) :
    Except Refusal (Option (Mid (Common W₀ Rc Ky) X₀)) :=
  let stored := H.storedWords w₀ rc
  (ready F B H w₀ rc x c).bind fun R =>
  (ChainProgress.start ⟨1, 0, stored, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  midInW ⟨1, 0, stored, treeOwn⟩ R.shared ρ.shared a₂ a

end ProofFile.Honest

#print axioms ProofFile.Honest.midInW
#print axioms ProofFile.Honest.midAtW
#print axioms ProofFile.Honest.midSharedAtW
