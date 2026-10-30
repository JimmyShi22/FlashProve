-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DescRuns.lean: a file's decision (`FileDescription.run`, Johnson/Desc/Block.lean) as
three runs in a row. A SHEET OF STATEMENTS: four definitions with code, and two propositions written
as `def … : Prop`. NOTHING IS PROVED IN THIS FILE.

The setting. The library takes a file's verifier as three runs, one for each hash chain, each on
what the verifier is shown of its chain (`runRow`, OnBytes/Maker/RowWhole.lean; `rowOf`,
OnBytes/Maker/Row.lean). A description's decision is one function of the instance and the three
views (`FileDescription.runEnd`). Here the three runs OF A DESCRIPTION are written out, on its own fields
and `chainAt` alone, and it is said what lies between them and the decision.

Main names.
  `sealRound`; `descRun₁`, `descRun₂`, `descRun₃`.
  THE STATEMENTS: `RunEndIs` · `RunGivesRow`.

Why the runs are cut so. The top theorem for a proof file asks that the row says yes at the
instance WITHOUT what is asked of the proof, while the file's yes is at the instance itself. So the
three runs read the instance through `pub` alone, and the two readers of the instance itself,
`okStart` and `fin`, stay out of the row. `RunEndIs` hands both to whoever ties the relation at
the public part to the relation at the instance: under the decision's yes they hold, `fin` at the
very ends that the three folds reach.

Limits. (1) GENERAL IN THE DESCRIPTION: no block of the protocol, no plan and no size is named;
nothing is said on soundness or on acceptance. (2) That the runs are those of the rule of
composition (`Three.ofStarts`, Johnson/Desc/Sound/FileRule.lean) is Johnson/Desc/Sound/
DescThree.lean's. (3) The second chain's end e₃ is handed on by no run: the third run is a test;
`RunEndIs` names e₃ under its own clause. (4) A refusal's words are dropped. (5) A description that
says yes to all and one that says no to all both meet the two statements, and rightly: `RunEndIs` is
an equivalence between two writings of one decision; `RunGivesRow` goes one way: the row is laxer;
neither claims anything of what is decided. (6) THE ROW HOLDS NOTHING OF `fin`: ALSO WHAT `fin` ASKS
OF THE THREE ENDS ALONE IS LOST TO IT, unless a block or `start₃` asks it too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import OnBytes.Maker.RowWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker (runRow)

/-! ## 1 The three runs of a description -/

variable {Xi : Type}

/-- The empty round that closes the first chain: what `withEmptySealRound` puts behind the first view's
rounds. -/
def sealRound : Fmt.RoundView := ⟨[], ⟨[], [], [], none⟩⟩

/-- **The first chain's run.** Every word of the view is below the prime; the fold of the chain's
own blocks, at the view with the sealing round put back, from the first record that the instance's
PUBLIC PART gives. It hands on the public part and the chain's last record. A refusal's words are
dropped. It reads the instance through `pub` alone. -/
def descRun₁ (F : FileDescription Xi) : Xi → Fmt.View → Option (F.XiPub × F.S₁) := fun x v =>
  if viewWordsBelowPrime v then
    (chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v)).toOption.map
      fun s => (F.pub x, s)
  else none

/-- **The shared chain's run.** It starts from the public part alone; its last record is packed
behind what was handed on. -/
def descRun₂ (F : FileDescription Xi) : F.XiPub × F.S₁ → Fmt.View → Option (F.XiPub × F.S₁ × F.S₂) :=
  fun a v =>
    if viewWordsBelowPrime v then
      (chainAt "the shared chain" 0 F.shared.blocksInOrder (F.start₂ a.1) v).toOption.map
        fun s => (a.1, a.2, s)
    else none

/-- **The second chain's run** (the third in the file's order). Yes where every word is below the
prime, `start₃` gives a first record of the public part and the two earlier ends, and the fold
from it returns. NEITHER `fin` NOR `okStart` IS IN IT. -/
def descRun₃ (F : FileDescription Xi) : F.XiPub × F.S₁ × F.S₂ → Fmt.View → Bool := fun a v =>
  viewWordsBelowPrime v && ((F.start₃ a.1 a.2.1 a.2.2).toOption.bind fun s =>
                (chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s v).toOption).isSome

/-- **What the decision's yes is.** `FileDescription.runEnd` gives the three ends e₁, e₂, e₃ JUST WHERE:
the tests on the plan pass; the test on the instance passes; the first run hands on e₁ behind the
public part; the shared chain's run, from that, hands on e₂; every word of the third view is below
the prime; `start₃` gives a first record from which the second chain's fold returns e₃; and the
last test says yes AT THESE ENDS. An equivalence: the decision asks nothing else. -/
def RunEndIs : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) (e₁ : F.S₁) (e₂ : F.S₂)
    (e₃ : F.S₃),
    F.runEnd x v₁ v₂ v₃ = .ok (e₁, e₂, e₃) ↔
      F.planOk = true ∧ F.okStart x = true ∧ descRun₁ F x v₁ = some (F.pub x, e₁) ∧
        descRun₂ F (F.pub x, e₁) v₂ = some (F.pub x, e₁, e₂) ∧ viewWordsBelowPrime v₃ = true ∧
        (∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
          chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ v₃ = .ok e₃) ∧
        F.fin x e₁ e₂ e₃ = true

/-- **The decision's yes gives the yes of the three runs in a row** (`runRow`,
OnBytes/Maker/RowWhole.lean). -/
def RunGivesRow : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View),
    F.run x v₁ v₂ v₃ = true →
      runRow (descRun₁ F) (descRun₂ F) (descRun₃ F) x v₁ v₂ v₃ = true


-- the three runs fit the library's row of three runs, at any description
example (Xi : Type) (F : FileDescription Xi) : Xi → Fmt.View → Fmt.View → Fmt.View → Bool :=
  runRow (descRun₁ F) (descRun₂ F) (descRun₃ F)

end VerifiableInference.Desc.Sound
