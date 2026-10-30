-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowKeep.lean: a lookup's row of parts that passes its tables on
from move to move, beside `lookRow` (Honest/K3/Row.lean). Definitions with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a store is a value of `Store`, a kept state a value of
`Kept`, a row's own state a value of `RowOwn` (Honest/K3/KeptTypes.lean); a job with a kept state is
a value of `KeepJob` (Honest/SumKeep.lean).

Why. Every move of `lookRow` at `fastJobs` makes its side's leaves and product tree anew
(Honest/K3/JobsFast.lean, under "Cost"). In the row of this file the tables of a lookup are made
once, behind the round that samples alpha, and each masked sumcheck binds one challenge at each
move.

What is defined.
  `Keeps`: the two letters of the row: for each stage that is a masked sumcheck its job with a kept
    state; and the maker of the store.
  `partKeep`: the part of a stage. At a stage with a job: `keepPart` at that job, under the names of
    `partOf`. At `Stage.alpha`: nothing is sent, and the store is passed on. At every other stage
    without a job: nothing is sent, and what was passed on stays. Behind the last round of
    `Stage.bits`, which is the row's last, `rowOwn₀` is passed on: the store is dropped.
  `lookRowKeep`, `proverSideOfLookupKeepingTablesAtOneOwner`: the row; the row at its place.
  `proverSideOfLookupInChainKeepingTablesAtOneOwner`: the row seated in a chain's letters. Beside `proverSideOfLookupInChainAtOneOwner`'s arguments it takes get
    and set, which read and lay the row's own state in the chain's.

Imported: Honest/SumKeep.lean, and through it and Honest/K3/Row.lean the files Honest/Sum.lean,
Honest/Side.lean, Honest/Frame.lean and Honest/ForKinds.lean.

Users. Honest/K3/RowKeepFill.lean, which fills `Keeps` at the jobs of Honest/K3/JobsKeepKey.lean and
its sisters; Honest/K3/LotKeep.lean, the lot beside `rowLot` (Honest/K3/LotRow.lean);
Honest/K3/Law/Keep/RowKeepLaw.lean, where hypotheses on the letters are named under which this row
shows what `lookRow` shows.

Limits. Letters: nothing here says that a job of `Keeps` has the shape of its stage's call, that its
earlier job is the one that `lookRow` plays, or that the store holds what the jobs would make. So
nothing here says that this row sends what `lookRow` sends. Nothing asks that get and set fit each
other. The store is dropped only where `Stage.bits` has a job. How long a move takes is not said and
has not been measured.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeep
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.KeptTypes
import Johnson.Desc.ProofFile.Honest.K3.RowKeepParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3

variable {V V₁ W₁ X₁ : Type}

/-- **The two letters of a row that passes its tables on.** -/
structure Keeps where
  /-- a stage's job with a kept state; none at a stage that sends nothing -/
  job : Stage → Option (KeepJob Ask (Option Store) Kept)
  /-- the lookup's store: of the input and of the challenges heard, the last of which is that of the
  round that samples alpha -/
  store : Ask → List Fmt.Drawn → Store

/-- **The part of a stage.** Here i is its number in the row. -/
def partKeep (Kp : Keeps) (a : At) (s : Stage) (i : Nat) : Part V Ask RowOwn :=
  match Kp.job s with
  | some J =>
    let p : Part V Ask RowOwn := keepPart (sumName a.place i) (endName a.place i) J
    if s = .bits then p.lastHand fun _ => rowOwn₀ else p
  | none =>
    if s = .alpha then quietLay fun t => (some (Kp.store t.input t.heard), none) else quietAt

/-- **A lookup's row of parts that passes its tables on**: a part for each stage, in order. -/
def lookRowKeep (Kp : Keeps) (a : At) : List (Part V Ask RowOwn) :=
  (stages a.face).zipIdx.map fun x => partKeep Kp a x.1 x.2

/-- The row at its place, typed at the jobs' own input and the row's own state. -/
def proverSideOfLookupKeepingTablesAtOneOwner (Kp : Keeps) (a : At) : Placed V Ask RowOwn := ⟨a.place, lookRowKeep Kp a⟩

/-- **The row, seated in a chain's letters.** Here wit makes the jobs' input of what the chain's
halves are handed; get reads the row's own state in what the chain's parts pass on, and set lays it
there. No stop reads anything. -/
def proverSideOfLookupInChainKeepingTablesAtOneOwner (Kp : Keeps) (wit : W₁ → Ask) (get : X₁ → RowOwn) (set : X₁ → RowOwn → X₁)
    (a : At) : Placed V₁ W₁ X₁ :=
  ⟨a.place, (lookRowKeep (V := Unit) Kp a).map (Part.lift (fun _ => ()) wit get set)⟩

end ProofFile.Honest.K3
