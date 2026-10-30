-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkToySizes.lean: the public numbers of the small test configuration, in the forms in
which the statements on the program's blocks ask for them.

A statement on a block of the program carries hypotheses on public sizes: which codes the program
holds, how many rows a stage has, which choices the parameters make. At the small test
configuration this file states a few of them and has Lean's kernel evaluate them.


Main definitions: `toySt1`, `toySt2`, `toySt3`, the three stages of the proximity test as the
program holds them; `toySent2`, `toySent3`, what the message of each code switch holds.
Main theorems.
 `toy_small`        no code of a stage is longer than 2^32.
 `side_columns`    the two sides' draws.
 `toy_othersPlain`  neither message that rides with a code switch is sampled.


















Not claimed. Nothing on another configuration.
-/
import OnBytes.Entry.File
import OnBytes.Iop.Link
import OnBytes.Iop.Prox
import OnBytes.Params.EntryRoundsToy
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.CsMet
import Run.PlanQXFastR
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M3Entry
import OnBytes.Slice.ToySg
import OnBytes.Slice.LinkAt

set_option autoImplicit false

namespace OnBytes.Slice
open OnBytes.Params (IoppStage)

/-! ## The codes and the stages -/

/-- The first stage as the program holds it: the group of the two folded rows. -/
def toySt1 : IoppStage := { code := 0, maskCode := 0, k := 3, h := 0 }
/-- The second stage as the program holds it. -/
def toySt2 : IoppStage := { code := 1, maskCode := 1, k := 2, h := 1 }
/-- The third stage as the program holds it. -/
def toySt3 : IoppStage := { code := 2, maskCode := 2, k := 0, h := 0 }

/-- No code of a stage is longer than 2^32. -/
theorem toy_small : toySg1.C.a ≤ 32 ∧ toySg1.Z.a ≤ 32 ∧ toySg2.C.a ≤ 32 ∧ toySg2.Z.a ≤ 32 ∧
    toySg3.C.a ≤ 32 ∧ toySg3.Z.a ≤ 32 := by
  decide

/-- From what the block of an entry's chain starts, for all parameters. -/
private theorem start_eq (p : Params.Link) : (Entry.start p).firstTree = 0 ∧
    (Entry.start p).samples = p.given.plan.samples ∧ (Entry.start p).st.codes = p.codes :=
  ⟨rfl, rfl, rfl⟩

/-- The plan's entries from which the block of an entry's chain starts, for all parameters. -/
private theorem start_entries (p : Params.Link) :
    (Entry.start p).entries = p.given.plan.rounds := rfl



/-! ## The link -/

/-- Either side of a link has the link's table, for all shapes. -/
private theorem side_index (Λ : Params.LinkShape) (b : Bool) (n : ℕ) :
    (Λ.side b n).index = Λ.table := rfl

/-- The draws at either side of a link, for all shapes. -/
theorem side_columns (Λ : Params.LinkShape) (n : ℕ) :
    (Λ.side false n).columns = Λ.columnsFirst ∧ (Λ.side true n).columns = Λ.columnsFurther :=
  ⟨rfl, rfl⟩



/-! ## The trees of the two code switches' messages -/

/-- What the prover's message of the first code switch holds: the new stage's oracle message, and
with it the fresh mask of the new stage's fold. -/
def toySent2 : Array OracleNotice :=
  #[⟨(switchTargetStage toySt2.code toySt2.maskCode toySt2.k toySt2.h 1).shape,
      (switchTargetStage toySt2.code toySt2.maskCode toySt2.k toySt2.h 1).leafClass⟩] ++
    #[foldMaskNotice (ioppFoldShape toySt2 {})]

/-- What the prover's message of the second code switch holds: the last stage's oracle message, and
with it the masking oracle of the base case. -/
def toySent3 : Array OracleNotice :=
  #[⟨(switchTargetStage toySt3.code toySt3.maskCode toySt3.k toySt3.h 1).shape,
      (switchTargetStage toySt3.code toySt3.maskCode toySt3.k toySt3.h 1).leafClass⟩] ++
    #[baseMaskNotice toySt3.code toySt3.maskCode 1 0]

/-- Neither message that rides with a code switch is sampled. -/
theorem toy_othersPlain : (foldMaskNotice (ioppFoldShape toySt2 {})).shape.answers = 0 ∧
    (baseMaskNotice toySt3.code toySt3.maskCode 1 0).shape.answers = 0 :=
  ⟨rfl, rfl⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.toy_small
#print axioms OnBytes.Slice.start_eq
#print axioms OnBytes.Slice.start_entries
#print axioms OnBytes.Slice.side_index
#print axioms OnBytes.Slice.side_columns
#print axioms OnBytes.Slice.toy_othersPlain
