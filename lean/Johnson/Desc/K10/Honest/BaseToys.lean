-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/BaseToys.lean: the test on the record in front of the closing of a segment
(`closeBaseB`, Johnson/Desc/K10/Honest/BaseB.lean) asked at records that have what BaseB.lean's member
lacks: a kept member, structured vectors, two mask rows, SAMPLED MEMBERS WITH THEIR SAMPLE ROWS.
`#guard` lines, and two members by Lean's kernel at which the theorems are called.

The records are those of two of the kind's toys (their data: Johnson/Desc/K10/Honest/ToyData.lean),
and the first one's with members sampled: B and C, which is kept; then A too, which has a
mask row. Each has one sample row, made by the verifier's own text (`Own.formMade`,
Johnson/Desc/Own/Send.lean). In a proof every member of a group is sampled, so every test takes sample
rows in; these do not pass the adding of a row.

The test says yes at each of these. It says no where one thing is bent: the plan's count of rows; the
plan's k; rows still owed a count; a row on an oracle message that is no member; an index beyond a
table; a structured vector with one variable too few; a written-out variable with another pair than
(1, 1); a slice beyond its vector; a variable written out twice; a sample row whose point is one
coordinate short; a term on a mask table with one variable too few. Each such line has a partner that
differs in that one thing and says yes.

Limits. The `#guard` lines are evaluations. The test reads neither the field of a main row nor a
row's target, so the toy with rows over the base field (Johnson/Desc/ProofFile/Honest/K10/ToyF.lean,
which a tree may lack) would show nothing more. A "no" line tries the wording of the facts; that the
test is not too strict is tried by the "yes" lines. Fifteen of the twenty facts have no "no" line.
The sampled records are still unlike what a run leaves, in things that the test does not read: no
pad and no ledger is set, and the toy's open rows have coefficients on the entries that are then
pads. So is the record with an open row whose term on a mask table is out of order: the adding would
refuse that row. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.BaseB
import Johnson.Desc.K10.Honest.ToyData
import Johnson.Desc.Own.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Toy.Base
open OnBytes (Statement oneE)
open ProofFile.Honest.K10.YesFree (closeBaseB)
open VerifiableInference.Desc.First.Close (Rec)

def St₀ : Statement := stOf ask₀ coin₀

/-- The statement with one more open row in its group. -/
def withRow (S : Statement) (r : OnBytes.Row) : Statement :=
  { S with groups := S.groups.modify 0 fun G => { G with rows := G.rows.push r } }

/-- A structured vector of five variables whose variable 0 is written out: its pair is (1, y); the
vector of which the written-out factor is a slice has n entries. -/
def dense (y : OnBytes.E) (n : Nat) : OnBytes.Tensor :=
  { OnBytes.Tensor.eq [e 2, e 3, e 5, e 7, e 11] with
    pairs := (oneE, y) :: (OnBytes.Tensor.eq [e 3, e 5, e 7, e 11]).pairs
    denseVars := [0], values := Array.replicate n (e 1) }

/-- The oracle message number o as sampled, with one answer: its sample row by the verifier's own
text, at the seed (z, 9). -/
def sampledAt (S : Statement) (o : Nat) (z : List OnBytes.E) : Statement :=
  { S with oracles := S.oracles.modify o fun x =>
      let sh := { x.shape with answers := 1 }
      { x with shape := sh, sampled := true
               sampleRows := ((VerifiableInference.Desc.Own.formMade S.codes sh o ⟨z, e 9⟩ 0).map
                 fun r => #[r]).getD #[] } }

/-- The first toy's statement with B (three index bits) and the kept C (four) sampled. -/
def StS : Statement := sampledAt (sampledAt St₀ 2 [e 2, e 3, e 5]) 3 [e 2, e 3, e 5, e 7]

/-- The same with the kept member's point one coordinate short. -/
def StShort : Statement := sampledAt (sampledAt St₀ 2 [e 2, e 3, e 5]) 3 [e 2, e 3, e 5]

/-- All three members sampled. A has main rows and a mask row: its sample row has a term on each
table. (Its point has six coordinates; the test reads the first five.) -/
def StAll : Statement := sampledAt StS 0 [e 2, e 3, e 5, e 7, e 11, e 13]

/-- A structured vector of three variables, as A's mask table has index bits, whose variable 0 is
written out with another pair than (1, 1). -/
def denseMask : OnBytes.Tensor :=
  { OnBytes.Tensor.eq [e 2, e 3, e 5] with denseVars := [0], values := #[e 1, e 2] }

-- yes at the two toys' records
#guard closeBaseB P ⟨none, fr, St₀⟩
#guard closeBaseB H.P ⟨none, H.fr, H.stOf ask₀ coin₀⟩
-- SAMPLE ROWS: both are there, and the plan counts them: yes · the plan does not count them: no ·
-- the kept member's point one coordinate short: no
#guard (StS.oracles.toList.map (·.sampleRows.size)) == [0, 0, 1, 1]
#guard closeBaseB { P with rows := 6 } ⟨none, fr, StS⟩
#guard !closeBaseB P ⟨none, fr, StS⟩
#guard (StShort.oracles.toList.map (·.sampleRows.size)) == [0, 0, 1, 1]
#guard !closeBaseB { P with rows := 6 } ⟨none, fr, StShort⟩
-- ALL MEMBERS SAMPLED: A's sample row has a term on the main and one on the mask table: yes
#guard (StAll.oracles.toList.map fun x => x.sampleRows.toList.map fun r =>
    r.terms.toList.map (·.part)) == [[[.main, .mask]], [], [[.main]], [[.main]]]
#guard closeBaseB { P with rows := 7 } ⟨none, fr, StAll⟩
-- of the vector of a term on a MASK table only the number of its variables is asked: three
-- variables: yes · the like out of order (the first line: it is): yes · one variable too few: no
#guard !denseMask.ok
#guard closeBaseB { P with rows := 5 }
  ⟨none, fr, withRow St₀ { terms := #[⟨0, .mask, OnBytes.Tensor.eq [e 2, e 3, e 5]⟩] }⟩
#guard closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { terms := #[⟨0, .mask, denseMask⟩] }⟩
#guard !closeBaseB { P with rows := 5 }
  ⟨none, fr, withRow St₀ { terms := #[⟨0, .mask, OnBytes.Tensor.eq [e 2, e 3]⟩] }⟩
-- one more row that is in order, and the plan counts it: yes
#guard closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { units := #[⟨0, .main, 31, e 1⟩] }⟩
#guard closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { units := #[⟨0, .mask, 0, e 1⟩] }⟩
-- no: the plan's count of rows · the plan's k · rows still owed a count
#guard !closeBaseB { P with rows := 5 } ⟨none, fr, St₀⟩
#guard !closeBaseB { P with k := 4 } ⟨none, fr, St₀⟩
#guard !closeBaseB P ⟨some 1, fr, St₀⟩
-- no: the like row on the fresh mask, which is no member · an index beyond the table
#guard !closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { units := #[⟨1, .mask, 0, e 1⟩] }⟩
#guard !closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { units := #[⟨0, .main, 32, e 1⟩] }⟩
-- a structured vector of the table's five variables: yes · with one variable too few: no
#guard closeBaseB { P with rows := 5 }
  ⟨none, fr, withRow St₀ { terms := #[⟨0, .main, OnBytes.Tensor.eq [e 2, e 3, e 5, e 7, e 11]⟩] }⟩
#guard !closeBaseB { P with rows := 5 }
  ⟨none, fr, withRow St₀ { terms := #[⟨0, .main, OnBytes.Tensor.eq [e 2, e 3, e 5, e 7]⟩] }⟩
-- a structured vector whose variable 0 is written out, with the pair (1, 1): yes · the same with
-- another pair there: no · the same with a vector too short for the slice: no · with variable 0
-- named twice: no
#guard closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { terms := #[⟨0, .main, dense oneE 2⟩] }⟩
#guard !closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { terms := #[⟨0, .main, dense (e 2) 2⟩] }⟩
#guard !closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { terms := #[⟨0, .main, dense oneE 1⟩] }⟩
#guard closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { terms := #[⟨0, .main, dense oneE 4⟩] }⟩
#guard !closeBaseB { P with rows := 5 } ⟨none, fr, withRow St₀ { terms := #[⟨0, .main,
  { dense oneE 4 with denseVars := [0, 0] }⟩] }⟩

/-! ### Two members by Lean's kernel, at which the theorems are called -/

/-- The test says yes at the first toy's record, which has a kept member and structured vectors: by
`decide +kernel`: Lean's kernel evaluates the test itself. -/
theorem kept_member : closeBaseB P ⟨none, fr, St₀⟩ = true := by decide +kernel

/-- So that record's block's decision says yes at every list of five rounds of the kind's shape:
`close_yes_of`, and beneath it `batch_rowfits`, called where the batched row has kept forms. -/
theorem kept_all_yes (rs : List Fmt.RoundView) (hl : rs.length = 5)
    (hs : ProofFile.Honest.K10.YesFree.ShapedAll rs) :
    ∃ s', ((VerifiableInference.Desc.First.Close.kind (Cl := Unit)) P).decide ⟨none, fr, St₀⟩ rs [] =
      .ok s' :=
  ProofFile.Honest.K10.YesFree.close_yes_of kept_member rs [] hl hs

/-- The like at the record with all three members sampled, one of them kept, one with a mask row. -/
theorem sampled_member : closeBaseB { P with rows := 7 } ⟨none, fr, StAll⟩ = true := by
  decide +kernel

theorem sampled_all_yes (rs : List Fmt.RoundView) (hl : rs.length = 5)
    (hs : ProofFile.Honest.K10.YesFree.ShapedAll rs) :
    ∃ s', ((VerifiableInference.Desc.First.Close.kind (Cl := Unit)) { P with rows := 7 }).decide
      ⟨none, fr, StAll⟩ rs [] = .ok s' :=
  ProofFile.Honest.K10.YesFree.close_yes_of sampled_member rs [] hl hs

end ProofFile.Honest.K10.Toy.Base

#print axioms ProofFile.Honest.K10.Toy.Base.kept_member
#print axioms ProofFile.Honest.K10.Toy.Base.kept_all_yes
#print axioms ProofFile.Honest.K10.Toy.Base.sampled_member
#print axioms ProofFile.Honest.K10.Toy.Base.sampled_all_yes
