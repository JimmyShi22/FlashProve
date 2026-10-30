-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/BeforeE.lean: the two tests on the plan that ask for the number of a tree's
sending round (beforeAt, Johnson/Desc/Block.lean; BookPlan.inTime, Johnson/Desc/BookPlan.lean), each
with the eager twin of that routine (SendRoundE.lean) in its place. General in the description: no
value is treated.

Main names.
  beforeAtE: beforeAt's text with sendRoundE 0 for sendRound. beforeAt_eq: the two are one.
  beforeOkAt D b₁ b₂ b₃: FileDescription.beforeOk's text over beforeAtE, at three lists of declared rounds
  and three lists of blocks. beforeOk_at: F.beforeOk is that at F's own.
  inTimeE, inTime_eq: the like for BookPlan.inTime.
Limits. The twins copy the two tests' texts; the equations hold the copies against the originals.
That the kernel gets through a given list is seen where a theorem is checked. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.SendRoundE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc

variable {S Cl : Type}

/-- beforeAt's text over the eager twin. -/
def beforeAtE (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) : Nat → List (Block S Cl) → Bool
  | _, [] => true
  | from', b :: l =>
    (b.before.all fun m =>
      let ds := if m.1 == 1 then D.1 else if m.1 == 2 then D.2.1 else D.2.2
      let os := if m.1 == 1 then O.1 else if m.1 == 2 then O.2.1 else O.2.2
      let last := if m.1 == c + 1 then from' + b.rounds.findIdx drawsAny else ds.length
      match sendRoundE 0 ds m.2 with
      | none => false
      | some i =>
        decide (1 ≤ m.1) && decide (m.1 ≤ c + 1) && decide (i ≤ last) &&
          (!((os[m.2]?).any fun o => o.tenants.any (·.sampled)) ||
            ds.zipIdx.any fun r =>
              r.1.entry.answers != 0 && decide (i < r.2) && decide (r.2 ≤ last))) &&
    beforeAtE D O c (from' + b.rounds.length) l

theorem beforeAt_eq (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) :
    ∀ (l : List (Block S Cl)) (f : Nat), beforeAt D O c f l = beforeAtE D O c f l
  | [], _ => by simp only [beforeAt, beforeAtE]
  | b :: l, f => by
    simp only [beforeAt, beforeAtE, beforeAt_eq D O c l, sendRound_eq]
    rfl

/-- FileDescription.beforeOk's text over beforeAtE, at three lists of rounds and three of blocks. -/
def beforeOkAt {S₁ S₂ S₃ : Type}
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (b₁ : List (Block S₁ Cl)) (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl)) : Bool :=
  let O := (oraclesOf b₁, oraclesOf b₂, oraclesOf b₃)
  beforeAtE D O 0 0 b₁ && beforeAtE D O 1 0 b₂ && beforeAtE D O 2 0 b₃

theorem beforeOk_at {Xi : Type} (F : FileDescription Xi) :
    F.beforeOk = beforeOkAt F.roundsDeclaredByBlocks F.first.blocksInOrder F.shared.blocksInOrder F.second.blocksInOrder := by
  simp only [FileDescription.beforeOk, beforeOkAt, beforeAt_eq]

/-- BookPlan.inTime's text over the eager twin. -/
def inTimeE (D : BookPlan.DeclaredRoundsByChain) (T : BookPlan.SentOraclesByChain) : Bool :=
  [D.1, D.2.1, D.2.2].zipIdx.all fun c => c.1.zipIdx.all fun d => d.1.opens.all fun o =>
    match o.2 with
    | .own n => (sendRoundE 0 c.1 n).any fun i =>
        decide (i + (if BookPlan.holdsSampled T c.2 n then 1 else 0) ≤ d.2)
    | .taken chain sent => c.2 == 2 && decide (chain < 2) &&
        (sendRoundE 0 (([D.1, D.2.1, D.2.2][chain]?).getD []) sent).isSome

theorem inTime_eq (D : BookPlan.DeclaredRoundsByChain) (T : BookPlan.SentOraclesByChain) :
    BookPlan.inTime D T = inTimeE D T := by
  simp only [BookPlan.inTime, inTimeE, roundOfRoot_eq]
  rfl

end Johnson.KB4

#print axioms Johnson.KB4.beforeAt_eq
#print axioms Johnson.KB4.beforeOk_at
#print axioms Johnson.KB4.inTime_eq
