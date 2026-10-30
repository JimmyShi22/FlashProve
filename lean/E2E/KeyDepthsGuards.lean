-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyDepthsGuards.lean

Two closed questions for `DepthsDeclared` at the key file's shared chain, by Lean's evaluator.
KeyDepthsKernel.lean imports this file.

  `depthOf`   the depth of each own tree, 0 to 10: a list reckoned by hand
  `depthsR`   every opening in the rounds before a border is of an own tree, at that tree's depth
  `takesFit`  a sending's own coins lie within the book's count at its address: where so, the cut in
                `sendTable` returns at every run's coins (`Cs.cut`, `look_due`)

Limits. Evaluations outside the kernel: no theorem. That `depthOf` is each table's real depth is what
the general lines of KeyDepthsAt.lean owe: here the rounds' declared depths are compared with the list. Nothing on
completeness, on soundness or on what is hidden.
-/
import E2E.KeyOpensGuards
import E2E.KeyBookHeldK12
import Johnson.Desc.ProofFile.Honest.K14.Sendings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyOpens
open ProofFile.Honest
open ProofFile.Honest.K14 (SendJob sendingPart jobU jobOmega sendPlace)
open AtPublicFiles.KeyBook (atFull keyBook)
open AtPublicFiles.AtFiles.Full (QK)

/-- The depth of each own tree of the shared chain. -/
def depthOf : List Nat := [24, 22, 13, 21, 17, 13, 14, 13, 18, 14, 15]

/-- Every opening before border n is of an own tree, at the depth that D lists. -/
def depthsR (R : List (List Fmt.DeclaredRound × Nat)) (D : List Nat) (n : Nat) : Bool :=
  ((R.take n).flatMap (·.1)).all fun d => d.opens.all fun o =>
    match o.2 with
    | .own j => o.1.a == D.getD j 0
    | .taken _ _ => false

/-- The sending's own coins against the book's count, in the shared chain. -/
def takesFit (B : ProverCoinCounts) (a : Addr) (J : SendJob) : Bool :=
  decide ((sendingPart J).takes.f ≤ (dueAt (B.rowsOf 1) a).f) &&
    decide ((sendingPart J).takes.e ≤ (dueAt (B.rowsOf 1) a).e)

-- Depth and source of every opening, member by member.
#eval keyR.map fun x => (x.1.flatMap (·.opens)).map fun o => (srcNum o.2, o.1.a)

-- Foretold: yes at 10, 11, 12; no at a depth bent at an own tree that is opened.
#guard depthsR keyR depthOf 10 && depthsR keyR depthOf 11 && depthsR keyR depthOf 12
#guard !depthsR keyR (depthOf.set 3 20) 10
#guard !depthsR keyR (depthOf.set 7 20) 11

-- Foretold: the two sendings' coins lie within the book; a place with no row says no.
#guard atFull fun K => takesFit (keyBook K) ⟨sendPlace 2, 0⟩ (jobU ⟨QK, 0⟩)
#guard atFull fun K => takesFit (keyBook K) ⟨sendPlace 5, 0⟩ (jobOmega ⟨QK, 0⟩)
#guard atFull fun K => !takesFit (keyBook K) ⟨sendPlace 3, 0⟩ (jobU ⟨QK, 0⟩)

end AtPublicFiles.KeyOpens

#print axioms AtPublicFiles.KeyOpens.depthOf
#print axioms AtPublicFiles.KeyOpens.depthsR
#print axioms AtPublicFiles.KeyOpens.takesFit
