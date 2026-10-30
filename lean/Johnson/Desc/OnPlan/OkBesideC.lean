-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkBesideC.lean: the file's own share of the tests on a planner's answer
(OkD.Share.beside, Johnson/Desc/OnPlan/OkShare.lean), TYPED AT THE PUBLIC PART AND THE CHAINS; and
that it is that share. Definitions with code, and one law.

IT STANDS OVER NO FILE THAT IMPORTS Mathlib.

How it is made. Each definition is the one of the same name in OkParamsDefs.lean, OkDesc.lean,
OkRead.lean, OkLists.lean or OkShare.lean (all in Johnson/Desc/OnPlan/), to the letter, with «c»
where the original has «p.chains» and «X» where it has «p.X». Its argument is
c : Model.Verify.Chains, and in front of it X : Model.Verify.Public where the definition, or one
that it calls, reads p.X. Two clauses do: remadeF, the first chain's plan made anew of the
sub-proofs' sizes; settingZ, the setting off the parameter file's lines.

Why. As for OkD.AtC.front2 (Johnson/Desc/OnPlan/OkFrontC.lean): the originals take the planner's
whole answer and read its fields «chains» and «X» alone; but its field «built» holds the links with
their routines, whose types name the verifier program's monads and its context. A description's test
on the plan is to reach none of them.

Main names (namespace VerifiableInference.OnPublicFiles.OkD.AtC): k12, front1, front3, file, entries;
beside X c: **the share**: all of the tests on the plan but those that fall to the shared chain's
blocks. beside_eq: OkD.Share.beside p = AtC.beside p.X p.chains.

What is not claimed. THAT IT SAYS YES AT ANY X, c: nothing is evaluated here. THAT THE TYPE
Model.Verify.Public NAMES NONE OF THE PROGRAM's MONADS: a walk over constants is to say. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.OnPlan.OkFrontC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

namespace AtC

/-- The first chain's parameters in a planner's answer. -/
abbrev proofFirst (c : Model.Verify.Chains) : Params.First := c.proof.first

/-- What is public about the proof file's tail, as the proof file's decision has it. -/
abbrev proofTail (c : Model.Verify.Chains) : Proof.TailPublic :=
  Proof.tailPublic c.proof Maker.noTable

/-- What linWithU returns at the tail's test on the table; the empty array where it returns
nothing. -/
def proofWu (c : Model.Verify.Chains) : Array OracleNotice :=
  (linWithU (proofTail c).lin).getD #[]

/-- The codes of the proof file's shared chain, as its parameter bytes are read back. -/
abbrev codesS (c : Model.Verify.Chains) : Codes := c.proof.shared.codes

/-- The shape of the test on the table, as the shared chain's parameter bytes are read back. -/
abbrev linS (c : Model.Verify.Chains) : Params.LinShape := c.proof.shared.lin

/-- The notices of the sending of the folded row. -/
def sentU (c : Model.Verify.Chains) : Array OracleNotice :=
  #[(⟨(linS c).fold.u, (linS c).fold.leafClass⟩ : OracleNotice)] ++ proofWu c

/-- The notices of the sending of Omega. -/
def sentO (c : Model.Verify.Chains) : Array OracleNotice := linMessageOmega (linS c)

/-- In the test on the table the masks go ahead. -/
def ahead (c : Model.Verify.Chains) : Bool := (linS c).masksAhead

/-- The stages of the test on the folded row's group fit together. -/
def stagesU (c : Model.Verify.Chains) : Bool :=
  ioppOk (codesS c) (linS c).testU c.proof.shared.given.plan.samples

/-- So do those of the test on Omega's group, where it has a group of its own. -/
def stagesO (c : Model.Verify.Chains) : Bool :=
  !(linS c).sharedSplitNeeded ||
    ioppOk (codesS c) (linS c).testOmega c.proof.shared.given.plan.samples

/-- So do those of the test on a request's own group. -/
def stagesW (c : Model.Verify.Chains) : Bool :=
  ioppOk (codesS c) (linS c).testOwn c.proof.second.given.plan.samples

/-- The first stage of the test on the folded row's group has the group's two codes. -/
def firstU (c : Model.Verify.Chains) : Bool :=
  firstIs (linS c).testU (linS c).fold.u.code (linS c).sharedMaskCode

/-- So has that of the test on Omega's group, where it has a group of its own. -/
def firstO (c : Model.Verify.Chains) : Bool :=
  !(linS c).sharedSplitNeeded ||
    firstIs (linS c).testOmega (linS c).omega.code
      (linS c).sharedMaskCode

/-- So has that of the test on a request's own group. -/
def firstW (c : Model.Verify.Chains) : Bool :=
  firstIs (linS c).testOwn (linS c).w.code (linS c).ownMaskCode

/-- Each of the three plans that the planner has made for the proof file's chains holds. -/
def heldS (c : Model.Verify.Chains) : Bool := c.made.proof.all (·.holds)

/-- The three made plans' entries are the three plans' entries as read back. -/
def readPlans (c : Model.Verify.Chains) : Bool :=
  decide (c.made.proof.map (·.plan.entries) =
    [c.proof.first.given.plan.entries, c.proof.shared.given.plan.entries,
      c.proof.second.given.plan.entries])

/-- The planner's own routine for the first chain, run anew at what is sized and at the sub-proofs'
sizes made out of X and the links that are sized, returns, and its entries are the first chain's
entries as read back. -/
def remadeF (X : Model.Verify.Public) (c : Model.Verify.Chains) : Bool :=
  let z := c.made.sized.proof
  match Params.firstPlan z (Model.Verify.subproofsWith X z.request.link) with
  | .ok P => decide (P.plan.entries = c.proof.first.given.plan.entries)
  | .error _ => false

/-- The same for the second chain. -/
def remadeW (c : Model.Verify.Chains) : Bool :=
  let z := c.made.sized.proof
  match Params.secondPlan z.set z.batch with
  | .ok P => decide (P.plan.entries = c.proof.second.given.plan.entries)
  | .error _ => false

/-- The setting in what is sized is what the parameter file's lines, as X holds them, fix. -/
def settingZ (X : Model.Verify.Public) (c : Model.Verify.Chains) : Bool :=
  decide (c.made.sized.proof.set = Params.settingOf X.P.frame)

/-- Each of the three made plans has that setting as its own. -/
def madeSets (c : Model.Verify.Chains) : Bool :=
  c.made.proof.all fun P => decide (P.set = c.made.sized.proof.set)

/-- What the steps ask at the shared chain's first rounds. -/
def frontWant (c : Model.Verify.Chains) : List (String × Nat × Nat × Nat × Nat × Nat × Nat) :=
  [("LIN point", (linS c).kCol, 0, 0, 0, 0, 0)] ++ sendWant (codesS c) (sentU c) ++
    [("LOC", 0, 0, (linS c).fold.columns,
      if (linS c).fold.columns == 0 then 0 else (linS c).fold.index.code.logN,
      0, 0)] ++
    sendWant (codesS c) (sentO c) ++ [("LIN zeta", (linS c).kRow, 0, 0, 0, 0, 0)] ++
    if (linS c).sharedSplitNeeded then [("SPLIT", 0, 0, 0, 0, 0, 0)] else []

/-- The plan's first entries have just these names and numbers. -/
def frontS (c : Model.Verify.Chains) : Bool :=
  (c.proof.shared.given.rounds.take (frontWant c).length).map numbersOf == frontWant c

/-- The chain's last entry counts no batched rows. -/
def sealS (c : Model.Verify.Chains) : Bool :=
  (c.proof.shared.given.rounds.getLast?.map (·.rows == 0)).getD false

def n1 (c : Model.Verify.Chains) : Bool := (proofFirst c).given.plan.samples == 1

def n2 (c : Model.Verify.Chains) : Bool := (proofFirst c).shape.choice.masksRide

def n4 (c : Model.Verify.Chains) : Bool := (proofTail c).second.given.plan.samples == 1

def n5 (c : Model.Verify.Chains) : Bool := (proofTail c).lin.choice.masksRide

def n6 (c : Model.Verify.Chains) : Bool := !(proofTail c).lin.ownSplitNeeded

def n8 (c : Model.Verify.Chains) : Bool := !(proofTail c).lin.testOwn.isEmpty

def n9 (c : Model.Verify.Chains) : Bool := !(proofFirst c).shape.link.isEmpty

/-- The proximity test, at its three places in the shared and the second chain. -/
def k12 (c : Model.Verify.Chains) : Bool := stagesU c && stagesO c && stagesW c && n8 c

/-- The first chain as a whole. -/
def front1 (X : Model.Verify.Public) (c : Model.Verify.Chains) : Bool :=
  n1 c && n2 c && n9 c && remadeF X c

/-- The second chain as a whole. -/
def front3 (c : Model.Verify.Chains) : Bool := n4 c && remadeW c

/-- What ties places or chains. -/
def file (X : Model.Verify.Public) (c : Model.Verify.Chains) : Bool :=
  n5 c && n6 c && ahead c && firstU c && firstO c && firstW c && heldS c &&
    readPlans c && settingZ X c && madeSets c

/-- The shared chain's entries as read back are what the steps want. -/
def entries (c : Model.Verify.Chains) : Bool := frontS c && sealS c

/-- All but k14, k1 and front2. -/
def beside (X : Model.Verify.Public) (c : Model.Verify.Chains) : Bool :=
  k12 c && front1 X c && front3 c && file X c && entries c

end AtC

/-- **It is the share.** -/
theorem beside_eq (p : Model.Verify.Planned) : Share.beside p = AtC.beside p.X p.chains := rfl

end VerifiableInference.OnPublicFiles.OkD
