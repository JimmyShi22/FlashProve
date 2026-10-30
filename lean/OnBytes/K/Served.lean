-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Served.lean: a test of the user's statement alone, which every yes of verify-on-bytes
without the option -policy has passed. Definitions only; the laws are in OnBytes/K/ServedLaws.lean.

The three stages of a whole call and the end of the call make, beside the checks of the key file,
the entry file and the proof file, tests that are functions of the user's statement (`UserStm`,
OnBytes/K/Stm.lean): the three public files, the request, the reply and the options.
  `keyFound`, `leafFound`, `requestFound`: the bodies of `keyStage`, `leafStage` and of `requestRun`
    with `requestStage` (OnBytes/Model/VerifyStages.lean), typed again without `Key.check`,
    `Entry.check`, `entryTable` and `Proof.check`. Where a stage returns, the like function returns
    the same; for the first two: where the file's check says yes, the two are equal.
  `tailAt`: the end of the call, by the program's own function (`Model.Stages.cpStagesRun`), on
    these three results, under the user's own ID.
  `servedAt Z x`: x's three public files are Z's, byte for byte; the options name an ID of 64 hex
    digits and 128 bits, and neither -no-proof-of-work nor -policy; the program's printed digest and
    the planner return on the three files; and `tailAt` ends in a yes.
What it is not. It is necessary for a yes under these options; that it is all that the call tests of
the statement is not stated: the call's first tests (`readFirst`, `readCall`: the bits against half
a digest, KL.bin's length, the parameter file's first line, the two lengths, the policy against the
request) and the shell's limits on the files' sizes are not called here. It tests nothing of the key
file, the entry file or the proof file, their heads and the key's table among them. Inside `tailAt`
the stages' ID is the user's own, so the end's two tests on the ID say nothing here: that the ID is
the key's table's is the run's matter. A call that names -policy, so every call that ends within
limits, is not served. The option -next-token is left free. Z is a letter: no description is tied to
it here.

-/
import OnBytes.K.Stm

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-- A description's three public files, as bytes. -/
structure Pub where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray

/-- What every stage holds, as far as it follows from the three public files, under a given ID. The
table is left empty: nothing below reads it. -/
def commonAt (p : Planned) (idHex : String) : Common :=
  { X := p.X, chains := p.chains, built := p.built, first := ⟨ByteArray.empty, []⟩, idHex := idHex }

/-- The body of the stage key without `Key.check`. -/
def keyFound (C : Common) (asked : Nat) : Except Refused Found := do
  let a ← named (C.acct C.chains.made.key asked "key")
  named (workHeldH (Params.needsWork C.chains.made.key) a.work)
  pure (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
    lidbSealed 0, some a.acct, a.work)

/-- The body of the stage leaf without `Entry.check`. -/
def leafFound (C : Common) (asked : Nat) : Except Refused Found := do
  let a ← named (C.acct [C.chains.made.entry] asked "leaf")
  named (workHeldH (Params.needsWork [C.chains.made.entry]) a.work)
  pure (lastLine (!C.X.p4) (askedBelowBar asked) (C.oneTimeForm)
    lidbSealed 0, some a.acct, a.work)

/-- The bodies of `requestRun` and `requestStage` without `entryTable` and `Proof.check`. -/
def requestFound (C : Common) (o : Options) (pol KL request y : ByteArray) (hasLayout : Bool) :
    Except Refused Found := do
  named (refuseIf (request.size % 4 != 0 || y.size % 4 != 0) "statement-required")
  let so ← named (Head.stFromCall (words32 request) (words32 y) C.X.T)
  let cov ← named (Head.coveredOf so C.X.T C.X.P.h.V)
  let a ← named (C.acct C.chains.made.proof o.bits "request")
  let item ← named
    (match Proof.requestItem pol KL request with
    | some w => pure w
    | none => throw "internal-request-item")
  named (statementHeld C.X item)
  let _ ← named (linksOf C.X cov)
  named (workHeldH (Params.needsWork C.chains.made.proof) a.work)
  pure (lastLine (!C.X.p4) (askedBelowBar o.bits) (servedForm (servedOf C o hasLayout so cov))
      C.X.P.settings.lidb C.X.P.settings.nminH,
    acctWhole C.chains.made.sized.set
      (some (C.chains.made.key ++ [C.chains.made.entry] ++ C.chains.made.proof)), a.work)

/-- What a whole call knows of the ID and of its options, at the ID i in lower-case digits and the
printed digest hp. -/
def cpAt (o : Options) (i hp : String) : CpId :=
  { asked := i, named := o.id.isSome, needed := true, policyGiven := o.policy.isSome, hPar := hp,
    noProofOfWork := o.noProofOfWork }

/-- The three stages' results where the three files' checks say yes. -/
def outsAt (C : Common) (x : UserStm) : List StageOut :=
  [C.oneTimeOut .key (keyFound C x.options.bits), C.oneTimeOut .leaf (leafFound C x.options.bits),
   stageOut .request C.idHex (requestFound C x.options x.pol x.KL x.request x.y true)]

/-- The end of a whole call where the three files' checks say yes, by the program's own function. -/
def tailAt (p : Planned) (x : UserStm) (i hp : String) : CallEnd :=
  cpStagesRun (outsAt (commonAt p i) x) none (askedBelowBar x.options.bits) x.options.bits
    (cpAt x.options i hp) (some (words32 x.request, (commonAt p i).policyLines))

/-- True for a yes. -/
def isYes : CallEnd → Bool
  | .yes _ _ => true
  | _ => false

/-- The options that are served: an ID is named; 128 bits; neither -no-proof-of-work nor -policy. -/
def optionsServed (o : Options) : Bool :=
  o.id.isSome && decide (o.bits = 128) && !o.noProofOfWork && o.policy.isNone

/-- The test. In words, with what it is not: the head of this file. -/
def servedAt (Z : Pub) (x : UserStm) : Bool :=
  decide (x.pol = Z.pol) && decide (x.lay = Z.lay) && decide (x.KL = Z.KL) &&
    optionsServed x.options &&
    match x.options.id.bind idAsked, Model.hPar x.pol x.KL (some x.lay),
        planned x.pol x.KL (some x.lay) with
    | some i, .ok hp, .ok p => isYes (tailAt p x i (Model.hex64 hp))
    | _, _, _ => false

end OnBytes.K
