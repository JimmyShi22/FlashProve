-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean: each definition of the whole program's twin over a monad
(OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean, VerifyStages.lean, VerifyChains.lean: sixteen definitions), at
the identity monad, the program's hash and, for the request file's digest, the second hash
function's own function, has the value of the port's own function (OnBytes/Model/Verify.lean,
VerifyStages.lean, VerifyChains.lean), at all arguments.

OnBytes/ChecksWithHashAsArgument/M/AtPort/Files.lean has this for the leaves: the checks of a key file, an entry file
and a proof file, the request's item, the two digests. Here it is carried up the spine: the plan,
the stages' common beginning, the three stages, the whole call; the calls on one file; the chains'
parameter bytes.

The twin's steps with refusals live in `ExceptT ε Id`, the port's in `Except ε`. `RelX x x'` says
that the run of x is x': full equality, refusals and their names included. It is kept by pure,
throw, bind, the lift from `Except ε`, and a lifted step of the identity monad against a plain
"let".

Main theorems. Each says: the twin at `(m := Id)`, `formatHashFastForm` (and, where the request's item is made,
`fun b => secondHashFunctionTree b`) is the port's function of the same name, at all arguments. No hypothesis, but
in `partCall_port`, which takes the stage's run as a letter on each side and asks that the two be
related. Fifteen by name; the sixteenth definition, `namedT`, has no port's function of its name:
`relX_namedT` ties it to `named`.
  `configuration_port`: with `planned_port`, `commonOf_port`, `common_port`, `commonOfCall_port`: up
    to the stages' common beginning.
  `keyStage_port`: with `leafStage_port`, `requestRun_port`, `requestStage_port`, `stagesOf_port`:
    the three stages.
  `wholeCall_port`: the whole call.
  `partCall_port`: with `keyCall_port`, `leafCall_port`, `planBytes_port`: the calls on one file;
    the chains' parameter bytes.

Limits: equalities of values, AT ONE POINT: the identity monad and the program's hash. Nothing is
said of the twin at another hash or over another monad. ONE PURE FUNCTION IS TIED,
`Model.Verify.wholeCall` with what it calls: the shell (the reads, the printed lines, the entry's
number) has no twin. ONE EQUATION AT ONE POINT DOES NOT SHOW THAT THE HASH IS A LETTER: it would
hold word for word of a twin that in some place called `formatHashFastForm` itself and let its letter lie. That
the letter reaches every call of the format's hash is no theorem. By the same walk, from the generic
`wholeCall` none of `formatHashFastForm`, `Fmt.formatHash`, `Fmt.HF`, `Fmt.oracle`, `Fmt.HO`, `Fmt.blake2b`, `Run.oBits`,
`Run.oB`, `Params.configurationDigest`, `Fmt.configDigest`, `Fmt.paramsDigest` is reached: a walk
over names in values, which a hash under another name would pass.
THE SECOND HASH FUNCTION IS A LETTER AT ONE CALL ALONE: the twin's second letter stands for the
request file's digest. Whatever it is, the second hash function is laid in fast. By a walk of Lean's
environment (definitions' values; no theorem), eight constants in the generic whole call's cone name
it in their own values: `OnBytes.TwoPort.M.Proof.requestItemOf`, `OnBytes.Proof.ParamLines.calls`,
`OnBytes.Model.textTH`, `OnBytes.Model.tableDigest`, `OnBytes.Model.parDigests`,
`OnBytes.Model.hParOf`, `OnBytes.Model.Verify.callsDigest`, `OnBytes.Attention.callsDigest`; so it
is reached through `readFirst`, `readCall` and `publicOf`.
What the twin leaves unturned is the port's own on both sides (among them `publicOf`, `chainsOf`,
`builtOf`, `readCall`, `readFirst`, `entryTable`, `Key.readTable`, `linksOf`, `statementHeld`,
`cpStagesRun`, the accounting). "The program's hash" is more than one text and one function: `formatHashFastForm`
is `Fmt.formatHash` (`formatHashFastForm_eq_formatHash`), and among others the ID's leaf goes through that equation. That the hash
by asking the realised oracle (`Fmt.HO Fmt.oracle`) is the same function is known on the hash's
domain alone (`Fmt.HO_oracle`, Fmt/Rules23Laws.lean) and is not used here.
`OnBytes.K.Oracle.twin_at_port` (OnBytes/K/Oracle/ReaderAt.lean) is another theorem: the entry
file's reader alone. Nothing on soundness. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Files
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify
import OnBytes.ChecksWithHashAsArgument.M.Model.ExceptHom

set_option autoImplicit false

namespace OnBytes.TwoPort.M.AtPort

open OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages

/-! ## Do-notation inside `ExceptT ε Id` against do-notation inside `Except ε` -/

/-- The run of x, a computation with refusals over the identity monad, is x'. -/
def RelX {ε α : Type} (x : ExceptT ε Id α) (x' : Except ε α) : Prop := x.run = x'

/-- Kept by pure. -/
theorem relX_pure {ε α : Type} (a : α) : RelX (pure a : ExceptT ε Id α) (pure a) := rfl

/-- Kept by throw. -/
theorem relX_throw {ε α : Type} (e : ε) : RelX (throw e : ExceptT ε Id α) (throw e) := rfl

/-- Kept by bind. -/
theorem relX_bind {ε α β : Type} {x : ExceptT ε Id α} {x' : Except ε α}
    {f : α → ExceptT ε Id β} {f' : α → Except ε β} (hx : RelX x x')
    (hf : ∀ a, RelX (f a) (f' a)) : RelX (x >>= f) (x' >>= f') := by
  unfold RelX at hx ⊢
  rw [Model.runE_bind]
  show (match x.run with
    | .ok a => (f a).run
    | .error e => (pure (.error e) : Id (Except ε β))) = x' >>= f'
  rw [hx]
  cases x' with
  | ok a => exact hf a
  | error e => rfl

/-- Lean's own lift of a pure step in `Except ε`. -/
theorem relX_liftE {ε α : Type} (x : Except ε α) : RelX (liftM x : ExceptT ε Id α) x := rfl

/-- A step in the identity monad, lifted and bound, against a plain value. -/
theorem relX_let {ε α β : Type} {a : Id α} {a' : α} {f : α → ExceptT ε Id β} {y' : Except ε β}
    (e : a = a') (h : RelX (f a') y') : RelX ((liftM a : ExceptT ε Id α) >>= f) y' := by
  subst e
  unfold RelX at h ⊢
  rw [Model.runE_bind]
  exact h

/-- `namedT` against `named`. -/
theorem relX_namedT {α : Type} {x : ExceptT String Id α} {x' : Except String α} (h : RelX x x') :
    RelX (M.Model.Verify.namedT x) (named x') := by
  unfold RelX at h ⊢
  unfold M.Model.Verify.namedT
  show named x.run = named x'
  rw [h]

/-! ## The spine -/

/-- The digest of the three configuration files. -/
theorem configuration_port (pol layout KL : ByteArray) :
    M.Model.Verify.configuration (m := Id) formatHashFastForm pol layout KL =
      OnBytes.Model.Verify.configuration pol layout KL := rfl

/-- All that follows from the three configuration files. -/
theorem planned_port (pol KL : ByteArray) (layout : Option ByteArray) :
    RelX (M.Model.Verify.planned (m := Id) formatHashFastForm pol KL layout)
      (OnBytes.Model.Verify.planned pol KL layout) := by
  unfold M.Model.Verify.planned OnBytes.Model.Verify.planned
  refine relX_bind (relX_liftE _) fun X => ?_
  refine relX_let (configuration_port _ _ _) ?_
  refine relX_bind (relX_liftE _) fun chains => ?_
  refine relX_bind (relX_liftE _) fun built => ?_
  exact relX_pure _

/-- The steps that all stages share after the plans are made. -/
theorem commonOf_port (X : Public) (cfg : ByteArray) (chains : Chains) (built : LinksH)
    (key : ByteArray) (asked : String) :
    RelX (M.Model.Verify.commonOf (m := Id) formatHashFastForm X cfg chains built key asked)
      (OnBytes.Model.Verify.commonOf X cfg chains built key asked) := by
  unfold M.Model.Verify.commonOf OnBytes.Model.Verify.commonOf
  dsimp only
  cases Key.readTable chains.tableShape cfg key with
  | ok x =>
    refine relX_bind (relX_pure _) fun first => ?_
    refine relX_let (commitmentId_port _ _ _) ?_
    refine relX_bind (relX_liftE _) fun _ => ?_
    exact relX_pure _
  | error e =>
    refine relX_bind (relX_liftE _) fun first => ?_
    refine relX_let (commitmentId_port _ _ _) ?_
    refine relX_bind (relX_liftE _) fun _ => ?_
    exact relX_pure _

/-- The stage key. -/
theorem keyStage_port (C : Common) (asked : Nat) (key : ByteArray) :
    RelX (M.Model.Verify.keyStage (m := Id) formatHashFastForm C asked key)
      (OnBytes.Model.Verify.keyStage C asked key) := by
  unfold M.Model.Verify.keyStage OnBytes.Model.Verify.keyStage
  refine relX_bind (relX_liftE _) fun a => ?_
  refine relX_let (keyCheck_port _ _) ?_
  cases OnBytes.Key.check C.chains.key key with
  | error e => exact relX_liftE _
  | ok t => exact relX_bind (relX_liftE _) fun _ => relX_pure _

/-- The stage leaf. -/
theorem leafStage_port (C : Common) (asked : Nat) (entry : ByteArray) :
    RelX (M.Model.Verify.leafStage (m := Id) formatHashFastForm C asked entry)
      (OnBytes.Model.Verify.leafStage C asked entry) := by
  unfold M.Model.Verify.leafStage OnBytes.Model.Verify.leafStage
  refine relX_bind (relX_liftE _) fun a => ?_
  refine relX_let (entryCheck_port _ _ _) ?_
  cases OnBytes.Entry.check C.chains.made.entryLink C.first entry with
  | error e => exact relX_liftE _
  | ok t => exact relX_bind (relX_liftE _) fun _ => relX_pure _

/-- The stage request up to the verdict on the proof file. -/
theorem requestRun_port (C : Common) (o : Options) (r : Read) (entry : ByteArray) :
    RelX (M.Model.Verify.requestRun (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) C o r entry)
      (OnBytes.Model.Verify.requestRun C o r entry) := by
  unfold M.Model.Verify.requestRun OnBytes.Model.Verify.requestRun
  dsimp only
  refine relX_bind (relX_liftE _) fun _ => ?_
  refine relX_bind (relX_liftE _) fun so => ?_
  refine relX_bind (relX_liftE _) fun cov => ?_
  refine relX_bind (relX_liftE _) fun further => ?_
  refine relX_bind (relX_liftE _) fun a => ?_
  refine relX_let (requestItem_port _ _ _) ?_
  cases OnBytes.Proof.requestItem r.pol r.KL r.request with
  | some w =>
    refine relX_bind (relX_pure _) fun item => ?_
    refine relX_bind (relX_liftE _) fun _ => ?_
    refine relX_bind (relX_liftE _) fun ls => ?_
    refine relX_let (proofCheck_port _ _ _ _ _ _ _ _) ?_
    exact relX_pure _
  | none =>
    refine relX_bind (relX_throw _) fun item => ?_
    refine relX_bind (relX_liftE _) fun _ => ?_
    refine relX_bind (relX_liftE _) fun ls => ?_
    refine relX_let (proofCheck_port _ _ _ _ _ _ _ _) ?_
    exact relX_pure _

/-- The stage request. -/
theorem requestStage_port (C : Common) (o : Options) (r : Read) (entry : ByteArray) :
    RelX (M.Model.Verify.requestStage (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) C o r entry)
      (OnBytes.Model.Verify.requestStage C o r entry) := by
  unfold M.Model.Verify.requestStage OnBytes.Model.Verify.requestStage
  refine relX_bind (relX_namedT (requestRun_port _ _ _ _)) fun x => ?_
  cases x.verdict with
  | refused e => exact relX_throw _
  | accepted => exact relX_bind (relX_liftE _) fun _ => relX_pure _

/-- What every stage has computed when it turns to its own file. -/
theorem common_port (p : Planned) (r : Read) :
    RelX (M.Model.Verify.Planned.common (m := Id) formatHashFastForm p r) (p.common r) :=
  commonOf_port _ _ _ _ _ _

/-- The same from the files of a call. -/
theorem commonOfCall_port (r : Read) :
    RelX (M.Model.Verify.commonOfCall (m := Id) formatHashFastForm r) (OnBytes.Model.Verify.commonOfCall r) := by
  unfold M.Model.Verify.commonOfCall OnBytes.Model.Verify.commonOfCall
  exact relX_bind (relX_namedT (planned_port _ _ _)) fun p => common_port p r

/-- The three stages' results, with the policy's lines. -/
theorem stagesOf_port (o : Options) (r : Read) (entry : ByteArray) :
    M.Model.Verify.stagesOf (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) o r entry =
      OnBytes.Model.Verify.stagesOf o r entry := by
  unfold M.Model.Verify.stagesOf OnBytes.Model.Verify.stagesOf
  have e : (M.Model.Verify.commonOfCall (m := Id) formatHashFastForm r).run =
      OnBytes.Model.Verify.commonOfCall r := commonOfCall_port r
  rw [e]
  cases OnBytes.Model.Verify.commonOfCall r with
  | error x => rfl
  | ok C =>
    have k : (M.Model.Verify.keyStage (m := Id) formatHashFastForm C o.bits r.key).run =
        OnBytes.Model.Verify.keyStage C o.bits r.key := keyStage_port _ _ _
    have l : (M.Model.Verify.leafStage (m := Id) formatHashFastForm C o.bits entry).run =
        OnBytes.Model.Verify.leafStage C o.bits entry := leafStage_port _ _ _
    have q : (M.Model.Verify.requestStage (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) C o r entry).run =
        OnBytes.Model.Verify.requestStage C o r entry := requestStage_port _ _ _ _
    show (do
      let k ← (M.Model.Verify.keyStage (m := Id) formatHashFastForm C o.bits r.key).run
      let l ← (M.Model.Verify.leafStage (m := Id) formatHashFastForm C o.bits entry).run
      let q ← (M.Model.Verify.requestStage (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) C o r entry).run
      pure ([C.oneTimeOut .key k, C.oneTimeOut .leaf l, stageOut .request C.idHex q],
        C.policyLines) : Id _) = _
    rw [k, l, q]
    rfl

/-- **At the identity monad, the program's hash and the second hash function's own function, the
whole call's twin is the port's own whole call.** -/
theorem wholeCall_port (o : Options) (f : Files) :
    M.Model.Verify.wholeCall (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) o f =
      OnBytes.Model.Verify.wholeCall o f := by
  unfold M.Model.Verify.wholeCall OnBytes.Model.Verify.wholeCall
  cases readCall o f with
  | error e => rfl
  | ok r =>
    cases f.entry with
    | none => rfl
    | some entry =>
      show (do
        let (stages, lines) ← M.Model.Verify.stagesOf (m := Id) formatHashFastForm (fun b => secondHashFunctionTree b) o r entry
        pure (cpStagesRun stages none (askedBelowBar o.bits) o.bits r.id
          (some (words32 r.request, lines))) : Id _) = _
      rw [stagesOf_port]
      rfl

/-! ## The calls on one file, and the chains' parameter bytes -/

/-- A call on one file alone, at two runs of the stage that are related. -/
theorem partCall_port (o : Options) (f : Files) (part : StageName)
    (run : Common → Read → ExceptT Refused Id Found) (run' : Common → Read → Except Refused Found)
    (h : ∀ C r, RelX (run C r) (run' C r)) :
    M.Model.Verify.partCall (m := Id) formatHashFastForm o f part run =
      OnBytes.Model.Verify.partCall o f part run' := by
  unfold M.Model.Verify.partCall OnBytes.Model.Verify.partCall
  split
  · rfl
  · cases readFirst o f false with
    | error e => rfl
    | ok r =>
      have e : (M.Model.Verify.commonOfCall (m := Id) formatHashFastForm r).run =
          OnBytes.Model.Verify.commonOfCall r := commonOfCall_port r
      dsimp only
      rw [e]
      cases OnBytes.Model.Verify.commonOfCall r with
      | error x => rfl
      | ok C =>
        have k : (run C r).run = run' C r := h C r
        show (do
          let out : StageOut ← (do
            let x ← (run C r).run
            pure (C.oneTimeOut part x) : Id StageOut)
          pure (cpStagesRun [out] (some part) (askedBelowBar o.bits) o.bits r.id none) : Id _) = _
        rw [k]
        rfl

/-- The call on a key file alone. -/
theorem keyCall_port (o : Options) (f : Files) :
    M.Model.Verify.keyCall (m := Id) formatHashFastForm o f = OnBytes.Model.Verify.keyCall o f :=
  partCall_port o f .key _ _ fun C r => keyStage_port C o.bits r.key

/-- The call on an entry file alone. -/
theorem leafCall_port (o : Options) (f : Files) :
    M.Model.Verify.leafCall (m := Id) formatHashFastForm o f = OnBytes.Model.Verify.leafCall o f := by
  unfold M.Model.Verify.leafCall OnBytes.Model.Verify.leafCall
  cases readFirst o f false <;> cases f.entry <;>
    first
      | rfl
      | exact partCall_port o f .leaf _ _ fun C _ => leafStage_port C o.bits _

/-- The parameter bytes of the seven chains. -/
theorem planBytes_port (bits : Nat) (policy KL : FileIn) (layout : Option FileIn) :
    RelX (M.Model.Verify.planBytes (m := Id) formatHashFastForm bits policy KL layout)
      (OnBytes.Model.Verify.planBytes bits policy KL layout) := by
  unfold M.Model.Verify.planBytes OnBytes.Model.Verify.planBytes
  refine relX_bind (relX_liftE _) fun x => ?_
  obtain ⟨pol, KL', layout'⟩ := x
  refine relX_bind ?_ fun p => ?_
  · have e : (M.Model.Verify.planned (m := Id) formatHashFastForm pol KL' layout').run =
        OnBytes.Model.Verify.planned pol KL' layout' := planned_port _ _ _
    show callNamed (M.Model.Verify.planned (m := Id) formatHashFastForm pol KL' layout').run = _
    rw [e]
  refine relX_bind (relX_liftE _) fun _ => ?_
  exact relX_pure _

end OnBytes.TwoPort.M.AtPort
