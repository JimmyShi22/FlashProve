-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieFront.lean: from the five answers of OnBytes/K/TopVC.lean to the verifier of the
front's argument system, evaluated at one hash function.

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean). "The programs" are the
prover and the verifiers that ship. "The tie" is the step from the program's exit code 0 to the yes
of the verifier of which the soundness theorem speaks. OnBytes/K/Top.lean states it at a served
statement, under named hypotheses, and with that verifier left abstract. "The front" is an argument
system in the sense of VerifiableInference/Statements.lean (`ArgumentSystem`); the soundness theorem
speaks of its verifier. The five answers, the typed strings (Test's, Link's and the session's) and
the served statements are explained in the heads of OnBytes/K/Top.lean and OnBytes/K/TopVC.lean.
"The ID's own written code" is the byte string that the programs hash to get the commitment ID.

The soundness theorem of the front speaks of an argument system's
`verify commitment prompt output proof`, a deterministic algorithm that queries one hash function.
It is made from a scheme over one hash function in two steps. First, the verifier's key goes behind
a digest: a proof brings the key, and the verifier compares the hash of the key's code `enc key`
with the commitment (`ZKCP.Arg.digestKey`). Second, the instance is built from the prompt, the
output tokens and further tokens that the proof brings (`ZKCP.Arg.buildInstance`).
OnBytes/K/TopVC.lean ends at five answers. This file goes on to the front's verifier, for any
scheme: the scheme's verifier is a parameter here, so that no field that is known to be false stands
in a structure.

Main definitions.
- `frontV` [Johnson/Top/FrontGeneral.lean]: the front's verifier, written with the library's own
  terms. It is what `ArgumentSystem.ofArgument` evaluates; the proved form of this is
  `frontV_is_verify` (Johnson/Top/TieOnFiles.lean [not in this library]).
- `CommitIs x c`: the commitment is not left abstract. `c` is the 256 bits of the bytes whose
  hexadecimal form is the ID in the user's options, as the program itself reads an ID
  (`Model.Verify.idAsked`).
- `FrontAt V`: the parameters that a front adds to a shape `V`. They are: the scheme `G` over one
  hash function, with its types of keys and proofs; `enc`, `build`, `bound` and `π₀`; how request
  and reply are read as prompt, output and further tokens (`prompt`, `output`, `aux`); how a key is
  made of the first table and its record alone (`keyOf`); and how a proof is made of Test's string,
  the further table with its record and Link's string, and the session's string (`prfOf`). `prompt`,
  `output` and `aux` are still parameters: they are to be the program's own reading of the request's
  and the reply's words. With empty lists the front's claim would be empty.
- `FrontHoles`: three named hypotheses. `runs`: the scheme's verifier, run at Lean's BLAKE2b, says
  yes where the five answers are yes. At a verifier that is the conjunction of its five parts over a
  coding `m` of the typed oracles in one hash function this is a theorem: `VC_det`
  (Johnson/Top/TieVC.lean) with `Rom.det_overOne`. `built`: the instance that the shape reads from
  request and reply (`insOf`) is the one that the front builds. `idHash`: the key made of a table
  and its record has a code, and the hash of that code, at Lean's BLAKE2b, is that table's
  commitment ID. The `enc` that is meant is the ID's own written code; that a given `enc` is that
  string is not said here.

Main theorems.
- `evaluate_ofRom` [Johnson/Top/FrontGeneral.lean]: the front's evaluation of an algorithm over one
  oracle is its run (`.det`) at that hash function.
- `front_yes` [Johnson/Top/FrontGeneral.lean]: general, and proved. If the instance is built, the
  key has a code, the hash of that code is the commitment, and the scheme's verifier over the one
  hash function says yes, then the front's verifier says yes.
- `commitIs_of_idIs`: where the ID is a table's (`IdIs`, which is proved of the first table), the
  commitment that it names is that table's commitment ID.
- `exit_front`: the exit code 0 (`YES` or `WITHIN LIMITS`) gives, at a served statement, that the
  front's verifier says yes, at the commitment that the user's ID names, at the prompt and output
  read from the user's request and reply (as `Fr.prompt` and `Fr.output` read them: still
  parameters), and at the key and proof read from the three files, evaluated at Lean's BLAKE2b
  (`Run.oBits`). This holds under the five named hypotheses of OnBytes/K/TopVC.lean and these three.

Why the key is a table and its record alone. The programs' ID binds the public files' digest, the
first table's name and its answers (by `Key.commitmentId`, OnBytes/Key/Table.lean, its string holds
the record's seed too, which is drawn from that name), and nothing of Test's string or of a link. If
a key held these too, `idHash` would ask one digest of many keys' codes. With the ID's own written
code, `enc` would then not be one to one, which the front's soundness asks of it; with a code that
is one to one, `idHash` would ask for collisions. With the key cut to root and record, Test's string
and the link travel in the proof, and `enc` can be the ID's own written bytes; `idHash` then says
how `Key.commitmentId` is defined, and, since by the format's rule (`Fmt.publishedBytes`,
Fmt/Rules4.lean) the ID's string takes the record's seed, that the seed of the record (`V.recOf`),
as `enc` spells it, is the one that `Key.seedsOf` draws at the table's name. The bytes without the
record's seed (`idBytes`, OnBytes/Tie/IdKey.lean) hold the root and the answers and not the record's
seed, so on keys (root, record) they are one to one only up to the seed: what the front's soundness
asks of `enc` in that case is the front's own hypothesis on the commitment, not this file's. An
`enc` that writes them does not write the string that `Key.commitmentId` hashes, whose closing list
is empty: no bit string is a code of both kinds (`idCode_ne`, Johnson/TypedOracleCompiler/Top/IdStringsApart.lean),
so `idHash` at such an `enc` can hold only where Lean's BLAKE2b gives one answer at two different
strings. That the bytes with the seed are one to one on keys (root, record) is not said here either:
there too what the front's soundness asks of `enc` is the front's own hypothesis. Of one written
code it is proved elsewhere: `encId_oneToOne` (Johnson/TypedOracleCompiler/Top/IdSeedAt.lean), on keys (c, (root,
record)) of that file's object, with the closing list empty. It is free where no key has a code
(`encId_hasCode`, Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean, gives codes under a condition on the shape).
Here `enc` stays a letter: nothing in this file lays that code in its place. None of this paragraph
is proved here: `idHash` stays a named hypothesis.

What is not claimed. What the heads of OnBytes/K/Top.lean and OnBytes/K/TopVC.lean do not claim is
not claimed here. A named hypothesis may be false, and not only unproved. Whether index binding
holds for a scheme whose prover chooses Test's string and the link after the commitment is a matter
for the front; nothing is said of it here. For proofs only; the program does not import this file.

-/
import OnBytes.K.TopVC
import Run.DetOverOne
import Run.OracleBits
import ZKCP.SpecialAny
import ZKCP.DigestKey
import ZKCP.BuildInstance
import ZKCP.CoinsFirstArg
import VerifiableInference.Deterministic
import Johnson.Top.FrontGeneral

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Iop Rom
open _root_.Run (bytesToDig oBits)
open VerifiableInference (Token Hash deterministicOf)

/-- The commitment that the user's ID names: the 256 bits of the bytes whose hexadecimal form is the
ID in the options, as the program reads an ID. -/
def CommitIs (x : UserStm) (c : ZKCP.Digest 256) : Prop :=
  ∃ id b, x.options.id = some id ∧ Model.Verify.idAsked id = some (Fmt.hex b) ∧ c = bytesToDig b

/-- Where the ID is a table's, the commitment that it names is that table's commitment ID. -/
theorem commitIs_of_idIs (x : UserStm) (t : Params.TableName) (h : IdIs x t) :
    ∃ pl, Model.Verify.planned x.pol x.KL (some x.lay) = .ok pl ∧
      CommitIs x (bytesToDig (Key.commitmentId pl.chains.tableShape pl.cfg t)) := by
  obtain ⟨pl, id, hp, hi, hid⟩ := h
  exact ⟨pl, hp, id, _, hi, hid, rfl⟩

/-- The parameters that a front adds to a shape. -/
structure FrontAt (V : Shape) where
  I : Type
  X : Type
  IVK : Type
  ISK : Type
  Pf : Type
  /-- The scheme over one hash function. -/
  G : ZKCP.Gen.Arg (rom 256) I X Unit IVK ISK Pf
  /-- The code of a key. -/
  enc : IVK → Option ZKCP.Str
  bound : ℕ
  build : List Token × List Token → List Token → Option X
  π₀ : IVK × Pf
  /-- The user's request and reply as a prompt and, in the next two fields, as output tokens and as
  the further tokens that a proof brings. The three are still parameters; with empty lists the
  front's claim would be empty. -/
  prompt : UserStm → List Token
  output : UserStm → List Token
  aux : UserStm → List Token
  /-- The shape's instance as the scheme's. -/
  ins : (x : UserStm) → V.Ins x → X
  /-- A key: the first table and its record alone. -/
  keyOf : (x : UserStm) → Params.TableName → V.Rec x → IVK
  /-- A proof: Test's string; the further table, its record and Link's string; the session's string.
  -/
  prfOf : (x : UserStm) → V.PiT x → Params.TableName → V.Rec x → V.PiL x → V.PiB x → Pf

/-- Three named hypotheses. -/
structure FrontHoles (V : Shape) (Fr : FrontAt V) : Prop where
  /-- Where the five answers are yes, the scheme's verifier, run at Lean's BLAKE2b, says yes. -/
  runs : ∀ x (t u : Params.TableName) (r rj : V.Rec x) (i : V.Ins x) πT πL πB,
    V.seed0 x (bytesToDig t.root) r = true → V.seed1 x (bytesToDig u.root) rj = true →
    V.vT x (bytesToDig t.root) r πT = true →
    V.vL x (bytesToDig t.root) (bytesToDig u.root) r rj πL = true →
    V.vB x (bytesToDig u.root) i rj πB = true →
    (Fr.G.V (Fr.keyOf x t r) (Fr.ins x i) (Fr.prfOf x πT u rj πL πB)).det (fun _ => oBits ()) = true
  /-- At a served statement the instance that the shape reads from request and reply (`insOf`) is
  the one that the front builds. -/
  built : ∀ x i, V.Served x → V.insOf x = some i →
    Fr.build (Fr.prompt x, Fr.output x) (Fr.aux x) = some (Fr.ins x i)
  /-- At a served statement, the key made of a table and its record has a code, and the hash of that
  code, at Lean's BLAKE2b, is the table's commitment ID under the planner's table shape and digest.
  The `enc` that is meant is the ID's own written code (see the head). -/
  idHash : ∀ x t r pl, V.Served x → Model.Verify.planned x.pol x.KL (some x.lay) = .ok pl →
    V.recOf x t = some r →
    ∃ code, Fr.enc (Fr.keyOf x t r) = some code ∧
      oBits () code = bytesToDig (Key.commitmentId pl.chains.tableShape pl.cfg t)

/-- The top statement at the front's verifier: the exit code 0 (`YES` or `WITHIN LIMITS`) gives, at
a served statement, that `frontV`, evaluated at Lean's BLAKE2b, says yes at the commitment that the
user's ID names. The hypotheses are `Holes5` and `FrontHoles`. Prompt, output and further tokens are
those of `Fr`: still parameters. -/
theorem exit_front (V : Shape) (R : Reading5 V) (H : Holes5 V R) (Fr : FrontAt V)
    (HF : FrontHoles V Fr) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      (V.Served (stmOf F a.options) →
        ∃ (table further : Params.TableName) (r rj : V.Rec (stmOf F a.options))
          (πT : V.PiT (stmOf F a.options)) (πL : V.PiL (stmOf F a.options))
          (πB : V.PiB (stmOf F a.options)) (c : ZKCP.Digest 256),
          CommitIs (stmOf F a.options) c ∧ IdIs (stmOf F a.options) table ∧
          V.recOf (stmOf F a.options) table = some r ∧
          V.recOf (stmOf F a.options) further = some rj ∧
          R.key (stmOf F a.options) F.key = some (table, πT) ∧
          R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
          R.prf (stmOf F a.options) F.ent F.proof F.entry = some πB ∧
          (frontV Fr.G Fr.enc Fr.bound Fr.build Fr.π₀ c
            (Fr.prompt (stmOf F a.options)) (Fr.output (stmOf F a.options))
            (Fr.aux (stmOf F a.options),
              (Fr.keyOf (stmOf F a.options) table r,
                Fr.prfOf (stmOf F a.options) πT further rj πL πB))).evaluate (oBits ()) =
            true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, hs⟩ :=
    exit_five V R H h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, fun hS => ?_⟩
  obtain ⟨table, further, r, rj, i, πT, πL, πB, hid, hr, hrj, hx, hk, he, hq, s0, s1, vt, vl, vb⟩ :=
    hs hS
  obtain ⟨pl, hpl, hci⟩ := commitIs_of_idIs _ table hid
  obtain ⟨code, hc, hd⟩ := HF.idHash _ table r pl hS hpl hr
  exact ⟨table, further, r, rj, πT, πL, πB, _, hci, hid, hr, hrj, hk, he, hq,
    front_yes Fr.G Fr.enc Fr.bound Fr.build Fr.π₀ (oBits ()) _ _ _ _ _ _ (Fr.ins _ i) code
      (HF.built _ i hS hx) hc hd (HF.runs _ table further r rj i πT πL πB s0 s1 vt vl vb)⟩

end OnBytes.K

#print axioms OnBytes.K.exit_front
