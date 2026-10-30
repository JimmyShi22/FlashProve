-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Prog.lean: a verifier of proof files as a function of two byte strings alone, the parameters'
bytes of the chain and a proof file, for the first toy (a product test).

The first toy is a test protocol for the claim that three rows a, b, c of one oracle message have
a_i b_i = c_i for every i (the heads of Fmt/M1Types.lean and Fmt/M1Psc.lean). The verifier's
challenges are drawn from a hash chain, and the parameters' bytes are hashed into the chain's first
value (`readChain`, Fmt/Rules8.lean). Nothing has to be written anew for a new set of files. Total
functions on bytes, with tests (#guard); two statements (`Fmt.M1.Spec.whoFromF_eq`,
`Fmt.M1.Spec.trailFromF_eq`) with proofs. No Mathlib.

Fmt/ParamsRead.lean cuts the parameters' bytes; Fmt/M1ParOf.lean reads the sizes off them;
Fmt/M1Plan.lean makes the description from the sizes; Fmt/Rules8.lean reads a file at a description;
Fmt/M1View.lean hands the view on; Fmt/M1All.lean decides. Here they are applied one after the
other.

Main names:
  `specFrom params : Option (Par × Spec)`: the sizes, and the description at the given bytes: plan,
    configuration's digest, further items and the nonce's bytes are those that were read. Refused:
    bytes that are not read; sizes that cannot be read off them; a plan that is not the plan of
    these sizes; a description whose parameters' bytes are not the given bytes; a description that
    fails its own conditions (`Spec.ok`).
  `whoFrom params file`: the outcome on a file.
  Trail, **trailFrom params file** what this library's side computes on the way, for a comparison
  with what
    another program prints:
      the parameters' digest, the run's value, the chain's first value;
      for every round: nonce, drawn elements, drawn positions, the chain's value behind it.
    `trailFrom` gives nothing (`none`) if the parameters are refused or if the reader refuses.
  `cfgFits params files`: the configuration's digest in the parameters is the digest of these public
    files (R4.9).
  `whoFromF`, `trailFromF`: the same by the fast reader (`wholeChainF`, Fmt/Rules8Fast.lean), for
    files of the toy's full sizes.
  `Spec.whoFromF_eq`, `Spec.trailFromF_eq`: `whoFromF` and `trailFromF` are equal to `whoFrom` and
    `trailFrom`, for all bytes. Both are proved here, from the theorem that the fast reader is the
    reader (`wholeChainF_eq`, Fmt/Rules8Fast.lean).

Tests (#guard), at the files of this library's own Python reference program at both of its small
sizes, taken as if they were a stranger's. From the parameters' bytes alone the sizes come out as
those that were written down; of the description the label, the parameters' bytes, the
configuration's digest and the number of rounds are tested at the first size, the number of rounds
at the second. `whoFrom` gives on all files of both lists (`Files.files`, `FilesB.files`) what the
table says, by stage alone (reader or decision: `Tiny.wants`, `Tiny.wantsB`, Fmt/M1Tiny.lean), not
by the part that the table names. On the first size's honest file the trail's three values and its
last value are the reader's, and the trail has 22 rounds. At both sizes the configuration fits its
public file; at the first it fits neither the other size's public file nor the empty list.

Limits: no theorem but the two on the fast forms. At a stranger's bytes `specFrom` may refuse
because an item is spelled otherwise than the format page's twelfth section rules: `Fmt.M1.check`
says which part fails.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1ParOf
import Fmt.M1Tiny
import Fmt.M1Targets
import Fmt.Rules8Fast

namespace Fmt
namespace M1

/-- The sizes and the description, from the parameters' bytes. What is refused: see the head. -/
def specFrom (params : ByteArray) : Option (Par × Spec) :=
  (paramsRead params).bind fun p => (parOf p).bind fun P =>
    let S := specOf P p.cfg p.others p.plan.nonce
    if fitsPlan p P && decide (S.params = params) && S.ok then some (P, S) else none

/-- The outcome on a file: the reader refuses, the decision refuses, or "accepted"; nothing if the
parameters are refused. -/
def whoFrom (params file : ByteArray) : Option Tiny.Who :=
  (specFrom params).map fun x => Tiny.who x.2 x.1 file

/-- The chain's value after each round, computed again from what was read. -/
def rhosOf (S : Spec) (o : ChainOut) : List String :=
  ((o.rounds.toList.zip S.rounds).foldl (fun (s : ByteArray × Nat × List String) x =>
    let r := nextRho S.label s.1 (s.2.1 + 1) x.1.msg x.2.kind x.2.entry.work x.1.nonce
    (r, s.2.1 + 1, s.2.2 ++ [hex r])) (o.rho0, 0, [])).2.2

/-- What Lean computes on the way: see `trailFrom` in the head. -/
structure Trail where
  pd     : String
  run    : Option String
  rho0   : String
  rounds : List (Nat × List Ext × List Nat × String)
  deriving Repr

def trailFrom (params file : ByteArray) : Option Trail :=
  (specFrom params).bind fun x => (wholeChain (m := Id) formatHash x.2 file).map fun o =>
    ⟨hex o.pd, o.run.map hex, hex o.rho0,
      (o.rounds.toList.zip (rhosOf x.2 o)).map fun y =>
        (y.1.nonce, y.1.drawn.elems, y.1.drawn.poss, y.2)⟩

/-- the configuration's digest in the parameters is the digest of these public files -/
def cfgFits (params : ByteArray) (files : List ByteArray) : Bool :=
  (paramsRead params).any fun p => p.cfg = configDigest files

/-! ## By the fast reader -/

def whoFromF (params file : ByteArray) : Option Tiny.Who :=
  (specFrom params).map fun x =>
    match wholeChainF x.2 file with
    | none => .reader
    | some o => if dec x.1 (viewOf x.2.firstTree o) then .accepted else .decision

def trailFromF (params file : ByteArray) : Option Trail :=
  (specFrom params).bind fun x => (wholeChainF x.2 file).map fun o =>
    ⟨hex o.pd, o.run.map hex, hex o.rho0,
      (o.rounds.toList.zip (rhosOf x.2 o)).map fun y =>
        (y.1.nonce, y.1.drawn.elems, y.1.drawn.poss, y.2)⟩

/-- The values that `targets` (Fmt/M1Targets.lean) computes, from a file's bytes. -/
def valuesFromF (params file : ByteArray) : Option (List E) :=
  (specFrom params).bind fun x =>
    (wholeChainF x.2 file).bind fun o => targets x.1 (ofView (viewOf x.2.firstTree o))

namespace Spec

def whoFromF_eq : Prop := ∀ params file : ByteArray, whoFromF params file = whoFrom params file
def trailFromF_eq : Prop :=
  ∀ params file : ByteArray, trailFromF params file = trailFrom params file

end Spec

theorem whoFromF_eq : Spec.whoFromF_eq := by
  intro params file
  have h : ∀ (S : _root_.Fmt.Spec) (b : ByteArray), wholeChainF S b = wholeChain (m := Id) formatHash S b :=
    _root_.Fmt.wholeChainF_eq
  unfold whoFromF whoFrom Tiny.who
  simp only [h]
  congr 1

theorem trailFromF_eq : Spec.trailFromF_eq := by
  intro params file
  have h : ∀ (S : _root_.Fmt.Spec) (b : ByteArray), wholeChainF S b = wholeChain (m := Id) formatHash S b :=
    _root_.Fmt.wholeChainF_eq
  unfold trailFromF trailFrom
  simp only [h]

-- From the parameters' bytes alone: the sizes; the description's parts.
#guard (specFrom Known.spec.params).any fun x => samePar x.1 tinyPar && x.2.label == 1 && decide (x.2.params = Known.spec.params) && decide (x.2.cfg = Known.cfg) && x.2.rounds.length == 22
#guard (specFrom KnownB.spec.params).any fun x => samePar x.1 KnownB.par && x.2.rounds.length == 21
-- The outcome on all files of both lists (`files`: the re-cut ones are not among them), against the
-- table, by stage (reader or decision) alone.
#guard Files.files.all fun x => whoFrom Known.spec.params x.2.1 == some (Tiny.wants x.2.2)
#guard FilesB.files.all fun x => whoFrom KnownB.spec.params x.2.1 == some (Tiny.wantsB x.2.2)
-- the trail is the reader's own
#guard ((trailFrom Known.spec.params Files.honest).map fun t => (t.pd, t.run, t.rho0, t.rounds.length)) = (Known.read Files.honest).map fun o => (hex o.pd, o.run.map hex, hex o.rho0, 22)
#guard ((trailFrom Known.spec.params Files.honest).bind fun t => t.rounds.getLast?.map (·.2.2.2)) = (Known.read Files.honest).map fun o => hex o.rho
-- the configuration and its public file
#guard cfgFits Known.spec.params [Known.pubFile] && cfgFits KnownB.spec.params [KnownB.pubFile]
#guard cfgFits Known.spec.params [KnownB.pubFile] == false && cfgFits Known.spec.params [] == false
-- Refused: no bytes; one byte less; a plan that is not the plan of its sizes.
#guard (specFrom ByteArray.empty).isNone
#guard (specFrom (Known.spec.params.extract 0 (Known.spec.params.size - 1))).isNone
#guard (specFrom (paramsBytes { planOf tinyPar with entries := (planOf tinyPar).entries.map fun e => if e.name == "BAT" then { e with rows := 5 } else e } Known.cfg (Known.items tinyPar))).isNone

-- the fast forms, run: the honest file; a file for the reader; a file for the decision; nineteen
-- values
#guard whoFromF Known.spec.params Files.honest = some .accepted && whoFromF Known.spec.params Files.alt_04 = some .reader && whoFromF Known.spec.params Files.cheat_01 = some .decision
#guard ((valuesFromF Known.spec.params Files.honest).map (·.length)) = some 19

end M1
end Fmt
