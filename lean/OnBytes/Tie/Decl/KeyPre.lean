-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/KeyPre.lean: the reading of a key file's three chains in front of the arms of the
compiled verifier: from the key file's bytes, at public digests d, to whatever a plain map makes of
what was read (at use: the proof string of the key file's protocol).

The key file's like of OnBytes/Tie/Decl/ProofPre.lean (`preP`), whose laws it has, name for name. A
bound that takes a reading in front of the arms takes it as a letter and asks of it, at
every d and all files: no public string; at most c questions, c one number.

Letters: D with `cfgOf` (the digest of the public files in d); Pt, the public strings, a decidable
property; `ksAt`, from a digest of the public files to the key file's three chains' parameters, or
nothing (at use: the planner's plain steps at a given digest: `plannedAt`,
OnBytes/Tie/ChainsAtCfg.lean; here a letter, so that no planner is imported); `tab`, the table at d
and these parameters by which queries at public strings are answered; asm, the plain map, from the
parameters, the file, the table and what was read.

Main names:
  `preT`: THE TERM. The parameters at d's digest; the program's own parse of the file's head
    (`Key.readTable` at the parameters' own shape and digest, as `Key.check` calls it); then
    `typedKR` (OnBytes/Tie/KeyAsked.lean) with the queries at public strings answered by the table
    (`pinP`, PinPred.lean). A refusal of a plain step returns nothing and asks nothing.
  `preT_off`, `preT_noCoin`: it asks no public string; no coin. NO HYPOTHESIS.
  `preT_det`: its value at every family. `preT_asks`: the twin's number at this d and this file,
    under the three premises of `readKey_asks`. `preT_asks_planned`
    (OnBytes/KeyLink/KeyCountPlanned.lean) has one number at every d and every file.
  `preT_twin`, `preT_program`: at the oracle made from the format's hash, if the table holds that
    oracle's own values at the public strings: where the twin at the hash over the format's oracle
    returns r, it makes asm of r; so under `KeyTwinAtO`, where the program's `Key.readKey` returns
    r.

Limits. The laws hold of every such term, whatever it reads: they have force only beside
`preT_program`. WHAT THE PIN DOES NOT GIVE: that the public strings which the reading asks are the
three strings of the chains' parameter bytes at d's digest: were there another, the table's value
there is fixed before a function is drawn, the reading's chains and the arm's would part, and the
term would say yes all but never. `preT_asks` has its number at one (d, file): that ONE number holds
at every digest wants that `ksAt`'s answers differ in digests and parameter bytes alone.
`KeyTwinAtO` is a premise here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.KeyAsked
import OnBytes.Tie.Decl.PinPred
import OnBytes.Key.Table

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Params (TableName KeyChains)
open OnBytes.Proof (TailRead)
open _root_.Iop (Dig)
open _root_.Run (digToBytes)

variable {D Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt]
  (tab : D → KeyChains → List Bool → Dig 256) (cfgOf : D → Dig 256)
  (ksAt : ByteArray → Option KeyChains)
  (asm : KeyChains → ByteArray → TableName → TailRead → Option Out)

/-- The plain steps: the parameters at a digest, and the program's own parse of the file's head. -/
def headAt (c keyFile : ByteArray) : Option (KeyChains × TableName × Nat) :=
  match ksAt c with
  | none => none
  | some k =>
    match Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg keyFile with
    | .error _ => none
    | .ok x => some (k, x.1, x.2)

/-- **THE TERM.** -/
def preT (d : D) (keyFile : ByteArray) : Rom.OComp (Rom.rom 256) (Option Out) :=
  match headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => .pure none
  | some a => pinP Pt (tab d a.1) (typedKR (asm a.1 keyFile a.2.1) a.1 a.2.1 keyFile a.2.2)

/-- **It asks no public string.** NO HYPOTHESIS. -/
theorem preT_off (d : D) (keyFile : ByteArray) :
    (preT Pt tab cfgOf ksAt asm d keyFile).AsksIn fun _ (s : List Bool) => ¬ Pt s := by
  unfold preT
  cases headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => trivial
  | some a => exact asksIn_pinP _ _ _

/-- It tosses no coin. NO HYPOTHESIS. -/
theorem preT_noCoin (d : D) (keyFile : ByteArray) :
    (preT Pt tab cfgOf ksAt asm d keyFile).NoCoin := by
  unfold preT
  cases headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => trivial
  | some a => exact noCoin_pinP _ _ _ (typedKR_noCoin _ _ _ _ _)

/-- Where a plain step refuses it asks nothing. -/
theorem preT_none (d : D) (keyFile : ByteArray)
    (h : headAt ksAt (digToBytes (cfgOf d)) keyFile = none) :
    preT Pt tab cfgOf ksAt asm d keyFile = .pure none := by
  unfold preT
  rw [h]

/-- Its value at every family. -/
theorem preT_det (g : Rom.Fam (Rom.rom 256)) (d : D) (keyFile : ByteArray) {k : KeyChains}
    {t : TableName} {j : Nat} (h : headAt ksAt (digToBytes (cfgOf d)) keyFile = some (k, t, j)) :
    (preT Pt tab cfgOf ksAt asm d keyFile).det g =
      (askedKAt (Run.oB (overP Pt (tab d k) g ())) k t keyFile j).bind (asm k keyFile t) := by
  unfold preT
  rw [h]
  show (pinP _ _ _).det g = _
  rw [det_pinP, typedKR_det]

open OnBytes.TwoPort.M.Asks in
/-- The twin's number, at this d and this file. -/
theorem preT_asks {N1 N2 N3 : Nat} (d : D) (keyFile : ByteArray) {k : KeyChains} {t : TableName}
    {j : Nat} (h : headAt ksAt (digToBytes (cfgOf d)) keyFile = some (k, t, j))
    (h1 : OneTimeBelow k t N1) (h2 : SharedBelow (OnBytes.Key.tailPublic k t) N2)
    (h3 : ∀ x first, (OnBytes.Key.oneTime k.oneTime).dryRun (OnBytes.Key.startOf k.oneTime) =
      some x → SecondBelow (OnBytes.Key.tailPublic k t) x.2 first N3) :
    (preT Pt tab cfgOf ksAt asm d keyFile).QueryBound
      ((2 * N1 + tailN (OnBytes.Key.tailPublic k t) N2 N3) * 2) := by
  unfold preT
  rw [h]
  exact queryBound_pinP _ _ _ _ (typedKR_asks _ _ _ _ _ h1 h2 h3)

/-- **The tie's half, from the twin.** At the oracle made from the format's hash: the table holds
that oracle's own values at every public string (hT); the twin at the hash over the format's oracle
returns r. -/
theorem preT_twin (d : D) (keyFile : ByteArray) {k : KeyChains} {t : TableName} {j : Nat}
    (h : headAt ksAt (digToBytes (cfgOf d)) keyFile = some (k, t, j))
    (hT : ∀ x, Pt x → tab d k x = Run.oBits () x) (r : TailRead)
    (hr : (TwoPort.M.Key.readKey (m := Id) (Fmt.HO Fmt.oracle) k t keyFile j).fromStart = .ok r) :
    (preT Pt tab cfgOf ksAt asm d keyFile).det Run.oBits = asm k keyFile t r := by
  unfold preT
  rw [h]
  show (pinP _ _ _).det Run.oBits = _
  rw [det_pinP_of_eq _ _ _ hT]
  exact typedKR_twin _ _ _ _ _ r hr

/-- **The tie's half.** The same under the named premise (hO), where the program's own reading
returns r. -/
theorem preT_program (d : D) (keyFile : ByteArray) {k : KeyChains} {t : TableName} {j : Nat}
    (h : headAt ksAt (digToBytes (cfgOf d)) keyFile = some (k, t, j))
    (hT : ∀ x, Pt x → tab d k x = Run.oBits () x) (hO : KeyTwinAtO k t keyFile j) (r : TailRead)
    (hr : (OnBytes.Key.readKey k t keyFile j).fromStart = .ok r) :
    (preT Pt tab cfgOf ksAt asm d keyFile).det Run.oBits = asm k keyFile t r :=
  preT_twin Pt tab cfgOf ksAt asm d keyFile h hT r (hO r hr)

end OnBytes.Tie
