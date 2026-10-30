-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/KeyLink/KeyCountOne.lean: ONE number bounds the questions of the key file's reading through
the oracle (`preT`, OnBytes/Tie/Decl/KeyPre.lean) at every public digest and every file.

A bound that takes a reading in front of the arms asks one number c at every d and all files.
`preT_asks` (KeyPre.lean) has a number at one d and one file, under three premises.
`readKey_asks1` (OnBytes/TieK/CountsAsks.lean) pays the three: its number is a function of the
chains' parameters and, by its text, of the table. Here: that number reads neither the table nor
the digests and parameter bytes in the parameters (OnBytes/Maker/AtCfg/Lay.lean's `lay`); so if the
parameters at all digests are wiped to one value, it is one number.

Main names:
  `keyCount ks t`: `readKey_asks1`'s number.
  `keyCount_table`, `keyCount_lay`: it is the same at every table, and at the parameters with any
    digests and parameter bytes laid. By `rfl`.
  `typedKR_asks1`: the reading asks at most `keyCount k t` strings. No premise.
  `headAt_ks`: what the plain steps return holds the parameters that `ksAt` has returned.
  `preT_asks_one`: if every answer of `ksAt` at a d's digest is wiped to the value to which K₀ is
    wiped, then at every d and every file `preT` asks at most `keyCount K₀ t₀` strings; t₀ any
    table.

Limits: THE PREMISE ON `ksAt` IS NOT SHOWN HERE: that the planner's plain steps at two digests give
parameters that differ in digests and parameter bytes alone. The number is not evaluated. Nothing on
which strings are asked. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.Decl.KeyPre
import OnBytes.TieK.CountsAsks
import OnBytes.Maker.AtCfg.Lay

set_option autoImplicit false

namespace OnBytes.KeyLink

open OnBytes.Tie OnBytes.TieK.Counts OnBytes.TwoPort.M.Asks
open OnBytes.Params (KeyChains TableName Lay3)
open OnBytes.Proof (TailRead)
open _root_.Iop (Dig)
open _root_.Run (digToBytes)

/-- The number of `readKey_asks1`. -/
def keyCount (ks : KeyChains) (t : TableName) : Nat :=
  (2 * dryN (Key.oneTime ks.oneTime) (Key.startOf ks.oneTime) +
    tailN (Key.tailPublic ks t) (sharedN (Key.tailPublic ks t))
      (secondN (Key.tailPublic ks t) (Key.oneTime ks.oneTime) (Key.startOf ks.oneTime))) * 2

/-- It does not read the table. -/
theorem keyCount_table (ks : KeyChains) (t t' : TableName) : keyCount ks t = keyCount ks t' := rfl

/-- It reads neither a digest nor parameter bytes. -/
theorem keyCount_lay (ks : KeyChains) (x : Lay3) (t : TableName) :
    keyCount (ks.lay x) t = keyCount ks t := rfl

/-- **The reading asks at most that many strings.** NO PREMISE. -/
theorem typedKR_asks1 {Out : Type} (asm : TailRead → Option Out) (k : KeyChains) (t : TableName)
    (file : ByteArray) (j : Nat) : (typedKR asm k t file j).QueryBound (keyCount k t) := by
  have b : (typedKR asm k t file j).QueryBound (keyCount k t + 0) :=
    Rom.OComp.QueryBound.bind
      ((Rom.queryBound_toRom _ _).2 (readKey_asks1 k t file j Session.start).2) fun _ => trivial
  exact b

variable {D Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt]
  (tab : D → KeyChains → List Bool → Dig 256) (cfgOf : D → Dig 256)
  (ksAt : ByteArray → Option KeyChains)
  (asm : KeyChains → ByteArray → TableName → TailRead → Option Out)

/-- What the plain steps return holds the parameters that `ksAt` has returned. -/
theorem headAt_ks {c keyFile : ByteArray} {a : KeyChains × TableName × Nat}
    (h : headAt ksAt c keyFile = some a) : ksAt c = some a.1 := by
  unfold headAt at h
  cases hk : ksAt c with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    dsimp only at h
    cases hx : Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg keyFile with
    | error e => rw [hx] at h; cases h
    | ok x =>
      rw [hx] at h
      cases h
      rfl

/-- **One number at every digest and every file.** -/
theorem preT_asks_one (K₀ : KeyChains) (t₀ : TableName)
    (hw : ∀ d k, ksAt (digToBytes (cfgOf d)) = some k → k.wipe = K₀.wipe) (d : D)
    (keyFile : ByteArray) :
    (preT Pt tab cfgOf ksAt asm d keyFile).QueryBound (keyCount K₀ t₀) := by
  unfold preT
  cases h : headAt ksAt (digToBytes (cfgOf d)) keyFile with
  | none => trivial
  | some a =>
    have e : keyCount a.1 a.2.1 = keyCount K₀ t₀ := by
      have e1 : keyCount a.1.wipe t₀ = keyCount K₀.wipe t₀ := by
        rw [hw _ _ (headAt_ks ksAt h)]
      exact e1
    show (pinP _ _ _).QueryBound _
    rw [← e]
    exact queryBound_pinP _ _ _ _ (typedKR_asks1 _ _ _ _ _)

end OnBytes.KeyLink
