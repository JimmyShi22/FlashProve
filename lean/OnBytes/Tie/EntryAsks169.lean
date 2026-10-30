-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryAsks169.lean: which strings of calls under the number 169 the asking half of the
entry's typing asks (`askedE`, `typedE`, `typedER`, OnBytes/Tie/EntryAsked.lean): no string but
that of the call that hashes the parameter bytes of the link's chain.

The asking half is the twin of `Entry.read`, asking, and then both tables' seeds. Its calls of the
hash have the numbers 160, 162, 164, 166, 172 and 174, but for the call under 169 at the parameter
bytes (OnBytes/ChecksWithHashAsArgument/M/Entry/RoadKeepsAt.lean). A call's string holds its number
(`oStr_number`, OnBytes/Tie/DigestPoint.lean).

Main names:
  `Only169 p s`: if s is the string of a call under 169, it is the string of the call that hashes p.
  `not169`: the string of a call under another number is no string of a call under 169.
  `keepsOnly p`: "every string that is asked has `Only169 p`", as a property that pure and bind
    keep.
  `askedE_only`, `typedE_only`, `typedER_only`: the three algorithms have it, at `q.given.bytes`.
  `typedER_onlyAtTypedOracleCompiler`: the last with `IsCall169` of OnBytes/TypedOracleCompiler/Run/PageXJoin.lean.

Limits: on every path, whatever the oracle answers. Nothing on how often that string is asked, on
the other strings, or on values. Nothing on the readings of a key file or a proof file. Nothing on
soundness. For proofs only; no program imports this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAsked
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadKeepsAt
import OnBytes.Slice.WalkOff
import OnBytes.TypedOracleCompiler.Run.PageXJoin
import Rom.AsksIn

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort
open OnBytes.Slice (IsCall169)
open _root_.Run (bytesToBits bytesToBits_inj)

/-- If s is the string of a call under 169, it is the string of the call that hashes p. -/
def Only169 (p : ByteArray) (s : List Bool) : Prop :=
  IsCall169 s → s = bytesToBits (digestStr p)

/-- The string of a call whose number is not 169 modulo 65536 is no string of a call under 169. -/
theorem not169 (half : UInt8) (n t i : ℕ) (st bs : ByteArray) (hn : n % 65536 ≠ 169) :
    ¬ IsCall169 (bytesToBits (Fmt.oStr half n t i st bs)) := by
  rintro ⟨half', t', i', st', bs', -, -, e⟩
  have e' : Fmt.oStr half n t i st bs = Fmt.oStr half' 169 t' i' st' bs' := bytesToBits_inj e
  have h1 := oStr_number half n t i st bs
  have h2 := oStr_number half' 169 t' i' st' bs'
  rw [e', h2] at h1
  exact hn (by omega)

/-- "Every string that is asked has `Only169 p`": pure has the property, and bind keeps it. -/
def keepsOnly (p : ByteArray) : M.Keeps (ZKCP.OComp 256) where
  ok := fun x => (Rom.toRom x).AsksIn fun _ s => Only169 p s
  ok_pure := fun _ => trivial
  ok_bind := fun x g hx hg => by
    show (Rom.toRom (x.bind g)).AsksIn _
    rw [Rom.toRom_bind]
    exact Rom.OComp.AsksIn.bind hg hx

/-- One question has the property if its string has. -/
theorem ok_askB (p s : ByteArray) (h : Only169 p (bytesToBits s)) :
    (keepsOnly p).ok (Run.askB s) :=
  ⟨h, fun _ => trivial⟩

/-- A call of the asking hash under a number other than 169 has the property. -/
theorem ok_HM (p : ByteArray) (n t i : ℕ) (st bs : ByteArray) (hn : n % 65536 ≠ 169) :
    (keepsOnly p).ok (Fmt.HM Run.askB n t i st bs) := by
  unfold Fmt.HM
  split
  · exact (keepsOnly p).ok_bind _ _ (ok_askB p _ fun h => absurd h (not169 _ _ _ _ _ _ hn)) fun _ =>
      (keepsOnly p).ok_bind _ _ (ok_askB p _ fun h => absurd h (not169 _ _ _ _ _ _ hn)) fun _ =>
        (keepsOnly p).ok_pure _
  · exact ok_askB p _ fun h => absurd h (not169 _ _ _ _ _ _ hn)

/-- The call that hashes p has the property. -/
theorem ok_HM_digest (p : ByteArray) :
    (keepsOnly p).ok (Fmt.HM Run.askB 169 0 1 Fmt.zero32 p) := by
  unfold Fmt.HM
  rw [if_neg (by decide)]
  exact ok_askB p _ fun _ => rfl

/-- The seeds of a table's record, asked, have the property. -/
theorem ok_seedsBy (p : ByteArray) (fl : Fmt.Fld) (name : ByteArray) (bits count : Nat) :
    (keepsOnly p).ok (seedsBy Run.askB fl name bits count) := by
  unfold seedsBy Slice.recordSeedsW
  refine (keepsOnly p).ok_bind _ _
    (ok_HM p 160 0 Fmt.recordLabel Fmt.zero32 _ (by decide)) fun _ => ?_
  exact (keepsOnly p).ok_bind _ _
    (M.EngineKeepsAt.ok_queryW (keepsOnly p) _ (ok_HM p) _ _ _ _ _ _) fun _ =>
      (keepsOnly p).ok_pure _

/-- The asking half asks no string of a call under 169 but that of its parameter bytes. -/
theorem askedE_only (q : Params.Link) (first : Params.TableName) (ent : ByteArray) :
    (keepsOnly q.given.bytes).ok (askedE q first ent) := by
  unfold askedE
  refine (keepsOnly _).ok_bind _ _
    (M.RoadKeepsAt.ok_read (keepsOnly _) _ (ok_HM _) q first ent (ok_HM_digest _)) fun r => ?_
  cases r with
  | error e => exact (keepsOnly _).ok_pure _
  | ok r =>
    refine (keepsOnly _).ok_bind _ _ (ok_seedsBy _ _ _ _ _) fun l0 => ?_
    refine (keepsOnly _).ok_bind _ _ (ok_seedsBy _ _ _ _ _) fun l1 => ?_
    exact (keepsOnly _).ok_pure _

/-- The same for the asking half with a plain map behind it. -/
theorem typedE_only {Out : Type} (asm : AskedE → Option Out) (q : Params.Link)
    (first : Params.TableName) (ent : ByteArray) :
    (keepsOnly q.given.bytes).ok (typedE asm q first ent) :=
  (keepsOnly _).ok_bind _ _ (askedE_only q first ent) fun _ => (keepsOnly _).ok_pure _

/-- The same over `Rom.rom 256`: every string of a call under 169 that `typedER` asks, on any path,
is the string of the call that hashes the parameter bytes of the link's chain. -/
theorem typedER_only {Out : Type} (asm : AskedE → Option Out) (q : Params.Link)
    (first : Params.TableName) (ent : ByteArray) :
    (typedER asm q first ent).AsksIn fun _ s =>
      IsCall169 s → s = bytesToBits (digestStr q.given.bytes) :=
  typedE_only asm q first ent

/-- The same with the like-named definition of OnBytes/TypedOracleCompiler/Run/PageXJoin.lean, which has the same
text. -/
theorem typedER_onlyAtTypedOracleCompiler {Out : Type} (asm : AskedE → Option Out) (q : Params.Link)
    (first : Params.TableName) (ent : ByteArray) :
    (typedER asm q first ent).AsksIn fun _ s =>
      TypedOracleCompiler.Run.IsCall169 s → s = bytesToBits (digestStr q.given.bytes) :=
  (typedER_only asm q first ent).mono fun _ _ h hs => h hs

end OnBytes.Tie
