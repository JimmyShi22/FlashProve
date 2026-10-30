-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/SeedPort.lean: where the program `verify-on-bytes` says yes on a whole call: the two
tables' records, as functions of the user's statement and the tables. For proofs only; the program
does not import this file.

`PortYesAt` (OnBytes/K/Top.lean) is what the exit code 0 says of the bytes, at the two tables that
the program threads from file to file. It holds that the chains of the call have one digest and one
shape of the stored tables (`Tie.SameChains`). So OnBytes/K/SeedRec.lean's `checks_block` applies.

Main names.
 `port_block`   from `PortYesAt`: the planner's value p, the two checks' yes and `Tie.SameChains`.
 `planZ`, `fieldZ`, `cfgZ`, `shapeZ`   what the planner makes of three public files: the link's
                field, the digest of the public files, the tables' shape. `planAt`, `fieldAt`,
                `cfgAt`, `shapeAt`: the same at the three public files of a user's statement.
 `pubOf_served`  a statement that passes `servedAt Z` (OnBytes/K/Served.lean) has Z's three files.
 `recAt x t`    the record of the table t under them (`plainRec`).
 `restOf sh cfg`, `nameOf_rest`   a table's name is its root, then bytes that do not hang on the
                table.
 `port_recs`    from `PortYesAt`: both roots have 32 bytes, and both tables' records fit the shape.

`restOf sh cfg` spells the bytes that OnBytes/TypedOracleCompiler/Run/FirstName.lean calls
`FirstName.restOf cfg sh.code.logN sh.code.ell sh.code.r sh.v sh.answers sh.saltBytes`: the two
texts are one term; whoever imports both can say so by rfl (Johnson/Top/TieSeedArm.lean does, in
`rest_small`).

What is not claimed. Nothing on how seeds are distributed; nothing on soundness.


-/
import OnBytes.K.Top
import OnBytes.K.SeedRec

set_option autoImplicit false

namespace OnBytes.K

/-- **Where the program says yes on a whole call**: the planner's value; the checks of the key file
and of the entry file said yes under its chains; these have one digest, that of the three public
files, and one shape of the tables. -/
theorem port_block (F : Files) (id : String) (table further : Params.TableName)
    (h : PortYesAt F id table further) :
    ∃ p : Model.Verify.Planned, Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.check p.chains.key F.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table F.ent = .ok further ∧
      Tie.SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]) := by
  obtain ⟨r, p, C, -, -, -, -, -, -, -, -, -, -, hp, -, -, hk, he, -, -, hsame, -⟩ := h
  exact ⟨p, hp, hk, he, hsame⟩

/-- What the planner makes of three public files, if it makes anything. -/
def planZ (Z : Pub) : Option Model.Verify.Planned :=
  (Model.Verify.planned Z.pol Z.KL (some Z.lay)).toOption

/-- The field of the link's chain. -/
def fieldZ (Z : Pub) : Fmt.Fld :=
  match planZ Z with
  | some p => p.chains.link.given.plan.field
  | none => .two

/-- The digest of the public files. -/
def cfgZ (Z : Pub) : ByteArray :=
  match planZ Z with
  | some p => p.cfg
  | none => ByteArray.empty

/-- The shape of the stored tables. -/
def shapeZ (Z : Pub) : Params.IndexShape :=
  match planZ Z with
  | some p => p.chains.tableShape
  | none => ⟨⟨0, 0, 0⟩, 0, 0, 0⟩

/-- The three public files of a user's statement. -/
def pubOf (x : UserStm) : Pub := ⟨x.pol, x.lay, x.KL⟩

/-- What the planner makes of a user's statement. -/
def planAt (x : UserStm) : Option Model.Verify.Planned := planZ (pubOf x)

/-- The field of the link's chain, at a user's statement. -/
def fieldAt (x : UserStm) : Fmt.Fld := fieldZ (pubOf x)

/-- The digest of the public files, at a user's statement. -/
def cfgAt (x : UserStm) : ByteArray := cfgZ (pubOf x)

/-- The shape of the stored tables, at a user's statement. -/
def shapeAt (x : UserStm) : Params.IndexShape := shapeZ (pubOf x)

/-- **A statement that is served at Z has Z's three public files**: so the planner's field, digest
and shape at it are those at Z. -/
theorem pubOf_served (Z : Pub) (x : UserStm) (h : servedAt Z x = true) : pubOf x = Z := by
  obtain ⟨h1, h2, h3, -⟩ := (servedAt_pins Z x).1 h
  unfold pubOf
  rw [h1, h2, h3]

/-- The record of a table, under what the planner makes of the user's statement. -/
def recAt (x : UserStm) (t : Params.TableName) : PlainRec :=
  plainRec (fieldAt x) (cfgAt x) (shapeAt x) t

/-- What stands behind the root in a table's name: the digest of the public files and six words of
the tables' shape. -/
def restOf (sh : Params.IndexShape) (cfg : ByteArray) : ByteArray :=
  cfg ++ Fmt.u64n sh.code.logN ++ Fmt.u64n sh.code.ell ++ Fmt.u64n sh.code.r ++ Fmt.u64n sh.v ++
    Fmt.u64n sh.answers ++ Fmt.u64n sh.saltBytes

/-- A table's name is its root, then these bytes. -/
theorem nameOf_rest (sh : Params.IndexShape) (cfg : ByteArray) (t : Params.TableName) :
    Key.nameOf sh cfg t = t.root ++ restOf sh cfg := by
  unfold Key.nameOf Fmt.tableName restOf
  simp only [ByteArray.append_assoc]

/-- **Where the program says yes on a whole call**: the planner's value is the one behind
`fieldAt`, `cfgAt` and `shapeAt` at the user's statement; both roots have 32 bytes; both tables'
records fit the shape. -/
theorem port_recs (F : Files) (o : Model.Verify.Options) (id : String)
    (table further : Params.TableName) (h : PortYesAt F id table further) :
    ∃ p : Model.Verify.Planned, planAt (stmOf F o) = some p ∧
      Key.check p.chains.key F.key = .ok table ∧
      Entry.check (p.chains.bytes .link) table F.ent = .ok further ∧
      Tie.SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]) ∧
      table.root.size = 32 ∧ further.root.size = 32 ∧
      (recAt (stmOf F o) table).Fits (shapeAt (stmOf F o)) ∧
      (recAt (stmOf F o) further).Fits (shapeAt (stmOf F o)) := by
  obtain ⟨p, hp, hk, he, hsame⟩ := port_block F id table further h
  have hpl : planAt (stmOf F o) = some p := by
    show (Model.Verify.planned F.pol F.KL (some F.lay)).toOption = some p
    rw [hp]
    rfl
  obtain ⟨h0, h1, -, f0, f1, -⟩ := checks_block p _ F.key F.ent table further hk he hsame
  refine ⟨p, hpl, hk, he, hsame, h0, h1, ?_, ?_⟩
  · unfold recAt fieldAt cfgAt shapeAt fieldZ cfgZ shapeZ
    rw [show planZ (pubOf (stmOf F o)) = some p from hpl]
    exact f0
  · unfold recAt fieldAt cfgAt shapeAt fieldZ cfgZ shapeZ
    rw [show planZ (pubOf (stmOf F o)) = some p from hpl]
    exact f1

end OnBytes.K
