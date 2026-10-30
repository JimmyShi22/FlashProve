-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/TopVC.lean: the top statement of OnBytes/K/Top.lean at a verifier in the form of the
compiled verifier with records, under five named hypotheses; the join is a theorem.

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean).

The compiled verifier with records (`VC`, Johnson/RecCompile/Cms.lean) takes a key, an instance and
a proof. The key is a root, its record, a typed string for the protocol Test, and a list of further
roots, each with its record and a typed string for the protocol Link. The proof is the number of a
further root and a typed string for a session. `VC` asks two seeds' queries, runs three compiled
verifiers, and returns the conjunction of the five answers. The files of a whole call supply these
five. The key file gives the first table's seed, and Test. The entry file gives the further table's
seed, and Link. The proof file gives the session.

Here that form is left abstract (`Shape`). Its parameters are the five answers, as functions to
Bool; the types of records, instances and typed strings, which depend on the user's statement; and
two readings of plain data: a table as the program holds it (root and answers) as a record, and
request and reply as an instance. Each of the five answers is to be the run, at the oracle functions
made from Lean's BLAKE2b, of the verifier's own part.

Main definitions.
- `Shape.target`: the `Target` (OnBytes/K/Top.lean) made from a shape. The key's part returns the
  table if its seed and Test say yes; the entry's part likewise with Link; the proof's part is the
  session.
- `Holes5`: the five named hypotheses `seed0`, `test`, `seed1`, `link` and `session`. Each says:
  where the program says yes, with these tables, at a served statement, the table's record or the
  typed string is read, and this answer is yes.
- `IdIs x t`: the ID in the user's options is, in hexadecimal, the commitment ID of the table `t`
  under the planner's table shape and the public files' digest. This is the program's own test of
  the ID.

Main theorems.
- `Shape.verify_iff`: the verifier of `Shape.target` is the conjunction of the five answers, at the
  records of the two tables and the instance.
- `holes_of_five`: `Holes5` gives `Holes` (OnBytes/K/Top.lean); the join is proved.
- `top5`: under `Holes5`, the exit code 0 (`YES` or `WITHIN LIMITS`) gives, at a served statement,
  the conjunction of the five answers at the fixed reading.
- `idIs_of_port`: `IdIs` is proved of the first table.
- `exit_five`: the same as `top5`, written out: the two tables, `IdIs` of the first, the records,
  the instance, the three typed strings as the fixed reading gives them, and each of the five
  answers.

What is not claimed. All that the head of OnBytes/K/Top.lean does not claim is not claimed here.
What an instance must meet, as that head lists it, holds here too: the five parameters must be the
five parts of one constant of the soundness theorem's statement. A named hypothesis may be false,
and not only unproved: the head of Johnson/Top/TieVC.lean names three of the five that are likely
false at the library's `VC` as it is spelt. A key of `VC` holds a list of further roots, and the
proof names one by its number; a whole call reads one entry file, whose number the proof file names,
so that number is the prover's choice. The list is rendered here by that one member. `test` and
`session` have not been weighed at three points where the typed queries meet the strings that the
prover and the verifiers that ship hash. The labels: each of a key's and of a proof's three chains
has a label of its own (the format page's R13.4, R14.3, R14.9, R14.10), while the typed queries have
one Fiat-Shamir oracle for each file's protocol. A prompt's tokens: they enter the proof's first
query byte for byte, with the request's two numbers, in the item "the request file's words", and
once more through a digest under the second hash function, in the item "request" (R14.3). A known
difference: the configuration's and the parameters' digests are answers of the hash function. This
third point touches `seed0`, `seed1` and `link` too: the seeds' first query holds the
configuration's digest. At one fixed hash function, where the served statements pin the three public
files, that digest is a constant; a soundness statement over a random function fixes it beforehand.
The two fields `test` and `session` also say that the fixed reading returns a typed string at every
key file and proof file that the program accepts. The program ties two openings of one position by
their digests alone, and a typed string has one opening at a position: so at a reading that makes
typed strings of such files these two fields say that no accepted file lists one position twice with
two different openings of one digest. No proof can give that of a fixed hash function. For proofs
only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Top
import Run.CodingBits

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Iop (Dig)
open _root_.Run (bytesToDig)

/-- The compiled verifier with records, left abstract in its own form. -/
structure Shape where
  /-- Which statements the description covers. -/
  Served : UserStm → Prop
  /-- The type of a table's record. The next four fields are the types of an instance and of the
  typed strings of Test, Link and a session. -/
  Rec : UserStm → Type
  Ins : UserStm → Type
  PiT : UserStm → Type
  PiL : UserStm → Type
  PiB : UserStm → Type
  /-- A table as the program holds it (root and answers), as a record. -/
  recOf : (x : UserStm) → Params.TableName → Option (Rec x)
  /-- The request and the reply, as an instance. -/
  insOf : (x : UserStm) → Option (Ins x)
  /-- The seed's query at the first root: is its seed the record's? -/
  seed0 : (x : UserStm) → Dig 256 → Rec x → Bool
  /-- The same at a further root. -/
  seed1 : (x : UserStm) → Dig 256 → Rec x → Bool
  /-- Test, at the first root and its record. -/
  vT : (x : UserStm) → Dig 256 → Rec x → PiT x → Bool
  /-- Link, at the two roots and their records. -/
  vL : (x : UserStm) → Dig 256 → Dig 256 → Rec x → Rec x → PiL x → Bool
  /-- A session, at the further root, the instance and the further record. -/
  vB : (x : UserStm) → Dig 256 → Ins x → Rec x → PiB x → Bool

namespace Shape
variable (V : Shape)

/-- The key's part: the table that the key file holds, and Test's typed string. -/
def vKey (x : UserStm) (k : Params.TableName × V.PiT x) : Option Params.TableName :=
  match V.recOf x k.1 with
  | some r =>
    if V.seed0 x (bytesToDig k.1.root) r && V.vT x (bytesToDig k.1.root) r k.2 then some k.1
    else none
  | none => none

/-- The entry's part, against the first table. -/
def vEnt (x : UserStm) (t : Params.TableName) (e : Params.TableName × V.PiL x) :
    Option Params.TableName :=
  match V.recOf x t, V.recOf x e.1 with
  | some r, some r' =>
    if V.seed1 x (bytesToDig e.1.root) r' &&
        V.vL x (bytesToDig t.root) (bytesToDig e.1.root) r r' e.2 then some e.1
    else none
  | _, _ => none

/-- The proof's part, against the further table. -/
def vPrf (x : UserStm) (u : Params.TableName) (p : V.PiB x) : Bool :=
  match V.recOf x u, V.insOf x with
  | some r', some i => V.vB x (bytesToDig u.root) i r' p
  | _, _ => false

/-- The target made from a shape. -/
def target : Target where
  Served := V.Served
  KeyV := fun x => Params.TableName × V.PiT x
  EntV := fun x => Params.TableName × V.PiL x
  PrfV := V.PiB
  Val := fun x => (Params.TableName × V.PiT x) × (Params.TableName × V.PiL x) × V.PiB x
  vKey := V.vKey
  vEnt := V.vEnt
  vPrf := V.vPrf
  pack := fun _ k e p => (k, e, p)
  verify := fun x v =>
    match V.vKey x v.1 with
    | some t =>
      match V.vEnt x t v.2.1 with
      | some u => V.vPrf x u v.2.2
      | none => false
    | none => false

/-- The verifier of `Shape.target` is the conjunction of the five answers, at the records of the two
tables and the instance. -/
theorem verify_iff (x : UserStm) (t u : Params.TableName) (πT : V.PiT x) (πL : V.PiL x)
    (πB : V.PiB x) :
    V.target.verify x ((t, πT), (u, πL), πB) = true ↔
      ∃ r r' i, V.recOf x t = some r ∧ V.recOf x u = some r' ∧ V.insOf x = some i ∧
        V.seed0 x (bytesToDig t.root) r = true ∧ V.seed1 x (bytesToDig u.root) r' = true ∧
        V.vT x (bytesToDig t.root) r πT = true ∧
        V.vL x (bytesToDig t.root) (bytesToDig u.root) r r' πL = true ∧
        V.vB x (bytesToDig u.root) i r' πB = true := by
  show (match V.vKey x (t, πT) with
    | some t' =>
      match V.vEnt x t' (u, πL) with
      | some u' => V.vPrf x u' πB
      | none => false
    | none => false) = true ↔ _
  unfold vKey vEnt vPrf
  constructor
  · intro h
    cases hr : V.recOf x t with
    | none => simp [hr] at h
    | some r =>
      cases hr' : V.recOf x u with
      | none =>
        by_cases c :
          (V.seed0 x (bytesToDig t.root) r && V.vT x (bytesToDig t.root) r πT) = true <;>
        simp [hr, hr', c] at h
      | some r' =>
        cases hi : V.insOf x with
        | none =>
          by_cases c :
            (V.seed0 x (bytesToDig t.root) r && V.vT x (bytesToDig t.root) r πT) = true <;>
          by_cases d :
            (V.seed1 x (bytesToDig u.root) r' &&
              V.vL x (bytesToDig t.root) (bytesToDig u.root) r r' πL) = true <;>
          simp [hr, hr', hi, c, d] at h
        | some i =>
          by_cases c : (V.seed0 x (bytesToDig t.root) r && V.vT x (bytesToDig t.root) r πT) = true
          · by_cases d :
              (V.seed1 x (bytesToDig u.root) r' &&
                V.vL x (bytesToDig t.root) (bytesToDig u.root) r r' πL) = true
            · simp [hr, hr', hi, c, d] at h
              rw [Bool.and_eq_true] at c d
              exact ⟨r, r', i, rfl, rfl, rfl, c.1, d.1, c.2, d.2, h⟩
            · simp [hr, hr', c, d] at h
          · simp [hr, c] at h
  · rintro ⟨r, r', i, hr, hr', hi, a, b, c, d, e⟩
    simp [hr, hr', hi, a, b, c, d, e]

end Shape

/-- One fixed reading for a shape: the table and the typed string of each of the first two files,
and the typed string of the third. -/
abbrev Reading5 (V : Shape) : Type := Reading V.target

/-- The five named hypotheses. In each, `o` are options that hold the ID and the bits 128, the
program says yes with the tables `table` and `further`, and the statement is served. -/
structure Holes5 (V : Shape) (R : Reading5 V) : Prop where
  /-- The first seed (the key file): the first table is read as a record, and the seed's query at
  its root gives the record's seed. -/
  seed0 : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) →
    ∃ r, V.recOf (stmOf F o) table = some r ∧
      V.seed0 (stmOf F o) (bytesToDig table.root) r = true
  /-- Test (the key file): the reading gives the program's own table and a typed string, and Test
  says yes. -/
  test : ∀ F o id table further r, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) → V.recOf (stmOf F o) table = some r →
    ∃ πT, R.key (stmOf F o) F.key = some (table, πT) ∧
      V.vT (stmOf F o) (bytesToDig table.root) r πT = true
  /-- The further seed (the entry file): as `seed0`, for the further table. -/
  seed1 : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    V.Served (stmOf F o) →
    ∃ r', V.recOf (stmOf F o) further = some r' ∧
      V.seed1 (stmOf F o) (bytesToDig further.root) r' = true
  /-- Link (the entry file): the reading gives the program's own further table and a typed string,
  and Link says yes. -/
  link : ∀ F o id table further r r', o.id = some id → o.bits = 128 →
    PortYesAt F id table further → V.Served (stmOf F o) → V.recOf (stmOf F o) table = some r →
    V.recOf (stmOf F o) further = some r' →
    ∃ πL, R.ent (stmOf F o) F.key F.ent = some (further, πL) ∧
      V.vL (stmOf F o) (bytesToDig table.root) (bytesToDig further.root) r r' πL = true
  /-- The session (the proof file): the request and the reply are read as an instance, the reading
  gives a typed string, and the session says yes. -/
  session : ∀ F o id table further r', o.id = some id → o.bits = 128 →
    PortYesAt F id table further → V.Served (stmOf F o) →
    V.recOf (stmOf F o) further = some r' →
    ∃ i πB, V.insOf (stmOf F o) = some i ∧ R.prf (stmOf F o) F.ent F.proof F.entry = some πB ∧
      V.vB (stmOf F o) (bytesToDig further.root) i r' πB = true

/-- The five named hypotheses give the four of OnBytes/K/Top.lean; the join is proved. -/
theorem holes_of_five (V : Shape) (R : Reading5 V) (H : Holes5 V R) : Holes V.target R where
  key := fun F o id table further hi hb h hs => by
    obtain ⟨r, hr, s0⟩ := H.seed0 F o id table further hi hb h hs
    obtain ⟨πT, hk, vt⟩ := H.test F o id table further r hi hb h hs hr
    refine ⟨(table, πT), hk, ?_⟩
    show V.vKey _ (table, πT) = some table
    unfold Shape.vKey
    simp [hr, s0, vt]
  entry := fun F o id table further hi hb h hs => by
    obtain ⟨r, hr, -⟩ := H.seed0 F o id table further hi hb h hs
    obtain ⟨r', hr', s1⟩ := H.seed1 F o id table further hi hb h hs
    obtain ⟨πL, he, vl⟩ := H.link F o id table further r r' hi hb h hs hr hr'
    refine ⟨(further, πL), he, ?_⟩
    show V.vEnt _ table (further, πL) = some further
    unfold Shape.vEnt
    simp [hr, hr', s1, vl]
  proof := fun F o id table further hi hb h hs => by
    obtain ⟨r', hr', -⟩ := H.seed1 F o id table further hi hb h hs
    obtain ⟨i, πB, hi', hp, vb⟩ := H.session F o id table further r' hi hb h hs hr'
    refine ⟨πB, hp, ?_⟩
    show V.vPrf _ further πB = true
    unfold Shape.vPrf
    simp [hr', hi', vb]
  join := fun x k e p t u hk he hp => by
    have hk : V.vKey x k = some t := hk
    have he : V.vEnt x t e = some u := he
    have hp : V.vPrf x u p = true := hp
    show (match V.vKey x k with
      | some t' =>
        match V.vEnt x t' e with
        | some u' => V.vPrf x u' p
        | none => false
      | none => false) = true
    rw [hk]
    show (match V.vEnt x t e with
      | some u' => V.vPrf x u' p
      | none => false) = true
    rw [he]
    exact hp

/-- The top statement at the form of the compiled verifier with records, under `Holes5`. If
`verify-on-bytes` returns 0 (`YES` or `WITHIN LIMITS`) and the user's statement is served, the fixed
reading of the files gives a value at which the abstract verifier `V.target.verify` says yes. That
verifier is the conjunction of the two seeds' answers, Test's, Link's and the session's
(`Shape.verify_iff`), which are parameters of `V`. -/
theorem top5 (V : Shape) (R : Reading5 V) (H : Holes5 V R) {args : List String} {s s' : World}
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
        ∃ v, R.valOf (stmOf F a.options) F = some v ∧
          V.target.verify (stmOf F a.options) v = true) :=
  top R (holes_of_five V R H) h

/-- The program's own test of the ID: the ID in the user's options is the commitment ID of the table
`t`. -/
def IdIs (x : UserStm) (t : Params.TableName) : Prop :=
  ∃ pl id, Model.Verify.planned x.pol x.KL (some x.lay) = .ok pl ∧ x.options.id = some id ∧
    Model.Verify.idAsked id = some (Fmt.hex (Key.commitmentId pl.chains.tableShape pl.cfg t))

/-- Where the program says yes, the ID is the first table's. -/
theorem idIs_of_port (F : Files) (o : Model.Verify.Options) (id : String)
    (table further : Params.TableName) (hi : o.id = some id)
    (h : PortYesAt F id table further) : IdIs (stmOf F o) table := by
  obtain ⟨r, pl, C, -, -, -, -, -, -, -, -, -, -, hp, -, -, -, -, -, hid, -⟩ := h
  exact ⟨pl, id, hp, hi, hid⟩

/-- The top statement, written out, under `Holes5`. If `verify-on-bytes` returns 0 (`YES` or
`WITHIN LIMITS`) and the user's statement is served, there are the two tables, with `IdIs` of the
first, their records, the instance, and the three typed strings as the fixed reading gives them, and
each of the five answers of the abstract `V` is yes. -/
theorem exit_five (V : Shape) (R : Reading5 V) (H : Holes5 V R) {args : List String} {s s' : World}
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
          (i : V.Ins (stmOf F a.options)) (πT : V.PiT (stmOf F a.options))
          (πL : V.PiL (stmOf F a.options)) (πB : V.PiB (stmOf F a.options)),
          IdIs (stmOf F a.options) table ∧
          V.recOf (stmOf F a.options) table = some r ∧
          V.recOf (stmOf F a.options) further = some rj ∧
          V.insOf (stmOf F a.options) = some i ∧
          R.key (stmOf F a.options) F.key = some (table, πT) ∧
          R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
          R.prf (stmOf F a.options) F.ent F.proof F.entry = some πB ∧
          V.seed0 (stmOf F a.options) (bytesToDig table.root) r = true ∧
          V.seed1 (stmOf F a.options) (bytesToDig further.root) rj = true ∧
          V.vT (stmOf F a.options) (bytesToDig table.root) r πT = true ∧
          V.vL (stmOf F a.options) (bytesToDig table.root) (bytesToDig further.root) r rj πL =
            true ∧
          V.vB (stmOf F a.options) (bytesToDig further.root) i rj πB = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp⟩ := main_zero_port h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, fun hs => ?_⟩
  obtain ⟨r, hr, s0⟩ := H.seed0 F a.options id table further hi hb hp hs
  obtain ⟨rj, hrj, s1⟩ := H.seed1 F a.options id table further hi hb hp hs
  obtain ⟨πT, hk, vt⟩ := H.test F a.options id table further r hi hb hp hs hr
  obtain ⟨πL, he, vl⟩ := H.link F a.options id table further r rj hi hb hp hs hr hrj
  obtain ⟨i, πB, hx, hq, vb⟩ := H.session F a.options id table further rj hi hb hp hs hrj
  exact ⟨table, further, r, rj, i, πT, πL, πB, idIs_of_port F a.options id table further hi hp, hr,
    hrj, hx, hk, he, hq, s0, s1, vt, vl, vb⟩

end OnBytes.K

#print axioms OnBytes.K.exit_five
#print axioms OnBytes.K.Shape.verify_iff
#print axioms OnBytes.K.holes_of_five
#print axioms OnBytes.K.top5
