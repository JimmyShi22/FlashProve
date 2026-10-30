-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Top.lean: the top statement of the tie between the program and the verifier of which the
soundness theorem speaks, with its hypotheses named.

"The program" is the Lean text `verify-on-bytes` (OnBytes/Main.lean); this repository builds no
stand-alone program from it. "The tie" is the statement: if the program says `YES` or `WITHIN
LIMITS`, then the verifier of which the soundness theorem speaks says yes. In this file that
verifier is left abstract (`Target`), and what is not proved stands as four named hypotheses
(`Holes`).

What is proved. `top`: if the entry function of the program returns 0, which covers both `YES` and
`WITHIN LIMITS`, then the call was a whole call on eight files read as bytes, with options `a` that
are a function of the arguments and hold the ID and 128 as the requested bits. The 128 is a field of
the options; it is no bound on an error. And if the user's statement is one that the description
serves, then one fixed reading of the bytes gives a typed value, and the abstract verifier accepts
that value at the user's statement. This holds under the four named hypotheses and nothing else:
no proof is left open and no axiom is added.

Words. A whole call is a call of the command `verify` with five names and options. It reads eight
files: three public files, the key file, one entry file, the request, the reply and the proof file.
"The ID" is the commitment ID that the user gives behind `-id`. "The description" is the protocol's
description, which comes from the public files. `PortYes` and `PortYesAt` name the program's yes.

Main definitions.
- `UserStm`: the statement that the user means. It is not left abstract. It is the bytes of the
  three public files, of the request and of the reply, and the options as read from the command line
  (the ID, the bits, `-next-token`, `-policy`, `-no-proof-of-work`). It holds no byte of the key,
  the entry or the proof file. It does not hold the entry's number, which the prover chooses: the
  program takes that number from the head of the proof file.
- `PortYesAt F id table further`: all that `main_zero_named` (OnBytes/Tie/ZeroNamed.lean) says of
  the bytes, and four further clauses (see "What is not claimed"), with names for the two
  tables that the program hands on from file to file. `Key.check` returns `table`; `Entry.check`
  against `table` returns `further`; `Proof.check` runs against `further`; the ID is that of
  `table`.
- `Target`: the verifier of which the soundness theorem speaks, left abstract. Its types depend on
  the user's statement, because the types of the typed strings depend on the description. Its three
  parts hand tables on as the program's checks do: the key's part returns a table, the entry's part
  takes it and returns a table, and the proof's part takes that one. `Served` says which statements
  the description covers.
- `Reading`: one fixed reading, made of functions of the user's statement and the files' bytes.
- `Holes`: the four named hypotheses. `key`, `entry` and `proof` each say: where the program's check
  says yes with these tables, the typed part says yes with the same tables. `join` says: where the
  three parts say yes, each with the table that the one before returned, the verifier says yes.

Main theorems. `main_zero_port`: the exit code 0 gives `PortYes`. `tie`: under `Holes`, at a served
statement, the program's yes gives the verifier's yes. `top`: the same from the exit code 0.

How the hypotheses split. The program reads each file as chains and decides on a chain by blocks
(OnBytes/Tie/KeyFile.lean). `key` splits into three chains (one-time, shared and second), which are
the compiler's layer, and the key's blocks, which are the decision's layer. In the compiler's layer
the program's decision on a chain is a black box; this file does not treat
the one-time chain in that layer. `entry` splits into one chain and the link's blocks. `proof`
splits into three chains and the request's blocks. `join` is the compiler of three chains joined.
All content on soundness lies in the decision's layer. Any account of the named hypotheses must
place each one: proved, taken as given, or left open. A named hypothesis may be false, and not only
unproved.

What an instance must meet. A verifier that says yes to everything meets every named hypothesis, so
these theorems are worth what their instance is worth. An instance must be one theorem with
no free parameter, in which all of the following hold.
- (a) `T.verify x v` unfolds to the run (`.det`, at the oracle functions made from `Fmt.oracle`) of
  the same constant, at the same arguments, as in the statement of the soundness theorem.
- (b) The decision is the description's and is not left abstract.
- (c) The hash enters by that `.det` alone. The soundness theorem speaks of a random oracle; the
  step to BLAKE2b is assumed, as is one on the second hash: lean/THEOREM.md, "Two hash functions".
- (d) The description and the parameters are a function of the user's statement alone.
- (e) The reading parses and does not search, and it does not branch on the program's verdict.
- (f) The three parts and `pack` are the library's terms.
- (g) The soundness theorem's relation at `x` is written in words.

What is not claimed. `PortYesAt` is weaker than the exit code 0. Beyond the clauses of
`main_zero_named` it hands on what OnBytes/K/ExitZero.lean proves of the same run: `StagesPassed`
(the profile, the threshold on the bits, the four conditions of the standard parameter form that are
tested in the stages for the key file and the entry file, the two files' accounts at 128 bits, and
the test on each account's note on work), and that the stage of the request passed. `PortYesAt` says
the last at some options that hold the ID and the bits 128; it does not say that these are the
options of the user's statement. The conditions of the request's stage itself, and the tests on
records and notes, are not unfolded: what the description needs of them must stand in `Served`, as a
property of the user's statement, or come from a further theorem. Nothing is said of the C++ program
`cp_verify` or of compiled code. The planner (`Model.Verify.planned`) fixes what a statement means
and is trusted. A yes speaks only of the positions that the request names. The bits come from the
soundness theorem's own bound, which `top` does not state. For proofs only; the program does not
import this file.

-/
import OnBytes.K.ExitServed

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event fileLimit wholeReads kindOf Asked)
open OnBytes.Proof

/-- The eight files of a whole call, as bytes, and the entry's number. -/
structure Files where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  key : ByteArray
  ent : ByteArray
  request : ByteArray
  y : ByteArray
  proof : ByteArray
  entry : Nat

/-- What this file hands on from the exit code 0 about the bytes, at the two tables that the program
hands on from file to file. The clauses are those of `main_zero_named`, without the form of the
arguments, the reads and the options. To these it adds the two clauses of `main_zero_stages`
(OnBytes/K/ExitZero.lean) on the stages; the second holds at some options with the ID and the bits
128; and two clauses of `main_zero_served` (OnBytes/K/ExitServed.lean): the program's shared record
holds the planner's own data, and the six further files are within the program's limits on a file.
It is weaker than the exit code 0: see "What is not claimed" in the head. -/
def PortYesAt (F : Files) (id : String) (table further : Params.TableName) : Prop :=
  ∃ (r : Model.Verify.Read) (p : Model.Verify.Planned) (C : Model.Verify.Common),
    r.pol = F.pol ∧ r.KL = F.KL ∧ r.layout = some F.lay ∧ r.key = F.key ∧ r.request = F.request ∧
    r.y = F.y ∧ r.proof = F.proof ∧ r.entry = F.entry ∧
    F.key.size ≤ fileLimit ∧ F.ent.size ≤ fileLimit ∧
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
    Model.Verify.commonOfCall r = .ok C ∧ C.chains = p.chains ∧
    Key.check p.chains.key F.key = .ok table ∧
    Entry.check (p.chains.bytes .link) table F.ent = .ok further ∧
    (∃ so cov item links,
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) C.X.T =
        .ok so ∧
      Model.Head.coveredOf so C.X.T C.X.P.h.V = .ok cov ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      Model.Verify.linksOf C.X cov = .ok links ∧
      Proof.check p.chains.proof further F.entry item F.request (Model.ofNat so.y)
        (Model.Stages.runLinksH (C.built.links.zipWith (fun b l => { b with run := l.run }) links)
          p.chains.proof.first C.X.layers.wsLay) F.proof = .accepted) ∧
    Model.Verify.idAsked id =
      some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg table)) ∧
    Tie.SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]) ∧
    StagesPassed C 128 ∧
    (∃ o ac w, o.id = some id ∧ o.bits = 128 ∧
      Model.Verify.requestStage C o r F.ent = .ok (.passed, ac, w)) ∧
    (C.X = p.X ∧ C.built = p.built) ∧
    (F.pol.size ≤ Shell.textLimit ∧ F.lay.size ≤ Shell.textLimit ∧ F.KL.size ≤ fileLimit ∧
      F.request.size ≤ fileLimit ∧ F.y.size ≤ fileLimit ∧ F.proof.size ≤ fileLimit)

/-- The same, at some tables. -/
def PortYes (F : Files) (id : String) : Prop := ∃ table further, PortYesAt F id table further

/-- The exit code 0 of the entry function (`YES` or `WITHIN LIMITS`). The arguments are `verify`,
five names and options that hold `-id` and, right behind it, the ID. The call's kind and its options
`a` are those that `kindOf` reads off the arguments. The program's operations gave eight reads that
were answered with the bytes `F`. The options hold the ID and the bits 128. And `PortYes F id`
holds. -/
theorem main_zero_port {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧ PortYes F id := by
  obtain ⟨config, ivk, request, y, proof, a, r, lay, ent, t, p, C, table, further, id, pre, post, e,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, ⟨ac, w, h17⟩, h18, h19,
    -⟩ := main_zero_served h
  exact ⟨config, ivk, request, y, proof, a,
    ⟨r.pol, lay, r.KL, r.key, ent, r.request, r.y, r.proof, r.entry⟩, t, id, pre, post, e, h1, h2,
    h12, h14, table, further, r, p, C, rfl, rfl, h3, rfl, rfl, rfl, rfl, rfl, h4, h5, h6, h7, h8,
    h9, h10, h11, h13, h15, h16, ⟨a.options, ac, w, h12, h14, h17⟩, h18, h19⟩

/-- The verifier of which the soundness theorem speaks, left abstract. Its types depend on the
user's statement. Its three parts hand tables on as the program's checks do. `Served` says which
statements the description covers. In an instance, `verify` is to be the run of the library's
compiled verifier at the oracle functions made from Lean's BLAKE2b: see "What an instance must meet"
in the head. -/
structure Target where
  Served : UserStm → Prop
  KeyV : UserStm → Type
  EntV : UserStm → Type
  PrfV : UserStm → Type
  Val : UserStm → Type
  vKey : (x : UserStm) → KeyV x → Option Params.TableName
  vEnt : (x : UserStm) → Params.TableName → EntV x → Option Params.TableName
  vPrf : (x : UserStm) → Params.TableName → PrfV x → Bool
  pack : (x : UserStm) → KeyV x → EntV x → PrfV x → Val x
  verify : (x : UserStm) → Val x → Bool

/-- One fixed reading: functions of the user's statement and of the files' bytes, and for the proof
also of the number of the entry file that was read. -/
structure Reading (T : Target) where
  key : (x : UserStm) → (key : ByteArray) → Option (T.KeyV x)
  ent : (x : UserStm) → (key ent : ByteArray) → Option (T.EntV x)
  prf : (x : UserStm) → (ent proof : ByteArray) → (entry : Nat) → Option (T.PrfV x)

variable {T : Target}

/-- The user's statement at the files that were read and the options that were typed. -/
def stmOf (F : Files) (o : Model.Verify.Options) : UserStm :=
  ⟨F.pol, F.lay, F.KL, F.request, F.y, o⟩

/-- The typed value that the fixed reading gives. -/
def Reading.valOf (R : Reading T) (x : UserStm) (F : Files) : Option (T.Val x) := do
  let k ← R.key x F.key
  let e ← R.ent x F.key F.ent
  let p ← R.prf x F.ent F.proof F.entry
  pure (T.pack x k e p)

/-- The named hypotheses. Each is a hypothesis of `top`. In
the first three, `o` are options that hold the ID and the bits 128, and the statement is served. -/
structure Holes (T : Target) (R : Reading T) : Prop where
  /-- The key file: where the program says yes and `Key.check` returns `table`, the key file is read
  and the typed key's verifier returns `table`. -/
  key : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    T.Served (stmOf F o) →
    ∃ k, R.key (stmOf F o) F.key = some k ∧ T.vKey (stmOf F o) k = some table
  /-- The entry file, likewise: the typed entry's verifier, against `table`, returns `further`. -/
  entry : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    T.Served (stmOf F o) →
    ∃ e, R.ent (stmOf F o) F.key F.ent = some e ∧ T.vEnt (stmOf F o) table e = some further
  /-- The proof file, likewise: the typed proof's verifier, against `further`, says yes. -/
  proof : ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    T.Served (stmOf F o) →
    ∃ p, R.prf (stmOf F o) F.ent F.proof F.entry = some p ∧ T.vPrf (stmOf F o) further p = true
  /-- The join: where the three parts say yes, each with the table that the one before returned, the
  verifier says yes at the packed value. -/
  join : ∀ x k e p t u, T.vKey x k = some t → T.vEnt x t e = some u → T.vPrf x u p = true →
    T.verify x (T.pack x k e p) = true

/-- The tie, on bytes: under the named hypotheses, at a served statement, the program's yes gives
the yes of the abstract verifier `T.verify` at the fixed reading. -/
theorem tie (R : Reading T) (H : Holes T R) (F : Files) (o : Model.Verify.Options) (id : String)
    (hi : o.id = some id) (hb : o.bits = 128) (h : PortYes F id) (hs : T.Served (stmOf F o)) :
    ∃ v, R.valOf (stmOf F o) F = some v ∧ T.verify (stmOf F o) v = true := by
  obtain ⟨table, further, h⟩ := h
  obtain ⟨k, hk, vk⟩ := H.key F o id table further hi hb h hs
  obtain ⟨e, he, ve⟩ := H.entry F o id table further hi hb h hs
  obtain ⟨p, hp, vp⟩ := H.proof F o id table further hi hb h hs
  refine ⟨T.pack _ k e p, ?_, H.join _ k e p table further vk ve vp⟩
  unfold Reading.valOf
  rw [hk, he, hp]
  rfl

/-- The top statement, under the named hypotheses `H`. If `verify-on-bytes` returns 0 (`YES` or
`WITHIN LIMITS`), the call was a whole call on the bytes `F` with the options `a`, which hold the ID
and the bits 128. If the user's statement (the bytes of the public files, of the request and of the
reply as read, and the options as typed) is served, the abstract verifier `T.verify` accepts, at
that statement, the typed value that the one fixed reading of `F` gives. -/
theorem top (R : Reading T) (H : Holes T R) {args : List String} {s s' : World}
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
      (T.Served (stmOf F a.options) →
        ∃ v, R.valOf (stmOf F a.options) F = some v ∧ T.verify (stmOf F a.options) v = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, hp⟩ :=
    main_zero_port h
  exact ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb,
    tie R H F a.options id hi hb hp⟩

end OnBytes.K

#print axioms OnBytes.K.main_zero_port
#print axioms OnBytes.K.tie
#print axioms OnBytes.K.top
