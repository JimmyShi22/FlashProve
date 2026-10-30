-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieOnFilesArms.lean: the statement, under named hypotheses, that links the Lean program
`verify-on-bytes` (OnBytes/Main.lean; "the program" below) to `verifyArms r`, the verifier of which
Johnson/Top/OnFilesArms.lean states soundness under its own named hypotheses: check by check. It is
at one fixed function, Lean's BLAKE2b, and in one direction.

What this file states. `exit_verifyArms`: under `ArmTies`: if the program exits with code 0 on a
served statement, then the files are excepted, or `(systemArms r).accepts`, at Lean's BLAKE2b as the
hash function, at the commitment that the user's ID names, at that prompt and output, and at the
proof made of the further tokens, the key and the strings that the fixed reading R gives of the
three files, is true. `verifyArms r` runs three checks over the one hash function, one for each file
that a prover sends. This file fills the parameters of OnBytes/K/TopVC.lean and
Johnson/Top/TieFront.lean with r's own terms, after Johnson/Top/TieInnerCompiledVerifier.lean. `TieArms r`:
what r does not fix and the linking statement must still define: which statements are served, how a
table is read as a record, and which files are excepted. `shapeArms`: the shape at r. Its parts for
the key file, the entry file and the proof file are the runs of r's three checks at Lean's BLAKE2b.
The shape's two parts for the seeds always say yes: the seeds' tests are intended to be inside the
checks, which are free fields of r (`InputArms`, Johnson/Top/OnFilesArms.lean). `runs_arms`: where
the three checks say yes at Lean's BLAKE2b, so does the scheme's verifier. `frontV_is_verifyArms`:
`frontV` (Johnson/Top/TieFront.lean) at r's terms is `verifyArms r`: by rfl.

Under which hypotheses. `ArmTies`: the named hypotheses, one for each check, and two more. All five
speak only of files on which the program has said yes, and of its own two tables. `records`: the
program's two tables are read as records; `key`: the key file's check says yes, or the files are
excepted; `entry`: the entry file's check likewise; `proof`: the proof file's check likewise;
`idHash`: the hash of the code of the key made of the program's first table is that table's
commitment ID.

What it does not show.
- All of `ArmTies` are hypotheses; none is proved here at any r; a hypothesis may be false, not
  only unproved. No r and no `TieArms r` is given.
- `Served`, `recOf`, `Excepted` and the reading R are parameters: where no statement is served all
  five hold and nothing is said; where all files are excepted the three checks' linking hypotheses
  hold trivially, by their second disjunct (`records` and `idHash` have no such limb).
- `Excepted` is an unconstrained parameter: for every r, `Served`, `recOf` and reading there is an
  `Excepted` at which the three checks' linking hypotheses hold trivially, by their second disjunct.
  Until it is a concrete definition (defined in this library, not a parameter) with a bound on its
  probability, the linking hypotheses say nothing; the test of saying something is: an r, a
  `Served`, a concrete `Excepted`, and one served call that ends in 0 and is not excepted.
- Of excepted files nothing is said: that a prover cannot make one is no statement of this file.
- This file and the soundness statement (Johnson/Top/OnFilesArms.lean) say something together only
  of an input r that holds nothing of the fixed hash function: the three checks, the key's code and
  the builder must reach the hash function by their queries alone (OnBytes/K/Top.lean's condition
  (c)). No hypothesis here asks it. A check that compares an answer with BLAKE2b's own value accepts
  under a random function with probability 2^-256 and always at BLAKE2b: at such an r all named
  hypotheses of both files hold and nothing is said (shown by a probe in Lean's kernel, outside this
  tree).
- At the input that is meant today this is not met: the hypothesis on the commitment ID (`idHash`)
  makes the key's code the ID's own string, which holds the public files' digest, an answer of the
  hash function, and the key's type has no place for it: so it is in the code as a constant, and a
  bound for each fixed constant gives none for one that the function chooses. The cure that is
  intended: the digest goes into the typed key, and the checks test it against the hash function's
  own answer (Johnson/Top/OnFilesArmsC.lean).
- All named hypotheses of both files also hold together at inputs that hold no hash and still say
  nothing: checks that always accept or that recompute the model, with `Served` true of true claims
  alone (shown by a second probe in Lean's kernel, outside this tree). So that all of them hold at
  one input is no test of saying something.
- What a concrete instance must meet beyond them, at least, by further probes: (1) every statement
  that passes the concrete test `servedAt Z` (OnBytes/K/Served.lean), and a concrete further test
  whose verdict does not hang on the values of the claimed output tokens, is served ("no model
  stands in it" would be a property of a term, not of a value, and shuts nothing out: a list of true
  claims passes it): `exit_verifyArms_served` (Johnson/Top/TieOnFilesArmsServed.lean) has a premise
  of that shape, in which the further test is an unconstrained parameter; (2) the linking hypotheses
  hold at every hash function, with the rewriting of the Lean port over a monad in which the hash is
  asked, at that function, in the program's place: the premise of Johnson/Top/SoundVia.lean; neither
  (1) nor (2) alone is enough; (3) the weights' type, the model and the claim are the description's
  own; (4) some call is served, ends in 0 and is not excepted; (5) `Excepted` is a concrete
  definition with a bound on its probability.
- Evaluation at Lean's BLAKE2b in the place of the random function of the soundness theorem is one
  step taken as given; another is on the second hash (lean/THEOREM.md, "Two hash functions").
- All that the heads of OnBytes/K/Top.lean, OnBytes/K/TopVC.lean, OnBytes/K/Parts.lean,
  Johnson/Top/TieFront.lean and Johnson/Top/OnFilesArms.lean do not claim.
- This file is at Lean's BLAKE2b alone. The statement of a proof's first chain holds the request
  file itself, next to an item made by the programs' second hash function, which is no value of
  Lean's BLAKE2b at a spelt string (`Params.First.statement`, OnBytes/Params/Chains.lean); nothing
  in this file links the two items. A check that asks for that item by queries is not the program's
  at BLAKE2b: a check that meets `proof` holds the second hash function as a fixed function (by an
  informal argument; not proved in Lean). That this file's hypotheses hold together with the bound
  of the proof file's check that is intended is not shown here. Were the request bound by that item
  alone, this file's hypotheses could not hold together with that bound (by an informal argument;
  not proved in Lean). In that case a check that holds the second hash function as a fixed function
  would have no small bound (the same informal argument).
- The forms at a fixed function made of both hash functions: Johnson/Top/TieOnFilesArmsAt.lean,
  TieOnFilesArmsAtServed.lean; the forms that later files build on: Johnson/Top/OnFilesArmsC.lean,
  OnFilesPortC.lean, PortWritten.lean. In this file "Lean's BLAKE2b" means one fixed function: the
  format's realised oracle on bit strings (`Run.oBits ()`: Lean's BLAKE2b read through the format's
  byte coding).
- For proofs only; the program does not import this file.

-/
import OnBytes.K.Tokens
import OnBytes.K.Parts
import Johnson.Top.TieFront
import Johnson.Top.OnFilesArms

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open VerifiableInference (Token)
open VerifiableInference.OnPublicFiles

variable (r : InputArms)

/-- What r does not fix and the tie must still write, but for the reading of the files. -/
structure TieArms where
  /-- the statements that the description covers -/
  Served : UserStm → Prop
  /-- a table as a record -/
  recOf : UserStm → OnBytes.Params.TableName → Option r.L.Rec
  /-- the files of which the tie says nothing. What is intended: files that themselves show a
  collision of the hash function, such as one position listed twice with two salts under one digest:
  the program ties the two by digests alone, and a typed string has room for one. It is an exception
  of the tie with no bound: nothing here says that a prover cannot make such files, and for every r,
  `Served`, `recOf` and reading there is an `Excepted` at which the three checks' ties hold for
  nothing: they say something only at a written `Excepted` with a bound on its probability. A caller
  whose exception speaks of the options and the two tables as well has to close it over these, with
  the program's own yes kept inside. -/
  Excepted : Files → Prop

variable {r} (T : TieArms r)

/-- The shape at r. -/
def shapeArms : Shape where
  Served := T.Served
  Rec := fun _ => r.L.Rec
  Ins := fun _ => r.X
  PiT := fun _ => OneProtocolProof 256 (batTC r.L r.aT)
  PiL := fun _ => OneProtocolProof 256 (batLC r.L r.aL)
  PiB := fun _ => ℕ × OneProtocolProof 256 r.L.onlineBatch
  recOf := T.recOf
  insOf := fun x => r.build (promptOf x, outputOf x) (auxOf x)
  seed0 := fun _ _ _ => true
  seed1 := fun _ _ _ => true
  vT := fun _ cm c π => (r.armK cm c π).det (fun _ => oBits ())
  vL := fun _ cm cm' c c' π => (r.armE cm cm' c c' π).det (fun _ => oBits ())
  vB := fun _ cm i c π => (r.armP cm i c π.1 π.2).det (fun _ => oBits ())

/-- The front at r. -/
def frontArms : FrontAt (shapeArms T) where
  I := r.I
  X := r.X
  IVK := KeyRoot 256 r.L
  ISK := r.ISK
  Pf := OfflineLinkOnlineProof 256 r.L r.aT r.aL
  G := schemeArms r
  enc := r.enc
  bound := r.bound
  build := r.build
  π₀ := r.π₀
  prompt := promptOf
  output := outputOf
  aux := auxOf
  ins := fun _ i => i
  keyOf := fun _ t c => ⟨bytesToDig t.root, c⟩
  prfOf := fun _ πT u cj πL πB => ⟨πB.1, some πT, (bytesToDig u.root, cj, some πL), some πB.2⟩

/-- Where the three checks say yes at Lean's BLAKE2b, the scheme's verifier, run there, says yes. -/
theorem runs_arms (x : UserStm) (t u : OnBytes.Params.TableName) (c cj : r.L.Rec) (i : r.X)
    (πT : OneProtocolProof 256 (batTC r.L r.aT)) (πL : OneProtocolProof 256 (batLC r.L r.aL)) (πB : ℕ × OneProtocolProof 256 r.L.onlineBatch)
    (vt : (shapeArms T).vT x (bytesToDig t.root) c πT = true)
    (vl : (shapeArms T).vL x (bytesToDig t.root) (bytesToDig u.root) c cj πL = true)
    (vb : (shapeArms T).vB x (bytesToDig u.root) i cj πB = true) :
    ((frontArms T).G.V ((frontArms T).keyOf x t c) ((frontArms T).ins x i)
      ((frontArms T).prfOf x πT u cj πL πB)).det (fun _ => oBits ()) = true := by
  show ((r.armK (bytesToDig t.root) c πT).bind fun a =>
    (r.armE (bytesToDig t.root) (bytesToDig u.root) c cj πL).bind fun b =>
    (r.armP (bytesToDig u.root) i cj πB.1 πB.2).bind fun d =>
      OComp.pure (a && b && d)).det (fun _ => oBits ()) = true
  have vt : (r.armK (bytesToDig t.root) c πT).det (fun _ => oBits ()) = true := vt
  have vl : (r.armE (bytesToDig t.root) (bytesToDig u.root) c cj πL).det (fun _ => oBits ()) =
    true := vl
  have vb : (r.armP (bytesToDig u.root) i cj πB.1 πB.2).det (fun _ => oBits ()) = true := vb
  simp only [OComp.det_bind]
  rw [vt, vl, vb]
  rfl

/-- `frontV` at r's terms is `verifyArms r`. -/
theorem frontV_is_verifyArms (c : ZKCP.Digest 256) (prompt output : List Token)
    (proof : List Token × (KeyRoot 256 r.L × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) :
    frontV (schemeArms r) r.enc r.bound r.build r.π₀ c prompt output proof =
      verifyArms r c prompt output proof := rfl

/-- The named hypotheses of the tie at r, check by check. In each, `o` are options that hold the ID
and the bits 128, the program says yes with the tables `table` and `further`, and the statement is
served. -/
structure ArmTies (R : Reading5 (shapeArms T)) : Prop where
  /-- the program's two tables are read as records -/
  records : ∀ F o id table further, o.id = some id → o.bits = 128 →
    PortYesAt F id table further → T.Served (stmOf F o) →
    (∃ c, T.recOf (stmOf F o) table = some c) ∧ ∃ cj, T.recOf (stmOf F o) further = some cj
  /-- the key file: the reading gives the program's own table and a typed string, and the key file's
  check, run at Lean's BLAKE2b, says yes; or the files are excepted -/
  key : ∀ F o id table further c, o.id = some id → o.bits = 128 → PortYesAt F id table further →
    T.Served (stmOf F o) → T.recOf (stmOf F o) table = some c →
    (∃ πT, R.key (stmOf F o) F.key = some (table, πT) ∧
      (r.armK (bytesToDig table.root) c πT).det (fun _ => oBits ()) = true) ∨ T.Excepted F
  /-- the entry file: the reading gives the program's own further table and a typed string, and the
  entry file's check says yes; or the files are excepted -/
  entry : ∀ F o id table further c cj, o.id = some id → o.bits = 128 →
    PortYesAt F id table further → T.Served (stmOf F o) → T.recOf (stmOf F o) table = some c →
    T.recOf (stmOf F o) further = some cj →
    (∃ πL, R.ent (stmOf F o) F.key F.ent = some (further, πL) ∧
      (r.armE (bytesToDig table.root) (bytesToDig further.root) c cj πL).det (fun _ => oBits ()) =
        true) ∨ T.Excepted F
  /-- the proof file: the request and the reply are read as an instance, the reading gives a typed
  string, and the proof file's check says yes; or the files are excepted -/
  proof : ∀ F o id table further cj, o.id = some id → o.bits = 128 →
    PortYesAt F id table further → T.Served (stmOf F o) →
    T.recOf (stmOf F o) further = some cj →
    (∃ i πB, r.build (promptOf (stmOf F o), outputOf (stmOf F o)) (auxOf (stmOf F o)) = some i ∧
      R.prf (stmOf F o) F.ent F.proof F.entry = some πB ∧
      (r.armP (bytesToDig further.root) i cj πB.1 πB.2).det (fun _ => oBits ()) = true) ∨
      T.Excepted F
  /-- the key made of the program's own first table and its record has a code, and the hash of that
  code, at Lean's BLAKE2b, is the table's commitment ID under the planner's shape and digest -/
  idHash : ∀ F o id table further c pl, o.id = some id → o.bits = 128 →
    PortYesAt F id table further → T.Served (stmOf F o) →
    Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl →
    T.recOf (stmOf F o) table = some c →
    ∃ code, r.enc ⟨bytesToDig table.root, c⟩ = some code ∧
      oBits () code = bytesToDig (Key.commitmentId pl.chains.tableShape pl.cfg table)

/-- The linking statement at `verifyArms r`, under `ArmTies`: five hypotheses, none proved here at
any r. See "What it does not show" in the head. -/
theorem exit_verifyArms (R : Reading5 (shapeArms T)) (A : ArmTies T R)
    {args : List String} {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
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
        (∃ (table further : OnBytes.Params.TableName) (c cj : r.L.Rec)
          (πT : OneProtocolProof 256 (batTC r.L r.aT)) (πL : OneProtocolProof 256 (batLC r.L r.aL))
          (πB : ℕ × OneProtocolProof 256 r.L.onlineBatch) (cm : ZKCP.Digest 256),
          CommitIs (stmOf F a.options) cm ∧ IdIs (stmOf F a.options) table ∧
          T.recOf (stmOf F a.options) table = some c ∧
          T.recOf (stmOf F a.options) further = some cj ∧
          R.key (stmOf F a.options) F.key = some (table, πT) ∧
          R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
          R.prf (stmOf F a.options) F.ent F.proof F.entry = some πB ∧
          (systemArms r).accepts (oBits ()) cm (promptOf (stmOf F a.options))
            (outputOf (stmOf F a.options))
            (auxOf (stmOf F a.options),
              (⟨bytesToDig table.root, c⟩,
                ⟨πB.1, some πT, (bytesToDig further.root, cj, some πL), some πB.2⟩)) = true) ∨
          T.Excepted F) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp⟩ := main_zero_port h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, fun hs => ?_⟩
  obtain ⟨⟨c, hc⟩, ⟨cj, hcj⟩⟩ := A.records F a.options id table further hi hb hp hs
  rcases A.key F a.options id table further c hi hb hp hs hc with ⟨πT, hk, vt⟩ | hx
  swap
  · exact Or.inr hx
  rcases A.entry F a.options id table further c cj hi hb hp hs hc hcj with ⟨πL, he, vl⟩ | hx
  swap
  · exact Or.inr hx
  rcases A.proof F a.options id table further cj hi hb hp hs hcj with ⟨i, πB, hx, hq, vb⟩ | hx
  swap
  · exact Or.inr hx
  have hid := idIs_of_port F a.options id table further hi hp
  obtain ⟨pl, hpl, hci⟩ := commitIs_of_idIs _ table hid
  obtain ⟨code, hcode, hd⟩ := A.idHash F a.options id table further c pl hi hb hp hs hpl hc
  exact Or.inl ⟨table, further, c, cj, πT, πL, πB, _, hci, hid, hc, hcj, hk, he, hq,
    front_yes (schemeArms r) r.enc r.bound r.build r.π₀ (oBits ()) _ _ _ _ _ _ i code hx hcode hd
      (runs_arms T (stmOf F a.options) table further c cj i πT πL πB vt vl vb)⟩

end OnBytes.K

#print axioms OnBytes.K.runs_arms
#print axioms OnBytes.K.frontV_is_verifyArms
#print axioms OnBytes.K.exit_verifyArms
