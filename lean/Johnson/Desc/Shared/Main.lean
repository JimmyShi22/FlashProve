-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Main.lean: a command that tries the decision on a proof file's shared hash chain
on a stored proof and on changed copies of its input.

This file is a driver and no part of the decision. A proof file holds three hash chains. The command
looks at one of them, the middle one, which a batch of requests shares. It is no verdict on a proof:
the other two chains, the key file, the entry file, every hash, every proof of work and every
opening of a tree are outside the decision that it tries.

What it does. It reads seven files of a folder: the three public files, an entry file, a request, a
reply and a proof. With the planner and the file-reading routines of the Lean verifier program
(OnBytes/Model/Verify.lean, OnBytes/Proof/File.lean) it makes three things: the sizes that follow
from the public files; the stored table's key; and the shared chain's view, that is, its rounds and
opened columns as a decision sees them. It calls the decision (Desc.Shared.descSharedZ, Par.lean) on
these three and prints YES or no and the place where the run stopped. Then it does the same at 36
changed inputs: each changes one thing in the view (23), in the sizes (8) or in the key (5). Beside
each stands the place at which the decision is expected to stop, and the line says whether it did.
The places' names are those of places (Fold.lean), with "par" and "front" before them; the command
prints what they mean.

To run it: from lean/, after a build, with libvob.so made as Ask/README.md says ("The faster way"):
    lake env lean --load-dynlib=./libvob.so --tstack=4000000 --run \
      Ask/SharedChain.lean <folder> [--plant]
Without the compiled library Lean interprets all the code: many minutes; not measured. The entry
point main is in Ask/SharedChain.lean, which tells more on the command line.

The decision that it tries is not written block by block.


Arguments. The first is the folder; without it the command reads examples/accepted-proof. A second
argument --plant sets the expected place of the first changed input wrong on purpose, to show that
the command is able to fail: that run must return 1.

Exit status. 0 if the stored proof's answer is YES and each changed input is refused at its expected
place; 1 if any line is not as expected; 2 if the arguments are wrong, a file cannot be read, or the
three things cannot be made from the files.

Limits.
  A change is made in memory, after the files have been read. No file is altered and no hash is
    computed again, so nothing here tries the checks on hashes. Some changes are to drawn values,
    which a prover cannot choose.
  An input that a change left as it was would get YES, and so be printed as not expected. There is
    no other check that a change changes something.
  The comparison is as fine as a place: which check inside that step refuses is not compared.
  The expected places are those seen on two stored proofs. They are data of this file, not derived.
  The command is cut to the example folders. It always reads ivk/leaf/0.bin as the entry file,
    whichever stored copy the proof file's head names. The changes name rounds 0 to 7 by number, and
    these are the shared chain's rounds only at a shape with a split. At another folder the command
    can return 1 or 2 for these reasons alone.
  Where the three things cannot be made, the print names the routine that refused. Its own reason is
    dropped (named), except where the parsing of the proof file refuses.
  Much of what runs is the verifier program's own code: its planner and file-reading routines here,
    and inside the decision its planner's routine for this chain's plan, its seven routines that
    change the statement and the book of trees, and its routine for a proximity test. The routine
    that parses the proof file has accepted the form of the file's bytes before the decision sees
    anything, and it makes a dry run of the first chain's checks to learn that form.

What is not claimed. Nothing is proved here, and nothing is claimed on soundness, on an honest
prover or on hiding.

It imports no module of Mathlib, so it can be compiled to a native program.
What this comment says of the command rests on reading and on runs; it is not machine-checked.


-/
import Johnson.Desc.Shared.Par
import OnBytes.Model.Verify
import OnBytes.Proof.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Drive
open OnBytes OnBytes.Params OnBytes.Model Desc.Shared

/-- The seven stored files. -/
structure Files where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  ent : ByteArray
  request : ByteArray
  y : ByteArray
  proof : ByteArray

/-- Reads the seven files of a folder. -/
def filesOf (dir : String) : IO Files := do
  let rd (p : String) : IO ByteArray := IO.FS.readBinFile (dir ++ "/" ++ p)
  pure { pol := ← rd "config/policy.txt", lay := ← rd "config/layout.txt",
         KL := ← rd "config/KL.bin", ent := ← rd "ivk/leaf/0.bin", request := ← rd "example.req",
         y := ← rd "example.y", proof := ← rd "example.proof" }

/-- Drops a failure's own reason and puts the string n in its place. -/
def named {ε α : Type} (n : String) : Except ε α → Except String α
  | .ok a => .ok a
  | .error _ => .error n

/-- The sizes, the table's key and the shared chain's view, all made by the verifier program's own
planner and file-reading routines. -/
def inputOf (F : Files) : Except String (Params.ProofSized × TableKey × Fmt.View) := do
  let p ← named "the planner" (Verify.planned F.pol F.KL (some F.lay))
  let so ← named "request and reply"
    (Head.stFromCall (Verify.words32 F.request) (Verify.words32 F.y) p.X.T)
  let cov ← named "the covered positions" (Head.coveredOf so p.X.T p.X.P.h.V)
  let item ← (Proof.requestItem F.pol F.KL F.request).elim (.error "the request's item") .ok
  let links ← named "the links" (Verify.linksOf p.X cov)
  let lk := Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
    p.chains.proof.first p.X.layers.wsLay
  let block := Proof.firstBlock p.chains.proof.first lk (Model.ofNat so.y)
  let q := p.chains.link
  let i ← named "the entry file's head" (Proof.readHead q.given.plan.field .entry F.ent)
  let t ← named "the entry file's table"
    (readTable q.given.plan.field (q.link.table.rows * q.link.table.answers) F.ent i)
  let copy ← named "the proof file's head" (Verify.cpProofHead F.proof)
  let r ← (Proof.readProof p.chains.proof t.1 copy item F.request block F.proof).fromStart
  pure (p.chains.made.sized.proof, r.key, r.shared.view)

/-- Where the run stops: "par" if the planner makes no plan, "front" if a check before round 0
refuses, the name of the step that refuses (places, Fold.lean), or "-" if none refuses. -/
def endsAt (z : Params.ProofSized) (key : TableKey) (v : Fmt.View) : String :=
  match parOfZ z.set z.codes z.batch key with
  | none => "par"
  | some p =>
    match front p z.codes v with
    | none => "front"
    | some m =>
      let rec go : List (String × (Mid Loc → Option (Mid Loc))) → Mid Loc → String
        | [], _ => "-"
        | (n, f) :: l, m => match f m with
          | none => n
          | some m' => go l m'
      go (places callG p) m

/-- The list with f applied to its entry number i. -/
def modAt {α : Type} (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, a :: l => f a :: l
  | i + 1, a :: l => a :: modAt f i l

/-- A triple with 1 added to its first word. -/
def bump (x : UInt64 × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 := (x.1 + 1, x.2.1, x.2.2)

/-- An item with 1 added to its first word. -/
def bumpGot : Fmt.ItemValue → Fmt.ItemValue
  | .e x => .e (bump x)
  | .answer x => .answer (bump x)
  | g => g

/-- The view with f applied to its round number k. -/
def onRound (k : Nat) (f : Fmt.RoundView → Fmt.RoundView) (v : Fmt.View) : Fmt.View :=
  { v with rounds := modAt f k v.rounds }

/-- The round with f applied to the elements that it draws. -/
def onElems (f : List Fmt.Ext → List Fmt.Ext) (r : Fmt.RoundView) : Fmt.RoundView :=
  { r with drawn := { r.drawn with elems := f r.drawn.elems } }

/-- The view with f applied to its opened column number i. -/
def onCol (i : Nat) (f : Nat × Nat × List UInt64 → Nat × Nat × List UInt64) (v : Fmt.View) :
    Fmt.View :=
  { v with opened := modAt f i v.opened }

/-- Changed inputs: a label, the place where the decision is expected to stop, and a change of the
view. -/
def onView : List (String × String × (Fmt.View → Fmt.View)) :=
  [("v1 round 0: the drawn point's first coordinate + 1", "testU",
      onRound 0 (onElems (modAt bump 0))),
   ("v2 round 0: one element fewer is drawn", "step0", onRound 0 (onElems (·.drop 1))),
   ("v3 round 0: the prover's message holds an item", "step0",
      onRound 0 fun r => { r with vals := [.e (0, 0, 0)] }),
   ("v4 round 1: the drawn seed's first coordinate + 1", "testU",
      onRound 1 (onElems (modAt bump 0))),
   ("v5 round 1: the drawn seed's factor set to 0", "step1",
      onRound 1 (onElems fun l => modAt (fun _ => (0, 0, 0)) (l.length - 1) l)),
   ("v6 round 1: one element fewer is drawn", "step1", onRound 1 (onElems (·.drop 1))),
   ("v7 round 2: the first answer + 1", "testU",
      onRound 2 fun r => { r with vals := modAt bumpGot 0 r.vals }),
   ("v8 round 2: the first answer is missing", "step1",
      onRound 2 fun r => { r with vals := r.vals.drop 1 }),
   ("v9 round 2: the answers are sent twice", "step1",
      onRound 2 fun r => { r with vals := r.vals ++ r.vals }),
   ("v10 round 3: the first drawn position + 1", "step2", onRound 3 fun r =>
      { r with drawn := { r.drawn with poss := modAt (· + 1) 0 r.drawn.poss } }),
   ("v11 the first opened column's first word + 1", "testU",
      onCol 0 fun y => (y.1, y.2.1, modAt (· + 1) 0 y.2.2)),
   ("v12 the first opened column's tree key + 1", "step2", onCol 0 fun y => (y.1 + 1, y.2)),
   ("v13 the first opened column is one word short", "step2",
      onCol 0 fun y => (y.1, y.2.1, y.2.2.dropLast)),
   ("v14 round 5: the first answer + 1", "testOmega",
      onRound 5 fun r => { r with vals := modAt bumpGot 0 r.vals }),
   ("v15 round 6: the second drawn point's first coordinate + 1", "testU",
      onRound 6 (onElems (modAt bump 0))),
   ("v16 round 7: the element sent + 1", "testU",
      onRound 7 fun r => { r with vals := modAt bumpGot 0 r.vals }),
   ("v17 round 7: two elements are sent", "step5",
      onRound 7 fun r => { r with vals := r.vals ++ r.vals }),
   ("v18 an empty round more after round 7", "testU", fun v =>
      { v with rounds := v.rounds.take 8 ++ [⟨[], ⟨[], [], [], none⟩⟩] ++ v.rounds.drop 8 }),
   ("v19 the last opened column's first word + 1", "testOmega", fun v =>
      onCol (v.opened.length - 1) (fun y => (y.1, y.2.1, modAt (· + 1) 0 y.2.2)) v),
   ("v20 one opened column more at the end", "seal",
      fun v => { v with opened := v.opened ++ v.opened.take 1 }),
   ("v21 one round more after the last", "seal",
      fun v => { v with rounds := v.rounds ++ [⟨[], ⟨[], [], [], none⟩⟩] }),
   ("v22 the last round is missing", "seal", fun v => { v with rounds := v.rounds.dropLast }),
   ("v23 a word of an opened column is not below the field's prime", "front",
      onCol 0 fun y => (y.1, y.2.1, modAt (fun _ => (0 : UInt64) - 1) 0 y.2.2))]

/-- Changed inputs: one of the sizes is changed; the view is not. -/
def onSizes : List (String × String × (Params.ProofSized → Params.ProofSized)) :=
  [("s1 the security target + 8 bits", "par",
      fun z => { z with set := { z.set with target := z.set.target + 8 } }),
   ("s2 the security target - 8 bits", "par",
      fun z => { z with set := { z.set with target := z.set.target - 8 } }),
   ("s3 the proof of work at rounds of positions + 4 bits", "par",
      fun z => { z with set := { z.set with
      workQuery := { z.set.workQuery with shared := z.set.workQuery.shared + 4 } } }),
   ("s4 the answers to a sample + 1", "front",
      fun z => { z with set := { z.set with samples := z.set.samples + 1 } }),
   ("s5 the number of columns read from the stored table - 1", "par",
      fun z => { z with batch := { z.batch with shape :=
      { z.batch.shape with fold := { z.batch.shape.fold with
        columns := z.batch.shape.fold.columns - 1 } } } }),
   ("s6 the sizes ask one coordinate more of the first point", "step0",
      fun z => { z with batch := { z.batch with shape :=
      { z.batch.shape with kLo := z.batch.shape.kLo + 1 } } }),
   ("s7 the first proximity test's sizes lose their last stage", "testU",
      fun z => { z with batch := { z.batch with
      folded := { z.batch.folded with stages := z.batch.folded.stages.dropLast } } }),
   ("s8 there is no main code at all", "par",
    fun z => { z with codes := { z.codes with base := #[] } })]

/-- Changed inputs: the table's key is changed; the view and the sizes are not. -/
def onKey : List (String × String × (TableKey → TableKey)) :=
  [("k1 the record's first answer + 1", "testU",
      fun k => { k with record := k.record.modify 0 fun e => addE e oneE }),
   ("k2 the record is one entry short", "step1", fun k => { k with record := k.record.pop }),
   ("k3 every seed's first coordinate + 1", "testU", fun k =>
      { k with seeds := k.seeds.map fun s => { s with z := modAt (fun e => addE e oneE) 0 s.z } }),
   ("k4 every seed's factor set to 0", "step1",
      fun k => { k with seeds := k.seeds.map fun s => { s with beta := zeroE } }),
   ("k5 the number of the item that holds the table's root + 1", "step2",
      fun k => { k with item := k.item + 1 })]

/-- The list with the expected place of its first entry set wrong on purpose. -/
def planted {α : Type} : List (String × String × α) → List (String × String × α)
  | [] => []
  | (n, _, f) :: l => (n, "a place that does not exist (planted)", f) :: l

/-- How to call the command. -/
def usage : String :=
  "To run it: from lean/, after a build, with libvob.so made as Ask/README.md says:\n" ++
  "  lake env lean --load-dynlib=./libvob.so --tstack=4000000 --run \\\n" ++
  "    Ask/SharedChain.lean <folder> [--plant]\n" ++
  "Without the compiled library Lean interprets all the code: many minutes; not measured.\n" ++
  "Arguments: a folder with a stored proof (default: examples/accepted-proof); then, if wanted, " ++
  "--plant, which sets one expected place wrong on purpose."

/-- What the places' names mean. -/
def legend : List String :=
  ["  -          the run went to the end: the answer is YES",
   "  par        the planner makes no plan for this chain from these sizes",
   "  front      a test before round 0: on the plan's first and last entries, or that every word",
   "             of the key's seeds, the view's items and its opened columns is below the prime",
   "  step0      round 0: the first point is drawn",
   "  step1      rounds 1 and 2: the folded row is sent and sampled; the record's rows",
   "  step2      round 3: positions are drawn; the stored table's columns are read",
   "  step3      rounds 4 and 5: the second message is sent and sampled",
   "  step4      round 6: the second point is drawn",
   "  step5      round 7: the claim is split between two groups of messages",
   "  testU      the proximity test on the first group",
   "  testOmega  the proximity test on the second group",
   "  seal       the last round; nothing may be left over"]

/-- One printed line. want is the expected place ("-" for YES). The answer and the place are
computed apart, and both are compared with want. Returns the line, whether the answer is yes, and
whether both are as expected. -/
def line (n want : String) (z : Params.ProofSized) (key : TableKey) (v : Fmt.View) :
    String × Bool × Bool :=
  let yes := descSharedZ z.set z.codes z.batch key v
  let at_ := endsAt z key v
  let ok := at_ == want && yes == (want == "-")
  (s!"{n}\t{if yes then "YES" else "no"}\tstopped at: {at_}\t{
    if ok then "as expected" else "NOT AS EXPECTED: EXPECTED " ++ want}", yes, ok)

/-- The print and the exit status for a folder. plant: see planted. -/
def run (dir : String) (plant : Bool) : IO UInt32 := do
  let F ← filesOf dir
  IO.println "The shared hash chain of a proof file: the decision, tried on a stored proof."
  IO.println "This is one of a proof file's three hash chains. It is no verdict on the proof."
  IO.println "This is a test run. Nothing is proved by it."
  IO.println usage
  if plant then
    IO.println "PLANTED: the first changed input expects a wrong place. The exit status must be 1."
  IO.println s!"folder\t{dir}"
  IO.println s!"bytes read\tpolicy | layout | KL | entry | request | reply | proof\t{[F.pol.size,
    F.lay.size, F.KL.size, F.ent.size, F.request.size, F.y.size, F.proof.size]}"
  match inputOf F with
  | .error e =>
    IO.println ("The input could not be made from the files. Refused by: " ++ e ++ ".")
    IO.println "Nothing was tried. Exit status 2."
    pure 2
  | .ok (z, key, v) =>
    IO.println s!"this chain\trounds | opened columns\t{[v.rounds.length, v.opened.length]}"
    IO.println ""
    IO.println "1. The stored proof, unchanged. The good answer is YES."
    let honest := line "the stored proof" "-" z key v
    IO.println honest.1
    IO.println ""
    IO.println "2. Changed inputs: one thing is changed in memory. The good answer at each is no."
    let ls := ((if plant then planted onView else onView).map fun (n, w, f) =>
        line n w z key (f v)) ++
      (onSizes.map fun (n, w, f) => line n w (f z) key v) ++
      (onKey.map fun (n, w, f) => line n w z (f key) v)
    for l in ls do
      IO.println l.1
    IO.println ""
    IO.println "Where a run can stop:"
    for l in legend do
      IO.println l
    IO.println ""
    let refused := (ls.filter (!·.2.1)).length
    let placed := (ls.filter (·.2.2)).length
    let good := honest.2.2 && placed == ls.length
    IO.println s!"Result\tthe stored proof: {if honest.2.1 then "YES" else "no"
      }\tchanged inputs refused: {refused} of {ls.length
      }\trefused at the expected place: {placed} of {ls.length}"
    IO.println (if good then "All lines are as expected. Exit status 0."
      else "Some line is NOT as expected: look for the words NOT AS EXPECTED. Exit status 1.")
    pure (if good then 0 else 1)

/-- The command for a folder. An input or output error, such as a file that cannot be read, gives
the exit status 2. -/
def command (dir : String) (plant : Bool) : IO UInt32 := do
  try
    run dir plant
  catch e =>
    IO.println ("Stopped by an input or output error: " ++ toString e ++ ". Exit status 2.")
    IO.println usage
    pure 2

/-- The command on its list of arguments: see the head for the arguments. -/
def entry (args : List String) : IO UInt32 :=
  match args with
  | [] => command "examples/accepted-proof" false
  | [dir] => command dir false
  | [dir, "--plant"] => command dir true
  | _ => do
    IO.println usage
    IO.println "The arguments were not understood. Exit status 2."
    pure 2

end Desc.Drive
