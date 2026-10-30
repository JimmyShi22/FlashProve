-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskAll.lean: one term that runs the checks of the key file, of the entry file and of
the proof file in a row, each on the form in which an outside parser has laid the file out, at the
small size, with the tests that join them to one commitment ID; its parts; and the entries that
evaluate it and print them. Definitions; they have code. Nothing is evaluated here.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Whose each input is. The user's (User): the three public parameter files, the commitment ID as text,
the request and the reply. The prover's, through an untrusted parser (Given): the parsed key file,
the parsed leaf file (this library's "entry file") and the parsed proof file, as bytes; and the
original leaf file, of which the proof file's check makes its record. Whoever starts the run: the
hash H.

The three joins.
  join 1, the user's commitment ID against the key file's table: it is a test in front of the key
    file's verifier (claim 3 of Johnson/RunOne/AskKey.lean), and the entry file's check makes it
    again (OnBytes/ShellOf/EntryJoin.lean).
  join 2, the key file's table against the first table of the entry file: the entry file's check
    takes its first table out of the same parsed key file, by its own reader: what ties that table
    to the one at which the key file's check judges is the part "read 4". The part "join 2" compares
    the parsed leaf file's own copy of the first table, at which no check judges; the entry file's
    reader refuses where that copy differs, too.
  join 3, the entry file's further table against the table that the proof file names: the part
    "join 3" here (furtherIs, OnBytes/ShellOf/EntryJoin.lean).
Two readers, written apart, read the parsed key file and the parsed proof file (Carrier.read,
OnBytes/Maker/Carrier.lean; rdKeyHead and rdProofHead, OnBytes/ShellOf/): the parts "read 4" and
"read 5" test that both give one table.

Main names.
  testsWith keyEnd proofEnd H U G: the ten tests in their order, each behind a thunk, with the key
    file's and the proof file's checks as letters.
  verifyAllAskSmall H U G : Bool: THE ONE TERM: all ten, at verifyKeyAskSmall
    (Johnson/RunOne/AskKey.lean) and verifyProofAskSmall (Johnson/RunOne/AskProof.lean). A term to
    prove things of; what runs is verifyAllAskRun.
  verifyAllAskSmallParts H U G: its parts, by name.
  verifyAllAskRun H U G : Bool: the same at the two checks' forms that run.
  tellAll: the tests one by one up to the first no, with a print. runAll: the entry, with controls
    that change the files in memory. runRows: a second entry, for sets of whole files.
The laws: Johnson/RunOne/AskAllLaws.lean, AskAllYes.lean, AskAllLink.lean, AskAllCopy.lean.

Limits. Those of the three checks, each in its own file's head; among them: the run values of the
first and third chains of the key file and of the proof file, and the link chain's, are taken as the
parsed files give them. The numbers of blocks are no input: each check is run at what its rounds
need. So the key file's test "plan 6" (that the number suffices) holds by the way the number is
made; the proof file's check takes the number itself. Which test inside a check has said no is not
printed here: that check's own asking file prints it.
H is an argument of the term, but not every hash beneath it is H. The planner beneath the checks
computes digests of public data by a fixed function (the head of Johnson/RunOne/AskKey.lean), and
the proof file's check makes the request's item by the second hash function, a fixed function too
(the head of Johnson/RunOne/ProofAt.lean). The entry file's reader (parseP,
OnBytes/ShellOf/EntryParsed.lean; untrusted) makes the public files' digest and draws the two
tables' seeds through H. The entry file's part calls H through oBO (OnBytes/ShellOf/EntryProg.lean:
H's answer laid as 256 bits), the two other checks through Fmt.HO: one function only where H answers
32 bytes.
The number of the stored copy in the parsed proof file is held against the number in the leaf file's
name by nothing; the proof file's check asks that it is 0, and the entries read ivk/leaf/0.bin. Of
the original leaf file the proof file's check takes one table's name (TieK.furtherOf) and nothing
else; that file is held to the parsed leaf file through the proof file's table alone (the proof
file's check compares that table with the one off the original leaf file; "join 3" compares it with
the parsed leaf file's further table).
The ten tests tie the tables' names (root and answers). The seeds of a table's record are drawn
three times, by each check under its own link (the key file's and the entry file's: the library's
small ground at the public files' digest; the proof file's: the plan's own): no test here compares
these links; all of them are made of the user's three files and the library. Where a commitment ID
is computed the first table's seeds are drawn again.
An evaluation is no theorem. Nothing on time or memory. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.AskKeyLaws
import Johnson.RunOne.AskProof
import OnBytes.ShellOf.EntryJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Ask.All
open OnBytes OnBytes.Maker _root_.Run
open OnBytes.ShellOf.EntryParsed (rdLeaf rdKeyHead yesSmallP rdProofHead furtherIs)

/-- What the user hands over. -/
structure User where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  /-- the commitment ID, as text -/
  id : String
  request : ByteArray
  y : ByteArray

/-- What comes from the prover's side. -/
structure Given where
  /-- the parsed key file -/
  key : ByteArray
  /-- the parsed leaf file -/
  leaf : ByteArray
  /-- the parsed proof file -/
  proof : ByteArray
  /-- the original leaf file -/
  ent : ByteArray

/-- The user's side of the key file's check. -/
def keyUser (U : User) : Key.User := ⟨U.pol, U.lay, U.KL, U.id⟩

/-- The files of the proof file's check. The number of blocks 0: its ground takes what the rounds
need. -/
def proofFiles (U : User) (G : Given) : Proof.Files :=
  ⟨U.pol, U.lay, U.KL, U.request, U.y, G.ent, 0⟩

/-- What the rounds of the key file need: the number of blocks for its check; 0 where no plan is
made (the check then says no at its first test). -/
def keyNeed (H : ByteArray → ByteArray) (U : User) : Nat :=
  match Key.groundOf H U.pol U.lay U.KL with
  | .ok Z => OnBytes.Flat.blocksT .two (Z.D.ds₁ ++ (Z.D.ds₂ ++ Z.D.ds₃))
  | .error _ => 0

/-- A parsed file's table in the form in which rdKeyHead and rdProofHead give it. -/
def headOf (k : Carrier.File) : ByteArray × List OnBytes.E :=
  (k.root, k.answers.map OnBytes.E.ofTriple)

/-- **The ten tests, in their order**, each behind a thunk. keyEnd, proofEnd: the key file's and the
proof file's checks. -/
def testsWith (keyEnd proofEnd : Carrier.File → Bool) (H : ByteArray → ByteArray) (U : User)
    (G : Given) : List (String × Thunk Bool) :=
  let kk := (Carrier.read Carrier.magicKey G.key).toOption
  let kp := (Carrier.read Carrier.magicProof G.proof).toOption
  let L := rdLeaf G.leaf
  let hK := rdKeyHead G.key
  let hP := rdProofHead G.proof
  [("read 1: the parsed key file can be read", Thunk.mk fun _ => kk.isSome),
    ("read 2: the parsed leaf file can be read", Thunk.mk fun _ => L.isSome),
    ("read 3: the parsed proof file can be read", Thunk.mk fun _ => kp.isSome),
    ("read 4: both readers of the parsed key file give one table",
      Thunk.mk fun _ => hK.isSome && decide (hK = kk.map headOf)),
    ("read 5: both readers of the parsed proof file give one table",
      Thunk.mk fun _ => hP.isSome && decide (hP = kp.map headOf)),
    ("join 2: the first table in the parsed leaf file is the parsed key file's table",
      Thunk.mk fun _ => match hK, L with
        | some K, some l => decide (K.1 = l.root0) && decide (K.2 = l.answers0)
        | _, _ => false),
    ("join 3: the further table in the parsed leaf file is the table that the parsed proof " ++
        "file names", Thunk.mk fun _ => furtherIs G.leaf G.proof),
    ("key: the key file's check, with join 1: the commitment ID computed from its table is the " ++
        "user's", Thunk.mk fun _ => kk.elim false keyEnd),
    ("entry: the entry file's check from the first table to the further table, under the " ++
        "user's commitment ID",
      Thunk.mk fun _ => yesSmallP H U.id ⟨U.pol, U.lay, U.KL⟩ G.key G.leaf),
    ("proof: the proof file's check", Thunk.mk fun _ => kp.elim false proofEnd)]

/-- **THE ONE TERM.** -/
def verifyAllAskSmall (H : ByteArray → ByteArray) (U : User) (G : Given) : Bool :=
  (testsWith (Key.verifyKeyAskSmall (keyNeed H U) H (keyUser U))
    (Proof.verifyProofAskSmall H (proofFiles U G)) H U G).all fun x => x.2.get

/-- Its parts, by name. -/
def verifyAllAskSmallParts (H : ByteArray → ByteArray) (U : User) (G : Given) :
    List (String × Bool) :=
  (testsWith (Key.verifyKeyAskSmall (keyNeed H U) H (keyUser U))
    (Proof.verifyProofAskSmall H (proofFiles U G)) H U G).map fun x => (x.1, x.2.get)

/-- The tests in the form that runs. -/
def testsRun (H : ByteArray → ByteArray) (U : User) (G : Given) : List (String × Thunk Bool) :=
  testsWith (Key.verifyKeyAskRun (keyNeed H U) H (keyUser U))
    (fun k => (Proof.verifyProofAskSmallPartsT H (proofFiles U G) k).all fun x => x.2) H U G

/-- **The one term in the form that runs.** -/
def verifyAllAskRun (H : ByteArray → ByteArray) (U : User) (G : Given) : Bool :=
  (testsRun H U G).all fun x => x.2.get

/-- The text of a test's name up to its colon. -/
def shortOf (s : String) : String := (s.splitOn ":").headD s

/-- One set of files: the tests one by one, up to the first no, with a print. It returns the lines.
-/
def tellAll (clk : Clock) (H : ByteArray → ByteArray) (U : User) (G : Given) :
    IO (List (String × Bool)) := do
  say clk ("verifier run: verifyAllAskRun (Johnson/RunOne/AskAll.lean), test by test, up to the " ++
    "first NO")
  say clk ("theorems cited, not checked by this run: verifyAllAskRun_eq, upToNo_all, " ++
    "verifyAllAskSmall_parts (Johnson/RunOne/AskAllLaws.lean, AskKeyLaws.lean): what these " ++
    "tests answer together is the value of verifyAllAskSmall")
  let mut out : List (String × Bool) := []
  for x in testsRun H U G do
    let b := x.2.get
    say clk s!"{x.1}: {yn b}"
    out := out ++ [(x.1, b)]
    unless b do break
  let a := out.all fun x => x.2
  say clk s!"ANSWER (all ten tests): {yn a}"
  if a then say clk notAVerification
  pure out

/-- The files of one set, from a folder and three paths. -/
def readSet (dir key leaf proof : String) : IO (User × Given) := do
  let rd (n : String) : IO ByteArray := IO.FS.readBinFile (dir ++ "/" ++ n)
  let U : User := ⟨← rd "config/policy.txt", ← rd "config/layout.txt", ← rd "config/KL.bin",
    trimmed (← IO.FS.readFile (dir ++ "/ID.txt")), ← rd "example.req", ← rd "example.y"⟩
  let G : Given := ⟨← IO.FS.readBinFile key, ← IO.FS.readBinFile leaf,
    ← IO.FS.readBinFile proof, ← rd "ivk/leaf/0.bin"⟩
  pure (U, G)

/-- How a control has ended: the names, up to the colon, of the tests that said no; and whether that
is what was expected (none: a yes). -/
def judged (expect : Option String) (o : List (String × Bool)) : List String × Bool :=
  let noes := (o.filter fun x => !x.2).map fun x => shortOf x.1
  (noes, match expect with
    | some w => noes == [w]
    | none => noes.isEmpty)

/-- The closing words of a control. A yes where a no was expected has a line of its own. -/
def markOf (expect : Option String) (j : List String × Bool) : String :=
  if j.2 then "AS EXPECTED"
  else if expect.isSome && j.1.isEmpty then
    "ALARM: A YES WHERE A NO WAS EXPECTED: changed files were accepted"
  else "NOT AS EXPECTED"

/-- The words of what is expected. -/
def expectLine : Option String → String
  | some w => s!"NO, at \"{w}\""
  | none => "yes"

/-- A variable of the environment that must be set. -/
def wantEnv (v what : String) : IO String := do
  let some p ← IO.getEnv v
    | throw (IO.userError s!"set {v} to the path of {what} (Ask/README.md)")
  pure p

/-- **The entry.** The variables of the environment: ASK_EXAMPLE: the folder of a stored example
(../examples/accepted-proof if it is not set); ASK_PARSED_KEY, ASK_PARSED_LEAF, ASK_PARSED_PROOF:
the three parsed files, made with tools/parser/. turns: the controls: a name; the name, up to its
colon, of the test that is expected to say NO (none: a yes is expected); what is changed, in memory.
It throws where the unchanged files get no yes, or a control does not end as expected. -/
def runAll (turns : List (String × Option String × (User × Given → User × Given))) :
    IO Unit := do
  let clk : Clock ← IO.mkRef (← IO.monoMsNow)
  let H : ByteArray → ByteArray := Fmt.oracle
  let dir ← envOr "ASK_EXAMPLE" "../examples/accepted-proof"
  let key ← wantEnv "ASK_PARSED_KEY" "the parsed key file"
  let leaf ← wantEnv "ASK_PARSED_LEAF" "the parsed leaf file"
  let proof ← wantEnv "ASK_PARSED_PROOF" "the parsed proof file"
  let (U, G) ← readSet dir key leaf proof
  say clk (s!"read: {dir}; {key}: {G.key.size} bytes; {leaf}: {G.leaf.size} bytes; {proof}: " ++
    s!"{G.proof.size} bytes")
  IO.eprintln "=== THE FILES UNCHANGED"
  let out ← tellAll clk H U G
  unless out.all fun x => x.2 do throw (IO.userError "the unchanged files did not get a yes")
  let mut all := true
  let mut n := 1
  for r in turns do
    IO.eprintln s!"=== CONTROL {n}: {r.1}. EXPECTED: {expectLine r.2.1}"
    let (U', G') := r.2.2 (U, G)
    let j := judged r.2.1 (← tellAll clk H U' G')
    say clk s!"CONTROL {n}: said no: {j.1}; {markOf r.2.1 j}"
    all := all && j.2
    n := n + 1
  unless all do throw (IO.userError "a control did not end as expected")

/-- **A second entry, for sets of whole files.** ASK_ROWS: a folder. rows: a name; what is expected,
as in runAll; a folder under ASK_ROWS that holds a whole set: config/, ID.txt, example.req,
example.y, ivk/leaf/0.bin, key.parsed.bin, proof.parsed.bin and leaf-0.parsed.bin (or, where that is
not there, leaf-1.parsed.bin). A row whose files cannot be read is void and counts as not as
expected. Where a set that is expected to get a yes gets a no, the run stops there: the later rows
would say nothing. It throws where a row does not end as expected. -/
def runRows (rows : List (String × Option String × String)) : IO Unit := do
  let clk : Clock ← IO.mkRef (← IO.monoMsNow)
  let H : ByteArray → ByteArray := Fmt.oracle
  let base ← wantEnv "ASK_ROWS" "the folder of the sets"
  let mut all := true
  for r in rows do
    IO.eprintln s!"=== ROW {r.1}: {r.2.2}. EXPECTED: {expectLine r.2.1}"
    let d := base ++ "/" ++ r.2.2
    let l0 := d ++ "/leaf-0.parsed.bin"
    let lf := if (← System.FilePath.pathExists l0) then l0 else d ++ "/leaf-1.parsed.bin"
    match ← (readSet d (d ++ "/key.parsed.bin") lf (d ++ "/proof.parsed.bin")).toBaseIO with
    | .error e =>
      say clk s!"ROW {r.1}: VOID: its files cannot be read ({e})"
      all := false
    | .ok (U, G) =>
      let j := judged r.2.1 (← tellAll clk H U G)
      say clk s!"ROW {r.1}: said no: {j.1}; {markOf r.2.1 j}"
      all := all && j.2
      if r.2.1.isNone && !j.2 then
        throw (IO.userError s!"row {r.1}: a set that was expected to get a yes got a no")
  unless all do throw (IO.userError "a row did not end as expected")

end Johnson.RunOne.Ask.All
