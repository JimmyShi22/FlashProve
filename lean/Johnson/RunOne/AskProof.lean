-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/AskProof.lean: the entry of the files of lean/Ask/ that run the compiled verifier of
the proof file's protocol, at the small size, on a proof file as an outside parser has laid it out.
Definitions with code, and their equations. Nothing is evaluated here.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Whose each input is. FROM THE USER: the three public parameter files, the request and the reply.
FROM THE PROVER: the entry file of the stored copy number 0 (its table's name is read, untested
here) and, THROUGH A PARSER THAT IS TRUSTED FOR NOTHING, the parsed proof file. Made here, of the
user's side and the table that the entry file names (Johnson/RunOne/ProofGround.lean): the plan and
the protocol's description; the instance: the request, and the record, whose seeds are drawn here.
NO INPUT: the commitment ID, the key file.
The hash O is an argument of every definition but `run`, which lays Fmt.oracle. The format's second
hash function is no argument: on the request file and on the public files it is a fixed function
here, never an oracle.

THE WHOLE ANSWER IS ONE DEFINITION: `verifyProofAskSmall O F k`: no where the ground is refused
(groundC, Johnson/RunOne/ProofGround.lean: the plan; its sizes against the small sizes; the
acceptance policy is exact match; the public values of a proof's first chain; the table's sizes; the
values that are used side by side fit each other; the record; the instance; three chains with
rounds); else five tests in front (the parsed file names the entry file's table, and the stored copy
number 0; the shared chain's run value is computed again; no run value is 32 zero bytes; five
digests have 32 bytes) and the term that judges. It is the "and" of its named parts
(`verifyProofAskSmall_parts`); `verifyProofAskSmallPartsT` is the same list in the form made for a
run (`verifyProofAskSmallPartsT_eq`). Behind the ground a run calls `bothAtT` once: the "and" of its
list is the whole answer (`answer_is`); where a test in front says no the whole answer is no
(`answer_no`), and the term is not made. `verifyProofAskBytes`: the same from the parsed file's
bytes: no where the reader refuses them.

The term that judges: `verifyProofSmall Z O k`: the guarded verdict along lists at the parsed file
and the binding tree's shape from the plan (verifyGuardCarrierAt,
OnBytes/Maker/ListedCarrierGuard.lean) at the proof file's values. By `verifyProofSmall_is` it is:
no where no proof string is laid of the parsed file (File.toBPrfAt,
OnBytes/Maker/CarrierTyping.lean); else the guarded verdict of the compiled verifier verifyOneProtocol
(verifyGuard, OnBytes/Maker/Page/GuardVerify.lean) at the description, the wire record and that very
string. The equation is for every Z. That the description and the wire record are the proof file's
is so at a ground that groundC makes, by groundC's text: no theorem says it. What is run is its
three parts (`partsOf`; partsCarrierAtT, Johnson/RunOne/GuardCarrierT.lean), in a form made for a
run: the test on queries by conditions (okJF), the oracle's answers as bytes first (famT), one
reading of the plain part a chain query (Lite.onceD), a round's draws off the blocks' bytes (ckPT):
each is the library's own by an equation without a premise; by `partsOf_yes` all three say yes
exactly where the term says yes.

Main names:
  `policyOf`: the kind of the acceptance policy in the user's parameter file, for the print.
  `verifyProofSmall`, `partsOf`, `partsOf_yes`, `verifyProofSmall_is`: see above.
  `Files`, `verifyProofAskSmall`, `verifyProofAskSmallParts`, `verifyProofAskSmallPartsT`,
    `bothAtT`, `verifyProofAskBytes`, `answer_is`, `answer_no`: above.
  `tell`: one run behind the ground, with its print.
  `run`: reads the variables and the files, makes the ground, runs the file as it lies, then one run
    for each turn of the parsed record or of the reply that it is handed (for a change of the reply
    the ground is made anew). It throws where ASK_PARSED is not set, a file cannot be read, the
    unchanged file gets no yes, or a change does not end as expected; not on a NO that is expected.
Limits: an evaluation of these is no theorem. The carrier of the typed oracles is hollow
(Johnson/RunOne/Hollow.lean), that of no theorem; the coding of typed queries into hash calls is
pageV's (Johnson/RunOne/ProofAt.lean), with part of its fields writing nothing. NOTHING TIES THE
TABLE TO A COMMITMENT ID HERE: the key file's and the entry file's parts of a verifier do that. The
seeds' queries are not asked: the record is made here. THE FIRST AND THE SECOND CHAIN's RUN VALUES,
which the parser gets by one hash call each on 32 random bytes of the proof file, ARE TAKEN AS THE
PARSED FILE GIVES THEM: the parsed file does not hold these bytes; in the compiled protocol the
values are a salt and a plain part that the prover sends. A parsed file that is bent at a field
which nothing reads (a digest of a path that the joint walk does not need, say) gets the same
answer. That `run` and `tell`, which are in IO, print what these definitions return is by their
texts: `run` matches on the ground and on the reader as verifyProofAskSmall and verifyProofAskBytes
do. The instance reaches the chain whole (xin := some). The number of blocks Kn is a letter of the
ground, at least what the rounds need; it is not the number at which the library's theorems on the
proof file stand. Nothing on soundness: in the library's theorems the soundness of the proof file's
description is a named hypothesis, and the description's own checks are written by hand after the
C++ verifier.
The program does not import this file.


-/
import Johnson.RunOne.AskShell
import Johnson.RunOne.ProofGround
import Johnson.RunOne.GuardCarrierT
import Johnson.RunOne.OnceD
import Johnson.RunOne.DrawT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.RunOne.Ask.Proof
open Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Compile hiding ON
open OnBytes.Flat Johnson.RunOne OnBytes.Maker _root_.Run
open OnBytes
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The name of the kind of the acceptance policy in the user's parameter file. -/
def policyOf (p : Model.Verify.Planned) : String :=
  Model.policyKind p.X.P.h.clipC p.X.P.h.theta p.X.P.h.cap p.X.P.h.logS p.X.P.h.digSh p.X.P.h.tabS

section At
variable (Z : GroundC)

/-- The carrier of the typed oracles: it holds what the verifier reads of one, and no more. -/
abbrev LAtP : BatchProtocolWithLeafBody Unit Yp := LAt Z.D Z.tF Z.tJ Z.rn (earlyS Z.A.p)

/-- How a symbol of a prover's oracle is written into a leaf's body. -/
def eS : (p : OPos (chainsOf Cs Z.D Z.tF Z.tJ ByteArray.empty).sh) →
    OSym (chainsOf Cs Z.D Z.tF Z.tJ ByteArray.empty).sh p → Body (LAtP Z) :=
  SCode.emb _ (scWhole (sbOf Z.A) Cs Z.D Z.tF Z.tJ ByteArray.empty)

/-- How a symbol of the stored table is written into a leaf's body. -/
def eE : _root_.Run.PQ.SgX → Body (LAtP Z) := (TypedOracleCompiler.Run.PQ.bodyS Z.D.a (sbOf Z.A)).embE

/-- The binding tree's shape, from the plan. -/
def shapeB : Params.LinBindingShape := Z.A.p.chains.proof.first.binding

/-- The coding of typed queries into the format's hash calls. -/
def pageOf (O : ByteArray → ByteArray) : Page.PageJ (LAtP Z) (Z.Kn + 1) :=
  pageV Z.D Z.tF Z.tJ Z.rn Z.Kn O Z.A

/-- What the calls of a chain query share, for a run: at the proof file's rows by one reading of the
plain part along the data (Lite.onceD, Johnson/RunOne/OnceD.lean). -/
def runOf (O : ByteArray → ByteArray) : RunJ (pageOf Z O) where
  key := onceJ (pageOf Z O).key
  proof := Lite.onceD Cs Z.D Z.tF Z.tJ ByteArray.empty
    (rdP Z.D Z.tF Z.tJ Z.rn (earlyS Z.A.p))
    (Page.silentProof (Fmt.HO O) Z.A.p.chains.proof (reqS Z.A.pol Z.A.KL))
  hk := fun _ => rfl
  hp := fun q => Lite.onceD_eq Cs Z.D Z.tF Z.tJ ByteArray.empty
    (rdP Z.D Z.tF Z.tJ Z.rn (earlyS Z.A.p))
    (Page.silentProof (Fmt.HO O) Z.A.p.chains.proof (reqS Z.A.pol Z.A.KL)) q

/-- **The term that judges**: the guarded verdict along lists at the parsed proof file. -/
def verifyProofSmall (O : ByteArray → ByteArray) (k : Carrier.File) : Bool :=
  verifyGuardCarrierAt (L := LAtP Z) Cs Z.Kn (chalP .two Z.Kn) Z.D Z.tF Z.tJ ByteArray.empty
    sil Z.rn (256 + 8 * sbOf Z.A) (8 * 32) .onl (eS Z) id some (eE Z) (shapeB Z) Z.cmsv Z.x k
    Z.A.p.cfg (frontC k) ⟨answersC k, k.run2⟩ k.run3 (pageOf Z O) O

/-- The letters of the term whose types hang on the kit C of challenge types. -/
structure KitLets (C : _root_.Run.PQ.CK) where
  chal : ∀ e k, (Fin Z.Kn → Dig 256) → C.Ch e k
  eS : (p : OPos (chainsOf C Z.D Z.tF Z.tJ ByteArray.empty).sh) →
    OSym (chainsOf C Z.D Z.tF Z.tJ ByteArray.empty).sh p → Body (LAtP Z)
  eP : PlainPart (chainsOf C Z.D Z.tF Z.tJ ByteArray.empty).sh
      (chainsOf C Z.D Z.tF Z.tJ ByteArray.empty).ann →
    PlainPart (shapeOf (LAtP Z) .onl) (TypedOracleCompiler.Compile.Batch.annOf (LAtP Z) .onl)

/-- The term's three parts at a kit and its letters. -/
def partsAt (O : ByteArray → ByteArray) (k : Carrier.File) (C : _root_.Run.PQ.CK)
    (A : KitLets Z C) : CarrierParts :=
  let bd := TypedOracleCompiler.Run.PQ.bodyS Z.D.a (sbOf Z.A)
  partsCarrierAtT (L := LAtP Z) C Z.Kn A.chal Z.D Z.tF Z.tJ ByteArray.empty sil Z.rn
    (256 + 8 * sbOf Z.A) (8 * 32) .onl A.eS A.eP some (fun s => bd.embE s) Z.cmsv Z.x k
    Z.A.p.cfg (frontC k) ⟨answersC k, k.run2⟩ k.run3 (pageOf Z O) (runOf Z O) O (shapeB Z)

/-- At two kits that are one, with the letters carried over, the parts are one. -/
theorem partsAt_cast (O : ByteArray → ByteArray) (k : Carrier.File) {C C' : _root_.Run.PQ.CK}
    (h : C = C') (A : KitLets Z C) : partsAt Z O k C' (h ▸ A) = partsAt Z O k C A := by
  subst h
  rfl

/-- The letters at the library's kit. What does not hang on a position is made once, here: the
rounds and the code of the leaves' bodies. -/
def letsOf : KitLets Z Cs :=
  let sh := (chainsOf Cs Z.D Z.tF Z.tJ ByteArray.empty).sh
  let sc := scWhole (sbOf Z.A) Cs Z.D Z.tF Z.tJ ByteArray.empty
  { chal := chalP .two Z.Kn, eS := fun q a => SCode.emb sh sc q a, eP := id }

/-- **Its three parts, for a run**: at the kit ckPT .two (Johnson/RunOne/DrawT.lean), which is the
library's kit ckP .two (ckPT_eq) with a round's draws read off the blocks' bytes: by the library's
own reading a round that draws very many entries does not end in any useful time. -/
def partsOf (O : ByteArray → ByteArray) (k : Carrier.File) : CarrierParts :=
  partsAt Z O k (ckPT .two) ((ckPT_eq .two).symm ▸ letsOf Z)

/-- **All three parts say yes exactly where the term says yes.** -/
theorem partsOf_yes (O : ByteArray → ByteArray) (k : Carrier.File) :
    (partsOf Z O k).yes = verifyProofSmall Z O k := by
  unfold partsOf
  rw [partsAt_cast]
  exact partsCarrierAtT_yes (L := LAtP Z) Cs Z.Kn (chalP .two Z.Kn) Z.D Z.tF Z.tJ
    ByteArray.empty sil Z.rn (256 + 8 * sbOf Z.A) (8 * 32) .onl (eS Z) id some (eE Z) Z.cmsv Z.x k
    Z.A.p.cfg (frontC k) ⟨answersC k, k.run2⟩ k.run3 (pageOf Z O) (runOf Z O) O (shapeB Z)

/-- **The term is the guarded verdict of the compiled verifier at the parsed file's string; no where
no proof string is laid of the parsed file.** -/
theorem verifyProofSmall_is (O : ByteArray → ByteArray) (k : Carrier.File) :
    verifyProofSmall Z O k =
      (k.toBPrfAt Cs Z.D Z.tF Z.tJ ByteArray.empty sil Z.rn Z.A.p.cfg (shapeB Z) (frontC k)
        ⟨answersC k, k.run2⟩ k.run3).elim false fun π =>
        Page.verifyGuard (L := LAtP Z) (pageOf Z O) O (256 + 8 * sbOf Z.A) (8 * 32) .onl
          (DscAt Z.D Z.tF Z.tJ Z.rn).batch (wqAt Z.D Z.tF Z.tJ Z.rn Z.Kn) (eS Z) id some
          (eE Z) (shapeB Z).logLeaves Z.cmsv Z.x π :=
  verifyGuardCarrierAt_is (L := LAtP Z) Cs Z.Kn (chalP .two Z.Kn) Z.D Z.tF Z.tJ
    ByteArray.empty sil Z.rn (256 + 8 * sbOf Z.A) (8 * 32) .onl (eS Z) id some (eE Z) (shapeB Z)
    Z.cmsv Z.x k Z.A.p.cfg (frontC k) ⟨answersC k, k.run2⟩ k.run3 (pageOf Z O) O

/-- The names of the parts of the whole answer. -/
def groundLine : String :=
  "ground: the plan, its sizes, the table's record and the claim can be made from the files"
def tableLine : String := "parsed file 1: it names the table that the entry file names"
def copyLine : String := "parsed file 2: its stored copy's number is 0"
def runTwoLine : String :=
  "parsed file 3: the shared chain's run value, computed here from the binding root, is the " ++
  "parsed file's"
def runsLine : String := "parsed file 4: none of the three run values is 32 zero bytes"
def lengthsLine : String :=
  "parsed file 5: its root, its three run values and the binding root have 32 bytes each"
def termLine : String :=
  "verifier: the guarded verdict of the compiled verifier at the proof in the parsed proof file"

/-- The names of the three parts of the term that judges; the third has two lines: has the guarded
run a value, and is it a yes. At this entry the line "guard" cannot say no: behind File.slotFits the
salt has the shape's number of bytes, which is the page's, and the leaf's number is laid by
File.toBPrf itself; it is a second lock, and part of the term that is cited. -/
def laidLine : String :=
  "proof form: the parsed proof file has the form of a proof of this protocol"
def fitLine : String :=
  "guard: the salt of the slot's leaf has the length that the format sets and ends in the " ++
  "leaf's number"
def valueLine : String :=
  "hash calls: every oracle query of the run has a hash call in the format"
def runLine : String := "run: the guarded run of the verifier"

/-- The five tests in front of the term. On the third and the fourth: in the format a chain's run
value is a hash (call 172, Fmt/Rules4.lean) of the digest of the chain's parameter bytes and 32 more
bytes: the binding tree's root at the shared chain, random bytes of the proof file at the two
others. The parsed file holds the three values and not the random bytes: so the shared chain's is
computed again here, under the label and the digest with which the page writes that chain's first
call, and THE TWO OTHERS ARE TAKEN AS THE PARSED FILE GIVES THEM. On the fifth: the reader of the
parsed file's bytes (Carrier.read) tests these lengths too; here they are asked of every record. -/
def tableOk (k : Carrier.File) : Bool :=
  k.root == Z.A.further.root && answersC k == Z.A.further.answers
def copyOk (k : Carrier.File) : Bool := decide (k.copy = 0)
def runTwoOk (O : ByteArray → ByteArray) (k : Carrier.File) : Bool :=
  decide (k.run2 = Fmt.HO O 172 0 (pageOf Z O).proof.lab₂ Fmt.zero32
    ((pageOf Z O).proof.pd₂ ++ k.bindRoot))
def runsOk (k : Carrier.File) : Bool := Fmt.runOk k.run1 && Fmt.runOk k.run2 && Fmt.runOk k.run3
def lengthsOk (k : Carrier.File) : Bool :=
  k.root.size == 32 && k.run1.size == 32 && k.run2.size == 32 && k.run3.size == 32 &&
    k.bindRoot.size == 32

/-- The tests in front of the term, each with its name. -/
def frontOf (O : ByteArray → ByteArray) (k : Carrier.File) : List (String × Bool) :=
  [(tableLine, tableOk Z k), (copyLine, copyOk k), (runTwoLine, runTwoOk Z O k),
    (runsLine, runsOk k), (lengthsLine, lengthsOk k)]

/-- The parts behind the ground; last: the value of the term that judges. -/
def partsWith (O : ByteArray → ByteArray) (k : Carrier.File) (last : Bool) :
    List (String × Bool) :=
  (groundLine, true) :: (frontOf Z O k ++ [(termLine, last)])

end At

/-- The files beside the parsed proof file. FROM THE USER: pol, lay, KL (the three public parameter
files), request, y (the reply), and blocks: the number of blocks of a chain's answer less two that
is asked for. FROM THE PROVER: ent, the entry file of the stored copy number 0. -/
structure Files where
  pol : ByteArray
  lay : ByteArray
  KL : ByteArray
  request : ByteArray
  y : ByteArray
  ent : ByteArray
  blocks : Nat

/-- What is made of the files. -/
def Files.ground (O : ByteArray → ByteArray) (F : Files) : Except String GroundC :=
  groundC O F.pol F.lay F.KL F.request F.y F.ent F.blocks

/-- **THE WHOLE ANSWER.** No where the ground is refused; else the tests in front and the term that
judges. NO INPUT: the commitment ID, the key file. -/
def verifyProofAskSmall (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) : Bool :=
  match F.ground O with
  | .error _ => false
  | .ok Z => ((frontOf Z O k).all fun x => x.2) && verifyProofSmall Z O k

/-- **Its parts**, each with its name. -/
def verifyProofAskSmallParts (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) :
    List (String × Bool) :=
  match F.ground O with
  | .error _ => [(groundLine, false)]
  | .ok Z => partsWith Z O k (verifyProofSmall Z O k)

/-- What a run makes behind the ground: the term's three parts, in the form made for a run, and the
parts of the whole answer with the last taken from them. One walk. -/
def bothAtT (Z : GroundC) (O : ByteArray → ByteArray) (k : Carrier.File) :
    CarrierParts × List (String × Bool) :=
  let p := partsOf Z O k
  (p, partsWith Z O k p.yes)

/-- **Its parts, for a run.** -/
def verifyProofAskSmallPartsT (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) :
    List (String × Bool) :=
  match F.ground O with
  | .error _ => [(groundLine, false)]
  | .ok Z => (bothAtT Z O k).2

/-- **The whole answer from the parsed file's bytes**: no where the reader refuses them. -/
def verifyProofAskBytes (O : ByteArray → ByteArray) (F : Files) (bytes : ByteArray) : Bool :=
  match Carrier.read Carrier.magicProof bytes with
  | .error _ => false
  | .ok k => verifyProofAskSmall O F k

/-- Named answers: a yes, a list, one more. -/
theorem all_parts (g t : String) (f : List (String × Bool)) (c : Bool) :
    (((g, true) :: (f ++ [(t, c)])).all fun x => x.2) = ((f.all fun x => x.2) && c) := by
  simp only [List.all_cons, List.all_append, List.all_nil, Bool.and_true, Bool.true_and]

/-- **The whole answer is the "and" of its parts.** -/
theorem verifyProofAskSmall_parts (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) :
    verifyProofAskSmall O F k = (verifyProofAskSmallParts O F k).all fun x => x.2 := by
  unfold verifyProofAskSmall verifyProofAskSmallParts
  cases F.ground O with
  | error _ => rfl
  | ok Z => exact (all_parts _ _ _ _).symm

/-- **The parts for a run are the parts.** -/
theorem verifyProofAskSmallPartsT_eq (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) :
    verifyProofAskSmallPartsT O F k = verifyProofAskSmallParts O F k := by
  unfold verifyProofAskSmallPartsT verifyProofAskSmallParts
  cases F.ground O with
  | error _ => rfl
  | ok Z => exact congrArg (partsWith Z O k) (partsOf_yes Z O k)

/-- **What a run prints behind the ground is the whole answer.** -/
theorem answer_is (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) (Z : GroundC)
    (h : F.ground O = .ok Z) :
    verifyProofAskSmall O F k = (bothAtT Z O k).2.all fun x => x.2 := by
  rw [verifyProofAskSmall_parts, ← verifyProofAskSmallPartsT_eq]
  unfold verifyProofAskSmallPartsT
  rw [h]

/-- **Where a test in front says no, the whole answer is no**: a run need not make the term. -/
theorem answer_no (O : ByteArray → ByteArray) (F : Files) (k : Carrier.File) (Z : GroundC)
    (h : F.ground O = .ok Z) (hf : ((frontOf Z O k).all fun x => x.2) = false) :
    verifyProofAskSmall O F k = false := by
  unfold verifyProofAskSmall
  rw [h]
  show (((frontOf Z O k).all fun x => x.2) && verifyProofSmall Z O k) = false
  rw [hf]
  rfl

/-- The second line after a yes. -/
def notTied : String :=
  "The table under this proof is the prover's word: not tied to your commitment ID here."

/-- The names, up to the colon, of the parts that say no. -/
def noesOf (l : List (String × Bool)) : List String :=
  (l.filter fun x => !x.2).map fun x => (x.1.splitOn ":").headD x.1

/-- The term's own three parts by name, as far as each was asked. -/
def beneathOf (p : CarrierParts) : List (String × Bool) :=
  if !p.laid then [(laidLine, false)]
  else if !p.fit then [(laidLine, true), (fitLine, false)]
  else
    match p.guarded with
    | none => [(laidLine, true), (fitLine, true), (valueLine, false)]
    | some b => [(laidLine, true), (fitLine, true), (valueLine, true), (runLine, b)]

/-- **One run behind the ground, with its print.** Where the tests in front say yes it calls bothAtT
once: the answer that it prints is the "and" of that list, which is the whole answer (answer_is).
Where one says no it does not make the term, and prints NO (answer_no). The term's own parts are
printed in front of its line, as commentary. The term is one evaluation: it prints nothing on its
way, and its whole time stands at the line "the verifier has run". It returns the parts, with the
term's own parts behind them, and the answer; where a test in front says no: the tests in front
alone, and no. -/
def tell (Z : GroundC) (clk : Clock) (O : ByteArray → ByteArray) (k : Carrier.File) :
    IO (List (String × Bool) × Bool) := do
  say clk (s!"parsed file: rounds {k.rounds1.length} | {k.rounds2.length} | {k.rounds3.length}; " ++
    s!"trees with rows {k.trees.length}; rows of the stored table {k.stored.length}")
  let front := frontOf Z O k
  say clk s!"{groundLine}: yes"
  for x in front do say clk s!"{x.1}: {yn x.2}"
  if !(front.all fun x => x.2) then
    say clk s!"{termLine}: not asked: a test in front says NO"
    say clk "ANSWER: NO"
    pure (front, false)
  else
    let r := bothAtT Z O k
    say clk s!"the verifier has run: one evaluation; {(beneathOf r.1).length} lines on it follow"
    for x in beneathOf r.1 do say clk s!"  {x.1}: {yn x.2}"
    say clk s!"{termLine}: {yn r.1.yes}"
    let a := r.2.all fun x => x.2
    say clk s!"ANSWER: {yn a}"
    if a then
      IO.eprintln notAVerification
      IO.eprintln notTied
    pure (r.2 ++ beneathOf r.1, a)

/-- **The entry.** The variables: ASK_EXAMPLE: the folder of a stored example
(../examples/accepted-proof if it is not set); ASK_PARSED: the parsed proof file; ASK_K: the number
of blocks of a chain's answer less two (what the rounds need if it is not set, and never less).
turns: after the file as it lies, one whole run for each: its words, the name up to the colon of a
part, or of a part of the term, that must say no (none: a yes is foretold), and the turn of the
parsed record, made in memory (none: the record has no place for it: that counts as a failure).
replies: the like on the user's side: a turn of the reply's bytes; the ground is made anew. It
throws where ASK_PARSED is not set, where a file cannot be read, where the ground is refused, where
the reader refuses the parsed file, where the file as it lies gets no yes, or a turn does not end as
foretold. -/
def run (turns : List (String × Option String × (Carrier.File → Option Carrier.File)))
    (replies : List (String × Option String × (ByteArray → Option ByteArray))) : IO Unit := do
  let clk : Clock ← IO.mkRef (← IO.monoMsNow)
  let O : ByteArray → ByteArray := Fmt.oracle
  let dir ← envOr "ASK_EXAMPLE" "../examples/accepted-proof"
  let asked := ((← IO.getEnv "ASK_K").bind String.toNat?).getD 0
  let some parsed ← IO.getEnv "ASK_PARSED"
    | throw (IO.userError ("set ASK_PARSED to the path of the parsed proof file; make that file " ++
        "with tools/parser/parse_files.sh (Ask/README.md)"))
  let rd (n : String) : IO ByteArray := IO.FS.readBinFile (dir ++ "/" ++ n)
  let pol ← rd "config/policy.txt"
  let lay ← rd "config/layout.txt"
  let KL ← rd "config/KL.bin"
  let request ← rd "example.req"
  let y ← rd "example.y"
  let ent ← rd "ivk/leaf/0.bin"
  let F : Files := ⟨pol, lay, KL, request, y, ent, asked⟩
  let bytes ← IO.FS.readBinFile parsed
  say clk (s!"read: {dir}: policy {F.pol.size} | layout {F.lay.size} | KL {F.KL.size} | request " ++
    s!"{F.request.size} | reply {F.y.size} | entry file {F.ent.size} bytes; {parsed}: " ++
    s!"{bytes.size} bytes")
  say clk ("verifier run: verifyProofAskSmall (Johnson/RunOne/AskProof.lean), part by part " ++
    "(answer_is, answer_no)")
  say clk ("theorem cited, not checked by this run: verifyProofSmall_is: the last part is the " ++
    "guarded verdict of the compiled verifier verifyBS at the proof in the parsed proof file")
  match F.ground O with
  | .error e =>
    say clk s!"{groundLine}: NO: {e}"
    say clk "ANSWER: NO"
    throw (IO.userError "the answer is NO")
  | .ok Z =>
  let D := Z.D
  say clk (s!"numbers: rounds in the three chains: {D.ds₁.length} | {D.ds₂.length} | " ++
    s!"{D.ds₃.length}; blocks needed: {blocksT .two (D.ds₁ ++ (D.ds₂ ++ D.ds₃))}; ASK_K = " ++
    s!"{Z.Kn}; bytes of an opening's salt {sbOf Z.A}; bytes of the slot's leaf's salt " ++
    s!"{sRof Z.A}; depth of the binding tree {(shapeB Z).logLeaves}; digests handed to the " ++
    s!"chain {Z.cmsv.length}; the acceptance policy: {policyOf Z.A.p}")
  match Carrier.read Carrier.magicProof bytes with
  | .error e =>
    say clk s!"parsed file: it cannot be decoded ({e}); make it again with tools/parser/"
    say clk "ANSWER: NO"
    throw (IO.userError "the answer is NO")
  | .ok k =>
  IO.eprintln "=== THE FILE UNCHANGED"
  let e ← tell Z clk O k
  unless e.2 do throw (IO.userError "the answer is NO")
  let mut all := true
  let mut n := 1
  for x in turns do
    IO.eprintln (s!"=== CONTROL {n}: {x.1}. EXPECTED: " ++
      (match x.2.1 with
        | some w => s!"NO, at \"{w}\""
        | none => "yes"))
    match x.2.2 k with
    | none =>
      say clk s!"CONTROL {n}: the parsed file has no place for this change: NOT AS EXPECTED"
      all := false
    | some k' =>
      let e ← tell Z clk O k'
      let ok := match x.2.1 with
        | some w => !e.2 && (noesOf e.1).contains w
        | none => e.2
      say clk (s!"CONTROL {n}: answer {yn e.2}; said no: {noesOf e.1}; " ++
        (if ok then "AS EXPECTED" else "NOT AS EXPECTED"))
      all := all && ok
    n := n + 1
  for x in replies do
    IO.eprintln (s!"=== CONTROL {n}: {x.1}. EXPECTED: " ++
      (match x.2.1 with
        | some w => s!"NO, at \"{w}\""
        | none => "yes"))
    match x.2.2 F.y with
    | none =>
      say clk s!"CONTROL {n}: the reply has no place for this change: NOT AS EXPECTED"
      all := false
    | some y' =>
      let e : List (String × Bool) × Bool ←
        match ({ F with y := y' } : Files).ground O with
        | .error w => do
          say clk s!"{groundLine}: NO: {w}"
          say clk "ANSWER: NO"
          pure ([(groundLine, false)], false)
        | .ok Z' => tell Z' clk O k
      let ok := match x.2.1 with
        | some w => !e.2 && (noesOf e.1).contains w
        | none => e.2
      say clk (s!"CONTROL {n}: answer {yn e.2}; said no: {noesOf e.1}; " ++
        (if ok then "AS EXPECTED" else "NOT AS EXPECTED"))
      all := all && ok
    n := n + 1
  unless all do throw (IO.userError "a control did not end as expected")

end Johnson.RunOne.Ask.Proof

#print axioms Johnson.RunOne.Ask.Proof.partsOf_yes
#print axioms Johnson.RunOne.Ask.Proof.verifyProofSmall_is
#print axioms Johnson.RunOne.Ask.Proof.verifyProofAskSmall_parts
#print axioms Johnson.RunOne.Ask.Proof.verifyProofAskSmallPartsT_eq
#print axioms Johnson.RunOne.Ask.Proof.answer_is
#print axioms Johnson.RunOne.Ask.Proof.answer_no
