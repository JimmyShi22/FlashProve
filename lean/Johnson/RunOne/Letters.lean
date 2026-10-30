-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Letters.lean: the proof file's reading at the hash over an oracle O, with the user's
side and the parser's side apart.
"The twin" of a routine of the program verify-on-bytes is that routine written once more with the
hash as an argument (OnBytes/ChecksWithHashAsArgument/M/).

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

THE USER's SIDE (`Claim`, `claimOf`): made of the three public files, the request and the reply
alone: the planner's twin's return at `Fmt.HO O`; the request's item (the second hash function: the
program's own, a fixed function); the request file's own bytes (`words`: the fourth item of the
first chain's statement); the reply; the model's links; the first chain's block. The text is that of
the clause on the proof file in `K.PortYesAtG` (OnBytes/K/TopG.lean), but for that clause's letter
hr, which is the program's own function here.
Of the planner's twin one call alone goes to O: the digest of the three public files. Inside it the
program's own `publicOf` still hashes public files with the programs' second hash function, a fixed
function whatever O is (the head of OnBytes/K/TopG.lean counts the places).
THE PARSER's SIDE (`parseAt`): reads what the prover sends, the entry file and the proof file: the
entry file's table by the program's own readers, untested (`TieK.furtherOf`); the proof file's three
chains by `readProofChainsG (Fmt.HO O)` at the claim's letters. Nothing of the claim is taken from
it.
This reader does more than cut the file up: it is the whole reader of the program verify-on-bytes,
at the hash. It recomputes the three chains, tests the proof of work, holds the file's positions
against the drawn ones (where the plan lists positions), walks every Merkle opening up to its root,
and returns nothing where one of these fails; of the program's check only the arithmetic decision is
left out. So a refusal of a file with a damaged byte is nearly always this reader's, and a verifier
that stands behind it is then never reached.
Each returns the name of the step that refused. Nothing is proved here.
Not here: the user's commitment ID; the test that request and reply are whole words (the program
makes it in `requestRun`, OnBytes/Model/VerifyStages.lean); any bound on the files' sizes; the
checks of the key file and the entry file. Nothing on soundness.


-/
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify
import OnBytes.TieK.G.ProofDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne

open OnBytes OnBytes.Proof OnBytes.TwoPort OnBytes.TieK OnBytes.TieK.G

/-- What is made of the user's own files. -/
structure Claim where
  p : Model.Verify.Planned
  item : ByteArray
  /-- the request file's own bytes, as the user handed them to `claimOf` -/
  words : ByteArray
  reply : E
  links : Blk LinksResult
  block : Blk FirstEnd

/-- The claim, made as the program's call makes it, but for the test on whole words (see the head),
the format's hash over O. -/
def claimOf (O : ByteArray → ByteArray) (pol lay KL request y : ByteArray) : Except String Claim :=
  match ((M.Model.Verify.planned (m := Id) (Fmt.HO O) pol KL (some lay)).run :
      Except String Model.Verify.Planned) with
  | .error e => .error ("the planner: " ++ e)
  | .ok p =>
    match Model.Head.stFromCall (Model.Verify.words32 request) (Model.Verify.words32 y) p.X.T with
    | .error e => .error ("request and reply: " ++ e)
    | .ok so =>
      match Model.Head.coveredOf so p.X.T p.X.P.h.V with
      | .error e => .error ("the covered positions: " ++ e)
      | .ok cov =>
        match Proof.requestItem pol KL request with
        | none => .error "the request's item"
        | some item =>
          match Model.Verify.linksOf p.X cov with
          | .error e => .error ("the links: " ++ e)
          | .ok links =>
            let lk := Model.Stages.runLinksH
              (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
              p.chains.proof.first p.X.layers.wsLay
            let reply := Model.ofNat so.y
            .ok ⟨p, item, request, reply, lk, firstBlock p.chains.proof.first lk reply⟩

/-- The parser's first half: the entry file's table and the proof file's three chains. entry: the
number of the stored copy, which the caller hands in. In the program it is the number that the proof
file's own head names (`cpProofHead`, OnBytes/Model/VerifyHeads.lean): the prover's, not the user's.
-/
def parseAt (O : ByteArray → ByteArray) (c : Claim) (entry : Nat) (ent proof : ByteArray) :
    Except String (Params.TableName × ChainsData) :=
  match furtherOf c.p.chains.link ent with
  | none => .error "the entry file's table"
  | some further =>
    match readProofChainsG (Fmt.HO O) c.p.chains.proof further entry c.item c.words c.block
        proof with
    | none => .error "the reading of the proof file returns nothing"
    | some d => .ok (further, d)

end Johnson.RunOne
