-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/TestToyProof.lean: what the program's call `toy-proof` answers on one stored test batch
(OnBytes/Shell/ProofToyFiles.lean), and on copies of its files that are altered by a recipe here.

1. The batch as the tool wrote it: accepted. The tool writes it as honest.
2. The proof with one bit turned at the start of each part, and at its end, cut by a byte and with a byte more: refused.
3. Another reply, request, stored copy or claims file: refused.
4. The file that names the table. The record has eight answers. One answer turned, or the root, is refused at the first
   chain. A file cut inside the record is refused before the proof is read. So the call reads the record's answers.

Where the names come from. They are this library's own names for its checks: the test holds them fast. The yes comes from
the tool, which writes these files as honest.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. Nothing on the compiled program: these run under Lean's evaluator when the file compiles. Nothing
on soundness, completeness or hiding.
-/
import OnBytes.Shell.Toys
import OnBytes.Shell.ProofToyFiles

namespace OnBytes.ShellTest.ToyProof

open OnBytes.Shell
open OnBytes.Shell.ProofToy

/-- A verdict in a word: "yes", or the refusal's name. -/
def said : Verdict → String
  | .accepted => "yes"
  | .refused r => r.check

/-- What the call says, at the batch's files but for those named. -/
def proofSaid (file : ByteArray := proof) (table : ByteArray := keyHead) (number : String := "0")
    (rq : ByteArray := request) (rp : ByteArray := reply) (cl : ByteArray := claims) : String :=
  said (toyProof 128 publicOne publicTwo table number rq rp cl file)

/-- A copy with the lowest bit of byte i turned. -/
def turned (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b.get! i ^^^ 1)

-- the record has eight answers
#guard (match Plan.toyForProofs publicOne publicTwo 128 with
  | .ok c => Proof.toyAnswers c.first c.shared c.second
  | .error _ => 0) == 8

-- the batch as the tool wrote it
#guard proofSaid == "yes"

-- the proof, altered
#guard [0, 12, 165332, 165444, 452380, proof.size - 1].map (fun i => proofSaid (turned proof i)) ==
  ["file-of-another-kind", "first-chain-reader-work", "shared-chain-reader-work",
   "shared-chain-reader-work", "second-chain-reader-work", "second-chain-reader-opening"]
#guard proofSaid (proof.extract 0 (proof.size - 1)) == "second-chain-reader-form"
#guard proofSaid (proof.push 0) == "bytes-left-over"

-- the other files
#guard proofSaid (rp := "1002 0 0\n".toUTF8) == "first-chain-decision-reply"
#guard proofSaid (rp := "1001 0 0".toUTF8) == "reply-spelling"
#guard proofSaid (number := "1") == "made-on-another-stored-copy"
#guard proofSaid (number := "x") == "stored-copy-number"
#guard proofSaid (rq := turned request 0) == "first-chain-reader-work"
#guard proofSaid (cl := turned claims 0) == "claims-forms"
#guard proofSaid (cl := turned claims (claims.size - 1)) == "second-chain-decision-linear-claim"

-- the file that names the table
#guard keyHead.size == 232
#guard proofSaid (table := turned keyHead 12) == "first-chain-reader-work"
#guard proofSaid (table := turned keyHead 48) == "first-chain-reader-work"
#guard proofSaid (table := turned keyHead 0) == "table-file-head"
#guard proofSaid (table := keyHead.extract 0 231) == "table-file-head"

end OnBytes.ShellTest.ToyProof
