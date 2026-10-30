-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TailAns.lean: a CLOSED function of a root and of a table's answers, in which no record
stands; and that, WHERE the test on the silent rounds says yes, it is the list that a proof file's
verifier with `codeA` for its code of answers lays behind the first of its outer roots (the list is
read off `cmsBA`; no statement here names a verifier).

THE LETTERS MEET; THIS IS NO TIE. One definition, two statements with their proofs.

Why. The test on a proof file's first query (`fFrontP`, OnBytes/Maker/Page/FitSilent.lean) holds a
letter tl: the outer roots behind the first, from the first and from the answers that the front
message bears. tl stands in the test, so in the cut, so in the proof file's encoding: it has to be
fixed before any call. The verifier lays there the root once more and the code of the ANSWERS OF THE
RECORD at which it is called (`cmsBA`, Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean). So a law is owed that
ties the record's answers to the table's (`hrest` in Johnson/Top/FrontSet.lean).
Here it is had from the verifier's own test on the silent rounds: that test says yes only where the
front message's answers are the record's, in the program's order; and the written code of a record's
answers is that list, element by element (`codeA_key`, OnBytes/Flat/RecordCode.lean).

  `tlAns c₀ ans`     c₀, then each answer as a digest (`digW`).
  `tlAns_of_key`     at a record whose key's array is the list ans: c₀ :: codeA (the record's
                     answers) is `tlAns c₀ ans`.
  `tlAns_of_silP`    the same where the proof file's test on the silent rounds (`silP`,
                     OnBytes/Flat/FilesAt.lean) says yes at the record and a front message.

Not claimed. That the silent rounds' test says yes at any call: not shown here. That any program
hashes this list. Nothing on soundness.

-/
import OnBytes.Flat.FilesAt
import OnBytes.Flat.RecordCode

set_option autoImplicit false

namespace OnBytes.Flat
open OnBytes.Slice OnBytes.Maker _root_.Iop

/-- The first outer root once more, then each of the table's answers as a digest. -/
def tlAns (c₀ : Dig 256) (ans : List OnBytes.E) : List (Dig 256) := c₀ :: ans.map digW

variable {v lg s : ℕ}

/-- At a record whose key's array is the list of answers. -/
theorem tlAns_of_key {B : Type} (val : B → GE) (r : RecP B v lg s) (c₀ : Dig 256)
    (ans : List OnBytes.E) (h : (keyOf val r).record.toList = ans) :
    c₀ :: codeA r.2 = tlAns c₀ ans := by
  rw [codeA_key val r, h]
  rfl

/-- **Where the proof file's test on the silent rounds says yes**: `c₀ :: codeA` (the record's
answers), which is what a verifier with `codeA` for its code of answers lays behind the first outer
root (`cmsBA`, Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean), is `tlAns` of that root and the front message's
answers. -/
theorem tlAns_of_silP {X : Type} (z : X × RecP NZ v lg s) (f : FrontMsg (List OnBytes.E))
    (j : _root_.Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t : ByteArray)
    (h : silP z f j t = true) (c₀ : Dig 256) : c₀ :: codeA z.2.2 = tlAns c₀ f.answers := by
  refine tlAns_of_key (fun β : NZ => β.val) z.2 c₀ f.answers ?_
  rw [(silP_answers z f j t h).1]
  unfold ansL
  rfl

end OnBytes.Flat

#print axioms OnBytes.Flat.tlAns_of_key
#print axioms OnBytes.Flat.tlAns_of_silP
