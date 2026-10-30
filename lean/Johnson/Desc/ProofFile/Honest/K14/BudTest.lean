-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudTest.lean: A PUBLIC TEST, WITH CODE: for each message of a
sending: a count at its tree's number is at most the encoding randomness r of the code of its main
rows, and of its mask rows. One definition; no statement. No kind is named.

  countsWithinB cnt j₀ codes sent   cnt: a count, by a tree's number over the file · j₀: the number
                  over the file of the sending's first tree · codes, sent: the sending's codes and
                  notices. It accepts at a message that lies in no tree, and wherever the trees
                  cannot be laid

Kin: a like test stands at the count by sources (readsWithinAtB at drawnForAt, in the files on the
simulator of a sending); this one takes the count as an argument, so that it can be evaluated at the
library's short lists of what a file's rounds open (E2E/TreeReadsAtWritten.lean).
-/
import Johnson.Desc.Own.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- **The test**: at each message's tree the count is within r of each sort of row that the message
has. -/
def countsWithinB (cnt : Nat → Nat) (j₀ : Nat) (codes : OnBytes.Codes)
    (sent : Array OnBytes.OracleNotice) : Bool :=
  (List.range sent.size).all fun k =>
    match ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).tree[k]? with
    | none => true
    | some τ =>
      ((sent.getD k default).shape.mainRows == 0 ||
          decide (cnt (j₀ + τ) ≤ (codes.base.getD (sent.getD k default).shape.code default).r)) &&
        ((sent.getD k default).shape.maskRows == 0 ||
          decide (cnt (j₀ + τ) ≤
            (codes.mask.getD (sent.getD k default).shape.maskCode default).r))

end ProofFile.Honest.K14
