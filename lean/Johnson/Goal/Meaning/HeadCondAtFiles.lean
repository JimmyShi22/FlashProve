-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadCondAtFiles.lean: the premises on public numbers that the laws on the
output head's own rounds and on the next token ask, at the two named sets of public files: the
stored full-size example (VerifierAndGoals.storedPublicFiles) and the same files with the second policy (VerifierAndGoals.zGap).

What the file holds.
  HeadPublic X    one record of what Johnson/Goal/Meaning/HeadCondScope.lean shows of a public part
                  X: K06CondAt X, all eighteen fields; the reference model's sizes; the two tests on
                  the plan; that a lot's seated block is there and passes its own test on the plan,
                  at every link's number and list of messages; the same of the next token's block.
  head_in_scope   HeadPublic X at all public files in the goals' scope.
  head_at_full    **whatever publicOf returns on the stored full-size files has HeadPublic.**
  head_at_gap     the same at the second named set.
The last two have ONE premise: that publicOf returns X on the named files, with or without the
layout file. That these files are in scope and that the goals' reader returns on them is a theorem:
VerifierAndGoals.filesRead (Johnson/Goal/Files/FilesReadProof.lean).

What it does not give. THAT publicOf RETURNS ON THE NAMED FILES IS NO THEOREM: it is held by an
evaluation alone (a #guard in Johnson/Goal/Meaning/ScopeRun.lean). Where it did not return, the last
two theorems would say nothing. The named files are the bytes written in Ladder/Stored.lean: that
they are the bytes of the repository's folder examples/ is not said. Nothing on soundness: these are
premises of laws, not the laws; that the list of premises is complete is not shown.

-/
import Johnson.Goal.Files.FilesReadProof
import Johnson.Goal.Meaning.HeadCondScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- What is shown of a public part. -/
structure HeadPublic (X : Public) : Prop where
  cond : Cond.K06CondAt X
  ref : Cond.K06Ref X.hS
  ok : ∀ w, (parOf X.hS w).ok = true
  laid : laidOk X = true
  there : ∀ l ms, (seatedClaims X l ms).isSome = true
  seated : ∀ l ms (b : Block S Claim), seatedClaims X l ms = some b → b.planOk = true
  reply : ∀ l, (Reply.blockOf X l).planOk = true

theorem head_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : HeadPublic X where
  cond := k06Cond_in_scope hZ hR h
  ref := k06Ref_in_scope hZ hR h
  ok := ok_in_scope hZ hR h
  laid := laidOk_in_scope hZ hR h
  there := there_in_scope h
  seated := fun _ _ _ hb => seated_in_scope hZ hR h hb
  reply := reply_in_scope hZ hR h

/-- **At the stored full-size files.** -/
theorem head_at_full {lay : Option ByteArray} {X : Public}
    (h : publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL lay = .ok X) : HeadPublic X := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.full
  exact head_in_scope hZ hR h

/-- **At the second named set.** -/
theorem head_at_gap {lay : Option ByteArray} {X : Public}
    (h : publicOf VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL lay = .ok X) : HeadPublic X := by
  obtain ⟨hZ, pp, hR, -⟩ := VerifierAndGoals.filesRead.other
  exact head_in_scope hZ hR h

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.head_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.head_at_full
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.head_at_gap
