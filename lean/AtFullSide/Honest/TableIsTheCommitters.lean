-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TableIsTheCommitters.lean: T1's proposition TableIsTheCommitters at the term, in
scope, at the return of the online maker: the maker's key is the committer's, and so are its stored
columns, at item 0 and nowhere else.

By what: committedColumnsWords (CommittedColumns.lean), at words; words in the field come back, so
the columns are equal in the field; key_of_atPure, eq_ofFill (ThruAtPure.lean).
-/
import AtFullSide.Honest.CommittedColumns
import Johnson.Desc.ProofFile.Honest.ThruAtPure
import E2E.TheHonestProverStatements

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.AtFiles AtPublicFiles.Committed
open OnBytes.Slice (frS ofF toF toF_ofF)
open ProofFile.Honest (eq_ofFill key_of_atPure)
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling)
open P5J

/-- Reading a list of field elements as words and back is the list. -/
theorem words_back (x : List Cb.Gl.F) : (x.map ofF).map toF = x := by
  induction x with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, toF_ofF, ih]

/-- Two columns that show the same words are the same. -/
theorem columns_of_words {a b : Option (List Cb.Gl.F)}
    (h : a.map (List.map ofF) = b.map (List.map ofF)) : a = b := by
  match a, b, h with
  | none, none, _ => rfl
  | none, some _, h => cases h
  | some _, none, h => cases h
  | some x, some y, h =>
    have e := congrArg (List.map toF) (Option.some.inj h)
    rw [words_back, words_back] at e
    rw [e]

/-- **TableIsTheCommitters, in scope, at what the online maker returns.** -/
theorem tableIsTheCommitters (Z : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) : TableIsTheCommitters A := by
  refine ⟨key_of_atPure hA, fun M ρ it p => ?_⟩
  have hs : A.H.stored = (onlineFilling Z).enc A.Z :=
    congrArg (fun A₀ : OnlineReturn Z => A₀.H.stored) (eq_ofFill hA)
  have hz := (ProofFile.Honest.K5.parts_of_atPure hA).1.pub
  have hw := committedColumnsWords Z scope hz M ρ it p
  rw [hs]
  exact (columns_of_words hw).symm

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.tableIsTheCommitters
