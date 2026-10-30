-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/TableRows.lean: the code switch's typed table (K2Caller.tableOf,
Johnson/Top/H0/K2Caller/Table.lean): WHERE IT RETURNS, THE PLANNER OF VERIFY-ON-BYTES HAS RETURNED,
AND THE TABLE HAS AT MOST AS MANY ROWS AS THAT PLANNER's REQUEST HAS LINKS. Statements with their
proofs, of all public files. A law file; no running text imports it.

  framesFrom_length   the planner's records from a group on are at most one more than the links
                      left.
  later_length        so those of them whose group's number is not 0 are at most the links.
  tableOf_rows        tableOf pol lay KL = .ok t gives p with
                      OnBytes.Model.Verify.planned pol KL (some lay) = .ok p and
                      t.length ≤ p.chains.made.sized.proof.request.link.length.
Spent by: SpotsOfRows.lean's spots_core.
Limits. NOTHING SAYS AT WHICH FILES tableOf RETURNS. Nothing on soundness.

-/
import Johnson.Top.H0.K2Caller.Table
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan

theorem framesFrom_length (z : ProofSized) :
    ∀ (gs : List ReqGroup) (l : ℕ) (links : List ReqLink) (open_ : List ℕ) (before : GroupSize),
      (framesFrom z l gs links open_ before).length ≤ links.length + 1
  | [], _, _, _, _ => by simp [framesFrom]
  | g :: gs, l, links, open_, before => by
    unfold framesFrom
    cases links with
    | nil => simp
    | cons a links =>
      have h := framesFrom_length z gs (l + 1) links (open_.drop 1) (closedGroup z g gs)
      simpa using h

theorem later_length (z : ProofSized) (gs : List ReqGroup) (links : List ReqLink)
    (open_ : List ℕ) (before : GroupSize) :
    ((framesFrom z 0 gs links open_ before).filter fun n => n.l != 0).length ≤ links.length := by
  cases gs with
  | nil => simp [framesFrom]
  | cons g gs =>
    unfold framesFrom
    have h0 : ((frameAt z 0 g gs links open_ before).l != 0) = false := by simp [frameAt]
    rw [List.filter_cons_of_neg (by rw [h0]; simp)]
    refine (List.length_filter_le _ _).trans ?_
    cases links with
    | nil => simp
    | cons a links =>
      have h := framesFrom_length z gs (0 + 1) links (open_.drop 1) (closedGroup z g gs)
      simpa using h

/-- **Where the typed table is made.** -/
theorem tableOf_rows {pol lay KL : ByteArray} {t : List SwRow} (h : tableOf pol lay KL = .ok t) :
    ∃ p, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧
      t.length ≤ p.chains.made.sized.proof.request.link.length := by
  unfold tableOf at h
  obtain ⟨x, hx, h⟩ := exc_bind h
  cases h
  unfold placesOf at hx
  obtain ⟨p, hp, hx⟩ := exc_bind hx
  obtain ⟨R, -, hx⟩ := exc_bind hx
  cases hx
  refine ⟨p, hp, ?_⟩
  simp only [List.length_map]
  exact later_length _ _ _ _ _

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.tableOf_rows
