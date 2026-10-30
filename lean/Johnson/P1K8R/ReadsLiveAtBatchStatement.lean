-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLiveAtBatchStatement.lean: THE TEST `readsLive`
(Johnson/Desc/K8/Honest/LinkedFew.lean: on each column of the ties' row some read has a coefficient
other than 0) SAYS YES AT DATA THAT HOLD THE OUTPUT HEAD's CLOSED LIST OF TABLES, UNDER ONE PREMISE
ON WHAT THE HEAD HEARD, WHICH THIS FILE AND THE FILE OF ITS PROOFS PAY NOWHERE. STATEMENTS ALONE:
one definition of a premise's form, this file's own, and one definition of a proposition. NOTHING IS
PROVED IN THIS FILE, and it is none of the library's goals: a lemma's statement.

WHAT IT IS NOT. CONDITIONAL: `HeardFine` IS SHOWN AT NO STATE HERE. Its three sizes are no public
numbers: they speak of what the head's own sub-protocol heard. A LAW ON DATA: NO STATE AND NO RUN IS
NAMED: at a state in front of the batching, along the caller's own fold: `ReadsLiveAlongFold`
(ReadsLiveAlongFoldStatement.lean of this folder). The head's segment alone. `publicOf` is the
planner as it stands at the format's second hash function (`publicOfO_older`,
Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean): at another hash nothing is said. The full size
alone.

  `HeardFine h x`      THIS FILE's OWN, A PREMISE's FORM: of what the head heard: no coordinate of
                       four points is 0 or 1 (x.Zl; the last h.la coordinates of x.wpl.r; x.tH.r;
                       x.tV.r); x.Zl has h.ls + h.lt coordinates, x.tH.r and x.tV.r h.lt each
  `ReadsLiveOfLaid`    in scope, where `publicOf` returns W: data tl with the closed list of tables
                       made of x, the plan's matrices and their number, at which `tiesLaid` says
                       yes: under HeardFine W.hS x: readsLive tl = true

NEAR. `Core` (Johnson/Desc/Reads/LiesBehind.lean) has two of the three sizes as its clauses hsTV and
hsTH, and the text of x.Zl as hX2: the theorems that end in it speak behind steps' yeses, of no
reached state.

Limits. A test's yes, under a premise. Nothing on any property.
-/
import Johnson.P1K8R.HeadListAtBatchStatement
import Johnson.Desc.K8.Honest.LinkedFew

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest (tiesLaid readsLive)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **What is asked of what the head heard.** This file's own: a premise's form. -/
def HeardFine (h : Head.Shape) (x : Head.Heard) : Prop :=
  (∀ w ∈ x.Zl.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
    (∀ ZV, VerifiableInference.Desc.Own.tailOf x.wpl.r h.la = some ZV →
      ∀ w ∈ ZV.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
    (∀ w ∈ x.tH.r.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
    (∀ w ∈ x.tV.r.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) ∧
    x.Zl.size = h.ls + h.lt ∧ x.tH.r.size = h.lt ∧ x.tV.r.size = h.lt

/-- The statement on data. Not proved here; a lemma's statement, none of the library's goals. -/
def ReadsLiveOfLaid : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : Option ByteArray) (W : Verify.Public)
    (cov : Head.Covered) (x : Head.Heard) (t : Head.Tables) (tl : HTailF2),
    VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    Verify.publicOf P.pol P.KL lay = .ok W →
    VerifiableInference.Desc.K8.ReadsQuiet.tables W.hS W.HLy W.H cov x = .ok t →
    tl.funs = t.funs → tl.mats = W.H.tl.mats → tl.NM = W.H.tl.NM → tiesLaid tl = true →
    HeardFine W.hS x → readsLive tl = true

end P1K8

#print axioms P1K8.HeardFine
#print axioms P1K8.ReadsLiveOfLaid
