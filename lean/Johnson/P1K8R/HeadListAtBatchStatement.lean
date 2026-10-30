-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HeadListAtBatchStatement.lean: THE KIND K8 (the sub-protocol that tests that values
are small), AT THE OUTPUT HEAD's SEGMENT: IN FRONT OF THE HEAD's BATCHING (number 347 of the first
chain's flat list) THE LIST OF TABLES IN THE SMALLNESS TEST's DATA IS THE LIST THAT THE HEAD's QUIET
STEP LAID AT PLACE 342 (`ReadsQuiet.tables`, Johnson/Desc/K8/ReadsQuiet.lean), AND THE MATRICES AND
THEIR NUMBER ARE THE PLAN's. STATEMENTS ALONE: one definition of a sentence on a state, this file's
own, and two definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the
library's goals: they are lemmas' statements. In the goals' scope, at an opening of the description;
at every state that the plain list reaches, from any start.

WHAT IT IS NOT. WHICH x: `HeadListLaid` SAYS THAT x STANDS IN THE STATE AT 343 AS WHAT THE HEAD HAS
HEARD (a.x = some x). THAT IT IS WHAT THE HEAD's OWN SUB-PROTOCOL LAID OF ITS CHALLENGES AT 341 IS
NOT SAID HERE; NOR THAT x STILL STANDS AT 347. Nothing on the values of any point; nothing on the
test `tiesLaid`; that the plan's number of matrices is h.NHf + 4 is not said. ONE SEGMENT OF 25.

  `HeadListLaid W s x t`  THIS FILE's OWN: an end's form: s stands in the head's segment with x as
      what the head has heard; the quiet step's routine returns t at the public part W's head and x;
      the data in s are closed, with t's list, the plan's matrices and the plan's number of them
  `HeadListAt343`  at every state reached at 343: there are such x and t
  `HeadListAt347`  at every state s' reached at 347: a state s reached at 343 from the same start
      (the same z), with such x and t; and the data in s' are closed, with t's list, the plan's
      matrices and the plan's number of them

NEAR. ON THE OTHER LIST: the library's `funs_from_reads_head`
(Johnson/Desc/First/Link/Law/FunsAtBatch.lean: from 347 back to 343, `S.funs?` stays), over its
`sameFuns_stretch`; beside it `sameTabs_stretch` (TabsStay.lean) and `sameOwn_stretch`
(OwnStay.lean): `S.funs?` at the head is the list of the state's own field t; `LiveTable`
(Johnson/Desc/K8/Honest/ReadsLiveOf.lean) reads the data's field funs. `head_lays_tl`
(Johnson/Desc/First/K8/LawCondText.lean) says which list the quiet step closes, the whole data,
without "a.x = some x". `k1Reads_makes_head` (LawCondK1.lean): two tests on the state behind place
342. `LinkJoin.planned_at_batch` (Link/Law/PlannedAtDraw.lean): the planned fields at all 25
batchings; blind to the list and its mark.

Limits. The blocks' decisions alone. Nothing on any measure. Nothing on any property.
-/
import Johnson.IMR.LinkSeat
import Johnson.Desc.K8.ReadsQuiet
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The closed list, at a state.** This file's own: an end's form. -/
def HeadListLaid (W : Verify.Public) (s : S) (x : Head.Heard) (t : Head.Tables) : Prop :=
  (∃ a, s.here = .head a ∧ a.x = some x) ∧
    (∃ cov, VerifiableInference.Desc.K8.ReadsQuiet.tables W.hS W.HLy W.H cov x = .ok t) ∧
    ∃ tl, s.tl? = some tl ∧ tl.funClosed = true ∧ tl.funs = t.funs ∧ tl.mats = W.H.tl.mats ∧
      tl.NM = W.H.tl.NM

/-- The statement at 343. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadListAt343 : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B →
    ∀ (Q : Type) (start : Q → S) (z : Q) (s : S), Reach 0 c.blocksInOrder start 343 (z, s) →
      ∃ x t, HeadListLaid Bs.G₀.W s x t

/-- The statement at 347. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadListAt347 : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B →
    ∀ (Q : Type) (start : Q → S) (z : Q) (s' : S), Reach 0 c.blocksInOrder start 347 (z, s') →
      ∃ s x t, Reach 0 c.blocksInOrder start 343 (z, s) ∧ HeadListLaid Bs.G₀.W s x t ∧
        ∃ tl, s'.tl? = some tl ∧ tl.funClosed = true ∧ tl.funs = t.funs ∧
          tl.mats = Bs.G₀.W.H.tl.mats ∧ tl.NM = Bs.G₀.W.H.tl.NM

end P1K8

#print axioms P1K8.HeadListLaid
#print axioms P1K8.HeadListAt343
#print axioms P1K8.HeadListAt347
