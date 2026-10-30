-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/StartAtHead.lean: the first state of the proof file's own first chain, under
the head `P5J.AtMgA`: it is one written value, and so is its shape.

Main names.
* `startFull`: the first state at the written codes, request's shape and layout of the full size:
  `S.firstRecord proofSizedFull.codes shapeFull layoutFull`. `startShFull`: its shape (`chainSh`,
  Johnson/Desc/First/Shape/Chain.lean). Closed terms: they read no public file.
* `first_at`: under the head the first chain's codes, request's shape and layout at the public part
  are the written ones.
* `s₀_at`: under the head the public part's state before the first segment is `startFull`.
* `start_at`: under the head, at every instance whose request passes the tests that need no reply,
  the shape of the chain's first state is `startShFull`.
* `start_facts`: what Lean's kernel finds at `startShFull`: no mark; the state's own place is
  "between" (here = 0); nothing owed; no reply; 25 links; 26 groups; 17 main codes and 14 mask
  codes; no message, no tree, no root; the state of the calls stands at link 0, moment 0, with no
  call run (inLink is false).

How. `AtMg.pins` (Johnson/P5T/FenceAtMg.lean) and `pinnedAt_of_row` give the verifier's own test on
the written values; `P5T.written_at_in_scope` (Johnson/P5T/WrittenAtScope.lean) gives the three
equations; `ProofFile.Law.pubBy_start` (Johnson/Desc/ProofFile/Law/PureMade.lean) and `start?_first`
(Johnson/Desc/First/EPubAtStart.lean) give the state; `ProofFile.Honest.start_shape`
(Johnson/Desc/ProofFile/Honest/Thread/ShapeFirst.lean) gives the shape.

Limits. The first state alone: no step from it. That the request passes is a premise of `start_at`.
`start_facts` is a list of readings, not the whole value. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ShapeFirst
import Johnson.P5T.FenceAtMg
import Johnson.P5T.WrittenAtScope
import Johnson.Desc.First.EPubAtStart
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (proofSizedFull pinnedAt_of_row)
open Johnson.G (layoutFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- The first state at the full size's written codes, request's shape and layout. -/
def startFull : S := S.firstRecord proofSizedFull.codes shapeFull layoutFull

/-- Its shape. -/
def startShFull : ChainSh := chainSh startFull

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the first chain's three public data are the written ones. -/
theorem first_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.first.codes = proofSizedFull.codes ∧ Zp.first.shape = shapeFull ∧
      Zp.first.layout = layoutFull := by
  have hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨hm, -⟩ := h.toAtMg.pins
  obtain ⟨-, a, b, c, -⟩ := P5T.written_at_in_scope h.scope hZ
    (pinnedAt_of_row (by rw [hm, Bool.or_true])) h.laid.laidPOf
  exact ⟨b, a, c⟩

/-- **Under the head the state before the first segment is the written one.** -/
theorem s₀_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Zp.s₀ = startFull := by
  obtain ⟨a, b, c⟩ := first_at h
  have h0 : S.start? (VerifiableInference.Desc.First.parP Zp.first) Zp.first.codes Zp.first.shape
      Zp.first.layout = some Zp.s₀ := ProofFile.Law.pubBy_start (st := ProofFile.plainStarts) h.laid.pub
  rw [VerifiableInference.Desc.First.start?_first h0, a, b, c]
  rfl

/-- **Under the head, where the request passes, the first state's shape is the written one.** -/
theorem start_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p : ProofFile.InstPub)
    (hp : (Zp.s₀.withReq (Verify.words32 p.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true) :
    chainSh (ProofFile.startS Zp p) = startShFull := by
  rw [ProofFile.Honest.start_shape Zp p hp, s₀_at h]
  rfl

/-- What Lean's kernel finds at the written shape. -/
theorem start_facts : startShFull.marked = false ∧ startShFull.here = 0 ∧
    startShFull.rowsOwed = none ∧ startShFull.reply = false ∧
    startShFull.check.frame.shape.link.length = 25 ∧ startShFull.check.frame.groups.size = 26 ∧
    startShFull.core.st.codes.base.size = 17 ∧ startShFull.core.st.codes.mask.size = 14 ∧
    startShFull.core.st.oracles.length = 0 ∧ startShFull.core.book.trees.length = 0 ∧
    startShFull.core.roots = 0 ∧ startShFull.check.frame.link = 0 ∧
    startShFull.check.frame.moment = 0 ∧ startShFull.check.inLink = false := by
  decide +kernel

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_at
#print axioms Johnson.AtFull.Shape.s₀_at
#print axioms Johnson.AtFull.Shape.start_at
#print axioms Johnson.AtFull.Shape.start_facts
#print axioms Johnson.AtFull.Shape.startFull
#print axioms Johnson.AtFull.Shape.startShFull
