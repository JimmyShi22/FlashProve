-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Pub/SmallOwed.lean: FOUR SMALL PREMISES OF THE LEDGER FOR "THE HEAD HAS A MEMBER",
EACH AS A LAW UNDER HYPOTHESES BY FIELD, WITH THE CLOSED FACTS AT THE
WRITTEN VALUES BY LEAN's KERNEL AND A NEGATIVE TEST. In the ledger's names: PubOwed.u₂ · u₅ · u₇
(Johnson/AtFull/Top/ProofLaidOfLedgers.lean) · hE (of a file of the ledger that is not in this
library).

  u₂ `u2_of_first`: FirstWritten f → f.codes.lengthsOk = true. A call: the closed fact is
    `lengths_written` (Johnson/Road/K4/K4PlanWritten.lean). Its negative:
    `lengthsOk_rejects` (Johnson/Goal/Numbers/LengthsOkWritten.lean).
  u₇ `reqOk_written` (closed) · `reqOk_no` (without a base code it says no) ·
    `startOk_written`: the four tests in front of the first state say yes at the written codes,
    request and layout, at as many answers to a sample as the written request has · `startOk_no`: at
    one more, no · **`u7_of_first`**: FirstWritten f · hn : f.given.plan.samples = the written
    request's answers ⟹ plainStarts.start (plainStarts.par f) f = some (S.firstRecord ‹the three
    written values›) · `samples_written`: the value proofThree.A.plan.plan (the written first plan
    in the form Fmt.Plan) has that number: so hn is no empty hypothesis IF what is read back is that
    value: that tie is not shown here · `u7_of_plan`: so hn from f.given.plan = that plan.
  u₅ `depth_of`: the two files' shapes give the stored table the depth 32 ⟹ depthOf (blankM m) = .ok
    32 · `depth_no`: at 32 and 31 it refuses · `key_depth_written`, `proof_depth_written` (closed) ·
    **`u5_of_sized`**: m.p.chains.made.sized = writtenSized ⟹ the same.
  hE **`hE_of_links`**: linksOf X cov returns · profile 4 · twelve groups ⟹ X.A[12]? = none. By the
    library's `place_kind_attention_size`. So hE falls to these three.
Limits. No hypothesis is shown to hold at any public files. hn is read back from parameter bytes:
who reads these back pays it. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import Johnson.Desc.ProofFile.Law.PlainIsMade
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.Ok.PlanWritten.Rounds
import Johnson.Road.K4.K4PlanWritten
import Johnson.Goal.Written.Made
import OnBytes.Tie.Pv.Tail.KindProved

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Pub

open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (proofSizedFull FirstWritten depthOf_congr)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.First (S parP)
open Johnson.G (layoutFull)
open Johnson.G.OfPlan (Made depthOf)

/-! ## u₂ -/

/-- **u₂**: the written codes' message lengths are powers of two. -/
theorem u2_of_first {f : Params.First} (h : FirstWritten f) : f.codes.lengthsOk = true := by
  rw [h.1]
  exact OnBytes.Road.K4.lengths_written

/-! ## u₇ -/

/-- The programs' own test on the codes and the request's shape accepts the written ones. -/
theorem reqOk_written : OnBytes.reqOk proofSizedFull.codes proofSizedFull.request = true := by
  decide +kernel

/-- A negative test: without a base code it rejects. -/
theorem reqOk_no :
    OnBytes.reqOk { proofSizedFull.codes with base := #[] } proofSizedFull.request = false := by
  decide +kernel

/-- **The four tests in front of the first state, at the written values.** -/
theorem startOk_written :
    S.startOk { firstTree := 0, samples := proofSizedFull.request.answers } proofSizedFull.codes
      proofSizedFull.request layoutFull = true := by
  unfold S.startOk
  rw [OnBytes.Road.K4.lengths_written, reqOk_written, OnBytes.Road.K4.layout_written]
  simp

/-- A negative test: at one answer more to a sample they say no. -/
theorem startOk_no :
    S.startOk { firstTree := 0, samples := proofSizedFull.request.answers + 1 }
      proofSizedFull.codes proofSizedFull.request layoutFull = false := by
  unfold S.startOk
  rw [OnBytes.Road.K4.lengths_written, reqOk_written, OnBytes.Road.K4.layout_written]
  simp

/-- **u₇**: the first state is made, at the three written values. -/
theorem u7_of_first {f : Params.First} (h : FirstWritten f)
    (hn : f.given.plan.samples = proofSizedFull.request.answers) :
    ProofFile.plainStarts.start (ProofFile.plainStarts.par f) f =
      some (S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull) := by
  obtain ⟨h1, -, h3, -, -, h6⟩ := h
  show S.startP (parP f) f.codes f.shape f.layout = _
  unfold S.startP parP
  rw [h1, h3, h6, hn, startOk_written]
  rfl

/-- The written first plan, in the form Fmt.Plan, has that number. That a reader of parameter bytes
returns this plan is not said here. -/
theorem samples_written :
    proofThree.A.plan.plan.samples = proofSizedFull.request.answers := by decide +kernel

/-- u₇, from the plan that is read back. -/
theorem u7_of_plan {f : Params.First} (h : FirstWritten f)
    (hg : f.given.plan = proofThree.A.plan.plan) :
    ProofFile.plainStarts.start (ProofFile.plainStarts.par f) f =
      some (S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull) :=
  u7_of_first h (by rw [hg]; exact samples_written)

/-! ## u₅ -/

/-- Where both files' shapes give the stored table the depth 32. -/
theorem depth_of {m : Made}
    (h1 : m.p.chains.made.sized.key.once.shape.fold.index.code.logN = 32)
    (h2 : m.p.chains.made.sized.proof.batch.shape.fold.index.code.logN = 32) :
    depthOf (ProofFile.Law.blankM m) = .ok 32 := by
  rw [depthOf_congr (m := m) (m' := ProofFile.Law.blankM m) rfl]
  unfold depthOf
  dsimp only
  rw [h1, h2]
  rfl

/-- A negative test: at two depths it refuses. -/
theorem depth_no {m : Made}
    (h1 : m.p.chains.made.sized.key.once.shape.fold.index.code.logN = 32)
    (h2 : m.p.chains.made.sized.proof.batch.shape.fold.index.code.logN = 31) :
    (depthOf m).toOption = none := by
  unfold depthOf
  dsimp only
  rw [h1, h2]
  rfl

/-- The key file's written shape gives the committed table the depth 32. -/
theorem key_depth_written : writtenSized.key.once.shape.fold.index.code.logN = 32 := by
  decide +kernel

/-- The proof file's written shape gives the committed table the depth 32. -/
theorem proof_depth_written : writtenSized.proof.batch.shape.fold.index.code.logN = 32 := by
  decide +kernel

/-- **u₅**, at the depth 32. -/
theorem u5_of_sized {m : Made} (hz : m.p.chains.made.sized = writtenSized) :
    depthOf (ProofFile.Law.blankM m) = .ok 32 :=
  depth_of (by rw [hz]; exact key_depth_written) (by rw [hz]; exact proof_depth_written)

/-! ## hE -/

/-- **hE**: at twelve groups there is no thirteenth attention's plan. -/
theorem hE_of_links {X : Verify.Public} {cov : Head.Covered} {ls : Array Stages.LinkH}
    (h : Verify.linksOf X cov = .ok ls) (h4 : X.p4 = true) (hN : X.NGr = 12) :
    X.A[12]? = none := by
  have e := OnBytes.Tie.Pv.Tail.KindProved.place_kind_attention_size h h4
  exact Array.getElem?_eq_none (by omega)

end Johnson.AtFull.Pub

#print axioms Johnson.AtFull.Pub.u2_of_first
#print axioms Johnson.AtFull.Pub.reqOk_written
#print axioms Johnson.AtFull.Pub.reqOk_no
#print axioms Johnson.AtFull.Pub.startOk_written
#print axioms Johnson.AtFull.Pub.startOk_no
#print axioms Johnson.AtFull.Pub.u7_of_first
#print axioms Johnson.AtFull.Pub.samples_written
#print axioms Johnson.AtFull.Pub.u7_of_plan
#print axioms Johnson.AtFull.Pub.depth_of
#print axioms Johnson.AtFull.Pub.depth_no
#print axioms Johnson.AtFull.Pub.key_depth_written
#print axioms Johnson.AtFull.Pub.proof_depth_written
#print axioms Johnson.AtFull.Pub.u5_of_sized
#print axioms Johnson.AtFull.Pub.hE_of_links
