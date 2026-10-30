-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/MadeInScope.lean: in the public part that the IOP as written in Lean for the
proof file computes (`pureRoad.pub`, Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean), at all public files in
the goals' scope, and where the test on what the planner configured says yes (`madePinnedAt`,
Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean), all four fields of what the planner configured that
do not hang on the digest of the public files are ONE WRITTEN VALUE (`writtenMade`,
Johnson/Goal/Written/Made.lean): all sizes, and all seven lists of rounds, each round with its error
bound: 67383 rounds. For every function in the second hash function's place; no hash is named.

How. Where that public part is computed, what the planner configured in it is the value of one call
of `configure` (`pub_configure`, Johnson/Desc/ProofFile/Law/PlainMade.lean), in scope at the written
lines (`args_of_steps`, Johnson/Goal/Numbers/KeyPlansAtPure.lean). Its sizes, field by field:
  the lines: `sized_lines` (Johnson/G/MadeSpelled.lean); the setting, a copy's file's sizes and
    codes: `sized_link` (OnBytes/Params/ConfigureLaws.lean) with `record_table`
    (OnBytes/Params/EntryStagesRecord.lean) and `writtenLink_sized`
    (Johnson/Desc/Ok/NumberPrices/MadeAtWritten.lean);
  the key file's sizes: `sized_key` (OnBytes/Plan/PlanListsConfigure.lean) with `keySized_returns`
    (Johnson/Goal/PlanValues/KeySizedReturns.lean) and `plainShapes_ranges` (KeyPlansAtPure.lean);
  the proof file's sizes: THE TEST. From the sizes follow six of the seven lists (`sixOfSized`,
    Johnson/Goal/Written/MadeOfSized.lean); the seventh, the proof file's first, is THE TEST's
    again; `free_of_sized` (Johnson/Goal/Written/ChainsW.lean) joins them.

Statements.
  `sized_ext`: a tool: sizes whose six fields are the written ones are the written sizes.
    `sized_of_configure`: what `configure` returns at the written lines, at shapes whose key sizing
    returns the written key sizes, and with the written sizes of a proof file, has the written
    sizes, whole.
  `made_of_written`: in scope, from the two equations `MadeWritten`: `freeOf Z.p.chains.made =
    writtenMade`.
  **`made_in_scope`**: in scope, from the test's yes: the same.
  `proof_plans_in_scope`: so the planner's three lists for the proof file are the three written
    ones: 48391 rounds.
  `first_written_in_scope`: and the six equations on the first chain's parameters as read back.
    `layout_in_scope`: the sixth by itself: the layout of a request's arrays is `layoutFull`
    (Johnson/G/LayoutLit.lean).   `sends_in_scope`: and the proof file's three lists of what is sent
    are the written ones (`proofSendsFull`, Johnson/G/SendsWritten.lean).
  `xShape_in_scope`: and the shape part of what the program `verify-on-bytes`'s reader makes of the
    public files is the written one (`xShapeFull`, Johnson/G/XShapeLit.lean); part by part:
    Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean.
  `par_in_scope`: the first chain's two numbers (`Par`, Johnson/Desc/First/State.lean) are 0 and the
    written shape's number of answers: from the text of `parP`, the first state's own test
    (`startOk`; `pubBy_start`, `startP_ok`, Johnson/Desc/ProofFile/Law/PureMade.lean) and the third
    of the six equations.   `start_in_scope`: the state before the first segment (`Z.s₀`) is what
    `S.startP` returns at written values alone: these two numbers, the written codes, the written
    shape of a request and the written layout. No evaluation is made here.

Is it empty? Each statement has a member only where the public part is computed and the test says
yes: that is the reference run's to show. That the written value passes the test is `madeIs_of`
(MadeTestLaws.lean).

Limits. That a verifier asks the test is not said here. That the test says yes at all public files
in scope is not shown: if a compared part moved with one of the eight free numbers or with the scale
file, honest files in scope would be rejected. Nothing says that an error bound bounds a count.
Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Goal.Numbers.KeyPlansAtPure
import Johnson.Goal.Written.ChainsW
import Johnson.G.MadeSpelled
import OnBytes.Params.ConfigureLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference VerifiableInference.PlanWritten VerifiableInference.Number.ByRuns
open OnBytes OnBytes.Params Johnson.G Johnson.G.MadeFree Lk6.AtPlan

/-- Sizes whose six fields are the written ones are the written sizes. -/
theorem sized_ext {z : Sized} (e1 : z.lines = recordLines) (e2 : z.set = recordSet)
    (e3 : z.proof = proofSizedFull) (e4 : z.key = keyFull) (e5 : z.link = writtenLink)
    (e6 : z.entryCodes = recordCodes) : z = writtenSized := by
  cases z
  simp only at e1 e2 e3 e4 e5 e6
  subst e1 e2 e3 e4 e5 e6
  rfl

/-- **The sizes, whole**, from the sizes of a proof file and the sizing of a key. -/
theorem sized_of_configure {x : Shapes} {cfg : ByteArray} {bits : ℕ} {made : Configured}
    (h : configure recordLines x cfg bits = .ok made)
    (hk : Plan.keySized recordLines x.ranges = some keyFull)
    (hp : made.sized.proof = proofSizedFull) : made.sized = writtenSized := by
  have hz := (configure_plans h).1
  obtain ⟨e2, T, hT, hL⟩ := sized_link hz
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have e56 : (made.sized.link, made.sized.entryCodes) = (writtenLink, recordCodes) :=
    Option.some.inj (hL.symm.trans writtenLink_sized)
  exact sized_ext (sized_lines hz) e2 hp (Option.some.inj ((sized_key hz).symm.trans hk))
    (congrArg Prod.fst e56) (congrArg Prod.snd e56)

section
variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

/-- **In scope, from the two equations: the four fields are the one written value.** -/
theorem made_of_written (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z) (hm : MadeWritten Z.p.chains.made) :
    freeOf Z.p.chains.made = writtenMade := by
  obtain ⟨v, hv⟩ := inScope_policy hW
  rw [hv] at h
  obtain ⟨ls, hs, hc, _, _⟩ := ProofFile.Law.pub_configure h
  obtain ⟨hf, hw⟩ := args_of_steps (publicSteps_of_O (ProofFile.Law.pub_public h))
  rw [hf] at hc
  exact free_of_sized hc
    (sized_of_configure hc (keySized_returns hw (plainShapes_ranges hs)) hm.1) hm.2

/-- **IN SCOPE, FROM THE TEST's YES: ALL SIZES AND ALL SEVEN LISTS OF ROUNDS ARE THE WRITTEN ONES.**
-/
theorem made_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    freeOf Z.p.chains.made = writtenMade := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  exact made_of_written hW h (made_of_pinned hy).1

/-- So the planner's three lists for the proof file are the three written ones. -/
theorem proof_plans_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] :=
  congrArg Free.proof (made_in_scope hW h hy)

/-- And the six equations on the first chain's parameters as read back. -/
theorem first_written_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) : FirstWritten Z.first := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  exact (made_of_pinned hy).2.1

/-- So the layout of a request's arrays, as read back, is the written one, whole. -/
theorem layout_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.layout = layoutFull :=
  (first_written_in_scope hW h hy).2.2.2.2.2

/-- And the proof file's three lists of what is sent are the written ones. -/
theorem sends_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.made.proof = proofSendsFull := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  exact (made_of_pinned hy).2.2.1

/-- And the shape part of what `verify-on-bytes`'s reader makes of the public files is the written
one. -/
theorem xShape_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    xShapeOf Z.p.X = xShapeFull := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  exact (made_of_pinned hy).2.2.2

/-- The first chain's two numbers: it takes over no tree, and the answers to each out-of-domain
(OOD) sample are as many as the written shape of a request says. No test is asked for them: where
the public part is computed the first state has passed its own test on the number of answers. -/
theorem par_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.P = ⟨0, proofSizedFull.request.answers⟩ := by
  have hZ : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts W.pol W.lay W.KL = .ok Z := h
  have hP : Z.P = Desc.First.parP Z.first := (ProofFile.Law.pubBy_fields hZ).2.2.2.2.1
  have hok := ProofFile.Law.startP_ok (ProofFile.Law.pubBy_start hZ)
  unfold Desc.First.S.startOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  have ha : Z.first.shape.answers = (Desc.First.parP Z.first).samples := hok.2.1.2
  rw [(first_written_in_scope hW h hy).2.2.1] at ha
  rw [hP]
  show (⟨0, (Desc.First.parP Z.first).samples⟩ : Desc.First.Par) = _
  rw [← ha]

/-- **The state before the first segment is a function of written values alone.** -/
theorem start_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Desc.First.S.startP ⟨0, proofSizedFull.request.answers⟩ proofSizedFull.codes
      proofSizedFull.request layoutFull = some Z.s₀ := by
  have hZ : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts W.pol W.lay W.KL = .ok Z := h
  have hs : Desc.First.S.startP (Desc.First.parP Z.first) Z.first.codes Z.first.shape
      Z.first.layout = some Z.s₀ := ProofFile.Law.pubBy_start hZ
  have hP : Z.P = Desc.First.parP Z.first := (ProofFile.Law.pubBy_fields hZ).2.2.2.2.1
  obtain ⟨f1, _, f3, _, _, f6⟩ := first_written_in_scope hW h hy
  rw [← hP, par_in_scope hW h hy, f1, f3, f6] at hs
  exact hs

end

end VerifiableInference.PlanWritten.Joined

#print axioms VerifiableInference.PlanWritten.Joined.sized_ext
#print axioms VerifiableInference.PlanWritten.Joined.sized_of_configure
#print axioms VerifiableInference.PlanWritten.Joined.made_of_written
#print axioms VerifiableInference.PlanWritten.Joined.made_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.proof_plans_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.first_written_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.layout_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.sends_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.xShape_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.par_in_scope
#print axioms VerifiableInference.PlanWritten.Joined.start_in_scope
