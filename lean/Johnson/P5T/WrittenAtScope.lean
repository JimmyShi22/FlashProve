-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/WrittenAtScope.lean: in the goals' scope, five parts of the public part Z of the IOP as
written in Lean are written values. One file for the files that state facts at these values. Three
statements with their proofs; nothing is evaluated; nothing new is shown: each equation is another
file's, gathered.

  `entries_in_scope`: the three chains' declared rounds' entries (of `Z.D`) are `esFull`
    (Johnson/P5T/PlanSeatsFull.lean): from the scope, "the public part is made" and "the value is
    laid": by `pubBy_entries` and `plans_written` (Johnson/Goal/Numbers/PlanWrittenPlans.lean).
  `written_at_in_scope`: with an accept of the verifier's test `madePinnedAt` besides: the proof
    file's three lists of sendings are `proofSendsFull`; the first chain's shape of a request, codes
    and layout, as read back, are `shapeFull`, `proofSizedFull.codes`, `layoutFull`; and the
    entries: by `sends_in_scope` and `first_written_in_scope`
    (Johnson/Goal/Numbers/MadeInScope.lean) and `request_shape_written`.
  `far_ties_in_scope`: the same by parts: the first two lists of sendings, the shape, the first two
    lists of entries.

Can the premises be met? Only where the public part is made, the test accepts and the value is laid:
the reference run's to show. Limits. Nothing on soundness.
-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.PlanWrittenPlans
import Johnson.Goal.Numbers.RequestWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open Johnson.G
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (pubBy_entries plans_written request_shape_written
  madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (sends_in_scope first_written_in_scope)

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- **The declared rounds' entries at the public part are the written ones**, all three chains. The
verifier's test on the sizes is not asked for it. -/
theorem entries_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    (Z.D.1.map (·.entry), Z.D.2.1.map (·.entry), Z.D.2.2.map (·.entry)) = esFull := by
  have hZ : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts W.pol W.lay W.KL = .ok Z := h
  obtain ⟨Z', hZ', p1, p2, p3⟩ := plans_written hW hl
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain ⟨d1, d2, d3⟩ := pubBy_entries hZ
  exact Prod.ext (d1.trans p1) (Prod.ext (d2.trans p2) (d3.trans p3))

/-- **Five equations at the public part, as one conjunction.** -/
theorem written_at_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    Z.made.proof = proofSendsFull ∧ Z.first.shape = shapeFull ∧
      Z.first.codes = proofSizedFull.codes ∧ Z.first.layout = layoutFull ∧
      (Z.D.1.map (·.entry), Z.D.2.1.map (·.entry), Z.D.2.2.map (·.entry)) = esFull := by
  have f := first_written_in_scope hW h hy
  exact ⟨sends_in_scope hW h hy, f.2.2.1.trans request_shape_written, f.1, f.2.2.2.2.2,
    entries_in_scope hW h hl⟩

/-- The same by parts, in the form of the law on the seats that lie far apart. -/
theorem far_ties_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    Z.made.proof.1 = proofSendsFull.1 ∧ Z.made.proof.2.1 = proofSendsFull.2.1 ∧
      Z.first.shape = shapeFull ∧ Z.D.1.map (·.entry) = esFull.1 ∧
      Z.D.2.1.map (·.entry) = esFull.2.1 := by
  obtain ⟨a, b, _, _, e⟩ := written_at_in_scope hW h hy hl
  exact ⟨congrArg (·.1) a, congrArg (·.2.1) a, b, congrArg (·.1) e, congrArg (·.2.1) e⟩

end P5T

#print axioms P5T.entries_in_scope
#print axioms P5T.written_at_in_scope
#print axioms P5T.far_ties_in_scope
