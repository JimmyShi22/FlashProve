-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/PlanInScope.lean: the ties that carry the closed facts of
Johnson/HB/LLHARD/PlanAtQFull.lean to what a verifier computes: in the goals' scope, at the public
part Z of the IOP as written in Lean for the proof file, under the yes of the one row on written
values (`madePinnedAt`, Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean). And the named tests there,
at Z's own terms.

The ties.
  `laid_in_scope`, `msgs_in_scope`: the layout and the shapes of Z's own first list of sendings, at
    Z's own codes, are `LFull` and `MFull`: by `laid_at`, `msgs_at`
    (Johnson/HB/LLHARD/LaidWritten.lean) from `first_written_in_scope`, `codes_written` and
    `sends_in_scope`.
  `likeFull_in_scope`: Z.first has the three equations that carry a place of K1 to the placeholder
    `qFull` (`LikeFull`, Johnson/Desc/K1/Law/QFull.lean).
  `gp_in_scope`: the chain's two numbers, off Z.P, are `gpFull`. `gpOf_in_scope`: the same at the
    lot's own name for them (`K1.gpOf Z`, Johnson/Desc/ProofFile/Lot/K1.lean).
  `lettersBy_first`, `blankBy_first`: the first chain's parameters in the ground that K1's lot reads
    (`ProofFile.blankBy`, Johnson/Desc/ProofFile/Pub.lean) are Z.first, which W's commitment reads: after
    the pattern of `blankBy_W` (Johnson/Desc/ProofFile/Law/MakerPublic.lean).
  `wMsg_in_scope`: what goes out with W at Z.first's linear shape is `wMsgFull`. The tests at Z's
    own terms: `indexCode_in_scope`, `indexLast_in_scope`, `opening_in_scope`, `w_in_scope`,
    `later_in_scope`. L stands in them as `LFull`, which by `laid_in_scope` is what `laidAtCodes`
    returns there; `planIndexSeatB LFull N` is `indexSeat_written` as it stands.

ONE ARGUMENT IS STILL A LETTER: N. Each test's statement takes equations on `N.indexNo`, `N.msgsAt
p`, `N.treesAt p` as premises. They are laid off what the sub-protocols tell, of which no written
list lies yet: nothing ties them.
(Where this and lean/THEOREM.md differ, the page holds.)

No evaluation is made here.

Limits. Each statement has a member only where the public part is computed and the row says yes: the
reference run's to show. Nothing on soundness.
-/
import Johnson.HB.LLHARD.PlanAtQFull
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.ProofFile.Lot.K1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params Johnson.G _root_.Desc.Plain
open VerifiableInference.PlanWritten (proofSizedFull madePinnedAt codes_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope sends_in_scope par_in_scope)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K12.Door (laidAtCodes msgsOfChain)
open VerifiableInference.Desc.K1 (qFull firstPar parLater parW LikeFull firstPar_full parLater_full
  parW_full)

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

/-- **The layout of Z's own first list of sendings, at Z's own codes, is the written one.** -/
theorem laid_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    laidAtCodes Z.first.codes Z.made.proof.1 = some LFull :=
  laid_at ((first_written_in_scope hW h hy).1.trans codes_written)
    (congrArg Prod.fst (sends_in_scope hW h hy))

theorem msgs_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    msgsOfChain Z.made.proof.1 = MFull :=
  msgs_at (congrArg Prod.fst (sends_in_scope hW h hy))

/-- **Z.first has the three equations that carry a place of K1 to the placeholder.** -/
theorem likeFull_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) : LikeFull Z.first :=
  ⟨(first_written_in_scope hW h hy).1.trans codes_written,
    (first_written_in_scope hW h hy).2.2.1, (first_written_in_scope hW h hy).2.1⟩

/-- The chain's two numbers, off Z.P. -/
theorem gp_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    (⟨Z.P.samples, Z.P.firstTree⟩ : GPar) = gpFull := by
  rw [par_in_scope hW h hy]
  rfl

/-- The same at the lot's own name for the two numbers. -/
theorem gpOf_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    K1.gpOf Z = gpFull :=
  gp_in_scope hW h hy

/-- The first chain's parameters in the segments' structures are the public part's. -/
theorem lettersBy_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {s : First.S} {G : ProofFile.Ground}
    (h : ProofFile.lettersBy mk Z s = .ok G) : G.first = Z.first := by
  unfold ProofFile.lettersBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

/-- **So K1's lot, which reads the ground's, and W's commitment, which reads the public part's, read
one value.** -/
theorem blankBy_first {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G : ProofFile.Ground}
    (h : ProofFile.blankBy mk Z = some G) : G.first = Z.first := by
  have h' : (ProofFile.lettersBy mk Z
      (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption = some G := h
  cases hx : ProofFile.lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok G' =>
    rw [hx] at h'
    have hG : G' = G := Option.some.inj h'
    exact hG ▸ lettersBy_first hx

/-- What goes out with W. -/
theorem wMsg_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    linMessageW Z.first.lin = some wMsgFull := by
  rw [(likeFull_in_scope hW h hy).lin]
  exact wMsg_written

/-! ## The tests at Z's own terms; N a letter -/

theorem indexCode_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {N : Numbers}
    (hn : N.indexNo = 4) :
    planIndexCodeB (msgsOfChain Z.made.proof.1) Z.first.codes N = true := by
  rw [msgs_in_scope hW h hy, (likeFull_in_scope hW h hy).codes]
  exact indexCode_written hn

theorem indexLast_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {N : Numbers}
    (hn : N.indexNo = 4) :
    planIndexLastB N (firstPar Z.first ⟨Z.P.samples, Z.P.firstTree⟩) = true := by
  rw [gp_in_scope hW h hy, firstPar_full (likeFull_in_scope hW h hy)]
  exact indexLast_written hn

/-- At the first segment's opening. -/
theorem opening_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {N : Numbers}
    {p : Option Place} (hm : N.msgsAt p = 0) (ht : N.treesAt p = 0) :
    planPlacesB LFull N p (firstPar Z.first ⟨Z.P.samples, Z.P.firstTree⟩) = true ∧
      planTreesB LFull N p (firstPar Z.first ⟨Z.P.samples, Z.P.firstTree⟩) = true ∧
      planShapesB (msgsOfChain Z.made.proof.1) N p
        (firstPar Z.first ⟨Z.P.samples, Z.P.firstTree⟩) = true := by
  rw [gp_in_scope hW h hy, firstPar_full (likeFull_in_scope hW h hy), msgs_in_scope hW h hy]
  exact first_written hm ht

/-- At W's sending. -/
theorem w_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {N : Numbers}
    {p : Option Place} (hm : N.msgsAt p = 197) (ht : N.treesAt p = 82) :
    planPlacesB LFull N p (parW Z.first ⟨Z.P.samples, Z.P.firstTree⟩ 4 wMsgFull) = true ∧
      planTreesB LFull N p (parW Z.first ⟨Z.P.samples, Z.P.firstTree⟩ 4 wMsgFull) = true ∧
      planShapesB (msgsOfChain Z.made.proof.1) N p
        (parW Z.first ⟨Z.P.samples, Z.P.firstTree⟩ 4 wMsgFull) = true := by
  rw [gp_in_scope hW h hy, parW_full (likeFull_in_scope hW h hy), msgs_in_scope hW h hy]
  exact w_written hm ht

/-- At each of the fifty later sendings. -/
theorem later_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    {x : ℕ × ℕ × ℕ × ℕ × ℕ} (hx : x ∈ laterFull) {N : Numbers} {p : Option Place}
    (hm : N.msgsAt p = x.2.2.2.1) (ht : N.treesAt p = x.2.2.2.2) :
    planPlacesB LFull N p
        (parLater Z.first ⟨Z.P.samples, Z.P.firstTree⟩ x.1 x.2.1 x.2.2.1) = true ∧
      planTreesB LFull N p
        (parLater Z.first ⟨Z.P.samples, Z.P.firstTree⟩ x.1 x.2.1 x.2.2.1) = true ∧
      planShapesB (msgsOfChain Z.made.proof.1) N p
        (parLater Z.first ⟨Z.P.samples, Z.P.firstTree⟩ x.1 x.2.1 x.2.2.1) = true := by
  rw [gp_in_scope hW h hy, parLater_full (likeFull_in_scope hW h hy), msgs_in_scope hW h hy]
  exact later_written hx hm ht

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.laid_in_scope
#print axioms VerifiableInference.Desc.K13.Law.msgs_in_scope
#print axioms VerifiableInference.Desc.K13.Law.likeFull_in_scope
#print axioms VerifiableInference.Desc.K13.Law.gp_in_scope
#print axioms VerifiableInference.Desc.K13.Law.gpOf_in_scope
#print axioms VerifiableInference.Desc.K13.Law.lettersBy_first
#print axioms VerifiableInference.Desc.K13.Law.blankBy_first
#print axioms VerifiableInference.Desc.K13.Law.wMsg_in_scope
#print axioms VerifiableInference.Desc.K13.Law.indexCode_in_scope
#print axioms VerifiableInference.Desc.K13.Law.indexLast_in_scope
#print axioms VerifiableInference.Desc.K13.Law.opening_in_scope
#print axioms VerifiableInference.Desc.K13.Law.w_in_scope
#print axioms VerifiableInference.Desc.K13.Law.later_in_scope
