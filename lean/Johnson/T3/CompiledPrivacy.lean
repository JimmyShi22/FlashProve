-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/CompiledPrivacy.lean: the compiler theorem on zero knowledge, proved: Spec.compiled_indexPrivacy of
VerifiableInference/Final/CompilerTheorems.lean, for ANY protocol, its three provers, a layout of hash queries and settings.
What is claimed is an implication from honest-verifier zero knowledge of the provers as interactive oracle proofs: this file proves zero
knowledge of no protocol. The scheme is the one over typed oracles, with the whole key shown (one hash function: CompilerAtVerifyProofs.lean).
How: the premise's clauses on each run give the library's conditions on simulators (at error 0) and on stops; the rest of PremW is
RunValuesAreSent, the conditions on coins, and the public conditions. Then wholeKeyPrivacy (Johnson/WholeKey/Main.lean).
  good_of_runByRun, stops_of_runByRun, ext_of_tables, noProverSide_of_public   the parts
  compiled_indexPrivacy   the statement

The proof does not use the statement's fields twoIndices, work and wholeView.
-/
import VerifiableInference.Final.CompilerTheorems
import Johnson.WholeKey.Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open OnBytes.Prover OnBytes.WholeKey Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X} {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}

/-- The statement's tables are ExtEnc. -/
theorem ext_of_tables {provers : HonestProvers L} (h : provers.SpeakOfTheirTables) :
    ExtEnc provers.toRecs :=
  ⟨h.offline, h.link, h.online⟩

/-- **The statement's first line gives the simulators' goodness, at error 0.** -/
theorem good_of_runByRun {w : HashLayout L offlineRoundMarks linkRoundMarks} {provers : HonestProvers L}
    {simulators : RunSimulators L} {inRange : I → Prop} {Served : I → X → Prop} {N : Budget}
    (h : RunByRun w.work provers simulators inRange Served N) :
    Sims.Good simulators.toSims provers.toRecs w.queryLayout inRange (fun _ => True) Served 0 0 0 where
  T := fun i r e hi _ => le_trans (pr_mono _ (by
    rintro ρ ⟨h1, h2⟩
    have q := h.offline (i, r, e) _ ⟨hi, rfl⟩ ρ h1
    rw [h.tables.offline] at q
    exact h2 q)) (le_of_eq (pr_empty _))
  Lk := fun i r e r' e' hi _ _ => le_trans (pr_mono _ (by
    rintro ρ ⟨h1, h2⟩
    have q := h.link (i, (r, e), (r', e')) _ ⟨hi, rfl⟩ ρ h1
    rw [h.tables.link] at q
    exact h2 q)) (le_of_eq (pr_empty _))
  B := fun n i r e x hi _ hx => le_trans (pr_mono _ (by
    rintro ρ ⟨h1, h2⟩
    have q := h.online n (i, r, e) _ ⟨hi, rfl, hx⟩ ρ h1
    have hext : (provers.onlineAtCopy n).ext (i, r, e) = L.encodeIndex i r := h.tables.online i r e n
    rw [hext] at q
    exact h2 q)) (le_of_eq (pr_empty _))

/-- **The statement's number is the private stops' measure.** -/
theorem stops_of_runByRun {w : HashLayout L offlineRoundMarks linkRoundMarks} {provers : HonestProvers L}
    {simulators : RunSimulators L} {inRange : I → Prop} {Served : I → X → Prop} {N : Budget}
    (h : RunByRun w.work provers simulators inRange Served N) :
    StopsSmall provers.toRecs w.queryLayout inRange (fun _ => True) Served N.offlineStops
      N.linkStops N.onlineStops where
  T := fun i r e hi _ => h.offlineStops (i, r, e) _ ⟨hi, rfl⟩
  Lk := fun i r e r' e' hi _ _ => h.linkStops (i, (r, e), (r', e')) _ ⟨hi, rfl⟩
  B := fun n i r e x hi _ hx => h.onlineStops n (i, r, e) _ ⟨hi, rfl, hx⟩

/-- **Index privacy of the compiled protocol, from the statement's clauses.** -/
theorem compiled_indexPrivacy : Spec.compiled_indexPrivacy := by
  intro I X L offlineRoundMarks linkRoundMarks w provers s simulators inRange Served N sessionsPerCopy R fixedIndex
    hZK hRun hCoins hPub hRel
  have hP : PremW w.queryLayout w.seedQueries w.answerCode w.compilerParameters
      (honestSide w provers s) simulators.toSims inRange (fun _ => True) Served s.coinNumbers
      (numbersOf N sessionsPerCopy) :=
    { ext := ext_of_tables hZK.runByRun.tables
      runVals := hRun
      reads := hPub.tableHides
      budget₀ := hPub.firstTableBudget
      budget₁ := hPub.copyBudget
      good := good_of_runByRun hZK.runByRun
      stops := stops_of_runByRun hZK.runByRun
      seeds := by
        refine le_trans (pr_mono _ ?_) (le_of_eq (pr_empty _))
        intro u hu
        exact hu trivial
      freeT := hPub.readsIgnoreNoncesOffline
      freeL := hPub.readsIgnoreNoncesLink
      freeB := hPub.readsIgnoreNoncesOnline
      wires := hPub.layoutIsLawful
      fmt := hPub.everyRoundHasAFormat
      backT := hPub.noncesAreReadBackOffline
      backL := hPub.noncesAreReadBackLink
      backB := hPub.noncesAreReadBackOnline
      plain := hPub.seedQueriesAreFirstTries
      coherent := hPub.marksAreCoherent
      isLocal := hPub.verifiersReadWhereTheySay
      coins := hCoins }
  exact wholeKeyPrivacy I X 256 L w.LeafBody offlineRoundMarks linkRoundMarks
    w.queryLayout w.seedQueries w.answerCode w.fixedSample w.compilerParameters
    (honestSide w provers s) simulators.toSims inRange (fun _ => True) Served s.coinNumbers
    (numbersOf N sessionsPerCopy) R fixedIndex hRel hP

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.compiled_indexPrivacy
