-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotStandLaidAtFull.lean: THE FIRST CHAIN OF THE KEY FILE's HONEST RUN STANDS, WITH NO PREMISE: at the library's three written
full-size public files (VerifierAndGoals.storedPublicFiles): there are a description of these files and the written book's data at which, at EVERY
index in range, all coins of the committer, every OOD seed, all coins of the run, EVERY border from 0 to 19 and EVERY list of
challenges that fits the rounds in front of it, the pair stands: the offline prover's first thread with its letter
(laidFirst, laidSaid, E2E/LotJoinLaid.lean), at the written key of that index, these coins and that seed. And it is said of
something: some index is in range; at every border some list fits.

  described_of_live, described_zFull   public files on which the test says yes have a description; so the written ones
  LotStandLaidAt Z, standLaid_at   the statement's text at a letter Z; it holds in scope where the test on the files says yes
  standLaid_zFull   THE STATEMENT: LotStandLaidAt storedPublicFiles, with no premise
  LotFoldSixteenAt Z, foldSixteen_of_stand, foldSixteen_zFull   a corollary: the verifier's fold over the first sixteen
                  sub-protocols RETURNS at rounds that drew any fitting list: so the premise of HeardOfFold
                  (E2E/FirstHEval.lean; E2E/LotHeardOfFold.lean) has members
  heard_at_members   lotHeardOfFold called at a return of that form: Lean's check that the form is the premise's own

By what: calls. standLaid_guarded (E2E/LotStandLaid.lean) with each of its five premises paid: the test on the public files:
AtFullSide.Top.theLive_zFull · scope: VerifierAndGoals.inScope_full · the book: full_made (E2E/KeyBookPassesNamed.lean) · the
description: key_sourced (E2E/KeyPublic.lean) · the relation: relKey_of (E2E/KeyTied.lean). An index in range: the matrix 0
(Johnson.Pack.inRange_zero, Johnson/Top/H/KeyMeaning.lean). After the pattern of stands_bare_zFull (E2E/KeyStartsBare.lean).

Limits. THAT THE TEST ON THE PUBLIC FILES SAYS YES AT storedPublicFiles IS A THEOREM OF THE SIDE LIBRARY (AtFullSide). storedPublicFiles IS A VALUE IN LEAN: it
is tied to no file on a disk. One triple of public files. A stand is a sentence "there is": it names no state, and nothing here
says that the frame's own run passes through it. The sentence is as strong as the files beneath it are right.
 The first chain alone: nothing on the shared or the last chain. No measure. Nothing on
soundness, completeness, hiding or binding.
-/
import E2E.LotStandLaid
import E2E.KeyStartsBare
import Johnson.Top.H.KeyMeaning

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles key_sourced relKey_of)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription)
open AtPublicFiles.Committed (AZ PadZ holdZ recAt)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub full_made)
open VerifierAndGoals (storedPublicFiles)
open ProofFile.Honest

/- As in E2E/KeyTied.lean: the search for this instance runs out of time. -/
local instance (priority := high) padsAtTheCrown : Nonempty AtPublicFiles.Committed.PadZ :=
  AtPublicFiles.Committed.pads_nonempty OnBytes.Slice.frS 402653181

/-- Public files on which the test says yes have a description. Stated at a letter Z: at the value storedPublicFiles Lean's kernel
would unfold the files. -/
theorem described_of_live (Z : VerifierAndGoals.PublicFiles) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ d, offlineDescription Z = .ok d := by
  obtain ⟨X, N, P, hs⟩ := key_sourced Z live
  obtain ⟨X₀, m, h0, hm, hX, hN, hP⟩ := hs.source
  exact ⟨⟨X, N, P⟩, by
    simp only [offlineDescription, h0, hm, hX, hN, hP, bind, Except.bind, pure, Except.pure]⟩

/-- The written public files have a description. -/
theorem described_zFull : ∃ d, offlineDescription storedPublicFiles = .ok d :=
  described_of_live storedPublicFiles AtFullSide.Top.theLive_zFull

/-- **The first chain stands at three public files Z**: the statement's text, at a letter Z. -/
def LotStandLaidAt (Z : VerifierAndGoals.PublicFiles) : Prop :=
  (∃ w₀ : FullSizeMatrix, AtPublicFiles.AtFiles.inRange w₀) ∧
    ∃ (d : OfflineDescription) (K₀ : KeyPub), offlineDescription Z = .ok d ∧
      fullPub = some K₀ ∧
      ∀ w₀ : FullSizeMatrix, AtPublicFiles.AtFiles.inRange w₀ → ∀ (rc : (protocolAtFiles Z).EncodingRandomness) (sd : (protocolAtFiles Z).OutOfDomainSeed)
        (k : Coins (keyBook K₀)) (b : Nat), b ≤ 19 →
        (∃ ds, drawsFit (declsTo (laidFirst Z d K₀ (w₀, rc, sd)
            (keyInstanceOfOutOfDomainSample (recAt (AZ Z) PadZ (holdZ Z) w₀ rc sd))).bs b) ds = true) ∧
          ∀ ds, drawsFit (declsTo (laidFirst Z d K₀ (w₀, rc, sd)
              (keyInstanceOfOutOfDomainSample (recAt (AZ Z) PadZ (holdZ Z) w₀ rc sd))).bs b) ds = true →
            ∃ s m E, ThrS (laidFirst Z d K₀ (w₀, rc, sd)
                (keyInstanceOfOutOfDomainSample (recAt (AZ Z) PadZ (holdZ Z) w₀ rc sd)))
              (laidSaid Z d K₀ (w₀, rc, sd)
                (keyInstanceOfOutOfDomainSample (recAt (AZ Z) PadZ (holdZ Z) w₀ rc sd))) b k s m E ∧
              m.st.heard = ds ∧
              m.st.input = inFirst w₀ rc (keyInstanceOfOutOfDomainSample (recAt (AZ Z) PadZ (holdZ Z) w₀ rc sd))

/-- It holds at all public files in scope on which the test says yes. Proved at a letter Z, for the kernel's sake. -/
theorem standLaid_at (Z : VerifierAndGoals.PublicFiles) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (scope : VerifierAndGoals.InScope Z = true) : LotStandLaidAt Z := by
  obtain ⟨d, hd⟩ := described_of_live Z live
  obtain ⟨K₀, hK⟩ := full_made
  exact ⟨⟨_, Johnson.Pack.inRange_zero⟩, d, K₀, hd, hK, fun w₀ hw rc sd k =>
    standLaid_guarded hd scope live hK (w₀, rc, sd) _
      (relKey_of (AZ Z) PadZ (holdZ Z) AtPublicFiles.AtFiles.inRange w₀ rc sd hw) k⟩

/-- **THE FIRST CHAIN STANDS, WITH NO PREMISE**: at the library's three written full-size public files. -/
theorem standLaid_zFull : LotStandLaidAt storedPublicFiles :=
  standLaid_at storedPublicFiles AtFullSide.Top.theLive_zFull VerifierAndGoals.inScope_full

/-- **The fold over the first sixteen sub-protocols returns**: the premise of HeardOfFold (E2E/FirstHEval.lean) has members:
the text, at a letter Z. Some list of challenges fits the rounds in front of border 16; and at every index in range, all
coins and every such list there are rounds that drew just that list on which the verifier's fold from the chain's start
returns, with nothing left over. -/
def LotFoldSixteenAt (Z : VerifierAndGoals.PublicFiles) : Prop :=
  (∃ w₀ : FullSizeMatrix, AtPublicFiles.AtFiles.inRange w₀) ∧
    ∃ (d : OfflineDescription) (K₀ : KeyPub), offlineDescription Z = .ok d ∧ fullPub = some K₀ ∧
      ∀ w₀ : FullSizeMatrix, AtPublicFiles.AtFiles.inRange w₀ → ∀ (rc : (protocolAtFiles Z).EncodingRandomness) (sd : (protocolAtFiles Z).OutOfDomainSeed)
        (_ : Coins (keyBook K₀)),
        (∃ ds, drawsFit (declsTo (AtPublicFiles.KeyThread.D d.source d.numbers d.later).first.blocksInOrder 16) ds =
          true) ∧
          ∀ ds, drawsFit (declsTo (AtPublicFiles.KeyThread.D d.source d.numbers d.later).first.blocksInOrder 16) ds =
              true →
            ∃ seen cols s, seen.map (·.drawn) = ds ∧
              VerifiableInference.Desc.foldBlocks 0
                ((AtPublicFiles.KeyThread.D d.source d.numbers d.later).first.blocksInOrder.take 16)
                ((AtPublicFiles.KeyThread.D d.source d.numbers d.later).start₁
                  (keyInstanceOfOutOfDomainSample (recAt (AZ Z) PadZ (holdZ Z) w₀ rc sd))) seen cols = .ok (s, [], [])

/-- It follows from the stand at border 16: the thread's clause «the state is what the fold returns». -/
theorem foldSixteen_of_stand {Z : VerifierAndGoals.PublicFiles} (h : LotStandLaidAt Z) : LotFoldSixteenAt Z := by
  obtain ⟨hw, d, K₀, hd, hK, hall⟩ := h
  refine ⟨hw, d, K₀, hd, hK, fun w₀ hw₀ rc sd k => ?_⟩
  obtain ⟨hsome, hst⟩ := hall w₀ hw₀ rc sd k 16 (by decide)
  refine ⟨hsome, fun ds hds => ?_⟩
  obtain ⟨s, m, E, hT, hh, hi⟩ := hst ds hds
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hT.1.2.2.2.2.1
  have hb : s₀ = (AtPublicFiles.KeyThread.D d.source d.numbers d.later).start₁ m.st.input.x := hbeg
  subst hb
  rw [hi] at hfold
  exact ⟨m.seen, cols, s, hseen.trans hh, hfold⟩

/-- **At the written public files, with no premise.** -/
theorem foldSixteen_zFull : LotFoldSixteenAt storedPublicFiles := foldSixteen_of_stand standLaid_zFull

/-- **HeardOfFold is spent at these members**: that the returns above are of the very form that HeardOfFold's premise has is
held by Lean's own check of this call: at each of them the state holds its claims on the keys at the prover's points. -/
theorem heard_at_members {Z : VerifierAndGoals.PublicFiles} (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (scope : VerifierAndGoals.InScope Z = true) {d : OfflineDescription} (hd : offlineDescription Z = .ok d)
    (x : VerifiableInference.Desc.Key.Xi) (seen : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (s : VerifiableInference.Desc.Key.FirstState)
    (h : VerifiableInference.Desc.foldBlocks 0
      ((AtPublicFiles.KeyThread.D d.source d.numbers d.later).first.blocksInOrder.take 16)
      ((AtPublicFiles.KeyThread.D d.source d.numbers d.later).start₁ x) seen cols = .ok (s, [], []))
    (tail : List Fmt.Drawn) :
    HeardAtKeys d.source d.numbers (seen.map (·.drawn) ++ tail) s :=
  lotHeardOfFold (sourced_of_description hd live) scope x seen cols s [] [] h tail

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.described_of_live
#print axioms AtPublicFiles.FirstH.Lots.described_zFull
#print axioms AtPublicFiles.FirstH.Lots.standLaid_at
#print axioms AtPublicFiles.FirstH.Lots.standLaid_zFull
#print axioms AtPublicFiles.FirstH.Lots.foldSixteen_of_stand
#print axioms AtPublicFiles.FirstH.Lots.foldSixteen_zFull
#print axioms AtPublicFiles.FirstH.Lots.heard_at_members
