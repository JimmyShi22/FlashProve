-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFoldedAtRows.lean: the offline file's row of the proximity test on G_u, place ⟨2, –, 9⟩, at the rows offlineRows (E2E/OfflineSides.lean): what the second
clause of OwedRest.owed (E2E/OfflineClauses.lean) asks of the row at that place, from hleft.

  foldedSimulators     the list of two that stands beside the half's two parts: firstSim, restSim at the simulators' job foldedSim
  FoldedLetters        what is asked of the rows' letters S and c at the place: the list is foldedSimulators; the condition at a part is OnEntry at the two
                       jobs; budBoth gives the positions
  LeftAtRun            THE NAMED PREMISE hleft, at one run: where the second part was called, LeftAtFolded at the run's own state and carried blocks
  owed_folded_at_rows  THE STATEMENT, at letters K and at any book that is the written one: at every row of the muted rows' shared list at the place: owedAt
  folded_at_value      the four equations on K hold at valueAt (E2E/KeyValueHolds.lean), in scope

What stays: LeftAtRun · T : ThreadsP, a letter: nothing of it is spent · FoldedLetters · H.storedWords = stOf K (the rows' prover keeps H's stored tables) ·
KeySourced, InScope, fullPub = some K₀, ready, due, silent, the run has returned.
Limits. As the head of E2E/OfflineFoldedOwed.lean. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineFoldedOwed
import E2E.OfflineSides
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows.Folded
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.Sim2
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open H2K.Member (codesKeyFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (proverSideOfTestOnU bsOf stOf wtOf rdOf)
open AtPublicFiles.KeyValueHolds (place_p12At)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y Wk : Type}

/-- The two simulators beside the half's two parts. -/
def foldedSimulators (K : KeyParts W₀ Rc X₀ Y Wk) (Pl : LaterPlaces) : List (Sim TableKey) :=
  [firstSim (foldedSim K Pl), restSim (foldedSim K Pl)]

/-- **What is asked of the rows' letters at the place.** -/
structure FoldedLetters {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc X₀ Y Wk) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y) : Prop where
  simulators : S.byChain.shared foldedTestPlace = foldedSimulators K Pl
  atPart : (c.shared foldedTestPlace).atPart =
    OnEntry Face.shared (foldedJob K Pl) (foldedSim K Pl) codesKeyFull 1 (pKU Pl).nums.first
  positions : ∀ n ds asks, budBoth (foldedSim K Pl) n ds asks →
    (c.shared foldedTestPlace).positions n ds asks

/-- **What is left, at one run**: where the second part was called, the two clauses on the asks at the run's own state and carried
blocks. -/
def LeftAtRun {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc X₀ Y Wk) (P : Prover W₀ Rc Xi TableKey Unit X₀ Y) (w₀ : W₀)
    (rc : Rc) (x : Xi) (k : Coins Bk) (ρ : Draws) (called : Addr → Bool) : Prop :=
  called ⟨foldedTestPlace, 1⟩ = true → ∀ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
    (ca : CsAll (restMember (V := Empty) (foldedJob K Pl) (foldedSim K Pl)).part.carries),
    midSharedAtW (keyFileDescription Xs N Pl) Bk P w₀ rc x k ρ ⟨foldedTestPlace, 1⟩ = .ok (some m) →
    carriedAt Bk k 1 ⟨foldedTestPlace, 1⟩
      (restMember (V := Empty) (foldedJob K Pl) (foldedSim K Pl)).part = .ok ca →
    LeftAtFolded (foldedJob K Pl) codesKeyFull (pKU Pl).nums.first (stretches _ ca) m

/-- **owedAt at the row of the test on G_u, at the muted offline rows, from what is left.** -/
theorem owed_folded_at_rows (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc X₀ Y Wk) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfTestOnU K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))
    (hOp : K.onOmega.place = omegaTestPlace) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ Y)
    (hc : FoldedLetters (Xs := Xs) (N := N) (Pl := Pl) K S c)
    (H : Prover W₀ Rc KeyInst TableKey Unit X₀ Y) (hst : H.storedWords = stOf K)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) Bk
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hsil : silentAt (keyFileDescription Xs N Pl)
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x ρ = none)
    (hR : ready (keyFileDescription Xs N Pl) Bk
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) Bk
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ = .ok r)
    (hleft : LeftAtRun (Xs := Xs) (N := N) (Pl := Pl) K
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ r.called) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, L.place = foldedTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  subst hB
  intro L hL hp
  have hUp : K.onU.place = foldedTestPlace := by
    rw [hU]
    exact place_p12At _ _
  have hpt : (pKU Pl).place = foldedTestPlace := H2K.JointK.place_of_p12At _ _
  -- the row is the row of the letter onU
  obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL₀
  have hgp : g.place = foldedTestPlace := hp
  obtain rfl : g = K.onU :=
    List.inj_on_of_nodup_map (shared_nodup' K hsp hUp hOp) hg
      (List.mem_append_right _ List.mem_cons_self) (hgp.trans hUp.symm)
  have hsh : ((offlineRows (keyFileDescription Xs N Pl) (keyBook K₀) K S c).mute.prover H).shared =
      (keyProver K).shared := by
    rw [prover_mute, offlineRows_prover_at]
  have hst' : ((offlineRows (keyFileDescription Xs N Pl) (keyBook K₀) K S c).mute.prover H).storedWords =
      stOf K := by
    rw [prover_mute, offlineRows_prover_at]
    exact hst
  have hrow : (rowOf (Cl := (keyFileDescription Xs N Pl).Cl) K.onU (S.byChain.shared K.onU.place)
      (c.shared K.onU.place)).mute.row = testPairs (foldedJob K Pl) (foldedSim K Pl) := by
    show partsBeside K.onU.parts (S.byChain.shared K.onU.place) = _
    rw [hUp, hc.simulators, hU]
    rfl
  have hOn : (rowOf (Cl := (keyFileDescription Xs N Pl).Cl) K.onU (S.byChain.shared K.onU.place)
      (c.shared K.onU.place)).mute.On =
      OnEntry Face.shared (foldedJob K Pl) (foldedSim K Pl) codesKeyFull 1 (pKU Pl).nums.first := by
    show (c.shared K.onU.place).atPart = _
    rw [hUp]
    exact hc.atPart
  have hbudL : ∀ n ds asks, budBoth (foldedSim K Pl) n ds asks →
      (rowOf (Cl := (keyFileDescription Xs N Pl).Cl) K.onU (S.byChain.shared K.onU.place)
        (c.shared K.onU.place)).mute.bud n ds asks := by
    intro n ds asks hb
    show (c.shared K.onU.place).positions n ds asks
    rw [hUp]
    exact hc.positions n ds asks hb
  refine owedAt_folded scope hS hK K hsend hsp hU hOp hsh hst' T hρ hsil hR hrun hL
    (hp.trans hpt.symm) hrow hOn hbudL ?_
  intro hcl m ca hm hca
  have hp' : (rowOf (Cl := (keyFileDescription Xs N Pl).Cl) K.onU (S.byChain.shared K.onU.place)
      (c.shared K.onU.place)).mute.place = foldedTestPlace := hp
  rw [hp'] at hcl hm hca
  exact hleft hcl m ca hm hca

/-- **The four equations on K at the value**, in scope, at the two tests' own numbers. -/
theorem folded_at_value {W₀ Rc : Type} (hS : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (K' : KeyParts W₀ Rc Unit Unit AtPublicFiles.KeyValues.WitK) (f : W₀ → Weights) (g : Rc → Nat → TableRand)
    (inR : W₀ → Bool) (d : W₀) (pO : VerifiableInference.Desc.K12.P12) (hO : pO.place = omegaTestPlace)
    (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF) (groups : List (List Nat)) (first : Nat) :
    (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first).send =
        ⟨parKey Xs Pl, 0⟩ ∧
      (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first).lin.S.sharedSplitNeeded =
        true ∧
      (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first).onU =
        proverSideOfTestOnU (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first).send (pKU Pl)
          (bsOf (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first))
          (stOf (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first))
          (wtOf (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first))
          (rdOf (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first)) ∧
      (AtPublicFiles.KeyValueHolds.valueAt K' Xs N Pl f g inR d (pKU Pl) pO ent groups first).onOmega.place =
        omegaTestPlace := by
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hS scope
  exact ⟨rfl, hQ.facts.two, rfl, hO⟩

end AtPublicFiles.OfflineRows.Folded

#print axioms AtPublicFiles.OfflineRows.Folded.owed_folded_at_rows
#print axioms AtPublicFiles.OfflineRows.Folded.folded_at_value
