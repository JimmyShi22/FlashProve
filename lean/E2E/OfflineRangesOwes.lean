-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRangesOwes.lean: at the key file's proximity test on the ranges (the first chain's place ⟨1,–,5⟩): WHAT IS
STILL OWED WHEREVER THE FIRST CHAIN's THREAD STANDS AT THE BORDER 15 (`OwesAtRanges`, E2E/OfflineRangesAsks.lean) IS PAID at
the thread of the honest filling (`Th`, `Fl`, `tbH`: E2E/FirstHSeat.lean, E2E/FirstHFill.lean), at all coins; so
`OnAtRun₁` at the test's row (E2E/OfflineRangesOnAtRun.lean) is left with ONE named premise on the run.

  `owes_at_ranges`       `OwesAtRanges` at that thread, from what is public at the three sendings (`FirstPublic`,
                       E2E/FirstHSeats.lean): an assembly of `owes_of_thr` (E2E/KeyRangesGrows.lean), `wit_is_job`,
                       `tb_is_sent` (E2E/FirstHRangeLots.lean), `old_of_tb` (E2E/KeyRangesWholeS.lean) and the three
                       closed lines of E2E/FirstHRangeClosed.lean
  `onAtRun_ranges_one`   **`OnAtRun₁` at the row, from hI alone**: the family of invariants T gives, at the border
                       15, that thread

Limits. hI IS A PREMISE: no family with this property is given here. THE SENTENCE ON VALUES IS MOVED, NOT PROVED: "the
group's open rows say true things of the member's words" is taken off the thread's own open sentence at the
border 15: it is owed by whoever shows that the thread stands there. The row's letters (hplace, hrow, hOn) and
the filling (hfirst, hg, hgS) are asked. The condition reads the input and the carried values: no later law may
take it as a hypothesis on a run and then speak of the random values as sampled anew. Nothing on any property.
-/
import E2E.OfflineRangesOnAtRun
import E2E.FirstHRangeClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Sim2 (simRanges OnEntry)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces pieces)
open H2K.Member (piKRFull codesKeyFull)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace msgPlace rideMsg)
open AtPublicFiles.KeyThread (rangesTestJob)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open AtPublicFiles.Key (msgJob)
open AtPublicFiles.FirstH (FirstPublic Th Fl tbH LaterFill tb_is_sent wit_is_job msg_zero msg_shape carry_fits)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

variable {W₀ Rc X₀ Wk : Type} {Z : PublicFiles} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums}
  {Pl : LaterPlaces} {K : KeyParts W₀ Rc X₀ Unit Wk} {f : W₀ → Weights}
  {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀} {rc : Rc} {x : Xi}

/-- **What is still owed at the border 15 is paid at the thread of the honest filling**, at all coins. -/
theorem owes_at_ranges (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (hp : FirstPublic (Pl := Pl) Xs N K f) (k : Coins (keyBook K₀)) :
    OwesAtRanges Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 (Fl Xs N Pl K f Q x) w₀ rc x
      (keyProver K).first (tbH Xs N Pl K f Q) k :=
  fun _ m _ c hT hc =>
    AtPublicFiles.KeyThread.owes_of_thr Xs N Pl _ _ 0 _ w₀ rc x _ _ hs scope hT _
      (wit_is_job hs scope hK hp (msg_zero hs scope hp) (msg_shape hs scope hp)
        (carry_fits hs scope hK hp) hT c hc)
      (AtPublicFiles.KeyThread.old_of_tb Xs N Pl _ _ 0 _ w₀ rc x _ _ hK hs scope c hT hc (tb_is_sent hp k m))

/-- **`OnAtRun₁` at the row of the test on the ranges, from one named premise on the run.** -/
theorem onAtRun_ranges_one {Ky : Type} (scope : InScope Z = true) (hs : KeySourced Z Xs N Pl)
    (hK : fullPub = some K₀) (hp : FirstPublic (Pl := Pl) Xs N K f)
    {H : Prover W₀ Rc Xi Ky Unit Unit Unit}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook K₀) W₀ Rc Ky Unit Unit Unit}
    {k : Coins (keyBook K₀)} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit Unit Unit}
    {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k ρ = .ok r) (first' : ℕ)
    (L : Lettered (keyBook K₀) (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Unit Xi)
    (hplace : L.place = rngPlace)
    (hrow : L.row = testPairs (rangesTestJob (X' := Unit) Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0)
      (simRanges Xs N Pl))
    (hOn : L.On = OnEntry Face.own (rangesTestJob (X' := Unit) Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0)
      (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first)
    (hfirst : (G.prover H).first = (keyProver K).first)
    (hg : ((G.prover H).first.find? fun g => g.place == rngPlace) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0)))
    (hgS : ((G.prover H).first.find? fun g => g.place == msgPlace) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit)
        (msgJob (X := Unit) (matrixEntryOf (Rc := Rc) f) Xs.Y.k.oneTime pieces (multiplicitiesGroups Xs) first'
          rideMsg)))
    (hI : ∀ s m E, T.I₁ 15 k s m E → Thr (Th Xs N Pl K f Q w₀ rc x) 15 k s m E) :
    OnAtRun₁ T ρ r L :=
  onAtRun_ranges_thread scope hs hK T hρ hR hrun (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0 first' L hplace
    hrow hOn hg hgS hp.treesAt1 (Fl Xs N Pl K f Q x) (tbH Xs N Pl K f Q)
    (by rw [hfirst]; exact hI) (by rw [hfirst]; exact owes_at_ranges hs scope hK hp k)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.owes_at_ranges
#print axioms AtPublicFiles.OfflineRows.onAtRun_ranges_one
