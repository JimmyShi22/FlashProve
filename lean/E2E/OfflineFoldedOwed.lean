-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineFoldedOwed.lean: the offline file's row of the proximity test on G_u: Lettered.owedAt at its list, at a run that has returned, from hleft.

  bud_folded                 the list's bud at the test on G_u: budOwed₂_at_KU (Johnson/M1/KeyBudU.lean) at the senders' own job
  owedAt_folded              THE STATEMENT at letters G, H, L: by owedAt_shared_of_onAtRun (E2E/OfflineOwedRowAtRun.lean) and onAtRun_folded_paid
                             (E2E/OfflineFoldedPaid.lean)

What stays. hleft (where the second part was called: LeftAtFolded at the run's own state and carried blocks) · T : ThreadsP, a letter: nothing of it is spent · the row's letters hplace, hrow, hOn,
hbudL («budBoth gives the list's bud») · the ties of the sides' prover to keyProver K and the four equations on K (E2E/OfflineFoldedPaid.lean) · KeySourced,
InScope, fullPub = some K₀, ready, due, silent.
Limits. The rule moves the debt and pays none of it. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineFoldedPaid
import E2E.OfflineOwedRowAtRun
import E2E.KeyBookThirdNamed
import Johnson.M1.KeyBudU

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows.Folded
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.Sim2
open OnBytes (TableKey)
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open H2K.Member (codesKeyFull piKUFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub omegaTestPlace)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyLay (proverSideOfTestOnU bsOf stOf wtOf rdOf)

section Row
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ Y Wk : Type}

/-- **The list's bud at the test on G_u**, at the senders' own job. -/
theorem bud_folded (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc X₀ Y Wk)
    (L : Lettered Bk (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (hplace : L.place = (pKU Pl).place)
    (hrow : L.row = testPairs (foldedJob K Pl) (foldedSim K Pl))
    (hbudL : ∀ n ds asks, budBoth (foldedSim K Pl) n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (keyFileDescription Xs N Pl).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (keyFileDescription Xs N Pl) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (keyFileDescription Xs N Pl) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (keyFileDescription Xs N Pl).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  obtain ⟨pk, Al⟩ := alike_KU scope hS
  obtain ⟨b, hf, hbp, hr, hor⟩ := find_folded scope hS.named (foldedJob K Pl) rfl
  exact OnBytes.M1.KeyBud.budOwed₂_at_KU scope hS.named L (foldedJob K Pl)
    (facts_KU facts_KUFull _ pk Al) (congrArg (·.stages) Al.nums) (H2K.JointK.place_of_p12At _ _) hf hbp
    hr hor rfl (foldedSim K Pl) rfl rfl hplace hrow hbudL

/-- **owedAt at the list of the test on G_u, from hleft.** -/
theorem owedAt_folded (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K₀ : KeyPub}
    (hK : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ Y Wk) (hsend : K.send = ⟨parKey Xs Pl, 0⟩)
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfTestOnU K.send (pKU Pl) (bsOf K) (stOf K) (wtOf K) (rdOf K))
    (hOp : K.onOmega.place = omegaTestPlace)
    {H : Prover W₀ Rc Xi TableKey Unit X₀ Y}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook K₀) W₀ Rc TableKey Unit X₀ Y}
    (hsh : (G.prover H).shared = (keyProver K).shared) (hst : (G.prover H).storedWords = stOf K)
    {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins (keyBook K₀)} {ρ : Draws}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hsil : silentAt (keyFileDescription Xs N Pl) (G.prover H) w₀ rc x ρ = none)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k ρ = .ok r)
    {L : Lettered (keyBook K₀) (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc TableKey) X₀
      TableKey} (hL : L ∈ G.shared)
    (hplace : L.place = (pKU Pl).place)
    (hrow : L.row = testPairs (foldedJob K Pl) (foldedSim K Pl))
    (hOn : L.On = OnEntry Face.shared (foldedJob K Pl) (foldedSim K Pl) codesKeyFull 1
      (pKU Pl).nums.first)
    (hbudL : ∀ n ds asks, budBoth (foldedSim K Pl) n ds asks → L.bud n ds asks)
    (hleft : r.called ⟨L.place, 1⟩ = true → ∀ (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀)
      (ca : CsAll (restMember (V := Empty) (foldedJob K Pl) (foldedSim K Pl)).part.carries),
      midSharedAtW (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k ρ ⟨L.place, 1⟩ = .ok (some m) →
      carriedAt (keyBook K₀) k 1 ⟨L.place, 1⟩
        (restMember (V := Empty) (foldedJob K Pl) (foldedSim K Pl)).part = .ok ca →
      LeftAtFolded (foldedJob K Pl) codesKeyFull (pKU Pl).nums.first (stretches _ ca) m) :
    L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
      (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) (keyBook K₀) (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called :=
  AtPublicFiles.OfflineRows.owedAt_shared_of_onAtRun hS.named.plan (AtPublicFiles.KeyBook.book_passes scope hS.named K₀ hK) hρ hsil
    hR hrun T hL
    (fun σ hσ u hu pre t n hc hn => bud_folded scope hS K L hplace hrow hbudL σ hσ u hu pre t n hc hn ρ hρ)
    (onAtRun_folded_paid scope hS hK K hsend hsp hU hOp hsh hst T hρ hR hrun L hplace hrow hOn hleft)

end Row

end AtPublicFiles.OfflineRows.Folded

#print axioms AtPublicFiles.OfflineRows.Folded.bud_folded
#print axioms AtPublicFiles.OfflineRows.Folded.owedAt_folded
