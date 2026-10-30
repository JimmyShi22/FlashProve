-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRangesOnAtRun.lean: `OnAtRun₁` (Johnson/Desc/ProofFile/Honest/Law/OwedAtRun.lean) AT THE ROW OF THE KEY FILE's
PROXIMITY TEST ON THE RANGES (the first chain's place ⟨1,–,5⟩), CONDITIONAL ON TWO NAMED PREMISES (hI, O below):
`onAtRun_ranges_book` (…/K12/Sim2/RowRangesPub.lean) with its premise hleft paid by the bridge of
E2E/OfflineRangesAsks.lean, out of the sentence `InsideOf` that this premise is handed.

  `insideOf_mono`            `InsideOf` at a weaker invariant
  `ranges_cut_fifteen`       in scope fifteen sub-protocols stand in front of the one at the test's place
  `onAtRun_ranges_thread`    **the statement**

WHAT IS ASKED, beside the row's letters (hplace, hrow, hOn), the filling (hg, hgS) and one public number (hj):
  hI   THE FAMILY OF INVARIANTS T GIVES, AT THE BORDER 15, THE FIRST CHAIN's THREAD: wherever T.I₁ 15 holds at the
       run's coins, `Thr (laid₁ …) 15` holds. No family with this property is given here
  O    `OwesAtRanges`: `RangesOwes` at every stand of the thread at 15, at the coins that the book lends: it holds
       the one sentence on values

Limits. Both are premises: no member of either is given here: the rule moves the debt and pays none of it. The
condition reads the input and the carried values: no later law may take it as a hypothesis on a run and then
speak of the random values as sampled anew. Nothing on any property.
-/
import E2E.OfflineRangesAsks
import E2E.OfflineSides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Sim2 (LeftAtRanges simRanges OnEntry onAtRun_ranges_book)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces pieces)
open OnBytes.Slice (GF)
open H2K.Member (piKRFull codesKeyFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace msgPlace rideMsg)
open AtPublicFiles.KeyThread (rangesTestJob laid₁ KeyFill)
open AtPublicFiles.Key (msgJob)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-- `InsideOf` at a weaker invariant. -/
theorem insideOf_mono {S Cl V W Y Pb : Type} {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain : ℕ}
    {hs : List (Placed V W Y)} {b : Block S Cl} {A A' : Coins Bk → S → Mid W Y → Env → Prop} {n : ℕ}
    {k : Coins Bk} {m : Mid W Y} {E : Env} (h : ∀ s m E, A k s m E → A' k s m E)
    (hin : InsideOf φ Bk chain hs b A n k m E) : InsideOf φ Bk chain hs b A' n k m E := by
  obtain ⟨s, m₀, E₀, l, ds, y, hA, r⟩ := hin
  exact ⟨s, m₀, E₀, l, ds, y, h _ _ _ hA, r⟩

section Key
variable {W₀ Rc Ky Cells M Smp Rec : Type} {Z : PublicFiles} {K : KeyPub} {Xs : Source} {N : H2U.PlaceNums}
  {Pl : LaterPlaces}

/-- In scope fifteen sub-protocols stand in front of the one at the test's place. -/
theorem ranges_cut_fifteen (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {pre t : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)}
    {b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl}
    (hcut : (keyFileDescription Xs N Pl).first.blocksInOrder = pre ++ b :: t) (hbp : b.place = rngPlace) :
    pre.length = 15 :=
  AtPublicFiles.KeyThread.length_of_cut (fun b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl => b.place)
    (keyFileDescription Xs N Pl).first.blocksInOrder pre t b (AtPublicFiles.KeyBook.fullFirst.map (·.1)) rngPlace 15 hcut
    (places_of_rows (AtPublicFiles.KeyBook.places_named scope hsrc.named).1) (by decide) hbp (by decide)

/-- **`OnAtRun₁` at the row of the test on the ranges, from the first chain's thread at the border 15.** -/
theorem onAtRun_ranges_thread (scope : InScope Z = true) (hsrc : KeySourced Z Xs N Pl)
    (hK : fullPub = some K) {H : Prover W₀ Rc Xi Ky Unit Unit Unit}
    {G : Sides (keyFileDescription Xs N Pl) (keyBook K) W₀ Rc Ky Unit Unit Unit} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins (keyBook K)} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit Unit Unit}
    {r : RunC (keyFileDescription Xs N Pl)}
    (T : ThreadsP (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K) (G.prover H) w₀ rc x k ρ = .ok r)
    (entry : Local W₀ Rc Xi Unit → ℕ → ℕ → GF) (groups : List (List ℕ)) (first first' : ℕ)
    (L : Lettered (keyBook K) (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc Xi Unit)
      (Local W₀ Rc Xi Unit) Unit Xi)
    (hplace : L.place = rngPlace)
    (hrow : L.row = testPairs (rangesTestJob (X' := Unit) Xs N Pl entry groups first) (simRanges Xs N Pl))
    (hOn : L.On = OnEntry Face.own (rangesTestJob (X' := Unit) Xs N Pl entry groups first)
      (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first)
    (hg : ((G.prover H).first.find? fun g => g.place == rngPlace) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl entry groups first)))
    (hgS : ((G.prover H).first.find? fun g => g.place == msgPlace) =
      some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit)
        (msgJob (X := Unit) entry Xs.Y.k.oneTime pieces groups first' rideMsg)))
    (hj : treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 1 = 1)
    (Lf : KeyFill (keyBook K) W₀ Rc Cells M Smp Rec)
    (tb : Fmt.TreeSource → Coins (keyBook K) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
    (hI : ∀ s m E, T.I₁ 15 k s m E →
      Thr (laid₁ Xs N Pl Lf w₀ rc x (G.prover H).first tb) 15 k s m E)
    (O : OwesAtRanges Xs N Pl entry groups first Lf w₀ rc x (G.prover H).first tb k) :
    OnAtRun₁ T ρ r L := by
  have hJ : (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p = piKRFull :=
    AtPublicFiles.KeyThread.place_sourced hsrc scope
  refine onAtRun_ranges_book scope hsrc hK T hρ hR hrun entry groups first first' L hplace hrow hOn
    hg hgS hj fun m ca σ pre t hσ S hin _ _ _ hca _ => ?_
  have hbp : σ.block.place = rngPlace :=
    (OnBytes.SendSim.At.place_of_seated hσ).trans (by rw [hJ]; exact ProofFile.Honest.K12.Sim2.place_KR)
  have hto : σ.roundsTo 1 = firstLen piKRFull.nums.stages := by
    rw [← hJ, ← Light.first_moves_len (V := Local W₀ Rc Xi Unit)
      (rangesTestJob (X' := Unit) Xs N Pl entry groups first)]
    unfold Side.roundsTo
    rw [OnBytes.SendSim.Seat.row_of_seated hσ]
    simp [testPairs]
  rw [ranges_cut_fifteen hsrc scope S.cut hbp, hto] at hin
  have hbm : σ.block ∈ (keyFileDescription Xs N Pl).first.blocksInOrder := by
    rw [S.cut]
    exact List.mem_append_right _ List.mem_cons_self
  rw [hplace] at hca
  exact ranges_left_of_inside Xs N Pl entry groups first Lf w₀ rc x (G.prover H).first tb hK hsrc
    scope σ.block hbm hbp (by rw [hbp]; exact hg) k m _ (insideOf_mono hI hin) O ca hca

end Key

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.insideOf_mono
#print axioms AtPublicFiles.OfflineRows.ranges_cut_fifteen
#print axioms AtPublicFiles.OfflineRows.onAtRun_ranges_thread
