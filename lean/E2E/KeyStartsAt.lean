--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStartsAt.lean: OF THE SEVEN PREMISES UNDER WHICH THE KEY FILE's SHARED THREAD STANDS AT ITS
FIRST TWO BORDERS (`Starts₂`, E2E/KeySharedStands.lean), WHAT IS HAD AT THE KEY FILE's OWN PROVER
(`keyProver`, E2E/KeyProver.lean) AND AT A FILLING OF THE LETTERS THAT IS TIED TO IT. Short
statements, by calls and one evaluation. NOTHING IS SHOWN OF ANY PROVER's RUN.

  `FilledAt K L`: TWO EQUATIONS ON THE LETTERS, in one structure: the stored table's columns are the
      prover's; the letter that reads the carried OOD sample off the instance is the library's own
      (`recBack`, Johnson/Top/Fire/Code/KeyAtName.lean)
  **`fits_of_own`**: where that letter is the library's and returns something at the instance, THE
      KEY FITS THE SHAPE's INDEX, in scope: the library's `fits_of_recBack`
      (Johnson/Top/Fire/Code/KeyAt32Letters.lean)
  **`bare_key`**: NO HALF OF THE KEY FILE's PROVER STANDS AT THE SHARED CHAIN's FRONT: where the
      prover's parts bear the key file's sixteen places (`KeyParts.AtAll`, E2E/KeyLaid.lean): the
      shared chain's eight by `keyProver_shared`; that none is the front's: by evaluation
  **`starts₂_key`**: so `Starts₂` at `keyProver K` is left with: the frame's own tests go through ·
      `FilledAt` · `KeyParts.AtAll` · something is said of this input · the carried OOD sample is
      there and is the cells' own

(That the key which the prover hands the shared chain is the instance's is `keyProver_key`: by
unfolding.)

Limits.
- NO MEMBER OF `FilledAt` IS TYPED. Parts of a prover that meet `KeyParts.AtAll`: `value_atAll`
  (E2E/OfflineSharedSixAtValue.lean), at `valueAt`: in scope, under `KeySourced` and the two tests'
  places.
- THAT THE FRAME's OWN TESTS GO THROUGH IS A PREMISE HERE; at the offline prover's parts and the
  written book it is `lotReadyReturnsWhole` (E2E/LotReadyWhole.lean), at every index in range, under
  the premises of its statement.
- "The carried OOD sample is the cells' own" stays a premise: it is on what the committer makes.
- `FilledAt` fixes the type of the carried OOD sample to the library's.

-/
import E2E.KeySharedStands
import E2E.KeyProver
import E2E.KeyPlaces
import E2E.KeyLaid
import Johnson.Top.Fire.Code.KeyAt32Letters

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared keyProver_key)
open AtPublicFiles.KeyBook (frontPlace foldedTestPlace omegaTestPlace)
open ProofFile.Honest

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp X₀' X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp OnBytes.Flat.RecFull) (w₀ : W₀) (rc : Rc)
  (x : Xi) (K : KeyParts W₀ Rc X₀' X' Wk) {Z : VerifierAndGoals.PublicFiles}

/-- **The letters are tied to the prover and to the library.** It is a definition: a premise's
form. -/
structure FilledAt : Prop where
  stored : ∀ a c, L.stored a c = (keyProver K).storedWords a c
  sample : L.base.recOf = LPFD.recBack

/-- **The key fits the shape's index**, where the library's own letter returns something. -/
theorem fits_of_own (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hrec : L.base.recOf = LPFD.recBack) {r : OnBytes.Flat.RecFull}
    (hr : L.base.recOf x = some r) : KeyFits Xs x := by
  obtain ⟨X₀, m, h0, hm, hX, -, -⟩ := hs.source
  rw [hrec] at hr
  exact LPFD.fits_of_recBack scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX
    hs.named.plan x r hr

/-- None of the eight places is the front's. -/
theorem front_apart : ∀ a ∈ [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5,
    K14.place 7, K14.place 8, foldedTestPlace, omegaTestPlace], (a == frontPlace) = false := by
  decide

/-- **No half of the key file's prover stands at the shared chain's front.** -/
theorem bare_key (hK : K.AtAll) : ∀ blk, (D Xs N Pl).shared.blocksInOrder[0]? = some blk →
    ((keyProver K).shared.find? fun g => g.place == blk.place) = none := by
  intro blk hblk
  have hb : ∃ b₀, (D Xs N Pl).shared.blocksInOrder[0]? = some b₀ ∧ b₀.place = frontPlace := ⟨_, rfl, rfl⟩
  obtain ⟨b₀, e₀, hp⟩ := hb
  obtain rfl : b₀ = blk := Option.some.inj (e₀.symm.trans hblk)
  rw [List.find?_eq_none]
  intro g hg
  have hm : g.place ∈ (keyProver K).shared.map (·.place) := List.mem_map.2 ⟨g, hg, rfl⟩
  rw [keyProver_shared K hK.splits, hK.onU, hK.onOmega] at hm
  rw [hp, front_apart _ hm]
  exact Bool.false_ne_true

/-- **What is left of the seven at the key file's own prover.** -/
theorem starts₂_key (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {k : Coins Bk} {R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀' X'}
    (hR : ready (D Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R) (hF : FilledAt L K)
    (hK : K.AtAll) (hrel : L.Rel w₀ rc x)
    (hown : ∃ r, L.base.recOf x = some r ∧ L.meetsT r (L.cells w₀ rc)) :
    Starts₂ Xs N Pl L w₀ rc x (keyProver K) k R :=
  ⟨hR, keyProver_key K x, bare_key Xs N Pl K hK, hF.stored,
    fits_of_own Xs N Pl L x hs scope hF.sample hown.choose_spec.1, hrel, hown⟩

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.fits_of_own
#print axioms AtPublicFiles.KeyThread.front_apart
#print axioms AtPublicFiles.KeyThread.bare_key
#print axioms AtPublicFiles.KeyThread.starts₂_key
