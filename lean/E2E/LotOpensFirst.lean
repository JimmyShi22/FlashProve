-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotOpensFirst.lean: what the key file's first chain opens.

It says: at every border 0 to 19 of the key file's first chain's thread T₁ (E2E/FirstHFill.lean: tbH
lays the ranges' test's own tables at own 2, 3, 4), every source that a round declared so far
opens is at hand, with the depth that the round declares, and no tree taken over bears an own tree's name.
These are the premises of oneColumns_of and walked_field (E2E/WalkedFrom.lean, WalkedField.lean) at T₁.

  LotOpensFirst   THE LOT's STATEMENT
  depth_rngTbl    own 2, 3, 4: rngTbl has the depths 19, 17, 20 at all k, w, h
  lot_opens_first   THE LOT: by opens_laid, declared_laid, depth_msg, depth_rngJob (E2E/LotOpensFirstLaid.lean)

By what. One member alone declares openings: number 15, the ranges' test (in front: IOP's pre_dry; behind:
post_shut); what it opens, by the kernel at the written place (rng_opens). That a text answers with a table
at EVERY family of coins is the book's: at own 1 msgJob_stated (the book has just the part's count), at own
2 to 4 full_lays (laysB at the key file's book) with IOP's members_ranges.

Limits. On declared openings and on logLength alone: nothing on a table's contents, nothing on a run:
no stand of T₁ is shown. The four premises (KeySourced, InScope, fullPub = some K₀, FirstPublic) stay
premises; of FirstPublic the field msg alone is spent. Q, K's other fields, f, w₀, rc, x stay letters.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotOpensFirstLaid
import E2E.FirstHSeat
import E2E.FirstHSeats
import Johnson.Desc.ProofFile.Honest.Thread.OneState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {W₀ Rc X₀ X' Wk : Type} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **What the key file's first chain opens.** -/
def LotOpensFirst : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → fullPub = some K₀ →
    FirstPublic (Pl := Pl) Xs N K f →
    (∀ n, n < 20 → (Th Xs N Pl K f Q w₀ rc x).opensAvailable n = true) ∧
      (∀ n, n ≤ 19 → ∀ k m, DepthsAt (Th Xs N Pl K f Q w₀ rc x) n k m) ∧
      ∀ j, Fmt.TreeSource.own j ∉ (Th Xs N Pl K f Q w₀ rc x).taken

end

/-! ## The lot -/

section
variable {W₀ Rc X₀ X' Wk : Type} (K₀ : KeyPub) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill (keyBook K₀) W₀ Rc) (w₀ : W₀)
  (rc : Rc) (x : Xi)

/-- **Own 2, 3, 4: rngTbl has the depths 19, 17, 20, at all k, w, h.** -/
theorem depth_rngTbl {Z : PublicFiles} (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hK₀ : fullPub = some K₀) {τ : Nat} (hτ : τ < 3) (k : Coins (keyBook K₀)) (w : In1 W₀ Rc)
    (h : List Fmt.Drawn) :
    (rngTbl Xs N Pl K f τ k w h).2.logLength = [19, 17, 20].getD τ 0 :=
  depth_rngJob K₀ Xs N Pl hsrc scope hK₀ _ _ 0 K.own₀ _ hτ k w h

/-- **What the key file's first chain opens.** -/
theorem lot_opens_first : LotOpensFirst K₀ Xs N Pl K f Q w₀ rc x := by
  intro Z hsrc scope hK₀ hp
  refine ⟨fun n _ => opens_laid Xs N Pl _ w₀ rc x _ _ hsrc scope n,
    fun n _ k m => depthsAt_of_declared (declared_laid Xs N Pl _ w₀ rc x _ _ hsrc scope ?_ n) k m,
    fun j hj => (List.not_mem_nil : ¬ Fmt.TreeSource.own j ∈ []) hj⟩
  intro p hp' k w h
  simp only [openedFirst, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl
  · show (ProofFile.Honest.K1.treeTbl 0 id K.msg K.own₀ 0 k w h).2.logLength = 22
    rw [hp.msg]
    exact depth_msg K₀ Xs N Pl f hsrc scope hK₀ K.own₀ k w h
  · exact depth_rngTbl K₀ Xs N Pl K f hsrc scope hK₀ (τ := 0) (by decide) k w h
  · exact depth_rngTbl K₀ Xs N Pl K f hsrc scope hK₀ (τ := 1) (by decide) k w h
  · exact depth_rngTbl K₀ Xs N Pl K f hsrc scope hK₀ (τ := 2) (by decide) k w h

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.depth_rngTbl
#print axioms AtPublicFiles.FirstH.Lots.lot_opens_first
