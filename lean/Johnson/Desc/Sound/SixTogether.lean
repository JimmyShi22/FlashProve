-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SixTogether.lean: WHAT K01's TOP ASKS OF THE PIECES AND OF THE DATA, AT THE CLOSED FORM OF THE PIECES (threeCap, Johnson/Goal/Skeleton/TheThree.lean), OUT OF «the description's data are D · its own test planOk accepts · the three flat lists' heads»: four_together of the same file (OfDesc · the cut · the cap · WrittenAs)
AND TWO MORE, OFF THE SAME data_ok: hRoots (each written round has as many roots among its items as its entry counts: fits_roots, ReadsOfData.lean, off the maker's test) · hFit (ChainFit at the first chain's held sub-protocols: fitOfOk, TilesOkProofs.lean; «all» := allOf D · dep := D.depth).
Nothing on soundness.
-/
import Johnson.Goal.Skeleton.TheThree
import Johnson.Desc.Sound.ReadsOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Err)

theorem held_rounds_flat {P S Cl : Type} (b : Block S Cl) (l : List (Block S Cl)) :
    (held (P := P) b :: l.map held).flatMap (·.rounds) = (b :: l).flatMap (·.rounds) := by
  show (List.map (held (P := P)) (b :: l)).flatMap (·.rounds) = _
  rw [List.flatMap_map]
  rfl

theorem held_last {P S Cl : Type} (b : Block S Cl) (l : List (Block S Cl))
    (hs : ((b :: l).getLast?.any fun x => !x.rounds.isEmpty) = true) :
    1 ≤ lastRounds (held (P := P) b) (l.map held) := by
  rw [lastRounds_eq]
  have e : List.map (fun x => x.rounds) (held (P := P) b :: l.map held) =
      (b :: l).map fun x => x.rounds := by
    show List.map _ (List.map (held (P := P)) (b :: l)) = _
    rw [List.map_map]
    rfl
  rw [e, List.getLast?_map]
  cases hg : (b :: l).getLast? with
  | none =>
    rw [hg] at hs
    cases hs
  | some x =>
    rw [hg, Option.any_some] at hs
    show 1 ≤ x.rounds.length
    cases hx : x.rounds with
    | nil =>
      rw [hx] at hs
      cases hs
    | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)

theorem six_together {Xi W : Type} {F : FileDescription Xi} {D : WholeD} {file : String}
    (h : F.data file = .ok D) (hp : F.planOk = true) {b₁ : Block F.S₁ F.Cl}
    {l₁ : List (Block F.S₁ F.Cl)} {b₂ : Block F.S₂ F.Cl} {l₂ : List (Block F.S₂ F.Cl)}
    {b₃ : Block F.S₃ F.Cl} {l₃ : List (Block F.S₃ F.Cl)} (q₁ : F.first.blocksInOrder = b₁ :: l₁)
    (q₂ : F.shared.blocksInOrder = b₂ :: l₂) (q₃ : F.second.blocksInOrder = b₃ :: l₃) :
    ∃ R₁ R₂ R₃ : OnBytes.Params.Rounds, D = dataOf F.tableDepth R₁ R₂ R₃ ∧
      WrittenAs [] (F.first.blocksInOrder.flatMap (·.rounds)) R₁ ∧
      (∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots) ∧
      (∀ (r : Fmt.RoundView) (k₁ : ℕ → ℕ) (ft₁ : ℕ),
        ChainFit (frameAt (dataOf F.tableDepth R₁ R₂ R₃) (allOf (dataOf F.tableDepth R₁ R₂ R₃)) k₁ ft₁)
          (dataOf F.tableDepth R₁ R₂ R₃).depth 0 (held (P := F.XiPub) b₁) (l₁.map held)
          (dataOf F.tableDepth R₁ R₂ R₃).ds₁ [r]) ∧
      ∀ e₁ e₂ e₃ (d wEnd : W),
        OfDesc F (threeCap F (dataOf F.tableDepth R₁ R₂ R₃) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd) ∧
        ((threeCap F (dataOf F.tableDepth R₁ R₂ R₃) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).p₁,
          (threeCap F (dataOf F.tableDepth R₁ R₂ R₃) b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ d wEnd).l₁) =
          cutRow (restCap e₁) [sealRound] 0 0 (dataOf F.tableDepth R₁ R₂ R₃).ds₁ (held b₁)
            (l₁.map held) ∧
        ∀ i ds, (restCap e₁ i ds).err = Err.cap 128 (uLT (ckP .two) ds) := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hok, hD⟩ := data_ok F file D h
  obtain ⟨w₁, w₂, w₃⟩ := written_as file F.roundsDeclaredByBlocks _ hR
  subst hD
  have hfits : OnBytes.Three.Whole.fits R₁ R₂ R₃ 2 = true := by
    have h' := hok
    unfold okAt at h'
    simp only [Bool.and_eq_true] at h'
    exact h'.1.1.1.1.1.1.1
  refine ⟨R₁, R₂, R₃, rfl, w₁, fits_roots hfits, fun r k₁ ft₁ => ?_, fun e₁ e₂ e₃ d wEnd =>
    ⟨threeCap_ofDesc e₁ e₂ e₃ d wEnd h hp q₁ q₂ q₃, rfl, fun _ _ => rfl⟩⟩
  refine (fitOfOk _ R₁ R₂ R₃ _ _ _ _ _ _ w₁ w₂ w₃ hok _ _ _ _ (held (P := F.XiPub) b₁) (l₁.map held)
    b₂ l₂ b₃ l₃ r k₁ k₁ k₁ ft₁ ft₁ ft₁ ?_ ?_ ?_ ?_).1
  · rw [held_rounds_flat, ← q₁]
    rfl
  · rw [← q₂]
    rfl
  · rw [← q₃]
    rfl
  · refine held_last b₁ l₁ ?_
    rw [← q₁]
    exact sealLast_any F (sealLast_of_planOk F hp)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.six_together
