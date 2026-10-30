-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrK2.lean: Johnson/IMR/FrAll.lean's FR AT KIND K2's OWN FIVE TEXTS: the code
switching's decision and the four quiet steps of the head's link and the finish. It goes beside
Johnson/Goal/Meaning/K2Share/K2Whole.lean's recAll_kept and RecFronts.lean, proof for proof.
  k2_rf; headFrontQ_rf, headOpenQ_rf, finishFrontQ_rf, finishBehindQ_rf.
OBJECT: the makers that ProofFile.onlineDescription's value lays. USER: Johnson/IMR/RowsSent.lean.
No soundness.
-/
import Johnson.IMR.FrAll
import Johnson.IMR.K2ShareAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Keeps (Fn Decides Whole)
open Meaning.K2 (EachF FR Carr framesIn ef_unmarked ef_enterHead ef_openHead ef_enterFin)
open _root_.Tw.K2 (firstFront finishFront firstBehind newGroupG sendByL8)

/-- **A yes of the code switching.** -/
theorem kept_rf {p : P2} {s s' : S} {rs gs}
    (h : decideWith sendByL8 p s rs gs = .ok s') : FR s s' := by
  intro Φ K R
  cases hp : p.stands with
  | link =>
    obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, L⟩ := link_inv hp h
    have hf : Φ f :=
      K _ _ R.walk ((behind_carried L.hBehind).1.trans (front_carried L.hFront).1)
    rw [L.hOut]
    intro f' hm
    have e : f' = f := by
      unfold framesIn at hm
      simpa [L.hHere, _root_.Johnson.Desc.First.Walk.firstKept] using hm
    rw [e]
    exact hf
  | head =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := head_inv hp h
    rw [H.hOut]
    intro f' hm
    refine R f' ?_
    unfold framesIn at hm ⊢
    rw [H.hHere]
    exact hm
  | finish =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := finish_inv hp h
    rw [H.hOut]
    intro f' hm
    refine R f' ?_
    unfold framesIn at hm ⊢
    rw [H.hHere]
    exact hm

theorem k2_rf {Cl : Type} (p : P2) : Whole FR (codeSwitchKind (Cl := Cl) p) :=
  ⟨fun _ _ _ _ h => kept_rf h, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **"H.0.front".** -/
theorem headFrontQ_rf (tl : HTailF2) : Fn FR (headFrontQ tl) := fun s t h Φ K R => by
  unfold headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, hx, h⟩ := ebind h
      obtain ⟨s₁, h1, h⟩ := ebind h
      have R1 : EachF Φ s₁ := ef_unmarked (ef_enterHead R tl) h1
      split at h
      · rename_i a ha
        cases h
        have hf : Φ x.f := K _ _ R.walk (front_carried hx).1
        intro f hm
        have F1 := R1
        unfold EachF framesIn at F1
        unfold framesIn at hm
        rw [ha] at F1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm F1
        rcases hm with rfl | rfl | rfl
        · exact F1 _ (Or.inl rfl)
        · exact hf
        · exact F1 _ (Or.inr (Or.inr rfl))
      · cases h

/-- **"H.1.quiet".** -/
theorem headOpenQ_rf (P : HeadPar) : Fn FR (headOpenQ P) := fun s t h Φ K R => by
  unfold headOpenQ at h
  split at h
  · rename_i a ha
    split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := ebind h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hfr, h⟩ := ebind h
        dsimp only at h
        have hafr : Φ a.fr := R _ (by unfold framesIn; rw [ha]; simp)
        have hf : Φ f := K _ _ hafr (behind_carried hb).1
        have hL := (_root_.Johnson.Desc.First.Walk.Law.front_ok hfr).2.2.1
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h1, h⟩ := ebind h
                have R1 : EachF Φ s₁ := ef_unmarked (ef_openHead R) h1
                split at h
                · rename_i b hb'
                  cases h
                  intro f' hm
                  have F1 := R1
                  unfold EachF framesIn at F1
                  unfold framesIn at hm
                  rw [hb'] at F1
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm F1
                  rcases hm with rfl | rfl | rfl
                  · exact hf
                  · exact F1 _ (Or.inr (Or.inl rfl))
                  · rw [hL]
                    exact hf
                · cases h
        · cases h
  · cases h

/-- **"F.0.front".** -/
theorem finishFrontQ_rf : Fn FR finishFrontQ := fun s t h Φ K R => by
  unfold finishFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i G x hG hx
        obtain ⟨s₁, h1, h⟩ := ebind h
        have R1 : EachF Φ s₁ := ef_unmarked (ef_enterFin R) h1
        split at h
        · rename_i a ha
          cases h
          obtain ⟨-, -, -, -, g5, -⟩ := finishFront_all hx
          have hf : Φ x.f := K _ _ R.walk g5
          intro f hm
          have F1 := R1
          unfold EachF framesIn at F1
          unfold framesIn at hm
          rw [ha] at F1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm F1
          rcases hm with rfl | rfl
          · exact F1 _ (Or.inl rfl)
          · exact hf
        · cases h
      · cases h
      · cases h

/-- **"F.0.quiet".** -/
theorem finishBehindQ_rf : Fn FR finishBehindQ := fun s t h Φ _ R => by
  unfold finishBehindQ at h
  split at h
  · rename_i a ha
    obtain ⟨m, -, rfl⟩ := Keeps.emap_ok h
    intro f hm
    refine R f ?_
    unfold framesIn at hm ⊢
    rw [ha]
    exact hm
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.k2_rf
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_rf
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_rf
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_rf
#print axioms VerifiableInference.Desc.First.K2.finishBehindQ_rf
