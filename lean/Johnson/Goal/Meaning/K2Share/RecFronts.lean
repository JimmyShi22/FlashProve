-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/RecFronts.lean: the code switch's four quiet steps at the
head's link and at the finish hand RecAll on (Johnson/Goal/Meaning/RecAll.lean; RecRel,
Johnson/Goal/Meaning/RecRel.lean); so does the whole place «F:1».


  headFrontQ_rec, headOpenQ_rec (Johnson/Top/H0/Tw/K2C/Head.lean), finishFrontQ_rec,
    finishBehindQ_rec (Tw/K2C/Finish.lean): each is Keeps.Fn (RecRel cs sh).
  finishFront_all: what the front of the finish's switch is made of.
  finishPlace_rec: Decides (RecRel cs sh) (finishPlace p).
LIMITS. These steps alone. No soundness is claimed.
-/
import Johnson.Goal.Meaning.K2Share.K2Whole
import Johnson.Top.H0.Tw.K2C.Head
import Johnson.Top.H0.Tw.K2C.Finish
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.Keeps (Fn Decides)
open Meaning.K2 (RecAll RecRel FramePub framesIn recAll_unmarked recAll_enterHead recAll_openHead
  recAll_enterFin recRel_trans)
open _root_.Tw.K2 (firstFront finishFront firstBehind newGroupG)

variable {cs : Codes} {sh : ReqShape}

theorem ebind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := Keeps.ebind_ok h

/-- **"H.0.front".** -/
theorem headFrontQ_rec (tl : HTailF2) : Fn (RecRel cs sh) (headFrontQ tl) := fun s t h R => by
  unfold headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, hx, h⟩ := ebind h
      obtain ⟨s₁, h1, h⟩ := ebind h
      have R1 : RecAll cs sh s₁ := recAll_unmarked (recAll_enterHead R tl) h1
      split at h
      · rename_i a ha
        cases h
        obtain ⟨g1, g2⟩ := front_frame hx
        have hf : FramePub sh x.f :=
          R.walk.carry g1 g2 (front_carried hx).1 (front_carried hx).2
        refine ⟨(link_front hx).2.1.trans R.codes, fun f hm => ?_, R.ok⟩
        have F1 := R1.frames
        unfold framesIn at hm F1
        rw [ha] at F1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm F1
        rcases hm with rfl | rfl | rfl
        · exact F1 _ (Or.inl rfl)
        · exact hf
        · exact F1 _ (Or.inr (Or.inr rfl))
      · cases h

/-- **"H.1.quiet".** -/
theorem headOpenQ_rec (P : HeadPar) : Fn (RecRel cs sh) (headOpenQ P) := fun s t h R => by
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
        obtain ⟨f1, f2, f3⟩ := behind_frame hb
        have hafr : FramePub sh a.fr := R.frames _ (by unfold framesIn; rw [ha]; simp)
        have hf : FramePub sh f := hafr.carry f1 f2 (behind_carried hb).1 (behind_carried hb).2
        have hL := (_root_.Johnson.Desc.First.Walk.Law.front_ok hfr).2.2.1
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h1, h⟩ := ebind h
                have R1 : RecAll cs sh s₁ := recAll_unmarked (recAll_openHead R) h1
                split at h
                · rename_i b hb'
                  cases h
                  refine ⟨f3.codes.trans R.codes, fun f' hm => ?_, R.ok⟩
                  have F1 := R1.frames
                  unfold framesIn at hm F1
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

/-- What the front of the finish's switch is made of. -/
theorem finishFront_all {S0 : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : finishFront S0 f = .ok x) :
    x.f.shape = f.shape ∧ x.f.groups = f.groups ∧ x.st.codes = S0.codes ∧
      (∃ G, f.groups[f.link]? = some G ∧ x.T = G.target) ∧ x.f.rows = f.rows ∧
      x.f.link = f.link := by
  unfold finishFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i G hG
      split at h
      · cases h
      · rename_i S' g hn
        cases h
        exact ⟨rfl, rfl, (newGroupG_tables hn).1, ⟨G, hG, rfl⟩, rfl, rfl⟩

/-- **"F.0.front".** -/
theorem finishFrontQ_rec : Fn (RecRel cs sh) finishFrontQ := fun s t h R => by
  unfold finishFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i G x hG hx
        obtain ⟨s₁, h1, h⟩ := ebind h
        have R1 : RecAll cs sh s₁ := recAll_unmarked (recAll_enterFin R) h1
        split at h
        · rename_i a ha
          cases h
          obtain ⟨g1, g2, g3, -, g5, g6⟩ := finishFront_all hx
          have hf : FramePub sh x.f := R.walk.carry g1 g2 g5 g6
          refine ⟨g3.trans R.codes, fun f hm => ?_, R.ok⟩
          have F1 := R1.frames
          unfold framesIn at hm F1
          rw [ha] at F1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm F1
          rcases hm with rfl | rfl
          · exact F1 _ (Or.inl rfl)
          · exact hf
        · cases h
      · cases h
      · cases h

/-- **"F.0.quiet".** -/
theorem finishBehindQ_rec : Fn (RecRel cs sh) finishBehindQ := fun s t h R => by
  unfold finishBehindQ at h
  split at h
  · rename_i a ha
    obtain ⟨m, -, rfl⟩ := Keeps.emap_ok h
    refine ⟨R.codes, fun f hm => R.frames f ?_, R.ok⟩
    unfold framesIn at hm ⊢
    rw [ha]
    exact hm
  · cases h

/-- **The whole place «F:1».** -/
theorem finishPlace_rec {Cl : Type} (p : P2) :
    Decides (RecRel cs sh) (finishPlace (Cl := Cl) p) := fun s rs gs s' h =>
  Keeps.andThen_decides (RecRel cs sh) (recRel_trans cs sh) p.name _ _
    (Keeps.andThen_decides (RecRel cs sh) (recRel_trans cs sh) p.name _ _
      (Keeps.quiet_decides _ _ _ _ _ _ finishFrontQ_rec) (k2_recAll cs sh p).1)
    (Keeps.quiet_decides _ _ _ _ _ _ finishBehindQ_rec) s rs gs s' h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.headFrontQ_rec
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_rec
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_rec
#print axioms VerifiableInference.Desc.First.K2.finishPlace_rec
