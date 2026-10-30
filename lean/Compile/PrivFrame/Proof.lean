-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/PrivFrame/Proof.lean: the frame of a proof of index privacy by a reduction around a game:
the proof of Spec.frame (Compile/PrivFrame/Spec.lean). General in the family of oracles, in the
scheme, in the reduction and in the game.

A general lemma. This file states no goal of the release.

  asW_world    a reduction around a game, taken with the calls of the real experiment, is the
               reduction with translated calls around the game.
  frame        the triangle inequality; the adversary with the reduction inside (interact_adv,
               Compile/Step1_defc_Gen.lean); the step from challengers to the definition
               (gluePrivacyWith, Compile/Batch/GluePrivacy.lean).
  frame_at_one    the first three premises can be met: by every reduction and every game, at the
               bounds 1 and 1. (With these bounds the conclusion says nothing.)
  idleWrap, idleGame, idle_consistent, frame_idle    all four premises met at once, the fourth too:
               a reduction that passes queries on, around a game that samples lazily.
Follows the pattern of closePubUTOf and privacyPubGrWithUOf (Compile/Batch/PubProgMainBGr.lean).

-/
import Compile.PrivFrame.Spec
import Compile.Batch.GluePrivacy
import Rom.LateAdv

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Compile
namespace PrivFrame
open Rom Prob ZKCP
open Compile.GlueB (GCall SCall GIn GAdm asW realW simOf forget)

theorem asW_world {S : OSpec} {X IVK Pf Out' In' : Type} (Wn : Type)
    (Wp : Wrap S (SCall X) (GIn IVK Pf) Out' In') (G : World S Out' In') :
    asW Wn (Wp.world G) = (Wp.pre (forget (Wn := Wn))).world G := rfl

theorem frame : Spec.frame := by
  intro S I X Wn PP IVK ISK Pf _ _ Out' In' R A B Wp w₀ Gr gr Gs gs Adm h z hop adm game cons
  refine GlueB.gluePrivacyWith S I X Wn PP IVK ISK Pf R A B (Wp.world Gs) (w₀, gs) _ cons ?_
  intro i α D t n hT hA
  refine le_trans (tv_triangle _
    ((interact (asW Wn (Wp.world (Gr i))) D (w₀, gr i)).map Prod.fst) _)
    (add_le_add (hop i α D t n hT hA) ?_)
  have hB : ∀ (G : World S Out' In') (g : G.σ),
      (interact (asW Wn (Wp.world G)) D (w₀, g)).map Prod.fst =
        (interact G ((Wp.pre forget).adv D w₀) g).map Prod.fst :=
    fun G g => interact_adv (Wp.pre forget) G D w₀ g
  rw [hB, hB]
  exact game i α _ t n (adm i α D t n hT hA)

/-- The frame's first three premises are met by every reduction and every game, at the bounds 1 and
1 and a game that admits everybody. -/
theorem frame_at_one (S : OSpec) (I X Wn PP IVK ISK Pf : Type) [Inhabited IVK] [Inhabited Pf]
    (Out' In' : Type) (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
    (Wp : Wrap S (SCall X) (GIn IVK Pf) Out' In') (w₀ : Wp.τ)
    (Gr : I → World S Out' In') (gr : ∀ i, (Gr i).σ) (Gs : World S Out' In') (gs : Gs.σ)
    (cons : (Wp.world Gs).Consistent) :
    Gen.HasIndexPrivacyWith R A B (simOf PP (Wp.world Gs) (w₀, gs)) fun _ _ => 1 + 1 :=
  frame S I X Wn PP IVK ISK Pf Out' In' R A B Wp w₀ Gr gr Gs gs (fun _ _ _ _ _ => True)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ _ _ _ _ => tv_le_one _ _)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => tv_le_one _ _) cons

/-! ## An idle member: all four premises met at once -/

/-- The reduction that passes every query on and replies to every call with no proof. -/
def idleWrap (S : OSpec) (X IVK Pf : Type) : Wrap S (SCall X) (GIn IVK Pf) Unit Unit where
  τ := Unit
  ans := fun w o q => .query o q fun r => .halt (r, w)
  rep := fun w _ => .halt (.inr [], w)

/-- The game that does nothing but sample the oracles lazily. -/
def idleGame (S : OSpec) : World S Unit Unit where
  σ := Table S
  answer := fun T o q => lazyAnswer T o q
  reply := fun T _ => PMF.pure ((), T)

theorem idle_answer (S : OSpec) (X IVK Pf : Type) (s : Unit × Table S) (o : S.ι) (q : S.Dom o) :
    ((idleWrap S X IVK Pf).world (idleGame S)).answer s o q =
      (lazyAnswer s.2 o q).map fun p => (p.1, (s.1, p.2)) := by
  show ((lazyAnswer s.2 o q).bind fun p => PMF.pure ((p.1, s.1), p.2)).map _ = _
  rw [PMF.map_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- The idle reduction around the idle game never answers one query in two ways. -/
theorem idle_consistent (S : OSpec) (X IVK Pf : Type) :
    ((idleWrap S X IVK Pf).world (idleGame S)).Consistent := by
  refine ⟨fun s => s.2, ?_, ?_, ?_⟩
  · rintro ⟨w, T⟩ o q r hr x hx
    rw [idle_answer, lazyAnswer_of_some hr, PMF.pure_map] at hx
    rw [(PMF.mem_support_pure_iff _ _).1 hx]
  · rintro ⟨w, T⟩ o q x hx
    rw [idle_answer] at hx
    cases hT : T o q with
    | some r =>
      rw [lazyAnswer_of_some hT, PMF.pure_map] at hx
      rw [(PMF.mem_support_pure_iff _ _).1 hx]
      exact ⟨hT, fun _ _ _ h => h⟩
    | none =>
      rw [lazyAnswer_of_none hT, PMF.map_comp] at hx
      obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
      exact ⟨Table.set_apply_same _ _ _ _, Table.sub_set hT r⟩
  · rintro ⟨w, T⟩ m x hx
    have e : ((idleWrap S X IVK Pf).world (idleGame S)).reply (w, T) m =
        PMF.pure (.inr [], (w, T)) := by
      show (PMF.pure (((.inr [] : GIn IVK Pf), w), T)).map _ = _
      rw [PMF.pure_map]
    rw [e] at hx
    rw [(PMF.mem_support_pure_iff _ _).1 hx]
    exact fun _ _ _ h => h

/-- All four premises of the frame met at once, for any scheme: the idle reduction, the idle game on
both sides, the bounds 1 and 0. -/
theorem frame_idle (S : OSpec) (I X Wn PP IVK ISK Pf : Type) [Inhabited IVK] [Inhabited Pf]
    (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ) :
    Gen.HasIndexPrivacyWith R A B
      (simOf PP ((idleWrap S X IVK Pf).world (idleGame S)) ((), Table.empty S))
      fun _ _ => 1 + 0 :=
  frame S I X Wn PP IVK ISK Pf Unit Unit R A B (idleWrap S X IVK Pf) () (fun _ => idleGame S)
    (fun _ => Table.empty S) (idleGame S) (Table.empty S) (fun _ _ _ _ _ => True)
    (fun _ _ => 1) (fun _ _ => 0) (fun _ _ _ _ _ _ _ => tv_le_one _ _)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => le_of_eq (tv_self _))
    (idle_consistent S X IVK Pf)

end PrivFrame
end Compile

#print axioms Compile.PrivFrame.frame
#print axioms Compile.PrivFrame.frame_idle
