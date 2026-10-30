-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/PrivFrame/Top.lean: the frame of a proof of index privacy by a reduction around a game
(Compile/PrivFrame/Spec.lean), WITH ITS PREMISES ASKED ONLY OF ADVERSARIES WHOSE FIRST MOVE IS THE
SETUP. A definition, a statement and their proofs. General in the family of oracles, in the scheme,
in the reduction and in the game.

General lemmas. This file states no goal of the release.

In the privacy experiment of the definition (ZKCP/Gen.lean) the adversary gets the key first and
asks afterwards. As one adversary against a challenger (top, Compile/Batch/GluePrivacy.lean) the
experiment begins with the call "setup": no draw and no query comes before it. An admissible
adversary (GAdm) may ask before its setup. So closeness is needed for fewer adversaries than Close
(Compile/Batch/SpecGlue.lean) names, and a proof may lean on "no query before the key is out".

  CloseTop             Close, for adversaries of the form: the call "setup", then k.
  privacyWith_of_top   from CloseTop to the definition, simulator named.
  Spec.frameTop, frameTop   the frame, its premises hop and adm asked of such adversaries alone.
  close_top            Close gives CloseTop: the new premise is the weaker one.
  CloseAt, privacyFor_of_top, Spec.frameAt, frameAt   the same FOR ONE INDEX: the premises at that
                       index alone, the conclusion the definition's clause at that index
                       (Gen.PrivacyFor), for every environment that is valid there.
A rider on frameAt: the reduction and the simulated game are letters beside the index, so frameAt by
itself does not say that one simulator serves all indices. That is said where it is called: there
the simulator must be fixed before the index.
Follows the proof of privacyWith_of_world (Compile/Batch/GluePrivacy.lean).

-/
import Compile.PrivFrame.Proof

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Compile
namespace PrivFrame
open Rom Prob ZKCP
open Compile.GlueB (GCall SCall GIn GAdm asW realW simOf forget Close)

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

/-- Closeness for the adversaries whose first move is the setup. -/
def CloseTop (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
    (G : World S (GCall X Wn) (GIn IVK Pf)) (s₀ : G.σ) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (α : Type) (k : GIn IVK Pf → Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
    (Adv.call .setup k).TotalBound t (n + 1) →
    GAdm (fun b => Gen.ValidBatch R B i b.pairs) (.call .setup k) false n →
    tv ((interact (realW A i) (.call .setup k) (none, Table.empty _)).map Prod.fst)
        ((interact G (.call .setup k) s₀).map Prod.fst) ≤ ζ t n

theorem close_top {R : Gen.RelPair I X Wn PP} {A : Gen.Arg S I X Wn IVK ISK Pf} {B : ℕ}
    {G : World S (GCall X Wn) (GIn IVK Pf)} {s₀ : G.σ} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : Close R A B G s₀ ζ) : CloseTop R A B G s₀ ζ :=
  fun i α k t n hT hA => h i α (.call .setup k) t n hT hA

/-- From challengers to the definition, simulator named: closeness is used at one adversary, whose
first move is the setup. -/
theorem privacyWith_of_top [Inhabited IVK] [Inhabited Pf] (R : Gen.RelPair I X Wn PP)
    (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ) (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ)
    (ζ : ℕ → ℕ → ℝ≥0∞) (hc : Sm.Consistent) (close : CloseTop R A B (asW Wn Sm) s₀ ζ) :
    Gen.HasIndexPrivacyWith R A B (simOf PP Sm s₀) ζ := by
  intro i Z hZ tV Vt N hV
  refine ⟨?_, GlueB.consistent_idealExp R Sm s₀ hc i Vt Z N⟩
  have e1 : (fun T => Rom.Pr (Gen.realExp A Vt Z i N) fun _ => T) =
      pr (Gen.realExp A Vt Z i N).law :=
    funext fun T => Rom.Pr_eq_law _ T
  rw [e1, GlueB.law_realExp A i Vt Z N, GlueB.idealExp_eq R Sm s₀ i Vt Z N]
  exact close i _ _ tV N (GlueB.top_totalBound Vt Z tV N hV) (GlueB.top_adm Vt Z hZ N)

/-- **The frame, for adversaries whose first move is the setup.** The letters are those of
Spec.frame. -/
def Spec.frameTop : Prop :=
  ∀ (S : OSpec) (I X Wn PP IVK ISK Pf : Type) [Inhabited IVK] [Inhabited Pf] (Out' In' : Type)
      (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
      (Wp : Wrap S (SCall X) (GIn IVK Pf) Out' In') (w₀ : Wp.τ)
      (Gr : I → World S Out' In') (gr : ∀ i, (Gr i).σ) (Gs : World S Out' In') (gs : Gs.σ)
      (Adm : I → (α : Type) → Adv S Out' In' α → ℕ → ℕ → Prop) (h z : ℕ → ℕ → ℝ≥0∞),
    (∀ (i : I) (α : Type) (k : GIn IVK Pf → Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
      (Adv.call .setup k).TotalBound t (n + 1) →
      GAdm (fun b => Gen.ValidBatch R B i b.pairs) (.call .setup k) false n →
      tv ((interact (realW A i) (.call .setup k) (none, Table.empty _)).map Prod.fst)
        ((interact (asW Wn (Wp.world (Gr i))) (.call .setup k) (w₀, gr i)).map Prod.fst) ≤ h t n) →
    (∀ (i : I) (α : Type) (k : GIn IVK Pf → Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
      (Adv.call .setup k).TotalBound t (n + 1) →
      GAdm (fun b => Gen.ValidBatch R B i b.pairs) (.call .setup k) false n →
      Adm i α ((Wp.pre forget).adv (.call .setup k) w₀) t n) →
    (∀ (i : I) (α : Type) (E : Adv S Out' In' α) (t n : ℕ), Adm i α E t n →
      tv ((interact (Gr i) E (gr i)).map Prod.fst) ((interact Gs E gs).map Prod.fst) ≤ z t n) →
    (Wp.world Gs).Consistent →
    Gen.HasIndexPrivacyWith R A B (simOf PP (Wp.world Gs) (w₀, gs)) fun t n => h t n + z t n

theorem frameTop : Spec.frameTop := by
  intro S I X Wn PP IVK ISK Pf _ _ Out' In' R A B Wp w₀ Gr gr Gs gs Adm h z hop adm game cons
  refine privacyWith_of_top R A B (Wp.world Gs) (w₀, gs) _ cons ?_
  intro i α k t n hT hA
  refine le_trans (tv_triangle _
    ((interact (asW Wn (Wp.world (Gr i))) (.call .setup k) (w₀, gr i)).map Prod.fst) _)
    (add_le_add (hop i α k t n hT hA) ?_)
  have hB : ∀ (G : World S Out' In') (g : G.σ),
      (interact (asW Wn (Wp.world G)) (.call .setup k) (w₀, g)).map Prod.fst =
        (interact G ((Wp.pre forget).adv (.call .setup k) w₀) g).map Prod.fst :=
    fun G g => interact_adv (Wp.pre forget) G (.call .setup k) w₀ g
  rw [hB, hB]
  exact game i α _ t n (adm i α k t n hT hA)

/-! ## For one index -/

/-- Closeness at one index, for the adversaries whose first move is the setup. -/
def CloseAt (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
    (G : World S (GCall X Wn) (GIn IVK Pf)) (s₀ : G.σ) (ζ : ℕ → ℕ → ℝ≥0∞) (i : I) : Prop :=
  ∀ (α : Type) (k : GIn IVK Pf → Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
    (Adv.call .setup k).TotalBound t (n + 1) →
    GAdm (fun b => Gen.ValidBatch R B i b.pairs) (.call .setup k) false n →
    tv ((interact (realW A i) (.call .setup k) (none, Table.empty _)).map Prod.fst)
        ((interact G (.call .setup k) s₀).map Prod.fst) ≤ ζ t n

/-- From challengers to the definition's clause for one index and one environment. -/
theorem privacyFor_of_top [Inhabited IVK] [Inhabited Pf] (R : Gen.RelPair I X Wn PP)
    (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ) (Sm : World S (SCall X) (GIn IVK Pf)) (s₀ : Sm.σ)
    (ζ : ℕ → ℕ → ℝ≥0∞) (hc : Sm.Consistent) (i : I) (close : CloseAt R A B (asW Wn Sm) s₀ ζ i)
    (Z : Gen.ViewEnv S IVK X Wn Pf) (hZ : Z.IsValid R B i) :
    Gen.PrivacyFor R A (simOf PP Sm s₀) ζ i Z := by
  intro tV Vt N hV
  refine ⟨?_, GlueB.consistent_idealExp R Sm s₀ hc i Vt Z N⟩
  have e1 : (fun T => Rom.Pr (Gen.realExp A Vt Z i N) fun _ => T) =
      pr (Gen.realExp A Vt Z i N).law :=
    funext fun T => Rom.Pr_eq_law _ T
  rw [e1, GlueB.law_realExp A i Vt Z N, GlueB.idealExp_eq R Sm s₀ i Vt Z N]
  exact close _ _ tV N (GlueB.top_totalBound Vt Z tV N hV) (GlueB.top_adm Vt Z hZ N)

/-- **The frame for one index i**: hop, adm and game are asked at i alone; the conclusion is the
definition's clause at i, for every environment that is valid at i. Gr, gr: the game's real side at
i. -/
def Spec.frameAt : Prop :=
  ∀ (S : OSpec) (I X Wn PP IVK ISK Pf : Type) [Inhabited IVK] [Inhabited Pf] (Out' In' : Type)
      (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
      (Wp : Wrap S (SCall X) (GIn IVK Pf) Out' In') (w₀ : Wp.τ) (i : I)
      (Gr : World S Out' In') (gr : Gr.σ) (Gs : World S Out' In') (gs : Gs.σ)
      (Adm : (α : Type) → Adv S Out' In' α → ℕ → ℕ → Prop) (h z : ℕ → ℕ → ℝ≥0∞),
    (∀ (α : Type) (k : GIn IVK Pf → Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
      (Adv.call .setup k).TotalBound t (n + 1) →
      GAdm (fun b => Gen.ValidBatch R B i b.pairs) (.call .setup k) false n →
      tv ((interact (realW A i) (.call .setup k) (none, Table.empty _)).map Prod.fst)
        ((interact (asW Wn (Wp.world Gr)) (.call .setup k) (w₀, gr)).map Prod.fst) ≤ h t n) →
    (∀ (α : Type) (k : GIn IVK Pf → Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
      (Adv.call .setup k).TotalBound t (n + 1) →
      GAdm (fun b => Gen.ValidBatch R B i b.pairs) (.call .setup k) false n →
      Adm α ((Wp.pre forget).adv (.call .setup k) w₀) t n) →
    (∀ (α : Type) (E : Adv S Out' In' α) (t n : ℕ), Adm α E t n →
      tv ((interact Gr E gr).map Prod.fst) ((interact Gs E gs).map Prod.fst) ≤ z t n) →
    (Wp.world Gs).Consistent →
    ∀ Z : Gen.ViewEnv S IVK X Wn Pf, Z.IsValid R B i →
      Gen.PrivacyFor R A (simOf PP (Wp.world Gs) (w₀, gs)) (fun t n => h t n + z t n) i Z

theorem frameAt : Spec.frameAt := by
  intro S I X Wn PP IVK ISK Pf _ _ Out' In' R A B Wp w₀ i Gr gr Gs gs Adm h z hop adm game cons
  refine privacyFor_of_top R A B (Wp.world Gs) (w₀, gs) _ cons i ?_
  intro α k t n hT hA
  refine le_trans (tv_triangle _
    ((interact (asW Wn (Wp.world Gr)) (.call .setup k) (w₀, gr)).map Prod.fst) _)
    (add_le_add (hop α k t n hT hA) ?_)
  have hB : ∀ (G : World S Out' In') (g : G.σ),
      (interact (asW Wn (Wp.world G)) (.call .setup k) (w₀, g)).map Prod.fst =
        (interact G ((Wp.pre forget).adv (.call .setup k) w₀) g).map Prod.fst :=
    fun G g => interact_adv (Wp.pre forget) G (.call .setup k) w₀ g
  rw [hB, hB]
  exact game α _ t n (adm α k t n hT hA)

end PrivFrame
end Compile

#print axioms Compile.PrivFrame.privacyWith_of_top
#print axioms Compile.PrivFrame.frameTop
#print axioms Compile.PrivFrame.privacyFor_of_top
#print axioms Compile.PrivFrame.frameAt
