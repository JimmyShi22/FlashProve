-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CarriedFirst.lean: `CarriedAt` (Johnson/Desc/First/Close/Law/Leads.lean)
FROM ITS TWO HALVES, THE FIRST WRITTEN IN THE GROUP's OWN LETTERS: the fold's parameters of the
caller are the shape's (`R.Sh.par`) where `foldedAt` reads them; the words that the step without
rounds hands to the arrangement are the group's word of the statement's words. By unfolding. A
theorem. No text already in the library turns.

  `carriedAt_of`: **CarryAt R N out (foldedAt R.Sh.par (readP (h + g) out.gamma) (R.Sh.rho.wd
    (R.G.word x.2.1.2)) x.2.2) · the kept messages' own joint has a witness at what is carried ⊢
    CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L x out.**
Limits. Book-keeping on two texts. The second half stays a premise. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.First.Close (CarryAt CarriedAt SlotNames foldedAt)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

theorem carriedAt_of (L : List (BatFoldCaller GE))
    (x : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (out : SingleRows)
    (h1 : CarryAt R N out (foldedAt R.Sh.par (readP (R.s.h + R.s.g) out.gamma)
      (R.Sh.rho.wd (R.G.word x.2.1.2)) x.2.2))
    (h2 : ∃ (z : Z.D) (v : (S.sub (R.sizeB keep Sb sl Z).kp).Wit × Wp),
      ((S.sub (R.sizeB keep Sb sl Z).kp).over A₀).relR
        ((batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) x.1 z).2,
          ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map x.2.1).2) v) :
    CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L x out := ⟨h1, h2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.carriedAt_of
