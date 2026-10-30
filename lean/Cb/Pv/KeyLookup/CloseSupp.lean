-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseSupp.lean: the join point, the closing, the zero point and the test of the bits
keep "every form in the state is 0 outside G" (`Inv`, `Dat.SuppX`: Cb/Pv/KeyLookup/AsmSupp.lean).

It imports Join.lean, CloseRows.lean, AsmSupp.lean and the library; no file of the port.

  `join_supp`, `zero_supp`    no condition: the join point's new form is a combination of the live
                              planes' forms; the zero point adds no form.
  `close_supp`, `bits_supp`   under `P.In G` (CloseRows.lean), and if the letter hands its state on.
  `close_supp_lib`, `bits_supp_lib`   at the library's verifier: under `P.In G` alone.
Nothing on an honest side.

-/
import Cb.Pv.KeyLookup.Join
import Cb.Pv.KeyLookup.CloseRows
import Cb.Pv.KeyLookup.AsmSupp
import Cb.Ld.LdLkpFormat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Finset

namespace Clo

theorem inv_draw {X X' : Type} (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (Ex : ExtSpec)
    {P : X → Prop} {Q : X' → Prop} (h : ∀ x β, P x → Q (nx x β)) : Inv (IOR.draw D nx Ex) P Q := by
  intro x y τ x' e hP
  rw [← Option.some.inj (show some (nx x (drawn τ)) = some x' from e)]
  exact h _ _ hP

theorem inv_passes {X₁ X₂ Rc : Type} {E₁ E₂ : ExtSpec} {R : IOR X₁ E₁ X₂ E₂} {r : X₁ → Rc}
    {r' : X₂ → Rc} (h : R.Passes r r') (Q : Rc → Prop) :
    Inv R (fun x => Q (r x)) fun x' => Q (r' x') := by
  intro x y τ x' e hP
  show Q (r' x')
  rw [h x y τ x' e]
  exact hP

end Clo

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A) (G : A.J → Prop)

theorem join_supp (Ex : ExtSpec) : Inv (A.joinK Ex).R (A.SuppX G) (A.SuppX G) :=
  Clo.inv_draw _ _ Ex fun x ϱ h =>
    ⟨h.all, h.run, h.roots, h.planes,
      fun j hj => Finset.sum_eq_zero fun θ _ => by
        unfold formAt
        split_ifs
        · rw [h.planes _ j hj, mul_zero]
        · exact mul_zero _,
      h.cls, h.rows⟩

theorem zero_supp (Ex : ExtSpec) : Inv (A.zeroK Ex).R (A.SuppX G) (A.SuppX G) :=
  Clo.inv_draw _ _ Ex fun _ _ h => ⟨h.all, h.run, h.roots, h.planes, h.top, h.cls, h.rows⟩

variable {G} {Ex : ExtSpec}

theorem close_supp (hP : P.In G) (SK : PscLtK E Ex)
    (h1 : (SK.core (A.En P).par).R.Passes Prod.snd PscPar.Mid.st) :
    Inv (A.closeK P SK).R (A.SuppX G) (A.SuppX G) :=
  ((Clo.inv_passes h1 (A.SuppX G)).pre _ _ fun x x' e h => by
      obtain rfl := Option.some.inj e
      exact h).post _ _ fun zz x' e h => by
      obtain rfl := Option.some.inj e
      refine ⟨h.all, h.run, h.roots, h.planes, h.top, h.cls, fun r hr => ?_⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact h.rows r hr
      · rw [List.mem_singleton.1 hr]
        exact A.rowE_supp P hP zz h.top

theorem bits_supp (hP : P.In G) (SK : PscLtK E Ex)
    (h1 : (SK.full (A.BT P).par).R.Passes Prod.snd PscPar.Out.st) :
    Inv (A.bitsK P SK).R (A.SuppX G) (A.SuppX G) :=
  ((Clo.inv_passes h1 fun s : (A.BT P).St => A.SuppX G s.1).pre _ _ fun x x' e h => by
      obtain rfl := Option.some.inj e
      exact h).post _ _ fun o x' e h => by
      obtain rfl := Option.some.inj e
      refine ⟨h.all, h.run, h.roots, h.planes, h.top, h.cls, fun r hr => ?_⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact h.rows r hr
      · rcases List.mem_cons.1 hr with hr | hr
        · rw [hr]
          exact A.rowU_supp P hP o
        · rw [List.mem_singleton.1 hr]
          exact A.rowV_supp P hP o

theorem close_supp_lib (hP : P.In G) :
    Inv (A.closeK P (PscLtK.lib E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.close_supp P hP _ (core_passes (A.En P).par Ex)

theorem bits_supp_lib (hP : P.In G) :
    Inv (A.bitsK P (PscLtK.lib E Ex)).R (A.SuppX G) (A.SuppX G) :=
  A.bits_supp P hP _ (psc_passes (A.BT P).par Ex)

end Dat
end Lk6

#print axioms Lk6.Dat.join_supp
#print axioms Lk6.Dat.zero_supp
#print axioms Lk6.Dat.close_supp
#print axioms Lk6.Dat.bits_supp
#print axioms Lk6.Dat.close_supp_lib
#print axioms Lk6.Dat.bits_supp_lib
