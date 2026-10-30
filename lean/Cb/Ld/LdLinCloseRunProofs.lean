-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseRunProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseRun.lean (a whole
test on a group, beside what the statement carries; the end of a chain).
Main names (statements and hypotheses: Cb/Ld/LdLinCloseRun.lean):
  `ldClose_run`: one whole test on a group, beside what is carried, as a closed piece of a chain.
  `ldClose_done`: the end of a chain, a step without rounds to the trivial statement, as a tail.
  `ldClose_run_data`: rounds, errors, and the numbers `pBad` and `pHid`.
The proof of `Spec.ldClose_run` is an assembly: the bridge (Cb/Ld/LdBatSigProofs.lean) is a piece
that sends no oracle; the test beside the carried part is a closed piece (`ClosedTr`,
Cb/Ld/LdLinCloseKit.lean); dropping the trivial statement is a step without rounds; each under the
hypotheses of its statement. Nothing is defined here that a statement reads.
-/
import Cb.Ld.LdLinCloseRun
import Cb.Ld.LdBatSigProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- the sources of a set of carried positions, under "drop the left part", are that set on the right
-/
theorem snd_src_right {E₁ E₂ : ExtSpec} [DecidableEq (E₁.prod E₂).Pos] (U : Finset E₂.Pos) :
    (U.biUnion (ExtMap.snd E₁ E₂).src).toRight = U := by
  ext q
  rw [Finset.mem_toRight, Finset.mem_biUnion]
  constructor
  · rintro ⟨u, hu, hq⟩
    rw [Sum.inr.inj (Finset.mem_singleton.1 hq)]
    exact hu
  · exact fun h => ⟨q, h, Finset.mem_singleton_self _⟩

theorem ldClose_done : Spec.ldClose_done := by
  classical
  intro X W Eo A w₀ q hA hq
  have hp := pieceTr_pure Unit X Unit Eo extNone W Unit A trivRels (fun _ => some ())
    (ExtMap.toNone Eo) (fun _ => ((), ())) (fun _ _ => w₀) q (fun _ => True)
    { isLocal := fun _ _ p _ => p.elim
      acc := fun _ _ _ _ => ⟨rfl, trivial⟩
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun _ _ => rfl
      know := fun x y _ _ ha _ _ => hA (x, y) ha }
    (fun U _ => by
      have : U.biUnion (ExtMap.toNone Eo).src = ∅ := by
        ext p
        simp [ExtMap.toNone]
      rw [this]
      exact hq)
  exact ⟨hp.good, hp.noHid, fun ρ p hp' => absurd hp' (Finset.notMem_empty _), hp.bears⟩

theorem ldClose_run : Spec.ldClose_run := by
  classical
  intro E B Kc St₀ Wp _ _ _ S G _ kp _ Sb sl Z L E₀ A₀ hc d d' T t qi qF hZ hL hF hT hq
  have h1 := closedTr_of_piece _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldBat_bridge E B Kc St₀ Wp S G kp Sb sl Z L E₀ A₀ hc qi
      (besideQ ((G.joint Sb sl Z).atMost t) qF) hZ hL hF hq)
  have h2 := (closedTr_beside Kc _ _ (LdCarX kp St₀) _ (LdCarE kp E₀) T.R _ _ (LdCarW kp Wp)
    T.H _ _ T.ext T.N ((S.sub kp).over A₀) _ qF hT).1
  have h3 := closedTr_of_piece _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pieceTr_pure Kc (Unit × LdCarX kp St₀) (LdCarX kp St₀) (extNone.prod (LdCarE kp E₀))
      (LdCarE kp E₀) (Unit × LdCarW kp Wp) (LdCarW kp Wp)
      (IOR.Rels.beside trivRels ((S.sub kp).over A₀)) ((S.sub kp).over A₀) (fun x => some x.2)
      (ExtMap.snd extNone (LdCarE kp E₀)) (fun a => (a.1.2, a.2.2)) (fun _ w => ((), w))
      (besideQ (fun _ => True) qF) qF
      { isLocal := fun y y' p h => Sum.inr.inj (h (Sum.inr p) (Finset.mem_singleton_self _))
        acc := fun _ _ _ h => ⟨rfl, h.2⟩
        onOut := fun x y x' h hx => by
          obtain rfl := Option.some.inj hx
          exact h.2
        keeps := fun _ _ => rfl
        know := fun x y x' w' _ hx h => by
          obtain rfl := Option.some.inj hx
          exact ⟨trivial, h⟩ }
      (fun U hU =>
        ⟨trivial, (congrArg qF
            (@snd_src_right extNone (LdCarE kp E₀)
              (fun a b => Classical.propDecidable (a = b)) U)).mpr hU⟩))
  exact closedTr_seq Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ _ _ _ h1
    (closedTr_seq Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d' _ _ _ _ _ h2 h3)

theorem ldClose_run_data : Spec.ldClose_run_data := by
  intro E B Kc St₀ _ _ _ S G _ kp _ Sb sl Z err E₀ T
  refine ⟨?_, rfl, rfl, rfl⟩
  show ((ldBridge G kp Sb Z St₀ E₀).shape ++ (T.R.shape ++ [])).length = _
  rw [List.length_append, List.append_nil, Nat.add_comm]
  rfl

end Cb
