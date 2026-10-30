-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkProofs.lean: the proofs of the statements of Cb/Obj/LdObjectLink.lean. No axiom
beyond Lean's three; no hypothesis beyond those in the statements' own text.

The step in front of the tail is a step without rounds (`Step`, Ior/Frame.lean); "a piece, then a
tail, is a tail" (`tailTr_cons`, Cb/Ld/LdTowerKit.lean); from a tail and the four bridging facts to
the two lists: `Cb.ldObj_link` (Cb/Obj/LdObjectTail.lean).

Main names (statements and hypotheses: Cb/Obj/LdObjectLink.lean):
  `ldOl_object`: `LinkListR` and `LinkKnowR` of `K.link T`, for a tail T.
  `ldOl_chain`: the same of the chain of Cb/Ld/LdLink.lean with a closing.
-/
import Cb.Obj.LdObjectLink
import Cb.Obj.LdObjectConfProofs
import Cb.Ld.LdLinkProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the members on the left, on the right, of a set of positions of two oracles -/
theorem ldOl_card_isLeft {α β : Type} (s : Finset (α ⊕ β))
    [DecidablePred fun p : α ⊕ β => p.isLeft = true] :
    (s.filter fun p => p.isLeft).card = s.toLeft.card := by
  have e : (s.filter fun p => p.isLeft) = s.toLeft.map Function.Embedding.inl := by
    ext p
    cases p <;> simp
  rw [e, Finset.card_map]

theorem ldOl_card_isRight {α β : Type} (s : Finset (α ⊕ β))
    [DecidablePred fun p : α ⊕ β => p.isRight = true] :
    (s.filter fun p => p.isRight).card = s.toRight.card := by
  have e : (s.filter fun p => p.isRight) = s.toRight.map Function.Embedding.inr := by
    ext p
    cases p <;> simp
  rw [e, Finset.card_map]

namespace LdCf
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E)

/-- an index decoder that answers excludes a collision -/
theorem free_of_isSome {y : Fin Cf.C₀.n → Cf.Sg} {rec : Cf.X.Rec} (h : (Cf.conf.D y rec).isSome) :
    ¬ Cf.X.Coll (Cf.tab y) rec.1 := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  exact ((ldCf_D F E Cf y rec i).mp hi).1

/-- the index decoder without a collision, where the format decodes -/
theorem D_of_dec {y : Fin Cf.C₀.n → Cf.Sg} {rec : Cf.X.Rec} (hc : ¬ Cf.X.Coll (Cf.tab y) rec.1)
    {U : Cf.Row × Cf.J → E} (hU : Cf.X.dec (Cf.tab y) rec = some U) :
    Cf.conf.D y rec = Cf.held (Cf.dnM U) := by
  classical
  show (if Cf.X.Coll (Cf.tab y) rec.1 then none
      else ((Cf.X.dec (Cf.tab y) rec).map Cf.dnM).bind Cf.held) = _
  rw [if_neg hc, hU]
  rfl

end LdCf

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] [Fintype E] in
theorem ldOl_enter : Spec.ldOl_enter F E := by
  classical
  intro Cf K
  refine pieceTr_pure Unit _ _ _ _ _ _ K.jIn (K.P.j0 K.free K.free) some K.two (fun a => a)
    (fun _ w => w) K.P.q0 K.P.q0 ?_ ?_
  · refine { isLocal := ?_, acc := fun _ _ _ h => ⟨rfl, h⟩, onOut := ?_,
             keeps := fun _ _ => rfl, know := ?_ }
    · intro y y' q h
      have h1 := h q (Finset.mem_singleton_self q)
      rcases q with q | q
      · exact congrArg Sum.inl h1
      · exact congrArg Sum.inr h1
    · intro x y x' hon hx
      obtain rfl := Option.some.inj hx
      exact hon
    · intro x y x' w' _ hx hR
      obtain rfl := Option.some.inj hx
      exact hR
  · intro U hU
    convert hU using 1
    ext p
    rw [ldLk_mem_biUnion]
    constructor
    · rintro ⟨a, ha, hp⟩
      rw [Finset.mem_singleton.1 hp]
      exact ha
    · exact fun h => ⟨p, h, Finset.mem_singleton_self p⟩

omit [Fintype F] [Fintype E] in
theorem ldOl_tail : Spec.ldOl_tail F E := fun Cf K _ d h =>
  tailTr_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d _ _ _ _ (ldOl_enter F E Cf K) h

omit [Fintype E] in
theorem ldOl_bridge : Spec.ldOl_bridge F E := by
  classical
  intro Cf K L hOK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x y w ⟨⟨hy0, -, ha0⟩, ⟨hy1, -, ha1⟩, i, η, η', hm0, hm1⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · show Cf.tab y.1 = _
      rw [hy0]
      exact Cf.tab_enc _ _
    · show Cf.X.ZR.val x.1.1 (Cf.X.view fun r => Code.liftWord E (Cf.full w.1.1.1 w.1.1.2 r)) =
        x.1.2
      rw [Cf.view_full]
      exact ha0.symm
    · show Cf.tab y.2 = _
      rw [hy1]
      exact Cf.tab_enc _ _
    · show Cf.X.ZR.val x.2.1 (Cf.X.view fun r => Code.liftWord E (Cf.full w.2.1.1 w.2.1.2 r)) =
        x.2.2
      rw [Cf.view_full]
      exact ha1.symm
    · intro r a
      show Cf.X.view (fun r => Code.liftWord E (Cf.full w.1.1.1 w.1.1.2 r)) (r, .inl (Cf.lay a)) =
        Cf.X.view (fun r => Code.liftWord E (Cf.full w.2.1.1 w.2.1.2 r)) (r, .inl (Cf.lay a))
      rw [Cf.view_full, Cf.view_full]
      show algebraMap F E (w.1.1.1 (r, .inl (Cf.lay a))) =
        algebraMap F E (w.2.1.1 (r, .inl (Cf.lay a)))
      rw [show w.1.1.1 = Cf.hold i η from hm0, show w.2.1.1 = Cf.hold i η' from hm1]
      rfl
  · exact fun a hon => ⟨Cf.free_of_isSome hon.1, hon.2⟩
  · rintro a w hon ⟨U₀, U₁, h0, h1, hs⟩
    show Cf.conf.D a.2.2 a.1.2 = Cf.conf.D a.2.1 a.1.1
    rw [Cf.D_of_dec hon.2 h1, Cf.D_of_dec (Cf.free_of_isSome hon.1) h0]
    exact (ldCf_held_same F E Cf L hOK U₀ U₁ hs).symm
  · intro U hU
    rw [ldOl_card_isLeft, ldOl_card_isRight]
    exact hU

omit [Fintype E] in
theorem ldOl_object : Spec.ldOl_object F E := by
  intro Cf K T L hOK hT
  obtain ⟨ha, hb, hc, hd⟩ := ldOl_bridge F E Cf K L hOK
  exact ldObj_link Cf.conf K.P.W0 (K.link T) (K.hLink0 T) K.jIn
    (K.extT T (fun _ _ => 0, fun _ _ => 0)) (K.numsT T) K.P.q0 K.t₀ K.t₁ K.fi
    (ldOl_tail F E Cf K T _ hT) ha hb hc hd

theorem ldOl_chain : Spec.ldOl_chain F E := fun Cf _ K S Z L ε₀ ε₁ d hOK hF hpl hS hZ =>
  ldOl_object F E Cf K (K.ofChain S Z ε₀ ε₁ d) L hOK
    (ldLk_tail K.P K.free K.free ε₀ ε₁ S d Z hF hpl hS hZ)

end
end Cb
