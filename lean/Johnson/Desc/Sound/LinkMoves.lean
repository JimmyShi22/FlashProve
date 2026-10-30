-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LinkMoves.lean: rules on links with keys (LinkJ, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean),
at parameters: no protocol occurs. They carry the rule for the shared chain (SharedRule.lean) to the
second chain's reduction in the library's row of three chains.

Limits: rules at parameters: no link of a protocol is shown to meet a premise.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.LinkJKit
import OnBytes.TypedOracleCompiler.Joined.MidLinks
import OnBytes.TypedOracleCompiler.Joined.CarryJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open TypedOracleCompiler.Joined (LinkJ shA)
open _root_.CompileK.Joined (onKey silentAt)
open _root_.Iop

variable {A B A' B' κ κ' κ₁ κ₂ WA WB : Type} {N : ℕ}

/-- A reduction over the same rounds that puts out only where K does, and then the same. -/
theorem linkJ_sub {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key' : B → κ'}
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : LinkJ K An N key key' on RA RB ext ε)
    (out' : A → Tr K.shape → Option B) (e : ∀ a τ b, out' a τ = some b → K.out a τ = some b) :
    LinkJ (⟨K.shape, out'⟩ : Reduction A B) An N key key' on RA RB ext ε := by
  obtain ⟨⟨bad, c, J⟩, adm⟩ := h
  refine ⟨⟨bad, fun a τ b w ha hτ hb hw => c a τ b w ha hτ (e a τ b hb) hw, J⟩,
    fun a ha τ j j' b b' hb hb' => ?_⟩
  obtain ⟨aj, haj, ho⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨aj', haj', ho'⟩ := Option.bind_eq_some_iff.1 hb'
  exact adm a ha τ j j' b b' (Option.bind_eq_some_iff.2 ⟨aj, haj, e _ _ _ ho⟩)
    (Option.bind_eq_some_iff.2 ⟨aj', haj', e _ _ _ ho'⟩)

/-- Along an equation of lists of rounds. -/
theorem linkJ_castShape (K : Reduction A B) (s : Shape) (h : K.shape = s) {key : A → κ}
    {key' : B → κ'} {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (hl : LinkJ K (shA K.shape) N key key' on RA RB ext ε) :
    LinkJ (⟨s, fun a τ => K.out a (cast (congrArg Tr h.symm) τ)⟩ : Reduction A B) (shA s) N key
      key' on RA RB (fun a τ w => ext a (cast (congrArg Tr h.symm) τ) w)
      (cast (congrArg Err h) ε) := by
  subst h
  exact hl

/-- Every statement counts: the relation in front is enlarged by the statements outside the
condition. -/
theorem linkJ_offOn {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key' : B → κ'}
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : LinkJ K An N key key' on RA RB ext ε) :
    LinkJ K An N key key' (fun _ => True) (Reduction.orOff on RA) RB ext ε := by
  obtain ⟨⟨bad, c, J⟩, adm⟩ := h
  refine ⟨⟨bad, fun a τ b w _ hτ hb hw => ?_, J⟩, adm⟩
  by_cases ha : on a
  · exact Or.inl (c a τ b w ha hτ hb hw)
  · exact Or.inr ha

/-- **A link, run on a part of a larger statement and glued back.** pre: the part. glue: how what
the link puts out is laid back. The key in front k₁ determines the link's; the key behind k₂ is a
function of k₁ and the link's key behind; a witness behind is one of what the link puts out. -/
theorem linkJ_glued {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key' : B → κ'}
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : LinkJ K An N key key' on RA RB ext ε) (pre : A' → A)
    (glue : A' → B → B') (k₁ : A' → κ₁) (k₂ : B' → κ₂) (R₂ : B' → WB → Prop) (g : κ₁ → κ)
    (hg : ∀ a, key (pre a) = g (k₁ a)) (G : κ₁ → κ' → κ₂)
    (hG : ∀ a b, k₂ (glue a b) = G (k₁ a) (key' b)) (hR : ∀ a b w, R₂ (glue a b) w → RB b w) :
    LinkJ (onKey K pre glue) An N k₁ k₂ (fun a => on (pre a)) (fun a w => RA (pre a) w) R₂
      (fun a τ w => ext (pre a) τ w) ε := by
  obtain ⟨⟨bad, c, J⟩, adm⟩ := h
  have hk : ∀ a : Fin N → Option A', IOR.SameKey k₁ a →
      IOR.SameKey key fun j => (a j).map pre := by
    intro a ha j j' x x' hx hx'
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.1 hx'
    rw [hg, hg, ha j j' y y' hy hy']
  refine ⟨⟨fun a => bad (pre a), fun a τ b' w ha hτ hb hw => ?_, fun a ha => ?_⟩,
    fun a ha τ j j' b b' hb hb' => ?_⟩
  · obtain ⟨b, hb1, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact c (pre a) τ b w ha hτ hb1 (hR a b w hw)
  · refine cast (congrArg (JWithin N _ _ _) (funext fun j => ?_)) (J _ (hk a ha))
    cases a j <;> rfl
  · obtain ⟨aj, haj, h1⟩ := Option.bind_eq_some_iff.1 hb
    obtain ⟨aj', haj', h1'⟩ := Option.bind_eq_some_iff.1 hb'
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1 h1'
    rw [hG, hG, ha j j' aj aj' haj haj']
    refine congrArg (G (k₁ aj')) (adm _ (hk a ha) τ j j' x x' ?_ ?_)
    · show ((a j).map pre).bind _ = _
      rw [haj]
      exact hx
    · show ((a j').map pre).bind _ = _
      rw [haj']
      exact hx'

/-- The same with a relation beside, which each larger statement has of its own: Rc. Where the link
puts out, a witness behind gives, by the link's extractor, a witness of Rc in front. Rc is in no
key. -/
theorem linkJ_gluedBeside {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key' : B → κ'}
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : LinkJ K An N key key' on RA RB ext ε) (pre : A' → A)
    (glue : A' → B → B') (k₁ : A' → κ₁) (k₂ : B' → κ₂) (R₂ : B' → WB → Prop)
    (Rc : A' → WA → Prop) (g : κ₁ → κ) (hg : ∀ a, key (pre a) = g (k₁ a)) (G : κ₁ → κ' → κ₂)
    (hG : ∀ a b, k₂ (glue a b) = G (k₁ a) (key' b)) (hR : ∀ a b w, R₂ (glue a b) w → RB b w)
    (hc : ∀ a τ b w, K.out (pre a) τ = some b → R₂ (glue a b) w → Rc a (ext (pre a) τ w)) :
    LinkJ (onKey K pre glue) An N k₁ k₂ (fun a => on (pre a))
      (fun a w => RA (pre a) w ∧ Rc a w) R₂ (fun a τ w => ext (pre a) τ w) ε := by
  obtain ⟨⟨bad, c, J⟩, adm⟩ := linkJ_glued h pre glue k₁ k₂ R₂ g hg G hG hR
  refine ⟨⟨bad, fun a τ b' w ha hτ hb hw => ⟨c a τ b' w ha hτ hb hw, ?_⟩, J⟩, adm⟩
  obtain ⟨b, hb1, rfl⟩ := Option.map_eq_some_iff.1 hb
  exact hc a τ b w hb1 hw

/-- **A shared round in front that the link does not read**, behind a test t on what it sends: the
error 0. -/
theorem linkJ_front {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key' : B → κ'}
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : LinkJ K An N key key' on RA RB ext ε) (r : Round) (a : RAnn r)
    (ha : a.kind = .sh) (t : A → r.Msg → Bool) (d : WA) :
    LinkJ (⟨r :: K.shape, fun x τ => if t x τ.1 then K.out x τ.2.2 else none⟩ : Reduction A B)
      ((a, An) : RoundSplits (r :: K.shape)) N key key' on RA RB (fun x τ w => ext x τ.2.2 w)
      ((0, ε) : Err (r :: K.shape)) := by
  have h0 := (LinkJ.silentSh r a ha N key on RA).seq h
    (fun _ _ _ hx hb => Option.some.inj hb ▸ hx) d
  refine linkJ_sub (K := (silentAt A r).seq K) h0 _ fun x τ b hb => ?_
  by_cases ht : t x τ.1 = true
  · rw [if_pos ht] at hb
    exact hb
  · rw [if_neg ht] at hb
    cases hb

end VerifiableInference.Desc.Sound
