-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfToyItem.lean: two lemmas on names and places, for the toy of weights-formedness (data:
Cb/Ld/LdWfToy.lean, Cb/Ld/LdWfToyMasks.lean).





Theorems and proofs. No parameter of a protocol.








Main names:
  `extend_reindex`: overwriting at places named through a bijection of the names.
  `LdWfP.Lks.placesOK_of`: the four plain conditions on places (Cb/Ld/LdLkpMaskPlaces2.lean) for the
    lookup of a forest of the preamble, from a naming of its own masks among the named entries.














Limits: this file says nothing on the size of errors (Cb/Ld/LdWfToyMasks.lean). No level of
security: the sending's error is not below its number of seeds (Cb/Ld/LdWfToyMasks.lean,
"Limits:").








Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfToyMasks
import Cb.Ld.LdWfBlocksMaskProofs
import Cb.Ld.LdLkpToyMask

set_option autoImplicit false

namespace Cb

variable [WfToy.ToyModel]

omit [WfToy.ToyModel] in
/-- overwriting at places named through a bijection of the names -/
theorem extend_reindex {I I' J V : Type} (σ : I ≃ I') (g : I' → J) (hg : Function.Injective g)
    (f : I → V) (k : J → V) :
    Function.extend (fun i => g (σ i)) f k = Function.extend g (fun c => f (σ.symm c)) k := by
  classical
  funext j
  by_cases h : ∃ c, g c = j
  · obtain ⟨c, rfl⟩ := h
    rw [hg.extend_apply]
    have h1 : Function.Injective fun i => g (σ i) := fun a b e => σ.injective (hg e)
    have h2 := h1.extend_apply f k (σ.symm c)
    simpa using h2
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ fun ⟨i, e⟩ => h ⟨σ i, e⟩]

omit [WfToy.ToyModel] in
/-- The four plain conditions on places for the lookup of a forest of the preamble, from a naming of
its own masks among the named entries (not all hypotheses are named here: see the statement below).
-/
theorem LdWfP.Lks.placesOK_of {E : Type} [Field E] [Fintype E] {C : Hiop.ConfigurationWithOutOfDomainSample} {P : LdWfP E C}
    (K : P.Lks) (f : ℕ) {Mk : Type} (pl : Mk → P.N) (code : (K.asm f).Nm → Mk)
    (hc : Function.Injective code) (hp : Function.Injective pl)
    (he : ∀ x, (K.asm f).plN x = Sum.inr (pl (code x))) (hb : ∀ c u j, pl c ≠ K.bAt f u j) :
    (K.asm f).PlacesOK (K.Dt f) where
  inj := fun x y h => by
    rw [he, he] at h
    exact hc (hp (Sum.inr_injective h))
  out := fun i h => by
    rw [he] at h
    rcases h with ⟨rc, e⟩ | ⟨u, j, e⟩
    · exact Sum.inr_ne_inl e
    · exact hb _ u j (Sum.inr_injective e)
  bits := fun u j => Or.inr ⟨u, j, rfl⟩
  keys := fun _ (m m' : P.bt.J → E) hm => by
    have e : (fun rc : P.Rw × (Fin P.k → Bool) => m (Sum.inl rc)) = fun rc => m' (Sum.inl rc) :=
      funext fun rc => hm (Sum.inl rc) (Or.inl ⟨rc, rfl⟩)
    show P.keyE f (fun rc => m (Sum.inl rc)) = P.keyE f (fun rc => m' (Sum.inl rc))
    rw [e]

end Cb
