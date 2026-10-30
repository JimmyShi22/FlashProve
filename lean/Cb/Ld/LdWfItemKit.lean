-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfItemKit.lean: book-keeping lemmas on the places of the own masks of a lookup argument on
the index, from one record (`Naming`).
A naming says where the own masks of the lookup of one forest of the preamble of weights-formedness
lie among the named entries. From one naming for each forest, `mok_of` gives `K.MOK K.rl`
(Cb/Ld/LdWfBlocksMask.lean), one hypothesis of `Spec.ldWfB_mm` (the item "masked messages"). From
one naming, `Y.pl` and `Y.sg_at` give, each at its own forest alone, two clauses of what the layout
of masks asks of the places (`MaskPl.OK`, Cb/Ld/LdWfMasksAll.lean): `plOK`, and `atEq` at a layout X
whose `atL l i` is `nm (sg i)`.

Definitions, theorems, for any field, configuration and data. Glue for toys and instances
(Cb/Ld/LdWfToyItem.lean did this by hand at one toy); no protocol.

Main names:
  `K.Naming f Mk`: nm : Mk → P.N injective; code, decode: the names of Cb/Ld/LdLkpMaskPlaces2.lean
    (`(K.asm f).Nm`) are the names Mk; each mask is at Sum.inr (nm (code x)); no nm c is the place
    of a bit.
  `Y.places`, `Y.mask`: the four plain conditions on places at the forest's data (`K.Dt f`); so
    `LkAsm2.MaskOK`.
  `K.rl f`: what the lookup's reading keeps (`LkAsm2.srAll`, Cb/Ld/LdLkpMaskAsm2.lean): data and own
    masks.
  `Y.pl`: the places of the chain's letters (its parameters, a record `MJ`,
    Cb/Ld/LdLkpMaskChain.lean; the places: Cb/Ld/LdLkpMaskPutLkp2.lean) are `MJ.Pl.OK`
    (Cb/Ld/LdLkpMaskPut.lean).

Limits: this file says nothing on a protocol. It says nothing on the other clauses of `MaskPl.OK`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfBlocksMaskProofs
import Cb.Ld.LdLkpMaskClaim
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

/-- overwriting at places named through a bijection of the names -/
theorem extend_along {I I' J V : Type} (σ : I ≃ I') (g : I' → J) (hg : Function.Injective g)
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

namespace LdWfP.Lks
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C} (K : P.Lks)

/-- A naming of the own masks that the lookup of forest f plays. -/
structure Naming (f : ℕ) (Mk : Type) where
  nm     : Mk → P.N
  code   : (K.asm f).Nm → Mk
  decode : Mk → (K.asm f).Nm
  dc     : ∀ x, decode (code x) = x
  cd     : ∀ c, code (decode c) = c
  inj    : Function.Injective nm
  at'    : ∀ x, (K.asm f).plN x = Sum.inr (nm (code x))
  nb     : ∀ c u j, nm c ≠ K.bAt f u j

/-- what the lookup's reading keeps -/
def rl (f : ℕ) : P.bt.J → Prop := (K.asm f).srAll (K.Dt f)

namespace Naming
variable {K} {f : ℕ} {Mk : Type} (Y : K.Naming f Mk)

theorem inr_inj : Function.Injective fun c : Mk => (Sum.inr (Y.nm c) : P.bt.J) := fun _ _ h =>
  Y.inj (Sum.inr_injective h)

include Y in
theorem places : (K.asm f).PlacesOK (K.Dt f) where
  inj := fun x y h => by
    rw [Y.at', Y.at'] at h
    have h1 := congrArg Y.decode (Y.inr_inj h)
    rwa [Y.dc, Y.dc] at h1
  out := fun i h => by
    rw [Y.at'] at h
    rcases h with ⟨rc, e⟩ | ⟨u, j, e⟩
    · exact Sum.inr_ne_inl e
    · exact Y.nb _ u j (Sum.inr_injective e)
  bits := fun u j => Or.inr ⟨u, j, rfl⟩
  keys := fun _ (m m' : P.bt.J → E) hm => by
    have e : (fun rc : P.Rw × (Fin P.k → Bool) => m (Sum.inl rc)) = fun rc => m' (Sum.inl rc) :=
      funext fun rc => hm (Sum.inl rc) (Or.inl ⟨rc, rfl⟩)
    show P.keyE f (fun rc => m (Sum.inl rc)) = P.keyE f (fun rc => m' (Sum.inl rc))
    rw [e]

include Y in
theorem mask : (K.asm f).MaskOK (K.Dt f) := ldLkpPlaces2_ok E _ _ Y.places

theorem sw_iff (j : P.bt.J) : (K.asm f).swAll j ↔ ∃ c, j = Sum.inr (Y.nm c) :=
  ⟨fun h => by
    obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E (K.asm f) j).1 h
    exact ⟨_, Y.at' i⟩,
      fun ⟨c, e⟩ => (ldLkpPlaces2_sw E (K.asm f) j).2 ⟨Y.decode c, by rw [e, Y.at', Y.cd]⟩⟩

/-- a named entry that the lookup's messages read is a bit's place or an own mask -/
theorem sr_named (n : P.N) (h : (K.asm f).srAll (K.Dt f) (Sum.inr n)) :
    (∃ u j, n = K.bAt f u j) ∨ ∃ c, n = Y.nm c := by
  rcases h with (⟨rc, e⟩ | ⟨u, j, e⟩) | hw
  · exact absurd e Sum.inr_ne_inl
  · exact Or.inl ⟨u, j, Sum.inr_injective e⟩
  · obtain ⟨c, e⟩ := (Y.sw_iff _).1 hw
    exact Or.inr ⟨c, Sum.inr_injective e⟩

variable (Rl : ℕ → P.bt.J → Prop)

include Y in
theorem pl : (K.pl Rl f).OK ∧ ∀ j, (K.pl Rl f).At j ↔ (K.asm f).swAll j :=
  (ldLkpPl2_asm E (K.asm f) C.E0 (C.Msg × P.S.Msg) Unit Unit P.msg (Rl f) (K.Dt f) Y.mask).1

theorem pl_ex (i : (K.pl Rl f).I) : ∃ c, (K.pl Rl f).pl i = Sum.inr (Y.nm c) :=
  (Y.sw_iff _).1 (((Y.pl Rl).2 _).1 ⟨i, rfl⟩)

/-- A bijection between the names of the places of the chain's letters and the names Mk. -/
def sg : (K.pl Rl f).I ≃ Mk :=
  Equiv.ofBijective (fun i => Classical.choose (Y.pl_ex Rl i))
    ⟨fun i i' h => (Y.pl Rl).1.inj (by
        have h1 := Classical.choose_spec (Y.pl_ex Rl i)
        have h2 := Classical.choose_spec (Y.pl_ex Rl i')
        have h' : Classical.choose (Y.pl_ex Rl i) = Classical.choose (Y.pl_ex Rl i') := h
        rw [h1, h2, h']),
      fun c => by
        obtain ⟨i, hi⟩ := ((Y.pl Rl).2 _).2 ((Y.sw_iff _).2 ⟨c, rfl⟩)
        exact ⟨i, Y.inr_inj ((Classical.choose_spec (Y.pl_ex Rl i)).symm.trans hi)⟩⟩

theorem sg_at (i : (K.pl Rl f).I) : (K.pl Rl f).pl i = Sum.inr (Y.nm (Y.sg Rl i)) :=
  Classical.choose_spec (Y.pl_ex Rl i)

/-- For a naming `Y`: the letters' overwriting is the overwriting of the named entries. -/
theorem put (Cc : ℕ → P.WSt → (P.bt.J → E) → Prop) (M : (K.dm Rl Cc f).Mk) (k : P.bt.J → E) :
    (K.dm Rl Cc f).put M k =
      Function.extend (fun c => (Sum.inr (Y.nm c) : P.bt.J))
        (fun c => (K.pl Rl f).ve M ((Y.sg Rl).symm c)) k :=
  ((ldWfML_put (E := E) C P K Rl Cc f (fun i => Y.nm (Y.sg Rl i)) (Y.pl Rl).1 (Y.sg_at Rl)).2
      M k).trans
    (extend_along (Y.sg Rl) (fun c => (Sum.inr (Y.nm c) : P.bt.J)) Y.inr_inj ((K.pl Rl f).ve M) k)

end Naming

/-- the conditions on places of all forests, from namings -/
theorem mok_of {Mk : ℕ → Type} (Y : ∀ f, K.Naming f (Mk f)) : K.MOK K.rl :=
  ⟨fun f _ => (Y f).mask, fun _ _ _ h => h⟩

end LdWfP.Lks
end Cb
