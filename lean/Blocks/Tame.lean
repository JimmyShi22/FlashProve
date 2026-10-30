-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Tame.lean: the property that, for explicit parts with a property Ia, whether the verifier of
a block rejects depends on its own randomness only (`Block.Tame`).
Terms: lean/GLOSSARY.md.

Why. Some blocks check the explicit part of a statement (what the verifier holds) before they go on:
that the list of deferred claims is well-formed (`Ledger.wf`, Blocks/ProductBlock.lean: every term
of a REL names an opened form in the list; REL, opened forms: Blocks/Form.lean), or that it has the
lengths for which a closing block is made. Blocks/TameBlocks.lean and the files after it prove that
these checks do not reject an explicit part with Ia. That Ia holds throughout the range reduction by
calls, on every transcript, honest or not, is neither stated nor proved in this library.
 * `Block.Tame B Bad Ia Ib`, for a set Bad of verifier randomness and properties Ia, Ib of the
   explicit part before and after the block B:
     `keeps`: if the explicit part before the block has Ia and the verifier does not reject, the
     explicit part after it has Ib: on every transcript, honest or not;
     `acc`: if the explicit part has Ia and ρ is outside Bad, the verifier does not reject, whatever
     the prover sends;
     `rej`: on Bad it rejects.
   So under Ia it accepts if and only if ρ ∉ Bad (`Block.Tame.isSome_iff`).
 * `Core.Tame K Ia Ib`: the same for a protocol K, with the public set `Bad` of its honest prover.
 * It carries over to two blocks in a row (`seq`), to a block that acts on a part of a larger
   statement (`on`, under hg, hp on the properties of the larger statement), to other indices of
   pads (`mapP`); Ia may be strengthened and Ib weakened (`conseq`).
 * The protocols of Blocks/Stage.lean (`Core.id`), Blocks/StageLib.lean, Blocks/StageRows.lean,
   Blocks/VecFlatTrack.lean, Blocks/VecJoinTrack.lean: `Core.tame_id` .. `tame_sendJoin`.
-/
import Blocks.StageRows
import Blocks.StageMap
import Blocks.VecFlatTrack
import Blocks.VecJoinTrack

set_option autoImplicit false

namespace Blocks

open Iop

/-- The verifier rejects on its own randomness only, for explicit parts with the property Ia; and Ia
before the block gives Ib after it. -/
structure Block.Tame {Xi Yi Xo Yo : Type} (B : Block Xi Yi Xo Yo) (Bad : Set (Rho B.shape))
    (Ia : Xi → Prop) (Ib : Xo → Prop) : Prop where
  /-- on every transcript that is not rejected, Ia gives Ib -/
  keeps : ∀ x ρ p xo, Ia x → B.pub x ρ p = some xo → Ib xo
  /-- for x with Ia, outside Bad the verifier accepts whatever the prover sends -/
  acc : ∀ x ρ p, Ia x → ρ ∉ Bad → (B.pub x ρ p).isSome = true
  /-- on Bad it rejects -/
  rej : ∀ x ρ p, ρ ∈ Bad → B.pub x ρ p = none

namespace Block.Tame

variable {X₁ Y₁ X₂ Y₂ X₃ Y₃ : Type}

/-- Under `Tame` and Ia the verifier accepts if and only if its randomness is outside Bad. -/
theorem isSome_iff {B : Block X₁ Y₁ X₂ Y₂} {Bad : Set (Rho B.shape)}
    {Ia : X₁ → Prop} {Ib : X₂ → Prop} (h : B.Tame Bad Ia Ib) {x : X₁} (hx : Ia x)
    (ρ : Rho B.shape) (p : Plains B.shape) :
    (B.pub x ρ p).isSome = true ↔ ρ ∉ Bad :=
  ⟨fun hs hb => by rw [h.rej x ρ p hb] at hs; exact Bool.noConfusion hs, h.acc x ρ p hx⟩

/-- Under `Tame` and Ia, whether the verifier accepts does not depend on what the prover sends. -/
theorem isSome_congr {B : Block X₁ Y₁ X₂ Y₂} {Bad : Set (Rho B.shape)} {Ia : X₁ → Prop}
    {Ib : X₂ → Prop} (h : B.Tame Bad Ia Ib) {x x' : X₁} (hx : Ia x) (hx' : Ia x')
    (ρ : Rho B.shape) (p p' : Plains B.shape) :
    (B.pub x ρ p).isSome = (B.pub x' ρ p').isSome := by
  by_cases hb : ρ ∈ Bad
  · rw [h.rej x ρ p hb, h.rej x' ρ p' hb]
  · rw [h.acc x ρ p hx hb, h.acc x' ρ p' hx' hb]

theorem conseq {B : Block X₁ Y₁ X₂ Y₂} {Bad : Set (Rho B.shape)} {Ia Ia' : X₁ → Prop}
    {Ib Ib' : X₂ → Prop} (h : B.Tame Bad Ia Ib) (ha : ∀ x, Ia' x → Ia x) (hb : ∀ x, Ib x → Ib' x) :
    B.Tame Bad Ia' Ib' :=
  ⟨fun x ρ p xo hx e => hb _ (h.keeps x ρ p xo (ha x hx) e),
    fun x ρ p hx => h.acc x ρ p (ha x hx),
    h.rej⟩

/-- Two blocks in a row. -/
theorem seq {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {Bad₁ : Set (Rho B₁.shape)}
    {Bad₂ : Set (Rho B₂.shape)} {Ia : X₁ → Prop} {Ib : X₂ → Prop} {Ic : X₃ → Prop}
    (h₁ : B₁.Tame Bad₁ Ia Ib) (h₂ : B₂.Tame Bad₂ Ib Ic) :
    (B₁.seq B₂).Tame (Rho.cylFst B₂.shape Bad₁ ∪ Rho.cylSnd B₁.shape Bad₂) Ia Ic where
  keeps := fun x ρ p xo hx e => by
    obtain ⟨x', e1, e2⟩ := Option.bind_eq_some_iff.mp e
    exact h₂.keeps x' _ _ xo (h₁.keeps x _ _ x' hx e1) e2
  acc := fun x ρ p hx hb => by
    have b1 : Rho.fst ρ ∉ Bad₁ := fun h => hb (Or.inl h)
    have b2 : Rho.snd (s := B₁.shape) ρ ∉ Bad₂ := fun h => hb (Or.inr h)
    obtain ⟨x', e1⟩ := Option.isSome_iff_exists.mp (h₁.acc x (Rho.fst ρ) (plFst p) hx b1)
    show ((B₁.pub x (Rho.fst ρ) (plFst p)).bind fun x' =>
        B₂.pub x' (Rho.snd (s := B₁.shape) ρ) (plSnd (s := B₁.shape) p)).isSome = true
    rw [e1]
    exact h₂.acc x' _ _ (h₁.keeps x _ _ x' hx e1) b2
  rej := fun x ρ p hb => by
    show ((B₁.pub x (Rho.fst ρ) (plFst p)).bind fun x' =>
        B₂.pub x' (Rho.snd (s := B₁.shape) ρ) (plSnd (s := B₁.shape) p)) = none
    rcases hb with hb | hb
    · rw [h₁.rej x _ _ hb]
      rfl
    · cases e1 : B₁.pub x (Rho.fst ρ) (plFst p) with
      | none => rfl
      | some x' => exact h₂.rej x' _ _ hb

/-- A block without rounds that does not reject an explicit part with Ia. (not all hypotheses are
named here: see the statement below) -/
theorem pure {f : X₁ → Option X₂} (g : Y₁ → Y₂) {Ia : X₁ → Prop} {Ib : X₂ → Prop}
    (h : ∀ x, Ia x → ∃ xo, f x = some xo ∧ Ib xo) :
    (Block.pure f g).Tame ∅ Ia Ib where
  keeps := fun x _ _ xo hx e => by
    obtain ⟨xo', e', hb⟩ := h x hx
    obtain rfl : xo' = xo := Option.some.inj (e'.symm.trans e)
    exact hb
  acc := fun x _ _ hx _ => by
    obtain ⟨xo', e', -⟩ := h x hx
    show (f x).isSome = true
    rw [e']
    rfl
  rej := fun _ _ _ hb => hb.elim

/-- A block of one round, whose verifier rejects exactly the challenges of Bd. (not all hypotheses
are named here: see the statement below) -/
theorem one {r : Round} {pb : X₁ → r.Chal → r.Plain → Option X₂} (im : Y₁ → r.Msg → r.Chal → Y₂)
    {Bd : Set r.Chal} {Ia : X₁ → Prop} {Ib : X₂ → Prop}
    (hacc : ∀ x c p, Ia x → c ∉ Bd → ∃ xo, pb x c p = some xo ∧ Ib xo)
    (hrej : ∀ x c p, c ∈ Bd → pb x c p = none) :
    (Block.one r pb im).Tame {ρ | ρ.1 ∈ Bd} Ia Ib where
  keeps := fun x ρ p xo hx e => by
    by_cases hb : ρ.1 ∈ Bd
    · exact absurd (e.symm.trans (hrej x ρ.1 p.1 hb)) (Option.some_ne_none xo)
    · obtain ⟨xo', e', h⟩ := hacc x ρ.1 p.1 hx hb
      obtain rfl : xo' = xo := Option.some.inj (e'.symm.trans e)
      exact h
  acc := fun x ρ p hx hb => by
    obtain ⟨xo', e', -⟩ := hacc x ρ.1 p.1 hx hb
    show (pb x ρ.1 p.1).isSome = true
    rw [e']
    rfl
  rej := fun x ρ p hb => hrej x ρ.1 p.1 hb

/-- A block of one round whose verifier applies a public check t to its challenge and checks nothing
else. -/
theorem oneIf {r : Round} (t : r.Chal → Bool)
    (g : X₁ → r.Chal → r.Plain → X₂) (im : Y₁ → r.Msg → r.Chal → Y₂)
    {Ia : X₁ → Prop} {Ib : X₂ → Prop} (h : ∀ x c p, Ia x → Ib (g x c p)) :
    (Block.one r (fun x c p => if t c then some (g x c p) else none) im).Tame
      {ρ | ρ.1 ∈ {c | t c = false}} Ia Ib :=
  one im
    (fun x c p hx hc => ⟨g x c p, if_pos (by
      cases hk : t c
      · exact absurd hk hc
      · rfl), h x c p hx⟩)
    fun _ c _ hc => if_neg (by
      rw [show t c = false from hc]
      exact Bool.false_ne_true)

/-- A block of one round whose verifier checks nothing. -/
theorem oneAll {r : Round} (g : X₁ → r.Chal → r.Plain → X₂) (im : Y₁ → r.Msg → r.Chal → Y₂)
    {Ia : X₁ → Prop} {Ib : X₂ → Prop} (h : ∀ x c p, Ia x → Ib (g x c p)) :
    (Block.one r (fun x c p => some (g x c p)) im).Tame {ρ | ρ.1 ∈ (∅ : Set r.Chal)} Ia Ib :=
  one im (fun x c p hx _ => ⟨g x c p, rfl, h x c p hx⟩) fun _ _ _ hc => hc.elim

/-- A block that acts on a part of a larger statement. -/
theorem on {X Y X' Y' : Type} {B : Block X₁ Y₁ X₂ Y₂} {Bad : Set (Rho B.shape)} {Ia : X₁ → Prop}
    {Ib : X₂ → Prop} (h : B.Tame Bad Ia Ib) (gx : X → X₁) (px : X → X₂ → X') (gy : Y → Y₁)
    (py : Y → Y₂ → Y') {Ja : X → Prop} {Jb : X' → Prop} (hg : ∀ x, Ja x → Ia (gx x))
    (hp : ∀ x xo, Ja x → Ib xo → Jb (px x xo)) :
    (B.on gx px gy py).Tame Bad Ja Jb where
  keeps := fun x ρ p xo hx e => by
    obtain ⟨x', e1, rfl⟩ := Option.map_eq_some_iff.mp e
    exact hp x x' hx (h.keeps _ ρ p x' (hg x hx) e1)
  acc := fun x ρ p hx hb => by
    show ((B.pub (gx x) ρ p).map (px x)).isSome = true
    rw [Option.isSome_map]
    exact h.acc _ ρ p (hg x hx) hb
  rej := fun x ρ p hb => by
    show (B.pub (gx x) ρ p).map (px x) = none
    rw [h.rej _ ρ p hb]
    rfl

end Block.Tame

variable {P P' E : Type} {a b c a' b' : Sorts}

/-- The verifier of the protocol rejects exactly on the public set `Bad`, for explicit parts with
Ia; and Ia before gives Ib after. -/
abbrev Core.Tame (K : Core P E a b) (Ia : a.X → Prop) (Ib : b.X → Prop) : Prop :=
  K.B.Tame K.H.Bad Ia Ib

namespace Core

theorem Tame.seq {K₁ : Core P E a b} {K₂ : Core P E b c} {Ia : a.X → Prop} {Ib : b.X → Prop}
    {Ic : c.X → Prop} (h₁ : K₁.Tame Ia Ib) (h₂ : K₂.Tame Ib Ic) : (K₁.seq K₂).Tame Ia Ic :=
  Block.Tame.seq h₁ h₂

theorem Tame.on {K : Core P E a b} {Ia : a.X → Prop} {Ib : b.X → Prop} (h : K.Tame Ia Ib)
    (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y) (py : a'.Y → b.Y → b'.Y)
    (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) {Ja : a'.X → Prop} {Jb : b'.X → Prop}
    (hg : ∀ x, Ja x → Ia (gx x)) (hp : ∀ x xo, Ja x → Ib xo → Jb (px x xo)) :
    (K.on gx px gy py ga pa).Tame Ja Jb :=
  Block.Tame.on h gx px gy py hg hp

theorem Tame.mapP {K : Core P E a b} {Ia : a.X → Prop} {Ib : b.X → Prop}
    (h : K.Tame Ia Ib) (ip : P → P') : (K.mapP ip).Tame Ia Ib := h

theorem tame_id (a : Sorts) (Ia : a.X → Prop) : (Core.id (P := P) (E := E) a).Tame Ia Ia :=
  Block.Tame.pure _ fun x hx => ⟨x, rfl, hx⟩

theorem tame_pure {f : a.X → Option b.X} (g : a.Y → b.Y) (nx : a.I → b.I) {Ia : a.X → Prop}
    {Ib : b.X → Prop} (h : ∀ x, Ia x → ∃ xo, f x = some xo ∧ Ib xo) :
    (Core.pure (P := P) (E := E) f g nx).Tame Ia Ib :=
  Block.Tame.pure g h

section Lib
variable [Field E]

theorem tame_pads (a : Sorts) {n : ℕ} (idx : Fin n → P) (Ia : a.X → Prop) :
    (Core.pads (E := E) a idx).Tame Ia Ia :=
  ⟨fun x _ _ xo hx e => by obtain rfl : x = xo := Option.some.inj e; exact hx,
    fun _ _ _ _ _ => rfl,
    fun _ _ _ hb => False.elim hb⟩

omit [Field E] in
theorem tame_nameVec (a : Sorts) (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) (Ia : a.X → Prop) :
    (Core.nameVec (P := P) (E := E) a r p₀ msg).Tame Ia Ia :=
  ⟨fun x _ _ xo hx e => by obtain rfl : x = xo := Option.some.inj e; exact hx,
    fun _ _ _ _ _ => rfl,
    fun _ _ _ hb => False.elim hb⟩

omit [Field E] in
theorem tame_send (a : Sorts) (X' Z : Type) (r : Round) (p₀ : r.Plain) (msg : a.I → (P → E) → r.Orc)
    (φ : r.Orc → Z) (fx : a.X → X') {Ia : a.X → Prop} {Ib : X' → Prop} (h : ∀ x, Ia x → Ib (fx x)) :
    (Core.send a X' Z r p₀ msg φ fx).Tame Ia Ib :=
  ⟨fun x _ _ xo hx e => by obtain rfl : fx x = xo := Option.some.inj e; exact h x hx,
    fun _ _ _ _ _ => rfl,
    fun _ _ _ hb => False.elim hb⟩

theorem tame_nameScalars (a : Sorts) {K : Type} (idx : K → P) (val : a.I → K → E) {Ia : a.X → Prop}
    {Ib : a.X × (K → E) → Prop} (h : ∀ x m, Ia x → Ib (x, m)) :
    (Core.nameScalars a idx val).Tame Ia Ib :=
  ⟨fun x _ p xo hx e => by obtain rfl : (x, p.1) = xo := Option.some.inj e; exact h x _ hx,
    fun _ _ _ _ _ => rfl,
    fun _ _ _ hb => False.elim hb⟩

theorem tame_sample (a : Sorts) (I' : Type) (C : Type) [Fintype C] [Nonempty C] (ok : C → Bool)
    (nx : a.I → C → I') {Ia : a.X → Prop} {Ib : a.X × C → Prop} (h : ∀ x c, Ia x → Ib (x, c)) :
    (Core.sample (P := P) (E := E) a I' C ok nx).Tame Ia Ib where
  keeps := fun x ρ _ xo hx e => by
    have e' : (if ok ρ.1 = true then some (x, ρ.1) else none) = some xo := e
    by_cases hk : ok ρ.1 = true
    · rw [if_pos hk] at e'
      obtain rfl := Option.some.inj e'
      exact h x _ hx
    · rw [if_neg hk] at e'
      exact absurd e'.symm (Option.some_ne_none xo)
  acc := fun x ρ _ _ hb => by
    have hk : ok ρ.1 = true := by
      cases hc : ok ρ.1
      · exact absurd hc hb
      · rfl
    show (if ok ρ.1 = true then some (x, ρ.1) else none).isSome = true
    rw [if_pos hk]
    rfl
  rej := fun x ρ _ hb => by
    have hk : ok ρ.1 = false := hb
    show (if ok ρ.1 = true then some (x, ρ.1) else none) = none
    rw [hk]
    rfl

theorem tame_test (a : Sorts) (I' C : Type) [Fintype C] [Nonempty C] (nx : a.I → C → I')
    {Ia : a.X → Prop} {Ib : a.X × C → Prop} (h : ∀ x c, Ia x → Ib (x, c)) :
    (Core.test (P := P) (E := E) a I' C nx).Tame Ia Ib :=
  tame_sample a I' C _ nx h

end Lib

section Vec
variable {F : Type} [Field F] [Field E] [Algebra F E] {X' Z : Type}

theorem tame_sendFlat (A : Type) (overF : A → Bool) (rows len M : A → ℕ) (K C : Type) [Fintype C]
    [Nonempty C] (a : Sorts) (p₀ : K → E) (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') {Ia : a.X → Prop} {Ib : X' → Prop}
    (h : ∀ x, Ia x → Ib (fx x)) :
    (Core.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx).Tame Ia Ib :=
  tame_send _ _ _ _ _ _ _ _ h

theorem tame_sendJoin {A : Type} (bF : Bool) (rows len : A → ℕ) (L : Join.Lay A) (M : ℕ)
    (ord : List A) (K C : Type) [Fintype C] [Nonempty C] (a : Sorts) (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F bF rows len) (φ : Join.Log E F bF rows len → Z)
    (fx : a.X → X') {Ia : a.X → Prop} {Ib : X' → Prop} (h : ∀ x, Ia x → Ib (fx x)) :
    (Core.sendJoin bF rows len L M ord K C a X' Z p₀ msg φ fx).Tame Ia Ib :=
  tame_send _ _ _ _ _ _ _ _ h

end Vec

end Core

end Blocks
