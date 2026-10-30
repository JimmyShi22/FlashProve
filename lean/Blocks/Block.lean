-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Block.lean: blocks (sub-protocols as reductions between statements) and their soundness.

A statement is a pair (x, y). The verifier holds the explicit part x. The implicit part y is
everything committed so far (the index, that is the committed matrix W, and all vectors sent):
relations are about it, but the verifier of a block never reads it. A `Block` consists of its rounds
(`shape`), the verifier's function `pub`, which computes the next explicit part from x, the
challenges and the plain parts of the prover's messages, or rejects, and the function `imp`, which
extends the implicit part by what the prover sent (words of this library: lean/GLOSSARY.md).

`Block.Clean` is round-by-round soundness of a block as a reduction: from a statement outside the
input relation the run ends, except with the stated errors, in a rejection or in a statement outside
the output relation (the prover is doomed: `Doomed`, Iop/Rbr.lean). The rules `Clean.conseq`,
`mono_err`, `frame`, `both` and `comp` come from Iop/Compose.lean through `Block.red`; the others
are proved here.

Three conventions for whoever writes a block:
 (1) Between blocks a relation is about the true object (a function of y and of the points in x),
     never about something that is sent later. `Block.name` (Blocks/BlockLib.lean) lets the prover
     send a scalar or a vector for a hidden quantity and replaces the true object by the sent one.
 (2) A block that samples a challenge by which a later block divides rejects if it is 0
     (`Block.sample`, Blocks/BlockLib.lean).
 (3) Soundness and completeness use different relations, so `Clean` and `AccOn`
     (Blocks/BlockHon.lean) have no relation in common.
-/
import Iop.Compose

namespace Blocks
open Iop Prob

/-! ## Plain parts of two shapes in a row -/

/-- Joins the plain parts of two consecutive shapes. -/
def plApp : {s t : Shape} → Plains s → Plains t → Plains (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (p, a), b => (p, plApp a b)

/-- The plain parts of the first shape. -/
def plFst : {s t : Shape} → Plains (s ++ t) → Plains s
  | [], _, _ => ()
  | _ :: _, _, (p, a) => (p, plFst a)

/-- The plain parts of the second shape. -/
def plSnd : {s t : Shape} → Plains (s ++ t) → Plains t
  | [], _, b => b
  | _ :: s, _, (_, a) => plSnd (s := s) a

theorem plFst_app : ∀ {s t : Shape} (a : Plains s) (b : Plains t), plFst (plApp a b) = a
  | [], _, (), _ => rfl
  | _ :: _, _, (p, a), b => by
      show (p, plFst (plApp a b)) = (p, a)
      rw [plFst_app a b]

theorem plSnd_app : ∀ {s t : Shape} (a : Plains s) (b : Plains t), plSnd (s := s) (plApp a b) = b
  | [], _, _, _ => rfl
  | _ :: s, _, (_, a), b => plSnd_app (s := s) a b

theorem plApp_fst_snd :
    ∀ {s t : Shape} (p : Plains (s ++ t)), plApp (plFst p) (plSnd (s := s) p) = p
  | [], _, _ => rfl
  | _ :: s, _, (p, a) => by
      show (p, plApp (plFst a) (plSnd (s := s) a)) = (p, a)
      rw [plApp_fst_snd a]

theorem plains_app :
    ∀ {s t : Shape} (a : Tr s) (b : Tr t), (Tr.app a b).plains = plApp a.plains b.plains
  | [], _, _, _ => rfl
  | _ :: _, _, (m, _, a), b => by
      show (m.2, (Tr.app a b).plains) = (m.2, plApp a.plains b.plains)
      rw [plains_app a b]

theorem plains_fst : ∀ {s t : Shape} (τ : Tr (s ++ t)), (Tr.fst τ).plains = plFst τ.plains
  | [], _, _ => rfl
  | _ :: _, _, (m, _, a) => by
      show (m.2, (Tr.fst a).plains) = (m.2, plFst a.plains)
      rw [plains_fst a]

theorem plains_snd :
    ∀ {s t : Shape} (τ : Tr (s ++ t)), (Tr.snd (s := s) τ).plains = plSnd (s := s) τ.plains
  | [], _, _ => rfl
  | _ :: s, _, (_, _, a) => plains_snd (s := s) a

/-! ## Blocks -/

/-- A block: the data. Xi, Yi are the explicit and the implicit part of the input statement, Xo, Yo
those of the output statement. -/
structure Block (Xi Yi Xo Yo : Type) where
  shape : Shape
  /-- the verifier: from x, its own randomness and the plain parts only; none = reject -/
  pub : Xi → Rho shape → Plains shape → Option Xo
  /-- the implicit part grows by what was sent -/
  imp : Yi → Tr shape → Yo

namespace Block

variable {Xi Yi Xo Yo X₁ Y₁ X₂ Y₂ X₃ Y₃ : Type}

/-- A block as a reduction between statements (x, y). -/
@[reducible] def red (B : Block Xi Yi Xo Yo) : Reduction (Xi × Yi) (Xo × Yo) where
  shape := B.shape
  out a τ := (B.pub a.1 τ.rho τ.plains).map fun xo => (xo, B.imp a.2 τ)

/-- The first block, then the second on its output. If the first rejects, the rounds of the second
still take place. -/
@[reducible] def seq (B₁ : Block X₁ Y₁ X₂ Y₂) (B₂ : Block X₂ Y₂ X₃ Y₃) : Block X₁ Y₁ X₃ Y₃ where
  shape := B₁.shape ++ B₂.shape
  pub x ρ p := (B₁.pub x (Rho.fst ρ) (plFst p)).bind fun x' =>
    B₂.pub x' (Rho.snd (s := B₁.shape) ρ) (plSnd (s := B₁.shape) p)
  imp y τ := B₂.imp (B₁.imp y (Tr.fst τ)) (Tr.snd (s := B₁.shape) τ)

@[inherit_doc] infixl:65 " ≫ " => Block.seq

/-- A block without rounds: the verifier computes a new explicit part, or rejects; the implicit part
is re-arranged.
It serves for consequences (an identity of polynomials), for re-bracketing and for forgetting. -/
@[reducible] def pure (f : Xi → Option Xo) (g : Yi → Yo) : Block Xi Yi Xo Yo where
  shape := []
  pub x _ _ := f x
  imp y _ := g y

/-- A block that acts on a part of a larger statement (a lens on each of the two parts): the part is
taken out by gx, gy, the output is put back by px, py, which may use everything else in the larger
statement. -/
@[reducible] def on {X Y X' Y' : Type} (B : Block Xi Yi Xo Yo) (gx : X → Xi) (px : X → Xo → X')
    (gy : Y → Yi) (py : Y → Yo → Y') : Block X Y X' Y' where
  shape := B.shape
  pub x ρ p := (B.pub (gx x) ρ p).map (px x)
  imp y τ := py y (B.imp (gy y) τ)


/-! ## Soundness -/

/-- Soundness of a block from Ri to Ro, with errors ε: on every statement outside Ri the
prover is doomed to a rejection or to an output statement outside Ro. It follows (`Clean.of_badFam`)
if there are sets of bad values within the errors such that on a transcript without a bad value an
output in Ro implies that the input is in Ri. -/
def Clean (B : Block Xi Yi Xo Yo) (Ri : Xi → Yi → Prop) (Ro : Xo → Yo → Prop) (ε : Err B.shape) :
    Prop :=
  B.red.Sound (fun a => Ri a.1 a.2) (fun b => Ro b.1 b.2) ε

/-- Clean, written out. -/
theorem clean_iff {B : Block Xi Yi Xo Yo} {Ri : Xi → Yi → Prop}
    {Ro : Xo → Yo → Prop} {ε : Err B.shape} :
    B.Clean Ri Ro ε ↔
    ∀ x y, ¬ Ri x y →
      Doomed B.shape ε (fun τ => ∀ xo, B.pub x τ.rho τ.plains = some xo → ¬ Ro xo (B.imp y τ)) := by
  constructor
  · intro h x y hxy
    refine Doomed.mono _ _ (fun τ hτ xo hxo => ?_) (h (x, y) hxy)
    exact hτ (xo, B.imp y τ) (by show (B.pub x τ.rho τ.plains).map _ = _; rw [hxo]; rfl)
  · intro h a ha
    refine Doomed.mono _ _ (fun τ hτ b hb => ?_) (h a.1 a.2 ha)
    have hb' : (B.pub a.1 τ.rho τ.plains).map (fun xo => (xo, B.imp a.2 τ)) = some b := hb
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb'
    exact hτ xo hxo

/-- How a block is proved sound: bad values within the errors and a backward step. The bad sets may
depend on the whole input statement and on the block's own earlier messages. -/
theorem Clean.of_badFam {B : Block Xi Yi Xo Yo} {Ri : Xi → Yi → Prop} {Ro : Xo → Yo → Prop}
    {ε : Err B.shape} (bad : Xi → Yi → BadFam B.shape) (hW : ∀ x y, (bad x y).Within ε)
    (hback : ∀ x y τ xo,
      (bad x y).Clean τ → B.pub x τ.rho τ.plains = some xo → Ro xo (B.imp y τ) → Ri x y) :
    B.Clean Ri Ro ε :=
  clean_iff.2 fun x y hxy =>
    doomed_of_clean _ _ (bad x y) _ (hW x y) fun τ hτ xo hxo hRo => hxy (hback x y τ xo hτ hxo hRo)

section Rules
variable {B : Block Xi Yi Xo Yo} {Ri Ri' Si : Xi → Yi → Prop} {Ro Ro' So : Xo → Yo → Prop} {ε ε' : Err B.shape}

/-- Consequence: a larger input relation, a smaller output relation. -/
theorem Clean.conseq (h : B.Clean Ri Ro ε)
    (hi : ∀ x y, Ri x y → Ri' x y) (ho : ∀ x y, Ro' x y → Ro x y) : B.Clean Ri' Ro' ε :=
  Reduction.Sound.conseq h (fun a => hi a.1 a.2) fun b => ho b.1 b.2

/-- Larger errors are weaker. -/
theorem Clean.mono_err (h : B.Clean Ri Ro ε) (hε : Err.le ε ε') : B.Clean Ri Ro ε' :=
  Reduction.Sound.mono_err h hε

/-- Frame rule with transport. A condition may be added on both sides if the one on the output
implies the one on the input; for this implication the relations of the block itself may be assumed.
The added condition need not be on copied components: the output condition may be about an object
that the prover has sent and the input condition about the true object, if Ro says that the two
agree. -/
theorem Clean.frame (h : B.Clean Ri Ro ε)
    (hc : ∀ x y τ xo,
      B.pub x τ.rho τ.plains = some xo → Ri x y → Ro xo (B.imp y τ) → So xo (B.imp y τ) → Si x y) :
    B.Clean (fun x y => Ri x y ∧ Si x y) (fun x y => Ro x y ∧ So x y) ε :=
  Reduction.Sound.frame_and_of (S := fun a : Xi × Yi => Si a.1 a.2)
      (S' := fun b : Xo × Yo => So b.1 b.2) h fun a τ b hb hRi hRo hSo => by
    have hb' : (B.pub a.1 τ.rho τ.plains).map (fun xo => (xo, B.imp a.2 τ)) = some b := hb
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb'
    exact hc a.1 a.2 τ xo hxo hRi hRo hSo

/-- One block, two pairs of relations (for challenges that have two roles at once): both hold
together, with the larger error in each round. -/
theorem Clean.both (h : B.Clean Ri Ro ε) (h' : B.Clean Ri' Ro' ε') :
    B.Clean (fun x y => Ri x y ∧ Ri' x y) (fun x y => Ro x y ∧ Ro' x y) (Err.max ε ε') :=
  Reduction.Sound.both h h'

/-- What soundness of a block means for a prover: outside the input relation the prover is doomed.
-/
theorem Clean.toSound (h : B.Clean Ri Ro ε) (x : Xi) (y : Yi) (hxy : ¬ Ri x y) :
    Doomed B.shape ε (fun τ => ¬ ∃ xo, B.pub x τ.rho τ.plains = some xo ∧ Ro xo (B.imp y τ)) :=
  Doomed.mono _ _ (fun _ hτ ⟨xo, hxo, hRo⟩ => hτ xo hxo hRo) (clean_iff.1 h x y hxy)

end Rules

theorem red_seq_out (B₁ : Block X₁ Y₁ X₂ Y₂) (B₂ : Block X₂ Y₂ X₃ Y₃)
    (a : X₁ × Y₁) (τ : Tr (B₁.shape ++ B₂.shape)) :
    (B₁.seq B₂).red.out a τ = (B₁.red.seq B₂.red).out a τ := by
  show ((B₁.pub a.1 (Rho.fst τ.rho) (plFst τ.plains)).bind fun x' =>
          B₂.pub x' (Rho.snd (s := B₁.shape) τ.rho) (plSnd (s := B₁.shape) τ.plains)).map
        (fun xo => (xo, B₂.imp (B₁.imp a.2 (Tr.fst τ)) (Tr.snd (s := B₁.shape) τ))) =
      ((B₁.pub a.1 (Tr.fst τ).rho (Tr.fst τ).plains).map fun xo =>
        (xo, B₁.imp a.2 (Tr.fst τ))).bind fun b =>
      (B₂.pub b.1 (Tr.snd (s := B₁.shape) τ).rho (Tr.snd (s := B₁.shape) τ).plains).map fun xo =>
        (xo, B₂.imp b.2 (Tr.snd (s := B₁.shape) τ))
  rw [Tr.rho_fst, Tr.rho_snd, plains_fst, plains_snd]
  cases B₁.pub a.1 (Rho.fst τ.rho) (plFst τ.plains) <;> rfl

/-- Sequential composition of soundness: if the middle relations agree, the errors are
concatenated. -/
theorem Clean.comp {B₁ : Block X₁ Y₁ X₂ Y₂} {B₂ : Block X₂ Y₂ X₃ Y₃} {R₁ : X₁ → Y₁ → Prop}
    {R₂ : X₂ → Y₂ → Prop} {R₃ : X₃ → Y₃ → Prop} {ε₁ : Err B₁.shape} {ε₂ : Err B₂.shape}
    (h₁ : B₁.Clean R₁ R₂ ε₁) (h₂ : B₂.Clean R₂ R₃ ε₂) :
    (B₁.seq B₂).Clean R₁ R₃ (Err.app ε₁ ε₂) := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => hτ b ((red_seq_out B₁ B₂ a τ).symm.trans hb))
    (Reduction.Sound.seq h₁ h₂ a ha)

/-- A block without rounds is sound if and only if its output relation implies its input
relation. -/
theorem clean_pure_iff {f : Xi → Option Xo} {g : Yi → Yo}
    {Ri : Xi → Yi → Prop} {Ro : Xo → Yo → Prop} :
    (pure f g).Clean Ri Ro () ↔ ∀ x y xo, f x = some xo → Ro xo (g y) → Ri x y := by
  rw [clean_iff]
  exact ⟨fun h x y xo hxo hRo => by_contra fun hn => h x y hn xo hxo hRo,
    fun h x y hn xo hxo hRo => hn (h x y xo hxo hRo)⟩

/-- Soundness on a part of a larger statement. If the block is sound from Ri to Ro (`h`), then
`B.on gx px gy py` is sound from R to R', with the same errors, given one backward step on
statements (`hback`): whenever the new larger statement is in R', the new part is in Ro, and, if the
old part is in Ri, the old larger statement is in R. -/
theorem Clean.on {X Y X' Y' : Type} {B : Block Xi Yi Xo Yo} {Ri : Xi → Yi → Prop}
    {Ro : Xo → Yo → Prop} {ε : Err B.shape} (h : B.Clean Ri Ro ε) {gx : X → Xi} {px : X → Xo → X'}
    {gy : Y → Yi} {py : Y → Yo → Y'} {R : X → Y → Prop} {R' : X' → Y' → Prop}
    (hback : ∀ x y xo yo, R' (px x xo) (py y yo) → Ro xo yo ∧ (Ri (gx x) (gy y) → R x y)) :
    (B.on gx px gy py).Clean R R' ε := by
  rw [clean_iff] at h ⊢
  intro x y hxy
  by_cases hRi : Ri (gx x) (gy y)
  · refine Doomed.of_forall _ _ fun τ x' hx' hR' => ?_
    obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact hxy ((hback x y xo _ hR').2 hRi)
  · refine Doomed.mono _ _ (fun τ hτ x' hx' hR' => ?_) (h _ _ hRi)
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact hτ xo hxo (hback x y xo _ hR').1

/-- As `Clean.on`, with the actual output in the backward step: the step may use that xo is an
output of the block and that the implicit output is the one that the block makes from gy y (for
instance that it extends gy y, or is gy y itself). -/
theorem Clean.on' {X Y X' Y' : Type} {B : Block Xi Yi Xo Yo} {Ri : Xi → Yi → Prop}
    {Ro : Xo → Yo → Prop} {ε : Err B.shape} (h : B.Clean Ri Ro ε) {gx : X → Xi} {px : X → Xo → X'}
    {gy : Y → Yi} {py : Y → Yo → Y'} {R : X → Y → Prop} {R' : X' → Y' → Prop}
    (hback : ∀ x y τ xo, B.pub (gx x) τ.rho τ.plains = some xo →
      R' (px x xo) (py y (B.imp (gy y) τ)) → Ro xo (B.imp (gy y) τ) ∧ (Ri (gx x) (gy y) → R x y)) :
    (B.on gx px gy py).Clean R R' ε := by
  rw [clean_iff] at h ⊢
  intro x y hxy
  by_cases hRi : Ri (gx x) (gy y)
  · refine Doomed.of_forall _ _ fun τ x' hx' hR' => ?_
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact hxy ((hback x y τ xo hxo hR').2 hRi)
  · refine Doomed.mono _ _ (fun τ hτ x' hx' hR' => ?_) (h _ _ hRi)
    obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hx'
    exact hτ xo hxo (hback x y τ xo hxo hR').1

end Block
end Blocks
