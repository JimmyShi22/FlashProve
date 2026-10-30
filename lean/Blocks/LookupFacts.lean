-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupFacts.lean: facts on a lookup argument for the protocols that contain one.

The argument, its three phases and its relations: Blocks/LookupBlock.lean, Blocks/LookupHon.lean,
Blocks/LookupStage.lean.

Which challenges are rejected at 0 is stated in Blocks/LookupBlock.lean, choice (2). Of the end
point z of the key side these are the coordinates that `LkPar.zf` selects; by default all, also
those by which no later block divides.

 * Accepted outputs. The end claim of the key side has the premise that no coordinate of the end
   point z that the verifier checks is 0. For an output of the verifier the premise is a fact, if 0
   < D and the order `ordK` is valid: `Lk.nz_of_pub_st14`.
 * What a phase changes. `Block.Keeps` B f g: whenever the verifier does not reject, g of the output
   is f of the input; `Block.Keeps.seq`. `Lk.pub_st5`, `Lk.pub_st6`.
 * Honest implies sound. `Lk.r7_of_h7`, `Lk.r8_of_h8`, `Lk.r10_of_h10` (stated with 2 ≠ 0 in E): a
   statement in the relation for the honest run after a phase is in the relation for soundness after
   that phase. So soundness and completeness are about the same claims.
-/
import Blocks.LookupSplit

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop

/-! ## 1. Challenges that are rejected at 0 -/

/-- If the verifier does not reject and `SC.NZ` held before, after the rounds no challenge that is
rejected at 0 is 0. -/
theorem SC.nz_of_pub_sc {E Y P Ξ ι : Type} [Field E] [Fintype E] [DecidableEq E]
    [DecidableEq ι] (S : SC E Y P Ξ ι) :
    ∀ (l : List ι) (x xo : S.X) (ρ : Rho (S.sc l).shape) (p : Plains (S.sc l).shape),
      (S.sc l).pub x ρ p = some xo → S.NZ l x.2.1 → S.NZ [] xo.2.1
  | [], x, xo, _, _, h, hx => by
      rw [← Option.some.inj h]
      exact hx
  | i :: l, x, xo, ρ, p, h, hx => by
      obtain ⟨x', hx', hxo⟩ := Option.bind_eq_some_iff.mp h
      refine SC.nz_of_pub_sc S l x' xo _ _ hxo ?_
      have h1 : S.pb i x ρ.1 p.1 = some x' := hx'
      unfold SC.pb at h1
      by_cases hc : S.nzv i = true ∧ ρ.1 = 0
      · rw [if_pos hc] at h1
        exact absurd h1 (by simp)
      · rw [if_neg hc] at h1
        rw [← Option.some.inj h1]
        exact SC.NZ.update S hx hc

/-- Under ho, without rejection: no coordinate of the next point of a product layer that is rejected
at 0 is 0. -/
theorem PL.pt_ne_zero {E Y P N Ξ : Type} [Field E] [Fintype E] [DecidableEq E] [Fintype N]
    [DecidableEq N] (L : PL E Y P N Ξ) (ho : L.OrdOK) {x : PLX N E Ξ} {ρ : Rho L.pl.shape}
    {p : Plains L.pl.shape} {xo : PL.XOut N E Ξ} (h : L.pl.pub x ρ p = some xo) :
    ∀ t < L.g + 1, L.nz t = true → xo.1.pt t ≠ 0 := by
  obtain ⟨x1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  have h3 := L.sc.nz_of_pub_sc _ _ _ _ _ h1 (L.nz_start ho _)
  obtain ⟨hok, _, rfl⟩ := L.fin_some h2
  intro t ht hnz
  cases t with
  | zero => exact L.ne_zero_of_okE hok hnz
  | succ t => exact h3 t (L.nzv_iff.mpr ⟨hnz, by omega⟩) List.not_mem_nil

/-! ## 2. What a block keeps -/

/-- Whenever the verifier does not reject, g of the output is f of the input. -/
def Block.Keeps {Xi Yi Xo Yo α : Type} (B : Block Xi Yi Xo Yo) (f : Xi → α) (g : Xo → α) : Prop :=
  ∀ x ρ p xo, B.pub x ρ p = some xo → g xo = f x

theorem Block.Keeps.seq {X₁ Y₁ X₂ Y₂ X₃ Y₃ α : Type} {B₁ : Block X₁ Y₁ X₂ Y₂}
    {B₂ : Block X₂ Y₂ X₃ Y₃} {f₁ : X₁ → α} {f₂ : X₂ → α} {f₃ : X₃ → α}
    (h : B₁.Keeps f₁ f₂) (h' : B₂.Keeps f₂ f₃) : (B₁.seq B₂).Keeps f₁ f₃ := by
  intro x ρ p xo hx
  obtain ⟨x', h1, h2⟩ := Option.bind_eq_some_iff.mp hx
  exact (h' x' _ _ xo h2).trans (h x _ _ x' h1)

/-- Whenever the verifier does not reject, the output has the property Q. -/
def Block.Ensures {Xi Yi Xo Yo : Type} (B : Block Xi Yi Xo Yo) (Q : Xo → Prop) : Prop :=
  ∀ x ρ p xo, B.pub x ρ p = some xo → Q xo

theorem Block.Ensures.after {X₁ Y₁ X₂ Y₂ X₃ Y₃ : Type} (B₁ : Block X₁ Y₁ X₂ Y₂)
    {B₂ : Block X₂ Y₂ X₃ Y₃} {Q : X₃ → Prop} (h : B₂.Ensures Q) : (B₁.seq B₂).Ensures Q := by
  intro x ρ p xo hx
  obtain ⟨x', _, h2⟩ := Option.bind_eq_some_iff.mp hx
  exact h x' _ _ xo h2

theorem Block.Ensures.kept {X₁ Y₁ X₂ Y₂ X₃ Y₃ α : Type} {B₁ : Block X₁ Y₁ X₂ Y₂}
    {B₂ : Block X₂ Y₂ X₃ Y₃} {f : X₂ → α} {g : X₃ → α} {Q : α → Prop}
    (h : B₁.Ensures fun x => Q (f x)) (h' : B₂.Keeps f g) :
    (B₁.seq B₂).Ensures fun x => Q (g x) := by
  intro x ρ p xo hx
  obtain ⟨x', h1, h2⟩ := Option.bind_eq_some_iff.mp hx
  show Q (g xo)
  rw [h' x' _ _ xo h2]
  exact h x _ _ x' h1

namespace Lk

variable {E Y Pd N : Type}
  [Field E] [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] (L : Lk E Y Pd N)

private theorem of_ite' {α : Type} {c : Bool} {a xo : α}
    (h : (if c then some a else none) = some xo) : xo = a := by
  cases c
  · exact absurd h (by simp)
  · exact (Option.some.inj h).symm

/-- Fields that the table side does not change. -/
abbrev k3 : LkX N E → E × (ℕ → E) × Form N E := fun x => (x.al, x.z, x.Cend)

/-- Fields that the root test does not change. -/
abbrev k8 : LkX N E → E × (ℕ → E) × Form N E × Form N E × (ℕ → E) × Form N E × (ℕ → E) × (ℕ → E) :=
  fun x => (x.al, x.z, x.Cend, x.v4, x.p4, x.v5, x.p5, x.p6)

theorem keeps_bT0 : L.bT0.Keeps k3 k3 := fun _ _ _ _ h => by rw [of_ite' h]; rfl
theorem keeps_bT (l : ℕ) : (L.bT l).Keeps k3 k3 := fun _ _ _ _ h => by
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl
theorem keeps_coTab : ∀ n l : ℕ, (L.coTab n l).B.Keeps k3 k3
  | 0, _ => fun _ _ _ _ h => by rw [← Option.some.inj h]
  | n + 1, l => (L.keeps_bT l).seq (keeps_coTab n (l + 1))
theorem keeps_bL : L.bL.Keeps k3 k3 := fun _ _ _ _ h => by
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl
theorem keeps_bB0 : L.bB0.Keeps k3 k3 := fun _ _ _ _ h => by rw [of_ite' h]
theorem keeps_bB : L.bB.Keeps k3 k3 := fun _ _ _ _ h => by
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
  rfl

/-- Under ho, without rejection: after the layers l, .., l + n of the key side no coordinate of the
running point that is rejected at 0 is 0. -/
theorem pt_of_coKey (ho : L.par.OrdOK) :
    ∀ (n l : ℕ) (x xo : LkX N E) (ρ : Rho (L.coKey (n + 1) l).B.shape)
        (p : Plains (L.coKey (n + 1) l).B.shape),
      (L.coKey (n + 1) l).B.pub x ρ p = some xo →
      ∀ t < l + (n + 1) + L.par.σ, L.par.kf (l + (n + 1)) t = true → xo.pt t ≠ 0
  | 0, l, x, xo, ρ, p, h => by
      obtain ⟨x', h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨xo', h3, rfl⟩ := Option.map_eq_some_iff.mp h1
      rw [← Option.some.inj h2]
      intro t ht hf
      exact (L.plK l).pt_ne_zero (ho.kOrd l) h3 t (by show t < l + L.par.σ + 1; omega) hf
  | n + 1, l, x, xo, ρ, p, h => by
      obtain ⟨x', _, h2⟩ := Option.bind_eq_some_iff.mp h
      intro t ht hf
      exact pt_of_coKey ho n (l + 1) x' xo _ _ h2 t (by omega)
        (by rw [show l + 1 + (n + 1) = l + (n + 1 + 1) by omega]; exact hf)

theorem ensures_coKey (ho : L.par.OrdOK) :
    ∀ n l : ℕ, 0 < n →
      (L.coKey n l).B.Ensures fun x => ∀ t < l + n + L.par.σ, L.par.kf (l + n) t = true → x.pt t ≠ 0
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, l, _ => fun x ρ p xo h => L.pt_of_coKey ho n l x xo ρ p h

/-- After the key side: z is the running point; the table side does not change it. -/
theorem keeps_after_key :
    (L.bKe.seq (L.bT0.seq ((L.coTab L.par.r 0).B.seq (L.bL.seq (L.bB0.seq L.bB))))).Keeps
      (fun x => x.pt) (fun x => x.z) :=
  Block.Keeps.seq (f₂ := fun x : LkX N E => x.z)
      (fun _ _ _ _ h => by rw [← Option.some.inj h]) fun x ρ p xo h =>
    congrArg (fun q : E × (ℕ → E) × Form N E => q.2.1)
      ((L.keeps_bT0.seq <|
          (L.keeps_coTab L.par.r 0).seq <|
          L.keeps_bL.seq <|
          L.keeps_bB0.seq L.keeps_bB)
        x ρ p xo h)

/-- Under ho, hD: no coordinate of the end point z of the key side that the verifier checks is 0,
whenever the verifier of steps 1 to 4 does not reject. So the end claim's premise holds of accepted
outputs. -/
theorem nz_of_pub_st14 (ho : L.par.OrdOK) (hD : 0 < L.par.D)
    {led : Ledger N E} {ρ : Rho L.st14.B.shape} {p : Plains L.st14.B.shape}
    {x : LkX N E} (h : L.st14.B.pub led ρ p = some x) :
    ∀ t < L.par.D + L.par.σ, L.par.zf t = true → x.z t ≠ 0 := by
  have h1 := Block.Ensures.after L.bAl
    (Block.Ensures.after L.bZY
      (Block.Ensures.kept
        (Q := fun z : ℕ → E =>
            ∀ t < 0 + L.par.D + L.par.σ, L.par.kf (0 + L.par.D) t = true → z t ≠ 0)
        (L.ensures_coKey ho L.par.D 0 hD) L.keeps_after_key))
    led ρ p x h
  intro t ht hf
  exact h1 t (by omega) (by rw [Nat.zero_add, L.par.kf_top]; exact hf)

/-! ## 3. What the degree check and the root test change -/

/-- Without rejection, the degree check stores ϱ6 and changes nothing else. -/
theorem pub_st5 {x xo : LkX N E} {ρ : Rho L.st5.B.shape}
    {p : Plains L.st5.B.shape} (h : L.st5.B.pub x ρ p = some xo) : ∃ ϱ, xo = { x with p6 := ϱ } :=
  ⟨_, (Option.some.inj h).symm⟩

theorem keeps_st6 : L.st6.B.Keeps k8 k8 :=
  Block.Keeps.seq (B₁ := L.bUV) (f₂ := k8) (fun _ _ _ _ h => by rw [of_ite' h]; rfl) <|
  Block.Keeps.seq (B₁ := L.bXi) (f₂ := k8) (fun _ _ _ _ h => by rw [← Option.some.inj h]) <|
  Block.Keeps.seq (B₁ := L.bRs) (B₂ := L.bRec) (f₂ := k8) (fun _ _ _ _ h => by
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl) fun _ _ _ _ h => by rw [of_ite' h]

/-- Without rejection, the root test keeps α, z, C_end, the forms v0 and the end points of the leaf
layer and of the bit layer, and ϱ6. -/
theorem pub_st6 {x xo : LkX N E} {ρ : Rho L.st6.B.shape}
    {p : Plains L.st6.B.shape} (h : L.st6.B.pub x ρ p = some xo) :
    xo.al = x.al ∧ xo.z = x.z ∧ xo.Cend = x.Cend ∧ xo.v4 = x.v4 ∧ xo.p4 = x.p4 ∧ xo.v5 = x.v5 ∧
    xo.p5 = x.p5 ∧ xo.p6 = x.p6 := by
  have hk := L.keeps_st6 x ρ p xo h
  simp only [Prod.mk.injEq] at hk
  exact hk

/-! ## 4. The relations for the honest run imply the relations for soundness -/

section Hon

variable [NeZero (2 : E)] (T : Lk.Vecs E Y) {U : Set Pd} {a : LkA E}
  {π : Pd → E} {x : LkX N E} {y : Y}

/-- The identity `LkPar.Ident` for the values of the sent tree products, if these are the true ones
and `TF` holds (and 2 ≠ 0 in E). -/
theorem ids_of_tz (htf : L.TF T y) (htz : L.TZ T x y) : L.IDS x y := fun θ hθ => by
  have h := htf.2.2 x.al θ hθ
  show L.V y (x.Zf θ) = _
  rw [htz.1 θ hθ, h]
  congr 1
  exact Finset.prod_congr rfl fun π hπ =>
    congrArg (· ^ 2 ^ π) (htz.2 θ hθ π (Finset.mem_range.mp hπ)).symm

theorem r7_of_h7 (h : L.H7 T U a π x y) : L.R7 T x y := by
  obtain ⟨⟨⟨_, _, _, _, htrue, _, htf⟩, _⟩, htz, hend, h4, h5⟩ := h
  exact ⟨htrue, ⟨htf.2.1, L.ids_of_tz T htf htz, fun _ => hend.2, h4⟩, h5⟩

theorem r8_of_h8 (h : L.H8 T U a π x y) : L.R8 T x y := by
  obtain ⟨⟨⟨⟨_, _, _, _, htrue, _, htf⟩, _⟩, htz, hend, h4, h5⟩, h6⟩ := h
  exact ⟨htrue, L.ids_of_tz T htf htz, fun _ => hend.2, h4, h5, h6⟩

theorem r10_of_h10 (h : L.H10 T U a π x y) : L.R10 T x y := by
  obtain ⟨⟨⟨_, _, _, _, htrue, _, _⟩, _⟩, hend, h4, h5, h6⟩ := h
  exact ⟨htrue, fun _ => hend.2, h4, h5, h6⟩

end Hon

end Lk

end Blocks
