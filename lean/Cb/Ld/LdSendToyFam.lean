-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendToyFam.lean: a family of two oracle messages, one that holds a vector and one that holds
masks only, with, under `StdFam.Hyp`, a sender that meets all conditions together.

Definitions, statement (`Cb.Spec.stdFam_all`) and proof, for variable codes and samples; what is
asked of them is the record `StdFam.Hyp`.
A guard against empty hypotheses.

This file shows, for two words in one prover message, that hypotheses on the two codes and the two
sample maps (`StdFam.Hyp`) yield the data of an honest prover (`Sig.Sender`, Cb/Ld/LdSendFam.lean)
with all that `Spec.ldSendFam_goodT` (Cb/Ld/LdSendFam.lean) and, for the reading `F.rd`,
`Spec.ldSendFam_fresh` (Cb/Ld/LdSendFresh.lean) ask of a sender.

The family (`F.sig`, names: Bool).
  false: the named member: its message holds a vector x : Ix → E and a pad;
  true: the mask-only member: its message holds masks μ : Im → E and a pad.
  Plain format (`OMsg.plain`, Cb/Ld/LdSig.lean); each has its own code (C₁, C₂), layout (ν₁, ν₂),
  sample (Z₁, Z₂) and radius (e₁, e₂). Pad entries are elements of E.
The sender (`F.snd Wr r0`). The witness is (x, r), r of any type Wr; r is handed on; r0 : Wr: the
fixed witness is (0, r0). Coins that go into the messages: the pad of the first; the masks and the
pad of the second; all independent (Cb/Ld/LdSendMem.lean: `Sig.Sender.ofMem`).
The reading for a coming masked block (`F.rd`): (the vector, the masks, r): it forgets both pads and
all encoding randomness. `F.putM`: the masks overwritten.
What is asked (`F.Hyp L₁ L₂ t₁ t₂`): of each code: its laws, lists of at most L_i codewords at the
radius, an encoding that hides t_i long positions; of each sample: it evades (`Sample.OK`), and it
is private under its pad at every seed (`Sample.Private`).

Main names:
  `Spec.stdFam_all`: under `F.Hyp L₁ L₂ t₁ t₂`, for every Wr and r0:
    the codes' laws, the bounds on lists of messages, "two messages of a list agree at few seeds":
    member by member; independent seeds are fair;
    the sender's laws; at every joint seed, however seeds are shared, the joint law of all answers
    does not depend on the witness (`Blind`); the family's encoding hides t₁ and t₂ long positions
    of its members;
    the messages read the first part of the witness alone; the conditions of Cb/Ld/LdSendFresh.lean
    (`Own.Laws`: over, lay, pad) for the reading above; the reading keeps r, and the overwriting
    does not touch it.

What `LdCode.Laws`, `Sig.Sender.Laws`, `Fair`, `ListLE`, `Evades`, `Blind` and `Hides` ask: the head
of Cb/Ld/LdRng.lean ("What the sending's hypotheses ask").

Limits: this file does not say that codes and samples with `F.Hyp` exist: see the instance
(`Spec.stdFam_toy7`, Cb/Ld/LdSendToyFam7.lean). It says nothing on any protocol.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendMem
import Cb.Ld.LdSendFreshProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data. -/
structure StdFam (E : Type) [Field E] [Fintype E] where
  Ix : Type
  [finIx : Fintype Ix]
  Im : Type
  [finIm : Fintype Im]
  Pd₁ : Type
  [finPd₁ : Fintype Pd₁]
  Pd₂ : Type
  [finPd₂ : Fintype Pd₂]
  P₁ : Type
  [finP₁ : Fintype P₁]
  P₂ : Type
  [finP₂ : Fintype P₂]
  C₁ : LdCode E P₁
  C₂ : LdCode E P₂
  ν₁ : C₁.J ≃ Ix ⊕ Pd₁
  ν₂ : C₂.J ≃ Im ⊕ Pd₂
  Z₁ : Sample E (Ix ⊕ Pd₁)
  Z₂ : Sample E (Im ⊕ Pd₂)
  e₁ : ℕ
  e₂ : ℕ

attribute [instance] StdFam.finIx StdFam.finIm StdFam.finPd₁ StdFam.finPd₂ StdFam.finP₁ StdFam.finP₂

namespace StdFam
variable {E : Type} [Field E] [Fintype E] (F : StdFam E)

@[reducible] def o₁ : OMsg E := OMsg.plain F.C₁ (F.Z₁.comap F.ν₁) F.e₁ fun _ => 0
@[reducible] def o₂ : OMsg E := OMsg.plain F.C₂ (F.Z₂.comap F.ν₂) F.e₂ fun _ => 0

/-- The family. -/
@[reducible] def sig : Sig E :=
  { O := Bool, om := fun b => match b with | false => F.o₁ | true => F.o₂ }

/-- two numbers, as a function of the name -/
def two (a b : ℕ) : F.sig.O → ℕ := fun c => match c with | false => a | true => b

/-- What is asked of codes and samples. -/
structure Hyp (L₁ L₂ t₁ t₂ : ℕ) : Prop where
  laws₁ : F.C₁.Laws
  laws₂ : F.C₂.Laws
  list₁ : F.C₁.ListAt F.e₁ L₁
  list₂ : F.C₂.ListAt F.e₂ L₂
  ok₁   : F.Z₁.OK
  ok₂   : F.Z₂.OK
  priv₁ : F.Z₁.Private E fun _ => True
  priv₂ : F.Z₂.Private E fun _ => True
  zk₁   : F.C₁.Zk t₁
  zk₂   : F.C₂.Zk t₂

variable (Wr : Type) (r0 : Wr)

open Classical in
/-- the sender of the named member -/
@[reducible] def m₁ : F.o₁.Sender ((F.Ix → E) × Wr) Unit where
  N := F.C₁.Nn
  upM := fun m => m
  upR := fun r => r
  Mk := F.Pd₁ → E
  put := fun w η j => withPad (F := E) w.1 η (F.ν₁ j)
  rest := fun _ => ()
  w0 := (0, r0)

open Classical in
/-- the sender of the mask-only member -/
@[reducible] def m₂ : F.o₂.Sender ((F.Ix → E) × Wr) Unit where
  N := F.C₂.Nn
  upM := fun m => m
  upR := fun r => r
  Mk := (F.Im → E) × (F.Pd₂ → E)
  put := fun _ k j => withPad (F := E) k.1 k.2 (F.ν₂ j)
  rest := fun _ => ()
  w0 := (0, r0)

open Classical in
/-- the same with the masks fixed -/
@[reducible] def m₂' (M : F.Im → E) : F.o₂.Sender ((F.Ix → E) × Wr) Unit where
  N := F.C₂.Nn
  upM := fun m => m
  upR := fun r => r
  Mk := F.Pd₂ → E
  put := fun _ η j => withPad (F := E) M η (F.ν₂ j)
  rest := fun _ => ()
  w0 := (0, r0)

@[reducible] def mem : ∀ a, (F.sig.om a).Sender ((F.Ix → E) × Wr) Unit
  | false => F.m₁ Wr r0
  | true => F.m₂ Wr r0

@[reducible] def mem' (M : F.Im → E) : ∀ a, (F.sig.om a).Sender ((F.Ix → E) × Wr) Unit
  | false => F.m₁ Wr r0
  | true => F.m₂' Wr r0 M

/-- The sender. -/
@[reducible] def snd : F.sig.Sender ((F.Ix → E) × Wr) Wr :=
  Sig.Sender.ofMem (F.mem Wr r0) (fun w => w.2) (0, r0)

variable {Wr}

/-- where the entry c of the vector stands; the vector and the masks, read off the messages -/
def at₁ (c : F.Ix) : F.C₁.J := F.ν₁.symm (Sum.inl c)
def vec (m : F.sig.Msg) : F.Ix → E := fun c => m false (F.at₁ c)
def msk (m : F.sig.Msg) : F.Im → E := fun i => m true (F.ν₂.symm (Sum.inl i))

/-- The extractor. -/
def back (m : F.sig.Msg) (r : Wr) : (F.Ix → E) × Wr := (F.vec m, r)

/-- The reading; the masks overwritten. -/
def rd (m : F.sig.Msg) (r : Wr) : (F.Ix → E) × (F.Im → E) × Wr := (F.vec m, F.msk m, r)
def putM (M : F.Im → E) (k : (F.Ix → E) × (F.Im → E) × Wr) : (F.Ix → E) × (F.Im → E) × Wr :=
  (k.1, M, k.2.2)

variable (Wr)

open Classical in
/-- The coins, split: own masks; nothing else; both pads. -/
@[reducible] def own : (F.snd Wr r0).Own (F.Im → E) where
  M0 := Unit
  Pd := (F.Pd₁ → E) × (F.Pd₂ → E)
  κ := { toFun := fun k => (((k true).1, ()), (k false, (k true).2))
         invFun := fun z a => match a with | false => z.2.1 | true => (z.1.1, z.2.2)
         left_inv := fun k => funext fun a => by cases a <;> rfl
         right_inv := fun _ => rfl }

end StdFam

namespace Spec

/-- All conditions together. -/
def stdFam_all : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (F : StdFam E) (L₁ L₂ t₁ t₂ : ℕ) (Wr : Type) (r0 : Wr),
    F.Hyp L₁ L₂ t₁ t₂ →
    (∀ a, (F.sig.om a).C.Laws) ∧
    (∀ a, (F.sig.om a).ListLE (F.two L₁ L₂ a)) ∧
    (∀ a, (F.sig.om a).Evades) ∧
    (Sig.Seeds.indep F.sig).Fair ∧
    (F.snd Wr r0).Laws F.back ∧
    (∀ Sd : F.sig.Seeds, (F.snd Wr r0).Blind Sd) ∧
    (F.snd Wr r0).Nn.Hides (F.sig.budT (F.two t₁ t₂)) ∧
    (∀ (w w' : (F.Ix → E) × Wr) k, w'.1 = w.1 → (F.snd Wr r0).put w' k = (F.snd Wr r0).put w k) ∧
    (∀ Sd : F.sig.Seeds, (F.own Wr r0).Laws Sd F.rd F.putM) ∧
    (∀ (m : F.sig.Msg) (r : Wr), (F.rd m r).2.2 = r) ∧
    ∀ (M : F.Im → E) (k : (F.Ix → E) × (F.Im → E) × Wr), (F.putM M k).2.2 = k.2.2

end Spec
end Cb

/-! ## Proofs -/

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem Ood.Sample.comap_symm {E J J' : Type} (Z : Sample E J) (ν : J' ≃ J) :
    (Z.comap ν).comap ν.symm = Z := by
  show ({ D := Z.D, S := Z.S, mat := fun ρ s n => Z.mat ρ s (ν (ν.symm n)),
          err := Z.err } : Sample E J) = Z
  simp only [Equiv.apply_symm_apply]

namespace StdFam
variable {E : Type} [Field E] [Fintype E] (F : StdFam E) (Wr : Type) (r0 : Wr)

theorem unif₁ (h : F.Z₁.Private E fun _ => True) : (F.m₁ Wr r0).Uniform := by
  refine ldSend_uniform_of_private E E F.o₁ _ Unit (F.m₁ Wr r0) F.Ix F.Pd₁ Unit F.ν₁
    (Equiv.punitProd _).symm (fun w _ => w.1) ?_ ?_
  · intro w k n
    show withPad (F := E) w.1 k (F.ν₁ (F.ν₁.symm n)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · show ((F.Z₁.comap F.ν₁).comap F.ν₁.symm).Private E fun _ => True
    rw [Sample.comap_symm]
    exact h

theorem unif₂ (h : F.Z₂.Private E fun _ => True) : (F.m₂ Wr r0).Uniform := by
  classical
  refine ldSend_uniform_of_private
    E E F.o₂ _ Unit (F.m₂ Wr r0) F.Im F.Pd₂ (F.Im → E) F.ν₂ (Equiv.refl _) (fun _ μ => μ) ?_ ?_
  · intro w k n
    show withPad (F := E) k.1 k.2 (F.ν₂ (F.ν₂.symm n)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · show ((F.Z₂.comap F.ν₂).comap F.ν₂.symm).Private E fun _ => True
    rw [Sample.comap_symm]
    exact h

theorem unif₂' (M : F.Im → E) (h : F.Z₂.Private E fun _ => True) : (F.m₂' Wr r0 M).Uniform := by
  refine ldSend_uniform_of_private E E F.o₂ _ Unit (F.m₂' Wr r0 M) F.Im F.Pd₂ Unit F.ν₂
    (Equiv.punitProd _).symm (fun _ _ => M) ?_ ?_
  · intro w k n
    show withPad (F := E) M k (F.ν₂ (F.ν₂.symm n)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · show ((F.Z₂.comap F.ν₂).comap F.ν₂.symm).Private E fun _ => True
    rw [Sample.comap_symm]
    exact h

theorem vec_put (w : (F.Ix → E) × Wr) (k : (F.snd Wr r0).Mk) :
    F.vec ((F.snd Wr r0).upM ((F.snd Wr r0).put w k)) = w.1 := by
  funext c
  show withPad (F := E) w.1 (k false) (F.ν₁ (F.ν₁.symm (Sum.inl c))) = w.1 c
  rw [Equiv.apply_symm_apply]
  rfl

theorem msk_put (w : (F.Ix → E) × Wr) (k : (F.snd Wr r0).Mk) :
    F.msk ((F.snd Wr r0).upM ((F.snd Wr r0).put w k)) = (k true).1 := by
  funext i
  show withPad (F := E) (k true).1 (k true).2 (F.ν₂ (F.ν₂.symm (Sum.inl i))) = (k true).1 i
  rw [Equiv.apply_symm_apply]
  rfl

open Classical in
theorem pad_unif (h₁ : F.Z₁.Private E fun _ => True) (h₂ : F.Z₂.Private E fun _ => True)
    (Sd : F.sig.Seeds) (s : Sd.D) (w : (F.Ix → E) × Wr) (M : F.Im → E) (k₀ : Unit) :
    (unif ((F.Pd₁ → E) × (F.Pd₂ → E))).map
        (fun η => (F.snd Wr r0).ans Sd s w ((F.own Wr r0).mk' M k₀ η)) =
      unif F.sig.Answ := by
  have h' := ldSendMem_uniform E F.sig _ Wr (F.mem' Wr r0 M) (fun w => w.2) (0, r0) Sd (fun a => by
    cases a
    · exact F.unif₁ Wr r0 h₁
    · exact F.unif₂' Wr r0 M h₂) s w
  let e : (F.Pd₁ → E) × (F.Pd₂ → E) ≃ ∀ a, (F.mem' Wr r0 M a).Mk :=
    { toFun := fun η a => match a with | false => η.1 | true => η.2
      invFun := fun k => (k false, k true)
      left_inv := fun _ => rfl
      right_inv := fun k => funext fun a => by cases a <;> rfl }
  rw [← h', ← map_unif_equiv e, PMF.map_comp]
  refine congrArg (fun φ => PMF.map φ _) (funext fun η => funext fun a => ?_)
  cases a <;> rfl

end StdFam

theorem stdFam_all : Spec.stdFam_all := by
  intro E _ _ F L₁ L₂ t₁ t₂ Wr r0 h
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, (ldSendFam_fair_indep E F.sig).1, ?_, fun Sd => ?_,
    ?_, ?_, fun Sd => ⟨fun _ _ _ => rfl, ⟨fun w _ => (w.1, 0, w.2), fun w M k₀ η => ?_⟩, ?_⟩,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · cases a
    · exact h.laws₁
    · exact h.laws₂
  · cases a
    · exact sig_list_of_code E F.o₁ L₁ h.list₁
    · exact sig_list_of_code E F.o₂ L₂ h.list₂
  · cases a
    · exact sig_evades_of_okOn E F.o₁ _
        (ood_okOn_comap E _ _ F.Z₁ F.ν₁ (fun _ => True) (ood_okOn_of_ok E _ F.Z₁ _ h.ok₁))
        fun _ _ _ _ _ => trivial
    · exact sig_evades_of_okOn E F.o₂ _
        (ood_okOn_comap E _ _ F.Z₂ F.ν₂ (fun _ => True) (ood_okOn_of_ok E _ F.Z₂ _ h.ok₂))
        fun _ _ _ _ _ => trivial
  · refine ldSendMem_laws E F.sig _ Wr (F.mem Wr r0) (fun w => w.2) (0, r0) F.back
      (fun a m r => ?_) fun w k => ?_
    · cases a <;> rfl
    · exact Prod.ext (F.vec_put Wr r0 w k) rfl
  · refine ldSendMem_blind E F.sig _ Wr (F.mem Wr r0) (fun w => w.2) (0, r0) Sd fun a => ?_
    cases a
    · exact ldSend_blind_of_uniform E F.o₁ _ Unit _ (F.unif₁ Wr r0 h.priv₁)
    · exact ldSend_blind_of_uniform E F.o₂ _ Unit _ (F.unif₂ Wr r0 h.priv₂)
  · refine ldSendMem_hides E F.sig _ Wr (F.mem Wr r0) (fun w => w.2) (0, r0)
      (F.two t₁ t₂) fun a => ?_
    cases a
    · exact h.zk₁
    · exact h.zk₂
  · intro w w' k hw
    funext a
    cases a
    · show (fun j => withPad (F := E) w'.1 (k false) (F.ν₁ j)) =
        fun j => withPad (F := E) w.1 (k false) (F.ν₁ j)
      rw [hw]
    · rfl
  · exact Prod.ext (F.vec_put Wr r0 w _) (Prod.ext (F.msk_put Wr r0 w _) rfl)
  · exact own_pad_of_uniform E F.sig _ Wr (F.snd Wr r0) (F.Im → E) (F.own Wr r0) Sd
      fun s w M k₀ => F.pad_unif Wr r0 h.priv₁ h.priv₂ Sd s w M k₀

end Cb
