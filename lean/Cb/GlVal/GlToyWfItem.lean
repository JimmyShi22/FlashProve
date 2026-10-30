-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyWfItem.lean: for the small test instance of the preamble of weights-formedness in
Cb/GlVal/GlToyWf.lean: the conditions on places that the theorems on a lookup's own masks take as
hypotheses are proved of its one lookup.

Definitions, statement (`Cb.Gl.Spec.gl_toyWfItem`) and proofs. A guard against empty theorems; no
parameter of a protocol. Data: Cb/GlVal/GlToyWf.lean (F the field with p = 2^64 - 2^32 + 1 elements,
E its cubic extension); the same at the field with 101 elements: Cb/Ld/LdWfToyItem.lean.

Main names:
  `namW l`: the naming (`LdWfP.Lks.Naming`, Cb/Ld/LdWfItemKit.lean) of the own masks that the toy's
    lookup plays: the toy's 35 names (`LkpToyE.Mk E`), at the named entries `mkAt c`.
  `linkW l`: the chain of the lookup, started with its exact claim, is a link of a chain of masked
    blocks (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean).
  `Spec.gl_toyWfItem`: for every l: the four plain conditions on places (`PlacesOK`,
    Cb/Ld/LdLkpMaskPlaces2.lean); `MaskOK` (Cb/Ld/LdLkpMaskAsm2.lean); the places of the own masks
    are the entries `mkAt c`; the overwriting in the item's parameters (`(Kl.dm Rl Kl.cc l).put`) is
    the overwriting of these entries; the link; no named entry that is read is one of the
    batching's.

No clause needs F = E: the lookup, its masks and its item "masked messages" live over E alone; F
enters through the keys only (entries of the index message, embedded), and the conditions on places
do not look at these entries.

Notation: `PlacesOK Dt` (Cb/Ld/LdLkpMaskPlaces2.lean), four fields: `inj`: `plN` is injective;
`out`: no `plN i` lies in Dt; `bits`: every `bAt u j` lies in Dt; `keys`: `key st` is the same at m,
m' that agree on Dt; `.s`, `.t`, `.k`, `.f`, `.e`, `.b`: the constructors of `LkAsm2.Nm` (the same
file): the tie's step 0; its further steps; the levels of the keys' tree; of the table's forest; the
closing; the bit test.

Limits: this file says nothing on the fields `lkpM`, `lkpC` of the preamble (`LdWfP.Blk.Hyp`,
Cb/Ld/LdWf.lean) at this toy. They need `K.OK` (`lks`, Cb/GlVal/GlToyWfMasks.lean). This file says
nothing on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyWfProofs
import Cb.Ld.LdWfItemKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Gl
namespace Wf8
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

def mkCodeW (l : ℕ) : (Kl.asm l).Nm → LkpToyE.Mk E
  | .s i => .inl (.inl i)
  | .t 0 _ i => .inl (.inr i)
  | .t (a + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le a)))
  | .k 0 _ i => .inr (.inl (.inl i))
  | .k (a + 1) h _ => absurd h (Nat.not_succ_le_zero a)
  | .f 0 _ i => .inr (.inl (.inr i))
  | .f (a + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le a)))
  | .e i => .inr (.inr (.inl i))
  | .b i => .inr (.inr (.inr i))

def mkDecodeW (l : ℕ) : LkpToyE.Mk E → (Kl.asm l).Nm
  | .inl (.inl i) => .s i
  | .inl (.inr i) => .t 0 Nat.one_pos i
  | .inr (.inl (.inl i)) => .k 0 (le_refl 0) i
  | .inr (.inl (.inr i)) => .f 0 Nat.one_pos i
  | .inr (.inr (.inl i)) => .e i
  | .inr (.inr (.inr i)) => .b i

theorem decode_codeW (l : ℕ) : ∀ x, mkDecodeW l (mkCodeW l x) = x
  | .s _ => rfl
  | .t 0 _ _ => rfl
  | .t (a + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le a)))
  | .k 0 _ _ => rfl
  | .k (a + 1) h _ => absurd h (Nat.not_succ_le_zero a)
  | .f 0 _ _ => rfl
  | .f (a + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le a)))
  | .e _ => rfl
  | .b _ => rfl

theorem code_decodeW (l : ℕ) : ∀ c, mkCodeW l (mkDecodeW l c) = c
  | .inl (.inl _) => rfl
  | .inl (.inr _) => rfl
  | .inr (.inl (.inl _)) => rfl
  | .inr (.inl (.inr _)) => rfl
  | .inr (.inr (.inl _)) => rfl
  | .inr (.inr (.inr _)) => rfl

theorem plN_eqW (l : ℕ) : ∀ x, (Kl.asm l).plN x = Sum.inr (mkAt (mkCodeW l x))
  | .s (.inl _) => rfl
  | .s (.inr _) => rfl
  | .t 0 _ (.inl _) => rfl
  | .t 0 _ (.inr _) => rfl
  | .t (a + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le a)))
  | .k 0 _ (.inl _) => rfl
  | .k 0 _ (.inr _) => rfl
  | .k (a + 1) h _ => absurd h (Nat.not_succ_le_zero a)
  | .f 0 _ (.inl _) => rfl
  | .f 0 _ (.inr _) => rfl
  | .f (a + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le a)))
  | .e (.inl _) => rfl
  | .e (.inr _) => rfl
  | .b (.inl _) => rfl
  | .b (.inr _) => rfl

theorem mkAt_injW : Function.Injective mkAt := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)

/-- The naming. -/
def namW (l : ℕ) : Kl.Naming l (LkpToyE.Mk E) where
  nm := mkAt
  code := mkCodeW l
  decode := mkDecodeW l
  dc := decode_codeW l
  cd := code_decodeW l
  inj := mkAt_injW
  at' := plN_eqW l
  nb := fun _ _ _ h => Sum.inr_ne_inl h

theorem placesW (l : ℕ) : (Kl.asm l).PlacesOK (Kl.Dt l) := (namW l).places
theorem maskW (l : ℕ) : (Kl.asm l).MaskOK (Kl.Dt l) := (namW l).mask
/-- What the lookup's reading keeps. (`LkAsm2.srAll`, Cb/Ld/LdLkpMaskAsm2.lean) -/
abbrev Rl : ℕ → P.bt.J → Prop := Kl.rl
theorem mokW : Kl.MOK Rl := Kl.mok_of namW
theorem sw_iffW (l : ℕ) (j : P.bt.J) : (Kl.asm l).swAll j ↔ ∃ c, j = Sum.inr (mkAt c) :=
  (namW l).sw_iff j
theorem plW (l : ℕ) : (Kl.pl Rl l).OK ∧ ∀ j, (Kl.pl Rl l).At j ↔ (Kl.asm l).swAll j :=
  (namW l).pl Rl
theorem plW_ex (l : ℕ) (i : (Kl.pl Rl l).I) : ∃ c, (Kl.pl Rl l).pl i = Sum.inr (mkAt c) :=
  (namW l).pl_ex Rl i
theorem inrMk_inj : Function.Injective fun c : LkpToyE.Mk E => (Sum.inr (mkAt c) : P.bt.J) :=
  (namW 0).inr_inj
def sgW (l : ℕ) : (Kl.pl Rl l).I ≃ LkpToyE.Mk E := (namW l).sg Rl
theorem sgW_at (l : ℕ) (i : (Kl.pl Rl l).I) : (Kl.pl Rl l).pl i = Sum.inr (mkAt (sgW l i)) :=
  (namW l).sg_at Rl i
theorem putW (l : ℕ) (M : (Kl.dm Rl Kl.cc l).Mk) (k : P.bt.J → E) :
    (Kl.dm Rl Kl.cc l).put M k =
      Function.extend (fun c => (Sum.inr (mkAt c) : P.bt.J))
        (fun c => (Kl.pl Rl l).ve M ((sgW l).symm c)) k :=
  (namW l).put Rl Kl.cc M k

/-- The index has a value: a word exists. -/
theorem valW : Nonempty Cf.conf.E0.Str :=
  ⟨Cf.conf.enc (fun _ => 5) (Classical.choice Cf.conf.neRnd)⟩

/-- The chain of the lookup is a link of a chain of masked blocks. -/
theorem linkW (l : ℕ) :
    (Kl.dc Rl l).Link ((Kl.asm l).chainA Cf.conf.E0 (Cf.conf.Msg × P.S.Msg) Unit Unit P.msg).H
      (fun w => mjCut (Rl l) (P.msg w.1)) (fun w => mjCut (Rl l) (P.msg w.1))
      ((Kl.asm l).srAll (Kl.Dt l)) (Kl.asm l).swAll (Kl.cc l) :=
  haveI := valW
  ldLkpMaskAsm2_link E p (Kl.asm l) (Kl.asm l).ValidMu Cf.conf.E0 (Cf.conf.Msg × P.S.Msg) Unit Unit
    P.msg (Kl.Dt l) (Rl l) (Kl.cc l) (adm l) (ldLkpAsm2_muValid E (Kl.asm l) (le_refl 2)) (maskW l)
    (fun _ h => h) (fun _ _ h => h) (ldLkpMask_claim_stab E (Kl.asm l) (Kl.Dt l) (placesW l))

/-- A named entry that the lookup's messages read is none of the batching's three. -/
theorem srW (l : ℕ) (n : Nm) (h : (Kl.asm l).srAll (Kl.Dt l) (Sum.inr n)) (i : WBt) :
    n ≠ btAt i := by
  rcases (namW l).sr_named n h with ⟨u, j, rfl⟩ | ⟨c, rfl⟩
  · exact bit_ne _ i
  · exact mk_ne c i

end Wf8

def Spec.gl_toyWfItem : Prop :=
  ∀ l : ℕ,
    (Wf8.Kl.asm l).PlacesOK (Wf8.Kl.Dt l) ∧
    (Wf8.Kl.asm l).MaskOK (Wf8.Kl.Dt l) ∧
    (∀ j, (Wf8.Kl.asm l).swAll j ↔ ∃ c, j = Sum.inr (Wf8.mkAt c)) ∧
    (∀ M k, (Wf8.Kl.dm Wf8.Rl Wf8.Kl.cc l).put M k =
      Function.extend (fun c => (Sum.inr (Wf8.mkAt c) : Wf8.P.bt.J))
        (fun c => (Wf8.Kl.pl Wf8.Rl l).ve M ((Wf8.sgW l).symm c)) k) ∧
    (Wf8.Kl.dc Wf8.Rl l).Link
      ((Wf8.Kl.asm l).chainA Wf8.Cf.conf.E0 (Wf8.Cf.conf.Msg × Wf8.P.S.Msg) Unit Unit Wf8.P.msg).H
      (fun w => mjCut (Wf8.Rl l) (Wf8.P.msg w.1)) (fun w => mjCut (Wf8.Rl l) (Wf8.P.msg w.1))
      ((Wf8.Kl.asm l).srAll (Wf8.Kl.Dt l)) (Wf8.Kl.asm l).swAll (Wf8.Kl.cc l) ∧
    ∀ n, (Wf8.Kl.asm l).srAll (Wf8.Kl.Dt l) (Sum.inr n) → ∀ i, n ≠ Wf8.btAt i

theorem gl_toyWfItem : Spec.gl_toyWfItem := fun l =>
  ⟨Wf8.placesW l, Wf8.maskW l, Wf8.sw_iffW l, Wf8.putW l, Wf8.linkW l, Wf8.srW l⟩

end Cb.Gl
