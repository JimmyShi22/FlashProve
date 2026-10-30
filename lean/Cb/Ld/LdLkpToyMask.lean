-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpToyMask.lean: the guard for the item "masked messages" of the assembled lookup: at the
toy lookup all its hypotheses are met together;
nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
This file is an example: at the toy lookup of Cb/Ld/LdLkpToy.lean every hypothesis of
`Spec.ldLkpMaskAsm2_link`, `Spec.ldLkpMaskAsm2_mm` (Cb/Ld/LdLkpMaskAsm2.lean), `Spec.mjLift2_subN`
and `Spec.mjLift2_clN` (Cb/Ld/LdLkpMaskLift2.lean) is proved, but for `[Nonempty Ex.Str]`, which
stays in the statement.

Statement (`Cb.Spec.ldLkp_toyMask`) and proof. A guard against empty theorems; no parameter of a
protocol.

The toy (Cb/Ld/LdLkpToy.lean: `toyA`, below A, over the field with 101 elements): two keys in the
table (5, 7); six sumchecks; one oracle message of 43 rows: 2 keys, 4 bits, 35 own masks, an idle
entry, the pad of the sample.
  `mkDt`: the data: the two keys and the four bits.
  `mkRd`: what the chain's reading keeps: the 41 places that are played. The pad and the idle entry
    are forgotten.
  `mkC`: the claim with which the lookup is started: every key is in the table, and the bits are
    multiplicities (the wide form `A.ValidMu`).

Main names: `Spec.ldLkp_toyMask` states:
  the four plain conditions on places (Cb/Ld/LdLkpMaskPlaces2.lean: `A.PlacesOK`) hold; so
  `A.MaskOK` holds (Cb/Ld/LdLkpMaskAsm2.lean);
  the conditions on numbers; "the vector is the multiplicities" is as the head asks (`MuOn`);
  the claim reads the data only; it reads no own mask; two tuples with different keys meet it (so it
  is not empty and does not fix the witness);
  the reading keeps data and own masks, and keeps neither the pad nor the idle entry;
  and so, for every kind of further oracles with at least one value, every tuple type and every
  reading of the entries: the chain is a link of a chain of masked blocks (`MJ.Link`,
  Cb/Ld/LdLkpMaskSp.lean); `A.chainA` and `A.baseA` have the item "masked messages" (`Honest.MM`,
  Ior/Masked.lean);
  over the toy's signature (one oracle message, with its sample), for every kind of further oracles
  with at least one value: the lookup with rows and mask form on the named entries only (`A.subN`)
  has the item, and its exact input relation gives the item's claim.
Also, for any data `A : LkAsm2 E` with `A.PlacesOK Dt`: the claim "keys in the table, bits are
multiplicities" reads the data only (`ldLkpMask_claim_reads`) and no own mask
(`ldLkpMask_claim_stab`): Cb/Ld/LdLkpMaskClaim.lean.

Limits: this file says nothing on real parameters.
It does not say that the masks are uniform and unseen when the lookup starts (the sending:
Cb/Ld/LdSendPscToy.lean has one for a single sumcheck).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskClaim
import Cb.Ld.LdLkpToy
import Cb.Ld.LdLkpAsm2Fmt
import Cb.Ld.LdLkpMaskLift2
import Cb.Ld.LdLkpMaskPlaces2Proofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

namespace LkpToy
open LdToy

/-- The data: the two keys, the four bits. -/
def mkDt : toyA.J → Prop := fun j => ∃ p : Bool ⊕ (Bool × Bool), j = .inl (.inl p)
/-- What the reading keeps: the places that are played. -/
def mkRd : toyA.J → Prop := fun j => ∃ p, j = plAt p
/-- The claim. -/
def mkC : toyA.St → (toyA.J → K) → Prop := toyA.lk.inP toyA.ValidMu

/-- The names of the own masks that are played, as the toy's names. -/
def mkCode : toyA.Nm → Mk
  | .s i => .inl (.inl i)
  | .t 0 _ i => .inl (.inr i)
  | .t (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .k 0 _ i => .inr (.inl (.inl i))
  | .k (l + 1) h _ => absurd h (Nat.not_succ_le_zero l)
  | .f 0 _ i => .inr (.inl (.inr i))
  | .f (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .e i => .inr (.inr (.inl i))
  | .b i => .inr (.inr (.inr i))

def mkDecode : Mk → toyA.Nm
  | .inl (.inl i) => .s i
  | .inl (.inr i) => .t 0 Nat.one_pos i
  | .inr (.inl (.inl i)) => .k 0 (le_refl 0) i
  | .inr (.inl (.inr i)) => .f 0 Nat.one_pos i
  | .inr (.inr (.inl i)) => .e i
  | .inr (.inr (.inr i)) => .b i

theorem mkDecode_code : ∀ x, mkDecode (mkCode x) = x
  | .s _ => rfl
  | .t 0 _ _ => rfl
  | .t (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .k 0 _ _ => rfl
  | .k (l + 1) h _ => absurd h (Nat.not_succ_le_zero l)
  | .f 0 _ _ => rfl
  | .f (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .e _ => rfl
  | .b _ => rfl

theorem plN_eq : ∀ x, toyA.plN x = mAt (mkCode x)
  | .s (.inl _) => rfl
  | .s (.inr _) => rfl
  | .t 0 _ (.inl _) => rfl
  | .t 0 _ (.inr _) => rfl
  | .t (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .k 0 _ (.inl _) => rfl
  | .k 0 _ (.inr _) => rfl
  | .k (l + 1) h _ => absurd h (Nat.not_succ_le_zero l)
  | .f 0 _ (.inl _) => rfl
  | .f 0 _ (.inr _) => rfl
  | .f (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .e (.inl _) => rfl
  | .e (.inr _) => rfl
  | .b (.inl _) => rfl
  | .b (.inr _) => rfl

theorem mAt_inj : Function.Injective mAt := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inl_injective h))

theorem mkPlacesOK : toyA.PlacesOK mkDt where
  inj := fun x y h => by
    rw [plN_eq, plN_eq] at h
    have h1 := congrArg mkDecode (mAt_inj h)
    rwa [mkDecode_code, mkDecode_code] at h1
  out := fun i ⟨p, h⟩ => by
    rw [plN_eq] at h
    exact Sum.inr_ne_inl (Sum.inl_injective h)
  bits := fun _ _ => ⟨.inr _, rfl⟩
  keys := fun _ m m' hm => funext fun _ => hm _ ⟨.inl _, rfl⟩

theorem mkRd_keeps (j : toyA.J) (h : toyA.srAll mkDt j) : mkRd j := by
  rcases h with ⟨p, rfl⟩ | hw
  · exact ⟨.inl p, (plAt_eq (.inl p)).symm⟩
  · obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw K toyA j).1 hw
    exact ⟨.inr (mkCode i), (plN_eq i).trans (plAt_eq (.inr (mkCode i))).symm⟩

end LkpToy

namespace Spec
open LdToy LkpToy

def ldLkp_toyMask : Prop :=
  toyA.PlacesOK mkDt ∧ toyA.MaskOK mkDt ∧ toyA.H.lkb.Adm 101 ∧ toyA.H.MuOn toyA.ValidMu ∧
  (∀ st k k', (∀ j, mkDt j → k j = k' j) → mkC st k → mkC st k') ∧
  MjStab mkC toyA.swAll ∧
  (mkC () w57 ∧ mkC () w55 ∧ toyA.key () w57 1 ≠ toyA.key () w55 1) ∧
  ((∀ j, toyA.srAll mkDt j → mkRd j) ∧ ¬ mkRd (.inr ()) ∧ ¬ mkRd idle) ∧
  (∀ (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → toyA.J → K),
    (toyA.mjChain Ex M Wp Kc msg mkRd).Link (toyA.chainA Ex M Wp Kc msg).H
      (fun w => mjCut mkRd (msg w.1)) (fun w => mjCut mkRd (msg w.1))
      (toyA.srAll mkDt) toyA.swAll mkC ∧
    (toyA.chainA Ex M Wp Kc msg).H.MM
      (((toyA.mjChain Ex M Wp Kc msg mkRd).narrow mkC).data fun w => mjCut mkRd (msg w.1)) ∧
    (toyA.baseA Ex M Wp Kc msg).H.MM
      (((toyA.mjBase Ex M Wp Kc msg mkRd).narrow mkC).data fun w => mjCut mkRd (msg w.1))) ∧
  ∀ (E₀ : ExtSpec) [Nonempty E₀.Str] (Kc Wp : Type),
    (toyA.subN iN Sg E₀ Kc Wp toyMsg).H.MM
      (toyA.dmN iN Sg (toyA.mjChain E₀ Sg.Msg Wp Kc toyMsg mkRd) mkC fun w =>
        mjCut mkRd (toyMsg w.1)) ∧
    ∀ (R0 : Rels Kc Unit E₀ (Sg.Msg × Wp)) x y w,
      (Sg.over (cj R0 toyMsg id (toyA.lk.inP toyA.ValidMu) toyA.lk.inR)).rel x y w →
      (toyA.dmN iN Sg (toyA.mjChain E₀ Sg.Msg Wp Kc toyMsg mkRd) mkC fun w =>
          mjCut mkRd (toyMsg w.1)).Cl
        ((toyA.dmN iN Sg (toyA.mjChain E₀ Sg.Msg Wp Kc toyMsg mkRd) mkC fun w =>
          mjCut mkRd (toyMsg w.1)).pub x)
        ((toyA.dmN iN Sg (toyA.mjChain E₀ Sg.Msg Wp Kc toyMsg mkRd) mkC fun w =>
          mjCut mkRd (toyMsg w.1)).kc w)

end Spec

open LdToy LkpToy in
theorem ldLkp_toyMask : Spec.ldLkp_toyMask := by
  have hP := mkPlacesOK
  have hM := ldLkpPlaces2_ok K toyA mkDt hP
  have hMu := ldLkpAsm2_muValid K toyA (le_refl 2)
  have hs := ldLkpMask_claim_stab K toyA mkDt hP
  have hr := ldLkpMask_claim_reads K toyA mkDt hP
  have hL : ∀ (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → toyA.J → K),
      _ := fun Ex _ M Wp Kc msg =>
    ldLkpMaskAsm2_link K 101 toyA toyA.ValidMu Ex M Wp Kc msg mkDt mkRd mkC adm hMu hM
      mkRd_keeps (fun _ _ h => h) hs
  refine ⟨hP, hM, adm, hMu, hr, hs, ⟨in57, in55, by decide⟩,
    ⟨mkRd_keeps, fun ⟨p, h⟩ => (plAt_ne p).2 h.symm, fun ⟨p, h⟩ => (plAt_ne p).1 h.symm⟩,
    fun Ex _ M Wp Kc msg => ⟨hL Ex M Wp Kc msg, ?_⟩, fun E₀ _ Kc Wp => ⟨?_, ?_⟩⟩
  · exact ldLkpMaskAsm2_mm K 101 toyA toyA.ValidMu Ex M Wp Kc msg mkDt mkRd mkC adm hMu hM
      mkRd_keeps (fun _ _ h => h) hs
  · exact mjLift2_subN K toyA Nm iN Sg E₀ Kc Wp toyMsg _ _ _ _ mkC (hL E₀ Sg.Msg Wp Kc toyMsg)
  · exact fun R0 =>
        mjLift2_clN K toyA Nm iN toyA.ValidMu Sg E₀ Kc Wp R0 toyMsg _ _ mkC fun st w h =>
      hr st _ _ (fun j hj => (mjCut_of (toyMsg w.1) (mkRd_keeps j (Or.inl hj))).symm) h

end Cb
