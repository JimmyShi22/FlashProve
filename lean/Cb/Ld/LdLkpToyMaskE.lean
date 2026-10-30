-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpToyMaskE.lean: the guard for the item "masked messages" of the assembled lookup, over any
finite field of characteristic above 6: at the toy lookup all its hypotheses are met together.
This file is an example: at the toy lookup of Cb/Ld/LdLkpToyE.lean every hypothesis of
`Spec.ldLkpMaskAsm2_link`, `Spec.ldLkpMaskAsm2_mm` (Cb/Ld/LdLkpMaskAsm2.lean), `Spec.mjLift2_subN`
and `Spec.mjLift2_clN` (Cb/Ld/LdLkpMaskLift2.lean) is proved, but for `[CharP E p]` and
`[Nonempty Ex.Str]`, which stay in the statements below; `Adm p` from `6 < p`.

Statements (`Cb.Spec.ldLkp_toyMaskAt`, `Cb.Spec.ldLkp_toyMaskE`) and proof. A guard against empty
theorems; no parameter of a protocol.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Cb/Ld/LdLkpToyMask.lean is this guard over the field with 101 elements. Here the field E is a
parameter, as in Cb/Ld/LdLkpToyE.lean (`toyA E`, below A: two keys in the table (5, 7); six
sumchecks; 43 entries: 2 keys, 4 bits, 35 own masks, an idle entry, one that nothing names). The
oracle messages are a parameter too: any signature S over E, any reading msg of the entries.
  `mkDt E`: the data: the two keys and the four bits.
  `mkRd E`: what the chain's reading keeps: the 41 places that are played. The idle entry and the
    entry that nothing names are forgotten.
  `mkC E`: the claim with which the lookup is started: every key is in the table, and the bits are
    multiplicities (`A.ValidMu`).

Main names: `Spec.ldLkp_toyMaskAt E p` states, in the order of its ten conjuncts:
  (1) the four plain conditions on places (`A.PlacesOK`); (2) so `A.MaskOK`; (3) the conditions on
  numbers at p; (4) `MuOn`;
  (5) the claim reads the data only; (6) it reads no own mask; (7) two tuples with different keys
  meet it;
  (8) the reading keeps data and own masks, and neither of the two other entries;
  (9) and so, for every kind of further oracles with at least one value, every tuple type and every
  reading: the chain is a link of a chain of masked blocks (`MJ.Link`, Cb/Ld/LdLkpMaskSp.lean);
  `A.chainA` and `A.baseA` have the item "masked messages" (`Honest.MM`, Ior/Masked.lean);
  (10) over every signature S over E, every reading msg, for every kind of further oracles with at
  least one value: the lookup with rows and mask form on the named entries only (`A.subN`) has the
  item, and its exact input relation gives the item's claim.
`Spec.ldLkp_toyMaskE E`: for every p with `CharP E p` and 6 < p.
`Spec.ldLkp_toyMaskAt`: A condition with parameters, used inside other statements; it is not itself
a claim.

Limits: this file says nothing on real parameters.
It does not say that the masks are uniform and unseen when the lookup starts.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpToyE
import Cb.Ld.LdLkpToyMask

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

namespace LkpToyE
variable (E : Type) [Field E] [Fintype E]

/-- The data: the two keys, the four bits. -/
def mkDt : (toyA E).J → Prop := fun j => ∃ p : Bool ⊕ (Bool × Bool), j = .inl (.inl p)
/-- What the reading keeps: the places that are played. -/
def mkRd : (toyA E).J → Prop := fun j => ∃ p, j = plAt E p
/-- The claim. -/
def mkC : (toyA E).St → ((toyA E).J → E) → Prop := (toyA E).lk.inP (toyA E).ValidMu

/-- The names of the own masks that are played, as the toy's names. -/
def mkCode : (toyA E).Nm → Mk E
  | .s i => .inl (.inl i)
  | .t 0 _ i => .inl (.inr i)
  | .t (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .k 0 _ i => .inr (.inl (.inl i))
  | .k (l + 1) h _ => absurd h (Nat.not_succ_le_zero l)
  | .f 0 _ i => .inr (.inl (.inr i))
  | .f (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .e i => .inr (.inr (.inl i))
  | .b i => .inr (.inr (.inr i))

def mkDecode : Mk E → (toyA E).Nm
  | .inl (.inl i) => .s i
  | .inl (.inr i) => .t 0 Nat.one_pos i
  | .inr (.inl (.inl i)) => .k 0 (le_refl 0) i
  | .inr (.inl (.inr i)) => .f 0 Nat.one_pos i
  | .inr (.inr (.inl i)) => .e i
  | .inr (.inr (.inr i)) => .b i

theorem mkDecode_code : ∀ x, mkDecode E (mkCode E x) = x
  | .s _ => rfl
  | .t 0 _ _ => rfl
  | .t (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .k 0 _ _ => rfl
  | .k (l + 1) h _ => absurd h (Nat.not_succ_le_zero l)
  | .f 0 _ _ => rfl
  | .f (l + 1) h _ => absurd h (Nat.not_lt.2 (Nat.succ_le_succ (Nat.zero_le l)))
  | .e _ => rfl
  | .b _ => rfl

theorem plN_eq : ∀ x, (toyA E).plN x = mAt (mkCode E x)
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

theorem mAt_inj : Function.Injective (mAt (E := E)) := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inl_injective h))

theorem mkPlacesOK : (toyA E).PlacesOK (mkDt E) where
  inj := fun x y h => by
    rw [plN_eq, plN_eq] at h
    have h1 := congrArg (mkDecode E) (mAt_inj E h)
    rwa [mkDecode_code, mkDecode_code] at h1
  out := fun i ⟨p, h⟩ => by
    rw [plN_eq] at h
    exact Sum.inr_ne_inl (Sum.inl_injective h)
  bits := fun _ _ => ⟨.inr _, rfl⟩
  keys := fun _ m m' hm => funext fun _ => hm _ ⟨.inl _, rfl⟩

theorem mkRd_keeps (j : (toyA E).J) (h : (toyA E).srAll (mkDt E) j) : mkRd E j := by
  rcases h with ⟨p, rfl⟩ | hw
  · exact ⟨.inl p, (plAt_eq E (.inl p)).symm⟩
  · obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E (toyA E) j).1 hw
    exact ⟨.inr (mkCode E i), (plN_eq E i).trans (plAt_eq E (.inr (mkCode E i))).symm⟩

end LkpToyE

namespace Spec
open LkpToyE

/-- A condition with parameters, which other statements and theorems use; it is not itself a
claim. -/
def ldLkp_toyMaskAt (E : Type) [Field E] [Fintype E] (p : ℕ) : Prop :=
  (toyA E).PlacesOK (mkDt E) ∧ (toyA E).MaskOK (mkDt E) ∧
  (toyA E).H.lkb.Adm p ∧ (toyA E).H.MuOn (toyA E).ValidMu ∧
  (∀ st k k', (∀ j, mkDt E j → k j = k' j) → mkC E st k → mkC E st k') ∧
  MjStab (mkC E) (toyA E).swAll ∧
  (mkC E () (w57 E) ∧ mkC E () (w55 E) ∧ (toyA E).key () (w57 E) 1 ≠ (toyA E).key () (w55 E) 1) ∧
  ((∀ j, (toyA E).srAll (mkDt E) j → mkRd E j) ∧ ¬ mkRd E (.inr ()) ∧ ¬ mkRd E idle) ∧
  (∀ (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → (toyA E).J → E),
    ((toyA E).mjChain Ex M Wp Kc msg (mkRd E)).Link ((toyA E).chainA Ex M Wp Kc msg).H
      (fun w => mjCut (mkRd E) (msg w.1)) (fun w => mjCut (mkRd E) (msg w.1))
      ((toyA E).srAll (mkDt E)) (toyA E).swAll (mkC E) ∧
    ((toyA E).chainA Ex M Wp Kc msg).H.MM
      ((((toyA E).mjChain Ex M Wp Kc msg (mkRd E)).narrow (mkC E)).data fun w =>
        mjCut (mkRd E) (msg w.1)) ∧
    ((toyA E).baseA Ex M Wp Kc msg).H.MM
      ((((toyA E).mjBase Ex M Wp Kc msg (mkRd E)).narrow (mkC E)).data fun w =>
        mjCut (mkRd E) (msg w.1))) ∧
  ∀ (S : Sig E) (E₀ : ExtSpec) [Nonempty E₀.Str] (Kc Wp : Type) (msg : S.Msg → (toyA E).J → E),
    ((toyA E).subN (iN E) S E₀ Kc Wp msg).H.MM
      ((toyA E).dmN (iN E) S ((toyA E).mjChain E₀ S.Msg Wp Kc msg (mkRd E))
        (mkC E) fun w => mjCut (mkRd E) (msg w.1)) ∧
    ∀ (R0 : Rels Kc Unit E₀ (S.Msg × Wp)) x y w,
      (S.over (cj R0 msg id ((toyA E).lk.inP (toyA E).ValidMu) (toyA E).lk.inR)).rel x y w →
      ((toyA E).dmN (iN E) S ((toyA E).mjChain E₀ S.Msg Wp Kc msg (mkRd E))
          (mkC E) fun w => mjCut (mkRd E) (msg w.1)).Cl
        (((toyA E).dmN (iN E) S ((toyA E).mjChain E₀ S.Msg Wp Kc msg (mkRd E)) (mkC E)
          fun w => mjCut (mkRd E) (msg w.1)).pub x)
        (((toyA E).dmN (iN E) S ((toyA E).mjChain E₀ S.Msg Wp Kc msg (mkRd E)) (mkC E)
          fun w => mjCut (mkRd E) (msg w.1)).kc w)

def ldLkp_toyMaskE (E : Type) [Field E] [Fintype E] : Prop :=
  ∀ (p : ℕ) [CharP E p], 6 < p → ldLkp_toyMaskAt E p

end Spec

open LkpToyE in
theorem ldLkp_toyMaskE (E : Type) [Field E] [Fintype E] : Spec.ldLkp_toyMaskE E := by
  intro p _ hp
  have hP := mkPlacesOK E
  have hM := ldLkpPlaces2_ok E (toyA E) (mkDt E) hP
  have hMu := ldLkpAsm2_muValid E (toyA E) (le_refl 2)
  have hs := ldLkpMask_claim_stab E (toyA E) (mkDt E) hP
  have hr := ldLkpMask_claim_reads E (toyA E) (mkDt E) hP
  have hL : ∀ (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → (toyA E).J → E),
      _ := fun Ex _ M Wp Kc msg =>
    ldLkpMaskAsm2_link E p (toyA E) (toyA E).ValidMu Ex M Wp Kc msg (mkDt E) (mkRd E) (mkC E)
      (adm E p hp) hMu hM (mkRd_keeps E) (fun _ _ h => h) hs
  refine ⟨hP, hM, adm E p hp, hMu, hr, hs, ⟨in57 E, in55 E, ne75 E p hp⟩,
    ⟨mkRd_keeps E, fun ⟨x, h⟩ => (plAt_ne E x).2 h.symm, fun ⟨x, h⟩ => (plAt_ne E x).1 h.symm⟩,
    fun Ex _ M Wp Kc msg => ⟨hL Ex M Wp Kc msg, ?_⟩, fun S E₀ _ Kc Wp msg => ⟨?_, ?_⟩⟩
  · exact ldLkpMaskAsm2_mm E p (toyA E) (toyA E).ValidMu Ex M Wp Kc msg (mkDt E) (mkRd E) (mkC E)
      (adm E p hp) hMu hM (mkRd_keeps E) (fun _ _ h => h) hs
  · exact mjLift2_subN E (toyA E) (Nm E) (iN E) S E₀ Kc Wp msg _ _ _ _
      (mkC E) (hL E₀ S.Msg Wp Kc msg)
  · exact fun R0 =>
        mjLift2_clN E (toyA E) (Nm E) (iN E) (toyA E).ValidMu
            S E₀ Kc Wp R0 msg _ _ (mkC E) fun st w h =>
      hr st _ _ (fun j hj => (mjCut_of (msg w.1) (mkRd_keeps E j (Or.inl hj))).symm) h

end Cb
