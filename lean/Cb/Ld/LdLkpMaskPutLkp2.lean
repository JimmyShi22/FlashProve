-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPutLkp2.lean: under `A.MaskOK Dt` (Cb/Ld/LdLkpMaskAsm2.lean), the own masks of the
assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean) are "overwrite the entries at named places": the
places of all its sumchecks.
This file gives, for the whole lookup argument, the places among the entries that, under the
conditions below, `put` overwrites (`MJ.Pl`, Cb/Ld/LdLkpMaskPut.lean).

Definitions, statements (in `Cb.Spec`) and proofs.
The statement of Cb/Ld/LdLkpMaskPutLkp.lean (`ldLkpPl_asm`), word for word, at the data and the `MJ`
records of Cb/Ld/LdLkpMaskAsm2.lean. The parts that are generic there (tie, tree, head, keys' side)
are used as they are. Not there: the sumcheck where no map is revealed (`PscPar.core`,
Cb/Ld/LdPsc.lean).

Main names:
  `Y.plC Ex Rd`, `Spec.mjPl_core`: the places of the block of Cb/Ld/LdLkpMaskCore.lean: `Y.wAt`, if
    these are different.
  `A.plForest`, `A.plChain`, `A.plBase`: the data (a type of places' names, the places, "a mask
    value is a value for each place"), put together as the records are.
  `Spec.ldLkpPl2_forest`: for l ≤ d and under `A.MaskOK Dt`: the places of the keys' side and of the
    levels below l.
  `Spec.ldLkpPl2_asm`: `A.MaskOK Dt` ⇒ `(A.plChain ..).OK`, and its places are `A.swAll`; the same
    for `A.plBase`.

Limits: this file says nothing on what is read. It does not say that these entries are uniform and
unseen when the lookup starts.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskPutLkpProofs
import Cb.Ld.LdLkpMaskAsm2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

/-- The places of a sumcheck where no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean). -/
def PscPar.plC
    {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec) (Rd : Y.J → Prop) :
    (Y.mjC Ex Rd).Pl :=
  ⟨PIdx Y.fmt, Y.wAt, Equiv.refl _⟩

end Cb

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type)
  (msg : M → A.J → E) (Rd : A.J → Prop)

def plForest : (l : ℕ) → (A.mjForest Ex M Wp Kc msg Rd l).Pl
  | 0 =>
    (plSegK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg Rd).post
      (fun x => some (A.enterT x)) (ExtMap.id Ex) A.enterT
  | l + 1 => (plForest l).seq (A.D.plLev Ex Rd l)

/-- The places of the own masks of the whole lookup: in a row: head, point, keys' side and forest,
the closing, the bit test. -/
def plChain : (A.mjChain Ex M Wp Kc msg Rd).Pl :=
  ((((A.H.plHead Ex M Wp Kc msg Rd).seq
          (MJ.Pl.silent A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold)).seq
        (A.plForest Ex M Wp Kc msg Rd A.d)).seq
      (A.En.par.plC Ex Rd)).seq
    ((MJ.Pl.silent A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.AllHold).seq
      (A.Bt.zc.next.plJ Ex (Equiv.refl _) Rd))

def plBase : (A.mjBase Ex M Wp Kc msg Rd).Pl :=
  (A.plChain Ex M Wp Kc msg Rd).post (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd

end LkAsm2
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def mjPl_core : Prop :=
  ∀ (Y : PscPar E) (Ex : ExtSpec) (Rd : Y.J → Prop),
    Function.Injective Y.wAt → (Y.plC Ex Rd).OK ∧ ∀ j, (Y.plC Ex Rd).At j ↔ ∃ i, j = Y.wAt i

def ldLkpPl2_forest : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd Dt : A.J → Prop) (l : ℕ),
    l ≤ A.d → A.MaskOK Dt →
    (A.plForest Ex M Wp Kc msg Rd l).OK ∧
    ∀ j, (A.plForest Ex M Wp Kc msg Rd l).At j ↔ A.swK j ∨ ∃ l' < l, A.D.ownAt l' j

/-- The whole lookup. -/
def ldLkpPl2_asm : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) (Rd Dt : A.J → Prop),
    A.MaskOK Dt →
    ((A.plChain Ex M Wp Kc msg Rd).OK ∧ ∀ j, (A.plChain Ex M Wp Kc msg Rd).At j ↔ A.swAll j) ∧
    ((A.plBase Ex M Wp Kc msg Rd).OK ∧ ∀ j, (A.plBase Ex M Wp Kc msg Rd).At j ↔ A.swAll j)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem mjPl_core : Spec.mjPl_core E := fun _ _ _ hi =>
  ⟨⟨hi, fun _ _ => rfl⟩, fun _ => ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩⟩

theorem ldLkpPl2_forest : Spec.ldLkpPl2_forest E := by
  intro A Ex M Wp Kc msg Rd Dt l
  induction l with
  | zero =>
      intro _ h
      obtain ⟨k1, k2⟩ :=
        ldLkpPl_segK E A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg Rd Dt A.swTie h.keyT
      obtain ⟨p1, p2⟩ := mjPl_post E A.J _ _ _ _ _ _ _ _
        (plSegK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg Rd) (fun x => some (A.enterT x))
        (ExtMap.id Ex) A.enterT k1
      exact ⟨p1,
        fun j =>
          (p2 j).trans
            ((k2 j).trans
              ⟨Or.inl, fun hh => hh.elim id fun ⟨_, hl, _⟩ => absurd hl (Nat.not_lt_zero _)⟩)⟩
  | succ l ih =>
      intro hld h
      obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le hld) h
      have hl := h.lev l hld
      obtain ⟨h3, h4⟩ := ldLkpPl_lev E A.D Ex Rd l (hl.inj l (le_refl _))
      refine ⟨mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ (A.plForest Ex M Wp Kc msg Rd l)
          (A.D.plLev Ex Rd l) h1 h3 fun j hj hj' => ?_,
        fun j => ?_⟩
      · rcases (h2 j).1 hj with hk | ⟨l', hl', hj⟩
        · exact h.kT j hk (Or.inl ⟨l, hld, (h4 j).1 hj'⟩)
        · exact hl.disj l' l hl' (le_refl _) j hj ((h4 j).1 hj')
      · refine (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _ (A.plForest Ex M Wp Kc msg Rd l)
          (A.D.plLev Ex Rd l) j).trans ?_
        constructor
        · rintro (hj | hj)
          · exact ((h2 j).1 hj).elim Or.inl fun ⟨l', hl', hj⟩ =>
              Or.inr ⟨l', Nat.lt_succ_of_lt hl', hj⟩
          · exact Or.inr ⟨l, Nat.lt_succ_self l, (h4 j).1 hj⟩
        · rintro (hk | ⟨l', hl', hj⟩)
          · exact Or.inl ((h2 j).2 (Or.inl hk))
          · rcases Nat.lt_or_ge l' l with h5 | h5
            · exact Or.inl ((h2 j).2 (Or.inr ⟨l', h5, hj⟩))
            · obtain rfl := Nat.le_antisymm (Nat.lt_succ_iff.1 hl') h5
              exact Or.inr ((h4 j).2 hj)

theorem ldLkpPl2_asm : Spec.ldLkpPl2_asm E := by
  intro A Ex M Wp Kc msg Rd Dt h
  obtain ⟨t1, t2⟩ := ldLkpPl_head E A.H Ex M Wp Kc msg Rd Dt h.tie
  obtain ⟨r1, r2⟩ := mjPl_silent E A.J _ _ A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold
  obtain ⟨f1, f2⟩ := ldLkpPl2_forest E A Ex M Wp Kc msg Rd Dt A.d (le_refl _) h
  obtain ⟨e1, e2⟩ := mjPl_core E A.En.par Ex Rd h.injE
  obtain ⟨s1, s2⟩ :=
    mjPl_silent E A.J _ _ A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.AllHold
  obtain ⟨b1, b2⟩ := mjPl_our E A.Bt.zc.next Ex A.J (Equiv.refl _) Rd h.injB
  have t3 : ∀ j, (A.H.plHead Ex M Wp Kc msg Rd).At j ↔ A.swTie j := t2
  have f3 : ∀ j, (A.plForest Ex M Wp Kc msg Rd A.d).At j ↔ A.swK j ∨ A.ownF j := f2
  have e3 : ∀ j, (A.En.par.plC Ex Rd).At j ↔ A.ownE j := e2
  have b3 : ∀ j, (A.Bt.zc.next.plJ Ex (Equiv.refl _) Rd).At j ↔ A.ownB j := b2
  -- head, point
  have o1 := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ (A.H.plHead Ex M Wp Kc msg Rd)
    (MJ.Pl.silent A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold) t1 r1 fun j _ => r2 j
  have a1 : ∀ j,
      ((A.H.plHead Ex M Wp Kc msg Rd).seq
        (MJ.Pl.silent A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold)).At j ↔
      A.swTie j := fun j =>
    (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _ (A.H.plHead Ex M Wp Kc msg Rd)
        (MJ.Pl.silent A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold) j).trans
      ⟨fun hj => hj.elim (t3 j).1 fun hj => absurd hj (r2 j), fun hj => Or.inl ((t3 j).2 hj)⟩
  -- keys' side, forest
  have hTK : ∀ j, A.swTie j → ¬ (A.swK j ∨ A.ownF j) := by
    rintro j hj (⟨l, hl, hk⟩ | ⟨l, hl, hf⟩)
    · exact h.keyT.io l hl j hj hk
    · exact (h.lev l hl).io l (le_refl _) j hj hf
  have o2 := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ _ (A.plForest Ex M Wp Kc msg Rd A.d) o1 f1
    fun j hj hj' => hTK j ((a1 j).1 hj) ((f3 j).1 hj')
  have a2 : ∀ j,
      (((A.H.plHead Ex M Wp Kc msg Rd).seq
          (MJ.Pl.silent A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold)).seq
        (A.plForest Ex M Wp Kc msg Rd A.d)).At j ↔
      A.swTie j ∨ A.swK j ∨ A.ownF j := fun j =>
    (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _ _ (A.plForest Ex M Wp Kc msg Rd A.d) j).trans
      (or_congr (a1 j) (f3 j))
  -- the closing
  have o3 := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ _ (A.En.par.plC Ex Rd) o2 e1 fun j hj hj' =>
    ((a2 j).1 hj).elim (fun a => h.inE j a ((e3 j).1 hj')) fun a =>
      a.elim (fun b => h.kT j b (Or.inr (Or.inl ((e3 j).1 hj')))) fun b => h.fE j b ((e3 j).1 hj')
  have a3 : ∀ j,
      ((((A.H.plHead Ex M Wp Kc msg Rd).seq
            (MJ.Pl.silent A.R.toIn.ev.D A.R.toIn.nxX Ex A.R.toIn.AllHold)).seq
          (A.plForest Ex M Wp Kc msg Rd A.d)).seq
        (A.En.par.plC Ex Rd)).At j ↔
      (A.swTie j ∨ A.swK j ∨ A.ownF j) ∨ A.ownE j :=
    fun j =>
      (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _ _ (A.En.par.plC Ex Rd) j).trans
        (or_congr (a2 j) (e3 j))
  -- the bit test
  have oB := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _
    (MJ.Pl.silent A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.AllHold)
    (A.Bt.zc.next.plJ Ex (Equiv.refl _) Rd) s1 b1 fun j hj => absurd hj (s2 j)
  have aB : ∀ j,
      ((MJ.Pl.silent A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.AllHold).seq
        (A.Bt.zc.next.plJ Ex (Equiv.refl _) Rd)).At j ↔
      A.ownB j := fun j =>
    (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _
        (MJ.Pl.silent A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.AllHold)
        (A.Bt.zc.next.plJ Ex (Equiv.refl _) Rd) j).trans
      ⟨fun hj => hj.elim (fun hj => absurd hj (s2 j)) (b3 j).1, fun hj => Or.inr ((b3 j).2 hj)⟩
  have o4 : (A.plChain Ex M Wp Kc msg
      Rd).OK := mjPl_seq E A.J _ _ _ _ _ _ _ _ _ _ _ _ o3 oB fun j hj hj' =>
    ((a3 j).1 hj).elim
      (fun a =>
        a.elim (fun b => h.inB j b ((aB j).1 hj')) fun b =>
          b.elim (fun c => h.kT j c (Or.inr (Or.inr ((aB j).1 hj')))) fun c =>
            h.fB j c ((aB j).1 hj'))
      fun a => h.eB j a ((aB j).1 hj')
  have a4 : ∀ j, (A.plChain Ex M Wp Kc msg Rd).At j ↔ A.swAll j := fun j => by
    refine (mjPl_at_seq E A.J _ _ _ _ _ _ _ _ _ _ _
        ((MJ.Pl.silent A.Bt.zc.toIn.ev.D A.Bt.zc.toIn.nxX Ex A.Bt.zc.toIn.AllHold).seq
          (A.Bt.zc.next.plJ Ex (Equiv.refl _) Rd)) j).trans
      ((or_congr (a3 j) (aB j)).trans ?_)
    constructor
    · rintro (((a | a | a) | a) | a)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inl a))
      · exact Or.inr (Or.inr (Or.inr (Or.inl a)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr a)))
    · rintro (a | a | a | a | a)
      · exact Or.inl (Or.inl (Or.inl a))
      · exact Or.inl (Or.inl (Or.inr (Or.inl a)))
      · exact Or.inl (Or.inl (Or.inr (Or.inr a)))
      · exact Or.inl (Or.inr a)
      · exact Or.inr a
  obtain ⟨p1, p2⟩ := mjPl_post E A.J _ _ _ _ _ _ _ _ (A.plChain Ex M Wp Kc msg Rd)
    (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd o4
  exact ⟨⟨o4, a4⟩, p1, fun j => (p2 j).trans (a4 j)⟩

end
end Cb
