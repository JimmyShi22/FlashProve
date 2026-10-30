-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSeed2.lean: THE TIE ON THE OOD SAMPLE AT THE SHARED CHAIN's READING, IN THE FORM THAT tie_of_sealReads ASKS. Johnson/RunOne/KeyFillSeed.lean's seals_seed₁ | tieS_fam one chain on: SealReads at (baseK cs l num at_ decT recOf orc₁).h₂ with the tie
«fun a ρ v => ∃ y₀, SeedIs cs s (stOf a) o₀ ρ y₀ ∧ v = fun _ => y₀». The shared chain's reading has TWO sources (Johnson/RunOne/KeyFillBase.lean's src₂), so there are two forms:
  seals_seed₂_hi     a member whose number is 3 or more (the shared chain's own messages): stOf a := a.2.st, the shared chain's own statement; o₀ is what orc₂ gives the number
  seals_seed₂_lo     a member whose number is below 3 (the messages handed on by the first chain): stOf a := a.1.2.d.st, the first chain's statement as handed on; o₀ is what orc₁ gives the number. THE THREE _lo FORMS HAVE NO USER THAT WE KNOW OF: they stand for src₂'s other arm; their premises are not shown met at the key file's members here
  tieS_fam₂_hi | _lo the sending kind's Sealed, at the reader symsW ∘ wordOf, gives hasSmp ∧ NoColl at the member's seat at B.h₂: by LPFD.tie_of_sealReads
  tieS_at₂_hi | _lo  the same with the member's shape and radius named (l.get i = (s, e)), so that no cast is wanted at the call: after LPFD.tieS_at (Johnson/Top/Fire/Code/Row10Seven.lean)
  orc₂_nums | orc₂_none   orc₂ gives 3 | 4 | 5 the numbers 0 | 2 | 3 · from 6 on it gives nothing: there the premise ho of the _hi forms cannot be met
EACH PROOF IS A CALL: Johnson/RunOne/KeyFillBase.lean's seals_h₂ at uniqK (that is sealsK_h₂), its tie rewritten by Johnson/RunOne/KeyFillChains.lean's seedIsS_iff₂_hi | _lo.
OBJECT: the tables' reading BaseSt.h₂; the sending kind's SeedIs | Sealed | Tie · USER: Johnson/RunOne/KeyFillSeed2At.lean (the _hi forms; meant beyond it: the premises tieS | tie4 | tie5 of Johnson/RunOne/KeyRows2225At.lean's keeps₂_send2_at | keeps₂_send5_at) · LETTERS: cs · l · num · at_ · decT · recOf · orc₁ · F · str.
NOT SAID: that any state of the shared chain holds the kind's row (SeedIs), or that Sealed holds anywhere: these are implications FROM Sealed · the ties at the call (the sending's codes, shape and radius are the member's; its reader of the words is this one) · the last chain's like. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs Sealed Tie)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

/-- What plan₂'s orc gives the tables' numbers 3 | 4 | 5: the shared chain's statement's messages 0 | 2 | 3. -/
theorem orc₂_nums : orc₂ 3 = some 0 ∧ orc₂ 4 = some 2 ∧ orc₂ 5 = some 3 := ⟨rfl, rfl, rfl⟩

/-- From 6 on it gives nothing. -/
theorem orc₂_none (k : ℕ) (hk : 6 ≤ k) : orc₂ k = none := by
  have h3 : (k == 3) = false := by rw [beq_eq_false_iff_ne]; omega
  have h4 : (k == 4) = false := by rw [beq_eq_false_iff_ne]; omega
  have h5 : (k == 5) = false := by rw [beq_eq_false_iff_ne]; omega
  simp [orc₂, h3, h4, h5]

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ) (at_ : Where)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  {XI Y' : Type} (F : FileDescription XI) (str : Y' → Strs)

/-- **SealReads AT B.h₂, AT THE SHARED CHAIN's OWN STATEMENT**, for a member whose number is 3 or more. -/
def seals_seed₂_hi (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hi : ¬ num i < 3) (o₀ : ℕ) (ho : orc₂ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) :
    SealReads F (baseK cs l num at_ decT recOf orc₁).h₂ str
      (fun y' => (portOmZ cs (l.get i).1 (l.get i).2).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (at_ (num i)).1 (at_ (num i)).2)))
      (portOmZ cs (l.get i).1 (l.get i).2).Z.val (fun a ρ v => ∃ y₀, SeedIs cs (l.get i).1 a.2.st o₀ ρ y₀ ∧ v = fun _ => y₀) (at_ (num i)).1 (at_ (num i)).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := fun a ρ v h => (seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).has a ρ v ((seedIsS_iff₂_hi cs l num orc₁ i hi a ρ v).2 ⟨o₀, ho, h⟩)
  inj := (seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).inj
  mem := fun a y' o z m ρ v hor hz h hM =>
    (seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).mem a y' o z m ρ v hor hz ((seedIsS_iff₂_hi cs l num orc₁ i hi a ρ v).2 ⟨o₀, ho, h⟩) hM

/-- **SealReads AT B.h₂, AT THE FIRST CHAIN's STATEMENT AS HANDED ON**, for a member whose number is below 3. -/
def seals_seed₂_lo (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hi : num i < 3) (o₀ : ℕ) (ho : orc₁ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1) :
    SealReads F (baseK cs l num at_ decT recOf orc₁).h₂ str
      (fun y' => (portOmZ cs (l.get i).1 (l.get i).2).InList (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (at_ (num i)).1 (at_ (num i)).2)))
      (portOmZ cs (l.get i).1 (l.get i).2).Z.val (fun a ρ v => ∃ y₀, SeedIs cs (l.get i).1 a.1.2.d.st o₀ ρ y₀ ∧ v = fun _ => y₀) (at_ (num i)).1 (at_ (num i)).2 where
  toU := toU cs (l.get i).1 (l.get i).2
  has := fun a ρ v h => (seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).has a ρ v ((seedIsS_iff₂_lo cs l num orc₁ i hi a ρ v).2 ⟨o₀, ho, h⟩)
  inj := (seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).inj
  mem := fun a y' o z m ρ v hor hz h hM =>
    (seals_h₂ cs l num at_ (rowIsK cs l) decT recOf orc₁ F str hinj hap i hlog hm (uniqK cs l i hT)).mem a y' o z m ρ v hor hz ((seedIsS_iff₂_lo cs l num orc₁ i hi a ρ v).2 ⟨o₀, ho, h⟩) hM

/-- **THE TIE AT B.h₂, a number from 3 on**: the sending kind's Sealed at the shared chain's own statement, at the reader symsW ∘ wordOf, gives the tables' two facts at the seat. -/
theorem tieS_fam₂_hi (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hi : ¬ num i < 3) (o₀ : ℕ) (ho : orc₂ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (a : P₂ × St₂) (y : Y')
    (h : Sealed cs (l.get i).1 (l.get i).2 (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y) (at_ (num i)).1 (at_ (num i)).2)) a.2.st o₀) :
    hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧ NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (str y) :=
  LPFD.tie_of_sealReads F (baseK cs l num at_ decT recOf orc₁).h₂ str cs (l.get i).1 (l.get i).2
    (fun y' => symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (at_ (num i)).1 (at_ (num i)).2)) (fun a => a.2.st) (fun _ => o₀) (at_ (num i)).1 (at_ (num i)).2
    (seals_seed₂_hi cs l num at_ decT recOf orc₁ F str hinj hap i hi o₀ ho hT hlog hm) a y h

/-- **THE TIE AT B.h₂, a number below 3**: Sealed at the first chain's statement as handed on. -/
theorem tieS_fam₂_lo (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hi : num i < 3) (o₀ : ℕ) (ho : orc₁ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (a : P₂ × St₂) (y : Y')
    (h : Sealed cs (l.get i).1 (l.get i).2 (symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y) (at_ (num i)).1 (at_ (num i)).2)) a.1.2.d.st o₀) :
    hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧ NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (str y) :=
  LPFD.tie_of_sealReads F (baseK cs l num at_ decT recOf orc₁).h₂ str cs (l.get i).1 (l.get i).2
    (fun y' => symsW cs (l.get i).1 (l.get i).2 (wordOf F (str y') (at_ (num i)).1 (at_ (num i)).2)) (fun a => a.1.2.d.st) (fun _ => o₀) (at_ (num i)).1 (at_ (num i)).2
    (seals_seed₂_lo cs l num at_ decT recOf orc₁ F str hinj hap i hi o₀ ho hT hlog hm) a y h

/-- tieS_fam₂_hi, the member's shape and radius named. -/
theorem tieS_at₂_hi (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hi : ¬ num i < 3) (o₀ : ℕ) (ho : orc₂ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (s : OnBytes.OracleShape) (e : ℕ) (hl : l.get i = (s, e)) (a : P₂ × St₂) (y : Y')
    (h : Sealed cs s e (symsW cs s e (wordOf F (str y) (at_ (num i)).1 (at_ (num i)).2)) a.2.st o₀) :
    hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧ NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (str y) := by
  have H := tieS_fam₂_hi cs l num at_ decT recOf orc₁ F str hinj hap i hi o₀ ho hT hlog hm a y
  rw [hl] at H
  exact H h

/-- tieS_fam₂_lo, the member's shape and radius named. -/
theorem tieS_at₂_lo (hinj : Function.Injective (seatAt l num at_)) (hap : ShapesApart l) (i : Fin l.length) (hi : num i < 3) (o₀ : ℕ) (ho : orc₁ (num i) = some o₀) (hT : Tie cs (l.get i).1)
    (hlog : ∀ o, F.oracleAt (seatAt l num at_ i).1 = some o → o.logLength = aOf cs (l.get i).1) (hm : (l.get i).1.mainRows = 0 ∨ (cMain cs (l.get i).1).a = aOf cs (l.get i).1)
    (s : OnBytes.OracleShape) (e : ℕ) (hl : l.get i = (s, e)) (a : P₂ × St₂) (y : Y')
    (h : Sealed cs s e (symsW cs s e (wordOf F (str y) (at_ (num i)).1 (at_ (num i)).2)) a.1.2.d.st o₀) :
    hasSmp (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a = true ∧ NoColl F (baseK cs l num at_ decT recOf orc₁).h₂ (at_ (num i)).1 (at_ (num i)).2 a (str y) := by
  have H := tieS_fam₂_lo cs l num at_ decT recOf orc₁ F str hinj hap i hi o₀ ho hT hlog hm a y
  rw [hl] at H
  exact H h

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.orc₂_nums
#print axioms Johnson.RunOne.KeyRows23.orc₂_none
#print axioms Johnson.RunOne.KeyRows23.seals_seed₂_hi
#print axioms Johnson.RunOne.KeyRows23.seals_seed₂_lo
#print axioms Johnson.RunOne.KeyRows23.tieS_fam₂_hi
#print axioms Johnson.RunOne.KeyRows23.tieS_fam₂_lo
#print axioms Johnson.RunOne.KeyRows23.tieS_at₂_hi
#print axioms Johnson.RunOne.KeyRows23.tieS_at₂_lo
