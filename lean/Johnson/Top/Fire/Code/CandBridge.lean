-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/CandBridge.lean: A RIDER TO CandCanBeLaid.lean: THE BRIDGE
  BETWEEN THE TWO
  READERS OF THE WORD, which that file leaves open.

  wordAt_eq_symsW   the reader of a member's word (Sound.wordAt, Johnson/Desc/Sound/MsgSig.lean)
                    IS symsW at the word off the strings (wordOf): one body, by its cases;
                    the two types are one by unfolding (Lean takes the ascription;
                    K1.sig_om (Johnson/Desc/K1/Law/Caller.lean) says it by rfl: not imported here)
  wordsOf_eq_symsW  the same of Sound.wordsOf … y i
  candAt_iff        CandAt (Johnson/Desc/Sound/WordsLaw.lean) UNFOLDS to: the record's
                    sample is some σ, and u is the library's Ood.Cand at the list of
                    symsW ∘ wordOf at σ: LaysReads' own premise
  sixS              the six as one `Sending` (Johnson/Desc/Sound/World.lean): l := six, the seats
                    the tables' own
  cand_laid_of_candAt₁ | ₂ | ₃   FROM CandAt TO Member AT baseK: cand_laid_j with hc paid
WHAT STILL PARTS, A NAMED PREMISE (hsm): THE SAMPLE: CandAt reads it off THE LETTER smp;
  the filling off the record (seedIsS: the sending kind's own tie).
  hsm SAYS: «a sample σ that smp holds at the six's member i has the answers σ.2 of
  SOME seed ρ that the record spells, with Z.val σ.1 = Z.val ρ»: a smp whose seed is a CHOSEN one
  (K1.smpAt) does not give the record's very seed; the library's Cand sees the seed through Z.val
  alone.
OBJECT: wordAt | CandAt against symsW (Johnson/Desc/Key/KeyFill.lean) and the filling · USER: the
  K12 rows behind tuple_core · LETTERS: G cs l seat · smp · CandCanBeLaid's.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.CandCanBeLaid
import Johnson.Desc.Sound.WordsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace LPFD.CandLaid
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice
open Johnson.Top.H (csKey)
open Johnson.RunOne
open Johnson.RunOne.KeyRows23

/-- **The two readers of a member's word are one.** -/
theorem wordAt_eq_symsW {XI : Type} (G : FileDescription XI) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (y : Strs)
    (i : Fin l.length) :
    (Sound.wordAt G cs l seat y i : (OmAt cs l i).Str) =
      symsW cs (l.get i).1 (l.get i).2 (wordOf G y (seat i).1 (seat i).2) := by
  funext p
  cases p <;> rfl

theorem wordsOf_eq_symsW {XI : Type} (G : FileDescription XI) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (y : Strs)
    (i : Fin l.length) :
    (Sound.wordsOf G cs l seat y i : (OmAt cs l i).Str) =
      symsW cs (l.get i).1 (l.get i).2 (wordOf G y (seat i).1 (seat i).2) :=
  wordAt_eq_symsW G cs l seat y i

/-- **CandAt, unfolded to LaysReads' premise.** -/
theorem candAt_iff {XI A : Type} (cs : OnBytes.Codes) (G : FileDescription XI)
    (smp : A → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (x : Sound.Mem) (a : A) (y : Strs) (m : (OmAt cs x.1.l x.2).Msg) :
    Sound.CandAt cs G smp x a y m ↔
      ∃ σ : (OmAt cs x.1.l x.2).Smp, smp a x.1 x.2 = some σ ∧
        Cb.Ood.Cand
          ((OmAt cs x.1.l x.2).InList (symsW cs (x.1.l.get x.2).1 (x.1.l.get x.2).2
            (wordOf G y (x.1.seat x.2).1 (x.1.seat x.2).2)))
          (OmAt cs x.1.l x.2).Z.val σ.1 σ.2 m := by
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, ?_⟩
    rw [← wordsOf_eq_symsW G cs x.1.l x.1.seat y x.2]
    exact h
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ, hσ, ?_⟩
    rw [← wordsOf_eq_symsW G cs x.1.l x.1.seat y x.2] at h
    exact h

/-- The six as one `Sending` (Johnson/Desc/Sound/World.lean). -/
def sixS : Sound.Sending := ⟨six, seatAt six numSix atSix⟩

variable {XI Y' Cells Rec : Type} (F : FileDescription XI) (str : Y' → Strs)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (orc₁ : ℕ → Option ℕ) (tab : Cells → ℕ → ℕ → OnBytes.F)

/-- **From CandAt to Member at chain 1's reading**: cand_laid₁ with hc paid. -/
theorem cand_laid_of_candAt₁
    (smp : (Xi × FirstState) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (a : (Xi × FirstState)) (y' : Y') (o : VerifiableInference.Desc.Oracle)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp) (u : (OmAt csKey six i).Msg)
    (ho : F.oracleAt (seatAt six numSix atSix i).1 = some o)
    (hz : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₁.smp a
      (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 = some z)
    (hsm : ∀ σ : (OmAt csKey six i).Smp, smp a sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D, (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₁ orc₁) i a ρ σ.2)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) (str y') i)
    (hc : Sound.CandAt csKey F smp ⟨sixS, i⟩ a (str y') u) :
    Member F (baseK csKey six numSix atSix decT recOf orc₁).h₁ o
        (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 (str y') z
        (ofU csKey (six.get i).1 (six.get i).2 u) ∧
      toU csKey (six.get i).1 (six.get i).2 (ofU csKey (six.get i).1 (six.get i).2 u) = u ∧
      ∀ (part : OnBytes.Part) (k : ℕ),
        KeyRows23.readE ((kreadFam csKey six numSix atSix tab).val
          (ofU csKey (six.get i).1 (six.get i).2 u) part k) =
          ofU csKey (six.get i).1 (six.get i).2 u part k := by
  obtain ⟨σ, hσ, h⟩ := (candAt_iff csKey F smp ⟨sixS, i⟩ a (str y') u).1 hc
  obtain ⟨ρ, e, hs⟩ := hsm σ hσ
  exact cand_laid₁ F str decT recOf orc₁ tab i hlog told a y' o z u ρ σ.2 ho hz hs hsh
    ⟨h.1, (congrFun e u).symm.trans h.2⟩

/-- **From CandAt to Member at chain 2's reading**: cand_laid₂ with hc paid. -/
theorem cand_laid_of_candAt₂
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (a : (P₂ × St₂)) (y' : Y') (o : VerifiableInference.Desc.Oracle)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp) (u : (OmAt csKey six i).Msg)
    (ho : F.oracleAt (seatAt six numSix atSix i).1 = some o)
    (hz : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp a
      (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 = some z)
    (hsm : ∀ σ : (OmAt csKey six i).Smp, smp a sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D, (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i a ρ σ.2)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) (str y') i)
    (hc : Sound.CandAt csKey F smp ⟨sixS, i⟩ a (str y') u) :
    Member F (baseK csKey six numSix atSix decT recOf orc₁).h₂ o
        (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 (str y') z
        (ofU csKey (six.get i).1 (six.get i).2 u) ∧
      toU csKey (six.get i).1 (six.get i).2 (ofU csKey (six.get i).1 (six.get i).2 u) = u ∧
      ∀ (part : OnBytes.Part) (k : ℕ),
        KeyRows23.readE ((kreadFam csKey six numSix atSix tab).val
          (ofU csKey (six.get i).1 (six.get i).2 u) part k) =
          ofU csKey (six.get i).1 (six.get i).2 u part k := by
  obtain ⟨σ, hσ, h⟩ := (candAt_iff csKey F smp ⟨sixS, i⟩ a (str y') u).1 hc
  obtain ⟨ρ, e, hs⟩ := hsm σ hσ
  exact cand_laid₂ F str decT recOf orc₁ tab i hlog told a y' o z u ρ σ.2 ho hz hs hsh
    ⟨h.1, (congrFun e u).symm.trans h.2⟩

/-- **From CandAt to Member at chain 3's reading**: cand_laid₃ with hc paid. -/
theorem cand_laid_of_candAt₃
    (smp : (P₃ × St₃) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (a : (P₃ × St₃)) (y' : Y') (o : VerifiableInference.Desc.Oracle)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp) (u : (OmAt csKey six i).Msg)
    (ho : F.oracleAt (seatAt six numSix atSix i).1 = some o)
    (hz : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃.smp a
      (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 = some z)
    (hsm : ∀ σ : (OmAt csKey six i).Smp, smp a sixS i = some σ →
      ∃ ρ : (OmAt csKey six i).Z.D, (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i a ρ σ.2)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) (str y') i)
    (hc : Sound.CandAt csKey F smp ⟨sixS, i⟩ a (str y') u) :
    Member F (baseK csKey six numSix atSix decT recOf orc₁).h₃ o
        (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 (str y') z
        (ofU csKey (six.get i).1 (six.get i).2 u) ∧
      toU csKey (six.get i).1 (six.get i).2 (ofU csKey (six.get i).1 (six.get i).2 u) = u ∧
      ∀ (part : OnBytes.Part) (k : ℕ),
        KeyRows23.readE ((kreadFam csKey six numSix atSix tab).val
          (ofU csKey (six.get i).1 (six.get i).2 u) part k) =
          ofU csKey (six.get i).1 (six.get i).2 u part k := by
  obtain ⟨σ, hσ, h⟩ := (candAt_iff csKey F smp ⟨sixS, i⟩ a (str y') u).1 hc
  obtain ⟨ρ, e, hs⟩ := hsm σ hσ
  exact cand_laid₃ F str decT recOf orc₁ tab i hlog told a y' o z u ρ σ.2 ho hz hs hsh
    ⟨h.1, (congrFun e u).symm.trans h.2⟩

end LPFD.CandLaid

#print axioms LPFD.CandLaid.wordAt_eq_symsW
#print axioms LPFD.CandLaid.wordsOf_eq_symsW
#print axioms LPFD.CandLaid.candAt_iff
#print axioms LPFD.CandLaid.sixS
#print axioms LPFD.CandLaid.cand_laid_of_candAt₁
#print axioms LPFD.CandLaid.cand_laid_of_candAt₂
#print axioms LPFD.CandLaid.cand_laid_of_candAt₃
