-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/CandCanBeLaid.lean: AN ANSWER IN LEAN TO A QUESTION («at which
  filling are The21's four K12 rows met; does it give, for a library's candidate u at the seat
  at_ k, an m : M with (i) Member … m AND (ii) R.val m = u's table?»). NO NEW MATTER: THREE CALLS.
AT THE FILLING AT WHICH The21Off STANDS (baseAt X decT recOf unfolds to
  baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc; readAt tab to
  kreadFam csKey six numSix atSix tab; M := Fill.Tab := Part → ℕ → GE), at each of the three
  chains' readings h₁ | h₂ | h₃ and at EVERY member i of the six: m := ofU … u:
  (i)   Member F B.h_j o ‹the seat› (str y') z (ofU … u): laysK_h_j's field «mem»
        (over fam_member_of_cand); that its «ofU» IS the filling's ofU: by rfl
  (ii') toU … (ofU … u) = u: toU_ofU: the table holds the candidate, entry for entry
  (ii)  R.val (ofU … u) part k, READ IN THE FIELD, is ofU … u part k: read_val. R.val's
        values are machine elements (OnBytes.E), the table's are field elements (GE): so «R.val m =
        u's table» holds UNDER readE, which is what R.same compares (kreadFam_same)
PAID HERE AT THE SIX: inj · apart · Tie · mains (seat_inj_six · shapesApart_six · tie_six ·
  mains_six, which is hm_six through its hmB_iff).
PREMISES LEFT, EACH PUBLIC OR THE CALLER's: hlog · told (what F tells of the seat's tree: both are
  clauses of Sound.SeatFits (Johnson/Desc/Sound/MsgSig.lean) at that seat: by seat_of_noFault from
  n01_scope | n2_scope at the seats 0 | 1 | 2) · ho · hz (the record's sample) · hs (the sending
  kind's tie at the record) · hsh (every leaf is shown) · hc (u is the library's candidate).
OBJECT: BaseSt's three readings at the filling · USER: the K12 rows ·
  LETTERS: F · str · Cells Rec · decT recOf orc₁ · tab. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowsEightSix

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

variable {XI Y' Cells Rec : Type} (F : FileDescription XI) (str : Y' → Strs)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (orc₁ : ℕ → Option ℕ) (tab : Cells → ℕ → ℕ → OnBytes.F)

/-- **A candidate can be laid, at chain 1's reading.** -/
theorem cand_laid₁ (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (a : Xi × FirstState) (y' : Y') (o : VerifiableInference.Desc.Oracle)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp) (u : (OmAt csKey six i).Msg)
    (ρ : (OmAt csKey six i).Z.D) (v : (OmAt csKey six i).Z.S → GE)
    (ho : F.oracleAt (seatAt six numSix atSix i).1 = some o)
    (hz : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₁.smp a
      (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 = some z)
    (hs : seedIsS csKey six numSix (rowIsK csKey six) (src₁ orc₁) i a ρ v)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) (str y') i)
    (hc : Cb.Ood.Cand
      ((OmAt csKey six i).InList (symsW csKey (six.get i).1 (six.get i).2
        (wordOf F (str y') (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2)))
      (OmAt csKey six i).Z.val ρ v u) :
    Member F (baseK csKey six numSix atSix decT recOf orc₁).h₁ o
        (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 (str y') z
        (ofU csKey (six.get i).1 (six.get i).2 u) ∧
      toU csKey (six.get i).1 (six.get i).2 (ofU csKey (six.get i).1 (six.get i).2 u) = u ∧
      ∀ (part : OnBytes.Part) (k : ℕ),
        KeyRows23.readE ((kreadFam csKey six numSix atSix tab).val
          (ofU csKey (six.get i).1 (six.get i).2 u) part k) =
          ofU csKey (six.get i).1 (six.get i).2 u part k :=
  ⟨(laysK_h₁ csKey six numSix atSix decT recOf orc₁ F str seat_inj_six shapesApart_six i (tie_six i)
      hlog (LPFD.mains_six i) told).mem a y' o z u ρ v ho hz hs hsh hc,
    toU_ofU csKey (six.get i).1 (six.get i).2 u,
    fun part k => read_val csKey six numSix atSix tab _ part k⟩

/-- **A candidate can be laid, at chain 2's reading.** -/
theorem cand_laid₂ (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (a : P₂ × St₂) (y' : Y') (o : VerifiableInference.Desc.Oracle)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp) (u : (OmAt csKey six i).Msg)
    (ρ : (OmAt csKey six i).Z.D) (v : (OmAt csKey six i).Z.S → GE)
    (ho : F.oracleAt (seatAt six numSix atSix i).1 = some o)
    (hz : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp a
      (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 = some z)
    (hs : seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i a ρ v)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) (str y') i)
    (hc : Cb.Ood.Cand
      ((OmAt csKey six i).InList (symsW csKey (six.get i).1 (six.get i).2
        (wordOf F (str y') (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2)))
      (OmAt csKey six i).Z.val ρ v u) :
    Member F (baseK csKey six numSix atSix decT recOf orc₁).h₂ o
        (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 (str y') z
        (ofU csKey (six.get i).1 (six.get i).2 u) ∧
      toU csKey (six.get i).1 (six.get i).2 (ofU csKey (six.get i).1 (six.get i).2 u) = u ∧
      ∀ (part : OnBytes.Part) (k : ℕ),
        KeyRows23.readE ((kreadFam csKey six numSix atSix tab).val
          (ofU csKey (six.get i).1 (six.get i).2 u) part k) =
          ofU csKey (six.get i).1 (six.get i).2 u part k :=
  ⟨(laysK_h₂ csKey six numSix atSix decT recOf orc₁ F str seat_inj_six shapesApart_six i (tie_six i)
      hlog (LPFD.mains_six i) told).mem a y' o z u ρ v ho hz hs hsh hc,
    toU_ofU csKey (six.get i).1 (six.get i).2 u,
    fun part k => read_val csKey six numSix atSix tab _ part k⟩

/-- **A candidate can be laid, at chain 3's reading.** -/
theorem cand_laid₃ (i : Fin six.length)
    (hlog : ∀ o, F.oracleAt (seatAt six numSix atSix i).1 = some o →
      o.logLength = aOf csKey (six.get i).1)
    (told : (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (a : P₃ × St₃) (y' : Y') (o : VerifiableInference.Desc.Oracle)
    (z : Σ i : Fin six.length, (OmAt csKey six i).Smp) (u : (OmAt csKey six i).Msg)
    (ρ : (OmAt csKey six i).Z.D) (v : (OmAt csKey six i).Z.S → GE)
    (ho : F.oracleAt (seatAt six numSix atSix i).1 = some o)
    (hz : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₃.smp a
      (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 = some z)
    (hs : seedIsS csKey six numSix (rowIsK csKey six) (src₃ orc₁) i a ρ v)
    (hsh : Sound.ShownAt F csKey six (seatAt six numSix atSix) (str y') i)
    (hc : Cb.Ood.Cand
      ((OmAt csKey six i).InList (symsW csKey (six.get i).1 (six.get i).2
        (wordOf F (str y') (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2)))
      (OmAt csKey six i).Z.val ρ v u) :
    Member F (baseK csKey six numSix atSix decT recOf orc₁).h₃ o
        (seatAt six numSix atSix i).1 (seatAt six numSix atSix i).2 (str y') z
        (ofU csKey (six.get i).1 (six.get i).2 u) ∧
      toU csKey (six.get i).1 (six.get i).2 (ofU csKey (six.get i).1 (six.get i).2 u) = u ∧
      ∀ (part : OnBytes.Part) (k : ℕ),
        KeyRows23.readE ((kreadFam csKey six numSix atSix tab).val
          (ofU csKey (six.get i).1 (six.get i).2 u) part k) =
          ofU csKey (six.get i).1 (six.get i).2 u part k :=
  ⟨(laysK_h₃ csKey six numSix atSix decT recOf orc₁ F str seat_inj_six shapesApart_six i (tie_six i)
      hlog (LPFD.mains_six i) told).mem a y' o z u ρ v ho hz hs hsh hc,
    toU_ofU csKey (six.get i).1 (six.get i).2 u,
    fun part k => read_val csKey six numSix atSix tab _ part k⟩

end LPFD.CandLaid

#print axioms LPFD.CandLaid.cand_laid₁
#print axioms LPFD.CandLaid.cand_laid₂
#print axioms LPFD.CandLaid.cand_laid₃
