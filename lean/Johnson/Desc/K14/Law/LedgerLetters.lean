-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerLetters.lean: THE TWO LETTERS THAT ARE LEFT BENEATH THE FILLING OF
RECORD, FILLED. The shared table's meaning and promise at our filling stand over two letters of the
table's own terms (mgJoint … MgZ, pmPoint … PmZ: Johnson/Desc/Sound/JointFilling.lean,
PointAtFilling.lean): of MgZ only the samples' rows are still read, of PmZ only the book-keeping at
the borders 0, 10, 11, 12. The ledger's top asks six premises of them. HERE: terms at which all six
hold by make.

  mgZ             any meaning M with its samples' rows laid as SmpSay at the fixed reader of words.
  mgZ_smp, mgZ_rides   nine_at_K | ten_at_K's hsmp (an equation: Iff.rfl) and share_seamed's hsr
                  (SampleRides, by smpSay_rides).
  pmZ             any promise P with its book-keeping laid: at border 0 "the key has the planned
                  sizes and o_u is not yet noted" (what "LIN point"'s law asks in front, one border
                  earlier: the front leaves the record); yes elsewhere.
  pmZ_zero, pmZ_yes   the top's hZ0, and hS12 | hP10 | hP11.
WHAT STAYS. That the chain's first record passes pmZ's test at border 0: the instance's key has the
planned sizes (owed from the entry's side) and no message is there (by make).
What is not claimed. No soundness; no level. NO MEMBER IS SHOWN.

-/
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.Sound.PointAtK14Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open OnBytes.Means (Words InOrder RowIn RowOn says_agree extends_of_grows)
open VerifiableInference.Desc (Wit Grows)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable (cs : Codes) {P₁ Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE) (num : Msg2 → ℕ)

/-- **The letter MgZ, filled**: the samples' rows are SmpSay's. -/
def mgZ (M : MeaningS St P₁ (Wit Cells Tok MsgT)) : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  { M with
    row := fun c s w => match c with
      | .sample μ => SmpSay (num μ) s (rgOf cs arr mem rd w)
      | c => M.row c s w }

theorem mgZ_smp (M : MeaningS St P₁ (Wit Cells Tok MsgT)) (μ : Msg2) (s : St) (w : Wit Cells Tok
    MsgT) :
    (mgZ cs arr mem rd num M).row (.sample μ) s w ↔ SmpSay (num μ) s (rgOf cs arr mem rd w) :=
  Iff.rfl

theorem mgZ_rides (M : MeaningS St P₁ (Wit Cells Tok MsgT)) : SampleRides (mgZ cs arr mem rd num M)
    num :=
  fun m s s' w g e h => smpSay_rides (num m) s s' _ g e h

/-- **The letter PmZ, filled.** At every border but 0 this letter's test accepts. At 1 to 9 other
fillings are laid over it; at 10, 11 and 12 it stands as it is, and accepts. The kind's own
sub-protocols end in front of border 9; what the two proximity tests, the chain's end and the last
chain's door want of the state stands beside this letter, at every border, in two slots: layX
(Johnson/Desc/K14/Law/LedgerOne.lean) and a letter X; both are laid in LedgerRow.lean, and X is
filled by XK (LedgerNineTen.lean), XW (LedgerDoor.lean) and Sh.X (SharedConst.lean), all in that
folder. So behind the test on G_u the promise does not say, among others, that the key fits, that
psi_sh has its length, where o_u sits, or how many rows are open. Nothing is drawn from this letter
at 10 or 11 but its own clause at the next border. What the laws ask of its book-keeping: at
sub-protocol 9 that its clause at 10 follow from the promise at 9 behind an accepting step (hP10; at
9 that promise holds the kind's own filling, not this letter's clause: so there the clause is
earned, not handed on); at sub-protocol 10 that its clause at 11 follow from the promise at 10, in
which its clause at 10 stands, behind an accepting step (hP11); at sub-protocol 11 that its clause
at 11 give its clause at 12 (hS12). The three laws stand under further premises, some of which name
this letter too. -/
def pmZ (p : Par) (P : PromMeaning St) : PromMeaning St :=
  { P with shape := fun k s => if k = 0 then shape1 p s && !notedU s else true }

theorem pmZ_zero (p : Par) (P : PromMeaning St) (s : St) (h : (pmZ p P).shape 0 s = true) :
    shape1 p s = true ∧ notedU s = false := by
  have h' : (shape1 p s && !notedU s) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h'
  exact ⟨h1, by simpa using h2⟩

theorem pmZ_yes (p : Par) (P : PromMeaning St) (k : ℕ) (hk : k ≠ 0) (s : St) :
    (pmZ p P).shape k s = true := if_neg hk

end Desc.K14.Law
