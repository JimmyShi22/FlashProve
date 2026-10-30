-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/TidyK2.lean: no soundness is claimed.
A statement that was owed (TidyK2Owed, stated in a file of this project that is not in this library): kind K2's sub-protocol with rounds (the code switch, K2.codeSwitchKind p) keeps «tidy in front, tidy behind» on the statement in the first chain's state.
  yes_rel            decideWith sendByL8 p s rs gs = .ok s' → R s.st s'.st, for every R with GroundQuiet R and K1.AdmitOn R (yes_keeps_whole, Johnson/Top/H0/Tw/K2C/KeepsWhole.lean, asks GroundKeeps R)
  **k2_decides_rel**   so: Decides (By R fun s => s.st) (codeSwitchKind p), at every p: no test on the plan, no «rounds that fit», no firstTree = 0 is spent
  **tidyK2**           the owed statement, in its own letters: ∀ p : K2.P2, p.firstTree = 0 → Fits (By TidyStay fun s : S => s.st) (K2.codeSwitchKind p : Block S Unit)
  tidyK2_decides     the stronger form at R := TidyStay
How. On both sides of the sending: the walk of Johnson/Top/H0/Tw/K2C/Keeps.lean, ported by program to GroundQuiet (K2KeepsQuiet.lean: yes_keepsQ). The sending: sendP_rel (SendPQuiet.lean). The new content: the rows that the sending's loop hands to the admitting are on their message: rowOn_form (FormOn.lean): of the program's own sample row, with no premise on the codes.
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SendPQuiet
import Johnson.ToldDescR.K2KeepsQuiet
import Johnson.Top.H0.Tw.K2C.Kind
import Johnson.Desc.Tidy.Stay
import Johnson.Desc.Tidy.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith yes_keepsQ)
open VerifiableInference.Desc.Keeps (Fits Decides fits_of_decides)
open VerifiableInference.Desc.Ground (By TidyStay GroundQuiet groundQuiet_tidy admitOn_tidy)
open VerifiableInference.Desc.K1 (AdmitOn)
open _root_.Tw.K2 (sendByL8)

variable {R : Statement → Statement → Prop}

/-- An accept of the switch keeps R from the statement in front to the statement behind. -/
theorem yes_rel (H : GroundQuiet R) (hA : AdmitOn R) {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') : R s.st s'.st := by
  obtain ⟨r₁, r₂, x, ids, sd, an, took, d', _, hs, h1, h2⟩ := yes_keepsQ H h
  exact H.trans h1 (H.trans (sendP_rel H hA hs) h2)

/-- **Every accepting decision of the switch keeps R.** -/
theorem k2_decides_rel {Cl : Type} (H : GroundQuiet R) (hA : AdmitOn R) (p : P2) :
    Decides (By R fun s : S => s.st) (codeSwitchKind p : Block S Cl) :=
  fun _ _ _ _ h => yes_rel H hA h

theorem tidyK2_decides {Cl : Type} (p : P2) :
    Decides (By TidyStay fun s : S => s.st) (codeSwitchKind p : Block S Cl) :=
  k2_decides_rel groundQuiet_tidy admitOn_tidy p

/-- **The row's sentence, in its own letters.** -/
theorem tidyK2 : ∀ p : VerifiableInference.Desc.First.K2.P2, p.firstTree = 0 →
    Fits (By TidyStay fun s : S => s.st) (VerifiableInference.Desc.First.K2.codeSwitchKind p : Block S Unit) :=
  fun p _ => fits_of_decides (tidyK2_decides p)

end ToldDesc

#print axioms ToldDesc.yes_rel
#print axioms ToldDesc.k2_decides_rel
#print axioms ToldDesc.tidyK2_decides
#print axioms ToldDesc.tidyK2
