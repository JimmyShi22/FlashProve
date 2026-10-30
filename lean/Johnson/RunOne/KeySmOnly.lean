-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySmOnly.lean: THE LOCAL PREMISE ON THE TABLES' ONE READING FOR ROWS THAT TURN THE STATEMENT's MESSAGES (the four proximity tests' rows 1.15 · 2.9 · 2.10 · 3.2; the sendings and joinings too): ReadsO (KeyThree.lean:153) asks the WHOLE array of messages, the WHOLE book and the codes to stand: a test breaks that (new messages come; members' ledgers are shut; masks are marked as spent; its trees enter the book). WHAT THE READING IN TRUTH READS OF A STATEMENT IS ONE MESSAGE's OWN RECORD, AND OF THAT RECORD THREE FIELDS:
  BaseSt.SmOnly     THE PREMISE, ON THE LETTER sm: the sample that a message's record holds is read off its shape · sampled · sampleRows alone (not off pad · groups · ledger · spentAsMask)
  smReads_of_only | smGroups_of_only   PROVED: it gives the two elder premises on sm (KeyOneReading.lean:81 · KeyLettersAt.lean:21)
  SampleAlike St St' o   the two statements have the same codes, and under the number o either both hold nothing or records that agree in these three fields
  sampleAlike_refl | smAt_of_only | bind_of_only   PROVED
  smp₁_of_only | smp₂_of_only   PROVED: at B.h₁ | B.h₂ (B.h₃: NOT TYPED: its reading parts by the record's border): the sample at a seat is unturned where the statement that the reading reads there is SampleAlike at the plan's number
OBJECT: B.h_j.smp · USER: whoever owes SamePins | «the samples agree at the pins still open» at a row that turns messages · LETTERS: T (the base).
Nothing on soundness.
-/
import Johnson.RunOne.KeyLettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key

variable {Cells M Smp Rec : Type} (T : BaseSt Cells M Smp Rec)

/-- The letter sm reads of a message's record its shape, whether it is sampled, and its sample's rows: nothing else. -/
def BaseSt.SmOnly : Prop := ∀ (c : Codes) (o : Nat) (x x' : OnBytes.Oracle), x'.shape = x.shape → x'.sampled = x.sampled → x'.sampleRows = x.sampleRows → T.sm c o x' = T.sm c o x

theorem smReads_of_only (h : T.SmOnly) : T.SmReads := fun c o x _ => h c o x _ rfl rfl rfl

theorem smGroups_of_only (h : T.SmOnly) : T.SmGroups := fun c o x _ => h c o x _ rfl rfl rfl

def SampleAlike (St St' : Statement) (o : Nat) : Prop :=
  St'.codes = St.codes ∧ ((St.oracles[o]? = none ∧ St'.oracles[o]? = none) ∨
    ∃ x x', St.oracles[o]? = some x ∧ St'.oracles[o]? = some x' ∧ x'.shape = x.shape ∧ x'.sampled = x.sampled ∧ x'.sampleRows = x.sampleRows)

theorem sampleAlike_refl (St : Statement) (o : Nat) : SampleAlike St St o := by
  refine ⟨rfl, ?_⟩
  cases h : St.oracles[o]? with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some x => exact Or.inr ⟨x, x, rfl, rfl, rfl, rfl, rfl⟩

theorem smAt_of_only (h : T.SmOnly) (St St' : Statement) (o : Nat) (ha : SampleAlike St St' o) : T.smAt St' o = T.smAt St o := by
  obtain ⟨hc, hn | ⟨x, x', hx, hx', e1, e2, e3⟩⟩ := ha
  · unfold BaseSt.smAt
    rw [hn.1, hn.2]
    rfl
  · unfold BaseSt.smAt
    rw [hx, hx', hc]
    exact h _ _ _ _ e1 e2 e3

theorem bind_of_only (h : T.SmOnly) (St St' : Statement) (q : Option Nat) (ha : ∀ o, q = some o → SampleAlike St St' o) : q.bind (T.smAt St') = q.bind (T.smAt St) := by
  cases q with
  | none => rfl
  | some o => exact smAt_of_only T h St St' o (ha o rfl)

theorem smp₁_of_only (h : T.SmOnly) (a a' : Xi × FirstState) (j t : Nat)
    (ha : ∀ o, T.orc₁ (T.arr j t) = some o → SampleAlike a.2.d.st a'.2.d.st o) : T.h₁.smp a' j t = T.h₁.smp a j t :=
  bind_of_only T h _ _ _ ha

theorem smp₂_of_only (h : T.SmOnly) (a a' : P₂ × St₂) (j t : Nat)
    (h1 : ∀ o, T.orc₁ (T.arr j t) = some o → SampleAlike a.1.2.d.st a'.1.2.d.st o)
    (h2 : ∀ o, orc₂ (T.arr j t) = some o → SampleAlike a.2.st a'.2.st o) : T.h₂.smp a' j t = T.h₂.smp a j t := by
  show (if T.arr j t < 3 then (T.orc₁ (T.arr j t)).bind (T.smAt a'.1.2.d.st) else (orc₂ (T.arr j t)).bind (T.smAt a'.2.st)) =
    (if T.arr j t < 3 then (T.orc₁ (T.arr j t)).bind (T.smAt a.1.2.d.st) else (orc₂ (T.arr j t)).bind (T.smAt a.2.st))
  rw [bind_of_only T h _ _ _ h1, bind_of_only T h _ _ _ h2]

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.smReads_of_only
#print axioms Johnson.RunOne.KeyRows23.smGroups_of_only
#print axioms Johnson.RunOne.KeyRows23.sampleAlike_refl
#print axioms Johnson.RunOne.KeyRows23.smAt_of_only
#print axioms Johnson.RunOne.KeyRows23.bind_of_only
#print axioms Johnson.RunOne.KeyRows23.smp₁_of_only
#print axioms Johnson.RunOne.KeyRows23.smp₂_of_only
