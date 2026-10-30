-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/KeyRowLaid.lean: THE KEY FILE's HALF OF THE ROW ON THE WRITTEN DATA
(`KeyWrittenOrRefuses`, Johnson/Goal/Numbers/PlanWrittenHalves.lean) AT THE KEY FILE's PIECE, with
no letter left: in scope, at every o, the piece refuses with words or lays the written data.

Main names.
  laidNo o Z: the two in a row, `publicOfO o` and then `Key.keyDataAndDecisionAtFixedDigest`, return a refusal.
  yesAsked_keyLaid: YesAsked (laidNo o) (laidYes o): a value or a refusal.
  key_row_laid (o d): KeyWrittenOrRefuses (descOrAt o d) (laidNo o).
  key_row_laid_at: the same with no maker and no letter d: in scope the two in a row return a
    refusal, or `(writtenKFull, r)` for some r.
  laidNo_run: where they return a refusal: `Key.laidOk` says no, and the laid decision
    (`Key.laidRun`) says no at every record and all views.
  keyNoToAll o Z: the laid decision says no at every record and all views.
  key_row_no (o d): a corollary: KeyWrittenOrRefuses (descOrAt o d) (keyNoToAll o).

Limits. WHAT "refuses" MEANS HERE. The row's own words for that letter are "the verifier says no to
everything at Z". `laidNo o Z` is THE PIECE's REFUSAL TO BE LAID: NOT YET THE VERIFIER's NO. All the
weight of `key_row_laid` lies in `laid_data_written` (Johnson/Goal/Numbers/KeySeatLaidAt.lean).
`laidNo_run` goes one step on: the key file's own decision then says no to everything. STILL OWED,
BY WHOEVER LAYS THE PIECE IN THE VERIFIER's TEXT: where the key file's piece is not laid, the
verifier says no to every proof and key file. `keyNoToAll` IS WEAKER THAN `laidNo` AS A FACT (a laid
piece whose decision said no to all would meet it too): so the "or" of `key_row_no` is not exclusive
by form. It is the key file's OWN decision's no: still not the verifier's. THAT THE PIECE IS LAID AT
ANY FILES IS NOT SHOWN HERE: by runs alone, at the goals' two named sets.
"AT EVERY o" IS WORTH "AT EVERY o AT WHICH THE PUBLIC PART IS ACCEPTED". In scope `publicOfO o`
returns only at an o whose digests of the four public tables are the format's: scope fixes these
words as plain numbers, and Johnson/Desc/Ok/PlanWritten/PublicAt.lean holds o's own digests against
them. At every other o a law here that has the yes among its premises holds of nothing.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Numbers.KeySeatLaidAt
import Johnson.Goal.Numbers.PlanWrittenHalves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes VerifiableInference.Desc

/-- The key file's piece refuses to be laid at the public files Z. -/
def laidNo (o : Nat → ByteArray → ByteArray) (Z : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ e, ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) = .error e

/-- A value or a refusal. -/
theorem laidNo_of_not_yes {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (h : ¬ laidYes o Z) : laidNo o Z := by
  unfold laidNo
  cases hv : (publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay with
  | error e => exact ⟨e, rfl⟩
  | ok x => exact absurd ⟨x.1, x.2, hv⟩ h

theorem yesAsked_keyLaid (o : Nat → ByteArray → ByteArray) : YesAsked (laidNo o) (laidYes o) :=
  fun _ _ h => laidNo_of_not_yes h

/-- **The key file's half of the row, at the key file's piece.** -/
theorem key_row_laid (o : Nat → ByteArray → ByteArray) (d : FileDescription Key.Xi) :
    KeyWrittenOrRefuses (descOrAt o d) (laidNo o) :=
  key_written_or_refuses (keyWrittenAt_of_laidFixed o d) (yesAsked_keyLaid o)

/-- **In scope the piece refuses with words or lays the written data.** -/
theorem key_row_laid_at {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Z = true) :
    (∃ e, ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) =
        .error e) ∨
      ∃ r, ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) =
        .ok (Johnson.G.writtenKFull, r) := by
  cases hv : (publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay with
  | error e => exact .inl ⟨e, rfl⟩
  | ok x =>
    obtain ⟨D, r⟩ := x
    obtain rfl := laid_data_written hZ hv
    exact .inr ⟨r, rfl⟩

/-- **Where the piece refuses, the key file's own decision says no to everything.** -/
theorem laidNo_run {o : Nat → ByteArray → ByteArray} {Z : VerifierAndGoals.PublicFiles} (h : laidNo o Z) :
    Key.laidOk ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) =
        false ∧
      ∀ rec v₁ v₂ v₃,
        Key.laidRun ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay)
          rec v₁ v₂ v₃ = false := by
  obtain ⟨e, he⟩ := h
  rw [he]
  exact ⟨rfl, fun _ _ _ _ => rfl⟩

/-- The key file's laid decision says no at every record and all views. -/
def keyNoToAll (o : Nat → ByteArray → ByteArray) (Z : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ rec v₁ v₂ v₃,
    Key.laidRun ((publicOfO o Z.pol Z.KL (some Z.lay)).bind fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay)
      rec v₁ v₂ v₃ = false

/-- A corollary: the row's key half at the decision's no to all. -/
theorem key_row_no (o : Nat → ByteArray → ByteArray) (d : FileDescription Key.Xi) :
    KeyWrittenOrRefuses (descOrAt o d) (keyNoToAll o) :=
  fun Z hZ => (key_row_laid o d Z hZ).imp (fun h => (laidNo_run h).2) id

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.yesAsked_keyLaid
#print axioms VerifiableInference.PlanWritten.key_row_laid
#print axioms VerifiableInference.PlanWritten.key_row_laid_at
#print axioms VerifiableInference.PlanWritten.laidNo_run
#print axioms VerifiableInference.PlanWritten.key_row_no
