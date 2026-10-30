-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSmMoves.lean: THE CONDITION ON THE TABLES' LETTER sm UNDER A RENAMING (BaseSt.SmMoves, declared in Johnson/RunOne/KeyPinsAtBase3.lean) HOLDS AT THE FILLING: an out-of-domain sample is read off a message's entry in the verifier's statement by its shape, its mark and its sample rows AS ROWS ON THE MESSAGE's OWN NUMBER: carried to another number with its rows renamed, it is the same sample. The guard SampleIn (every sample row lies on the message's own tables alone) IS SPENT, on the way back.
  renamed_add | renamed_addUnit | renamed_fold   Row.renamed goes through Row.add | Row.addUnit (plain pushes) and a fold of them
  sampleRow_renamed     (K1.sampleRow m o z β i y).renamed n = K1.sampleRow m n z β i y
  renamed_renamed       (r.renamed n).renamed o = r.renamed o
  renamed_of_rowIn      Means.RowIn St { code := 0, members := #[o] } r → r.renamed o = r
  rowIsK_moves          the sending kind's tie at (n, x') ↔ at (o, x)
  smFam_congr₂          KeyFillBase.lean's smFam_congr at two numbers (that one is its case n = o; it is proved there apart, by no call of this one)
  smMovesK              SmMoves (KeyPinsAtBase3.lean), unfolded, at baseK
OBJECT: SmMoves (KeyPinsAtBase3.lean); SampleIn (KeyHanded.lean) · USER: pins_laid (row 3.0) · LETTERS: cs l num at_ decT recOf orc₁. Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeed
import Johnson.RunOne.KeyHanded

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (sampleRow)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice

theorem renamed_add (r : OnBytes.Row) (o n : ℕ) (p : OnBytes.Part) (v : OnBytes.Tensor) : (r.add o p v).renamed n = (r.renamed n).add n p v := by
  simp only [OnBytes.Row.renamed, OnBytes.Row.add, Array.map_push]

theorem renamed_addUnit (r : OnBytes.Row) (o n : ℕ) (p : OnBytes.Part) (idx : ℕ) (c : OnBytes.E) : (r.addUnit o p idx c).renamed n = (r.renamed n).addUnit n p idx c := by
  simp only [OnBytes.Row.renamed, OnBytes.Row.addUnit, Array.map_push]

theorem renamed_fold {α : Type} (o n : ℕ) (P : α → OnBytes.Part) (I : α → ℕ) (C : α → OnBytes.E) : ∀ (l : List α) (r : OnBytes.Row),
    (l.foldl (fun r x => r.addUnit o (P x) (I x) (C x)) r).renamed n = l.foldl (fun r x => r.addUnit n (P x) (I x) (C x)) (r.renamed n)
  | [], _ => rfl
  | x :: l, r => by
    rw [List.foldl_cons, List.foldl_cons, renamed_fold o n P I C l, renamed_addUnit]

theorem renamed_start (n : ℕ) : ({ kind := .sample } : OnBytes.Row).renamed n = { kind := .sample } := by
  simp [OnBytes.Row.renamed]

/-- **The sending kind's sample row, renamed, is that kind's row at the new number.** -/
theorem sampleRow_renamed (m : VerifiableInference.Desc.K1.Msg) (o n : ℕ) (z : List OnBytes.E) (β : OnBytes.E) (i : ℕ) (y : OnBytes.E) :
    (sampleRow m o z β i y).renamed n = sampleRow m n z β i y := by
  have key : ∀ r : OnBytes.Row, ({ r with target := y } : OnBytes.Row).renamed n = { r.renamed n with target := y } := fun _ => rfl
  unfold sampleRow
  dsimp only
  rw [key]
  split <;> split <;> simp only [renamed_add, renamed_fold, renamed_start]

theorem renamed_renamed (r : OnBytes.Row) (n o : ℕ) : (r.renamed n).renamed o = r.renamed o := by
  simp [OnBytes.Row.renamed, Array.map_map, Function.comp_def]

theorem map_self {α : Type} (a : Array α) (f : α → α) (h : ∀ t ∈ a.toList, f t = t) : a.map f = a := by
  apply Array.ext'
  rw [Array.toList_map]
  exact (List.map_congr_left h).trans (List.map_id _)

theorem one_of_place (St : OnBytes.Statement) (o x : ℕ) (p : OnBytes.Part) (v i : ℕ)
    (h : OnBytes.Blk.placeOk St { code := 0, members := #[o] } x p v i = true) : x = o := by
  unfold OnBytes.Blk.placeOk at h
  simp only [Bool.and_eq_true] at h
  simpa using h.1.1.1

/-- **A row on one message's own tables alone is its own renaming to that message.** -/
theorem renamed_of_rowIn (St : OnBytes.Statement) (o : ℕ) (r : OnBytes.Row) (h : OnBytes.Means.RowIn St { code := 0, members := #[o] } r) : r.renamed o = r := by
  have h1 : (r.terms.map fun t => { t with oracle := o }) = r.terms := map_self _ _ fun t ht => by
    rw [← one_of_place St o _ _ _ _ (h.terms t ht)]
  have h2 : (r.units.map fun u => { u with oracle := o }) = r.units := map_self _ _ fun u hu => by
    rw [← one_of_place St o _ _ _ _ (h.units u hu)]
  have h3 : (r.runs.map fun w => { w with oracle := o }) = r.runs := map_self _ _ fun w hw => by
    rw [← one_of_place St o _ _ _ _ (h.runs w hw).2.2]
  have h4 : (r.forms.map fun f => { f with oracle := o }) = r.forms := map_self _ _ fun f hf => by
    rw [← one_of_place St o _ _ _ _ (h.forms f hf).1]
  unfold OnBytes.Row.renamed
  rw [h1, h2, h3, h4]

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))

/-- **The sending kind's tie moves with the renaming.** -/
theorem rowIsK_moves (i : Fin l.length) (St : OnBytes.Statement) (o n : ℕ) (x x' : OnBytes.Oracle) (hx : St.oracles[o]? = some x) (hin : SampleIn St o)
    (h1 : x'.sampled = x.sampled) (h2 : x'.sampleRows = x.sampleRows.map (·.renamed n)) (ρ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) :
    rowIsK cs l i n x' ρ v ↔ rowIsK cs l i o x ρ v := by
  unfold rowIsK
  constructor
  · rintro ⟨z, β, t, hs, hr, hR, hv⟩
    refine ⟨z, β, t, h1 ▸ hs, ?_, hR, hv⟩
    rw [h2] at hr
    have hl : x.sampleRows.toList.map (·.renamed n) = [sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) n z β 0 t] := by
      have := congrArg Array.toList hr
      rwa [Array.toList_map] at this
    obtain ⟨r, hr1, hr2⟩ : ∃ r, x.sampleRows.toList = [r] ∧ r.renamed n = sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) n z β 0 t := by
      cases hL : x.sampleRows.toList with
      | nil => rw [hL] at hl; cases hl
      | cons r L =>
        rw [hL, List.map_cons] at hl
        obtain ⟨e1, e2⟩ := List.cons.inj hl
        cases L with
        | nil => exact ⟨r, rfl, e1⟩
        | cons _ _ => cases e2
    have hown := renamed_of_rowIn St o r (hin x hx r (by rw [hr1]; exact List.mem_singleton.2 rfl))
    apply Array.ext'
    rw [hr1]
    show [r] = [sampleRow _ o z β 0 t]
    rw [← hown, ← renamed_renamed r n o, hr2, sampleRow_renamed]
  · rintro ⟨z, β, t, hs, hr, hR, hv⟩
    refine ⟨z, β, t, h1.symm ▸ hs, ?_, hR, hv⟩
    rw [h2, hr]
    simp [sampleRow_renamed]

variable (rowIs : ∀ i : Fin l.length, ℕ → OnBytes.Oracle → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)

/-- smFam_congr at two numbers. -/
theorem smFam_congr₂ (c : OnBytes.Codes) (o n : ℕ) (x x' : OnBytes.Oracle) (hsh : x'.shape = x.shape) (hrow : ∀ i ρ v, rowIs i n x' ρ v ↔ rowIs i o x ρ v) :
    smFam cs l rowIs c n x' = smFam cs l rowIs c o x := by
  classical
  show (if c = cs then
    (if h : ∃ i : Fin l.length, (l.get i).1 = x'.shape then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, rowIs h.choose n x' z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none)
    else none) = (if c = cs then
    (if h : ∃ i : Fin l.length, (l.get i).1 = x.shape then
      (if h' : ∃ z : (OmAt cs l h.choose).Smp, rowIs h.choose o x z.1 z.2 then some (⟨h.choose, h'.choose⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp) else none) else none)
    else none)
  rw [hsh]
  by_cases hc : c = cs
  · rw [if_pos hc, if_pos hc]
    by_cases h : ∃ i : Fin l.length, (l.get i).1 = x.shape
    · rw [dif_pos h, dif_pos h]
      exact dite_choose_congr _ _ (funext fun z => propext (hrow h.choose z.1 z.2)) fun z => (⟨h.choose, z⟩ : Σ i : Fin l.length, (OmAt cs l i).Smp)
    · rw [dif_neg h, dif_neg h]
  · rw [if_neg hc, if_neg hc]

variable (num : Fin l.length → ℕ) (at_ : Where)
  {Cells Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)

/-- **SmMoves, UNFOLDED, AT THE TABLES' ONE READING WITH THE SAMPLE's TIE FILLED.** -/
theorem smMovesK : ∀ (St : OnBytes.Statement) (o n : ℕ) (x x' : OnBytes.Oracle), St.oracles[o]? = some x → SampleIn St o → x'.shape = x.shape → x'.sampled = x.sampled →
    x'.sampleRows = x.sampleRows.map (·.renamed n) →
    (baseK cs l num at_ decT recOf orc₁).sm St.codes n x' = (baseK cs l num at_ decT recOf orc₁).sm St.codes o x :=
  fun St o n x x' hx hin e1 e2 e3 => smFam_congr₂ cs l (rowIsK cs l) St.codes o n x x' e1 fun i ρ v => rowIsK_moves cs l i St o n x x' hx hin e2 e3 ρ v

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.renamed_add
#print axioms Johnson.RunOne.KeyRows23.renamed_addUnit
#print axioms Johnson.RunOne.KeyRows23.renamed_fold
#print axioms Johnson.RunOne.KeyRows23.renamed_start
#print axioms Johnson.RunOne.KeyRows23.map_self
#print axioms Johnson.RunOne.KeyRows23.one_of_place
#print axioms Johnson.RunOne.KeyRows23.sampleRow_renamed
#print axioms Johnson.RunOne.KeyRows23.renamed_renamed
#print axioms Johnson.RunOne.KeyRows23.renamed_of_rowIn
#print axioms Johnson.RunOne.KeyRows23.rowIsK_moves
#print axioms Johnson.RunOne.KeyRows23.smFam_congr₂
#print axioms Johnson.RunOne.KeyRows23.smMovesK
