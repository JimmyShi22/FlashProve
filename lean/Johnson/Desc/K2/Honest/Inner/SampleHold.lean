-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/SampleHold.lean: A KEPT MEMBER's STORED SAMPLE ROW, CARRIED OVER BY A
CODE SWITCH, SAYS TRUE OF THE HONEST NEW MESSAGES, where the stored row says true of the member's
own entries. Statements and proofs.

  `reads_off`      a row that reads one message's main table alone has no coefficient elsewhere
  `size_old`       the size of a kept member's main table
  `old_value`      what a stored sample row is worth on the kept members' old messages
  `sample_holds`   the row carried over says true

By: `formOn_reads` (Johnson/Top/H0/K2Hands/FormOnReads.lean); `coefAt_eq`
(OnBytes/Slice/BlkRow.lean); Inner/KeptRows.lean.

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.KeptRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE readE coefAt formAt)
open OnBytes.Means (Says value onTable tableSize)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc.First.K2Hands (readsMain formOn samplesOf sampleRow)
open Finset (range)

/-- A row that reads one message's main table alone has no coefficient elsewhere. -/
theorem reads_off (o' : Nat) (row : OnBytes.Row) (h : readsMain o' row = true) (o : Nat)
    (p : Part) (J : Nat) (hne : ¬ (o = o' ∧ p = .main)) : coefAt row o p J = 0 := by
  unfold readsMain at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [OnBytes.Slice.coefAt_eq]
  have t0 : OnBytes.Slice.termsAt row o p J = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    have ht' := h1 t (by simpa using ht)
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hne ⟨hc.1 ▸ ht'.1, hc.2 ▸ ht'.2⟩
  have u0 : OnBytes.Slice.unitsAt row o p J = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    have hu' := h2 u (by simpa using hu)
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hne ⟨hc.1.1 ▸ hu'.1, hc.1.2 ▸ hu'.2⟩
  have r0 : OnBytes.Slice.runsAt row o p J = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    have hw' := h3 w (by simpa using hw)
    unfold OnBytes.Slice.runAt
    rw [if_neg]
    intro hc
    unfold OnBytes.Slice.runHits at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hne ⟨hc.1.1.1.1.1 ▸ hw'.1, hc.1.1.1.1.2 ▸ hw'.2⟩
  have f0 : OnBytes.Slice.formsAt row o p J = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    have hf' := h4 f (by simpa using hf)
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hne ⟨hc.1 ▸ hf', hc.2⟩
  rw [t0, u0, r0, f0]
  simp

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- The size of a kept member's main table. -/
theorem size_old (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) :
    tableSize S k.old .main =
      2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll) := by
  obtain ⟨s, _, hs, _, _, _, _, _, e5, e6, e7⟩ := kept_at hFr a k hk
  have hlt : k.old < S.oracles.size := A.seated.olds _ (List.mem_of_getElem? e6)
  have hx : S.oracles[k.old]? = some S.oracles[k.old] := Array.getElem?_eq_getElem hlt
  have hsh : S.oracles[k.old].shape = s := by
    rw [e7, Array.getD_eq_getD_getElem?, hx]
    rfl
  obtain ⟨kt, hkt⟩ := kept_target A a s hs
  have K := kept_fits A a s kt hs hkt
  have hpos : 0 < s.mainRows := by
    rw [← K.rows]
    exact A.keptPos kt (List.mem_of_getElem? hkt)
  rw [size_main S k.old _ hx (by rw [hsh]; exact hpos), hsh, kept_code A a s hs, e5]

/-- What a stored sample row is worth on the kept members' old messages. -/
theorem old_value (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (sample : OnBytes.Row) (hr : readsMain k.old sample = true) :
    value rdE S sample (oldWords (sizesAt S old T) old W) =
      ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
        coefAt sample k.old .main J *
          (W.kept a).entryIn (S.oracles.getD k.old default).shape J := by
  obtain ⟨s, _, hs, _, _, _, _, _, _, e6, e7⟩ := kept_at hFr a k hk
  have hlt : k.old < S.oracles.size := A.seated.olds _ (List.mem_of_getElem? e6)
  have hidx := Lists.idxOf_at _ a k.old A.fits.once e6
  have hget : (sizesAt S old T).kept.getD a {} = s := by
    rw [List.getD_eq_getElem?_getD, hs]
    rfl
  unfold value
  rw [Finset.sum_eq_single k.old]
  · have hm : onTable rdE S sample (oldWords (sizesAt S old T) old W) k.old .mask = 0 := by
      unfold onTable
      apply Finset.sum_eq_zero
      intro i _
      have : rdE.val (sample.coefficient k.old .mask i) = 0 :=
        reads_off k.old sample hr k.old .mask i (fun h => by cases h.2)
      rw [this, zero_mul]
    rw [hm, add_zero]
    unfold onTable
    rw [size_old A hFr a k hk]
    apply Finset.sum_congr rfl
    intro J _
    have hw : oldWords (sizesAt S old T) old W k.old .main J = (W.kept a).entryIn s J := by
      unfold oldWords
      rw [hidx]
      show (W.kept a).entryIn ((sizesAt S old T).kept.getD a {}) J = _
      rw [hget]
    rw [hw, ← e7]
    rfl
  · intro o _ ho
    have h0 : ∀ p, onTable rdE S sample (oldWords (sizesAt S old T) old W) o p = 0 := by
      intro p
      unfold onTable
      apply Finset.sum_eq_zero
      intro i _
      have : rdE.val (sample.coefficient o p i) = 0 :=
        reads_off k.old sample hr o p i (fun h => ho h.1)
      rw [this, zero_mul]
    rw [h0, h0, add_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hlt) h

/-- **A stored sample row, carried over.** -/
theorem sample_holds (A : AtSwitch S old T g anew W V)
    (hn : ∀ o ∈ anew.toList, o < S.oracles.size) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (sample : OnBytes.Row) (hm : sample ∈ samplesOf S k)
    (hr : readsMain k.old sample = true)
    (ht : Says rdE S sample (oldWords (sizesAt S old T) old W)) :
    Says rdE S (sampleRow Fr k sample) (newWords (sizesAt S old T) g anew V) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, e6, _⟩ := kept_at hFr a k hk
  have hst := A.fits.stored k.old (List.mem_of_getElem? e6) sample hm
  have hruns : sample.runs = #[] := Array.eq_empty_of_size_eq_zero hst.1
  have hforms : sample.forms = #[] := Array.eq_empty_of_size_eq_zero hst.2
  have h1 := value_worth A hn (sampleRow Fr k sample)
  have hco : coefAt (sampleRow Fr k sample) = coefAt (Fr.addKept {} k (formOn sample)) := rfl
  rw [hco, worth_addKept A hFr a k hk] at h1
  have h2 := old_value A hFr a k hk sample hr
  have hsame : ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
      formAt (formOn sample) J * (W.kept a).entryIn (S.oracles.getD k.old default).shape J =
      ∑ J ∈ range (2 ^ (k.rowBits + (S.codes.base.getD old.code default).logEll)),
        coefAt sample k.old .main J *
          (W.kept a).entryIn (S.oracles.getD k.old default).shape J := by
    apply Finset.sum_congr rfl
    intro J _
    rw [VerifiableInference.Desc.First.K2Hands.formOn_reads k.old sample hruns hforms hr J]
  have htg : (sampleRow Fr k sample).target = sample.target := rfl
  unfold Says at ht ⊢
  rw [h1, hsame, ← h2, htg]
  exact ht

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.sample_holds
