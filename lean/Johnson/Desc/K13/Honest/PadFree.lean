--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/PadFree.lean: the row (Eval) has no coefficient on an entry that masks an
OOD answer. Statements with their proofs.

When an open row is added, the verifier's text asks that the row has the coefficient 0 on every
place of every member's pad. It is the one clause of the adding that reads coefficients. Those of
(Eval) are made of challenges, so the clause could, by its form, hang on a challenge. It does not:
(Eval) names W's main table at the first 2^k entries of the vector alone, and single mask entries.
So the clause holds at every challenge, if W's pad stands behind these entries and no mask entry
that the claim names is a place of a pad.
Main names:
  `evalOf_val_zero`: the coefficient of (Eval) reads as 0 at a place that is neither among the first
    2^k entries of W's vector nor a mask entry of the claim.
  `sentAtM4_pad`: **the condition `SentAtM4.pad`** (Johnson/Desc/K13/Honest/RowsAccept.lean), from
    two conditions on places alone.
  `w_pad_behind`: half of the first of the two, from the test on the public shape: where W's pad is
    the one that the codes and W's shape give (`Send.pad`, OnBytes/Iop/Send.lean), each of its
    places in the main table holds an entry with a number from 2^kCol on. Where W has a mask row its
    pad lies in the mask table, no place of it is in the main table, and the sentence holds
    vacuously.

What is not claimed here. That a place of W's pad lies within W's table, and that the mask entries
which a ledger has given are no places of a pad: premises in this file. Nothing on soundness or on
hiding.

-/
import Johnson.Desc.K13.Honest.RowsAccept
import Johnson.Desc.Own.LinMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.K13.Law

/-- **Where (Eval) has the coefficient 0.** -/
theorem evalOf_val_zero {row : TensorRow} {w : ℕ} {lay : VectorLay}
    (hb : row.psi.length ≤ lay.bits) {o : ℕ} {part : OnBytes.Part} {idx : ℕ}
    (hT : w = o → OnBytes.Part.main = part →
      idx < 2 ^ lay.bits ∧ 2 ^ row.psi.length ≤ lay.entryAt idx)
    (hU : ∀ t ∈ row.masks, ¬ (t.1.oracle = o ∧ OnBytes.Part.mask = part ∧ t.1.index = idx)) :
    ρg.val ((evalOf row w lay).coefficient o part idx) = 0 := by
  have hterms : (evalOf row w lay).terms.toList =
      [⟨w, .main, lay.onTable (Tensor.eq row.psi)⟩] := rfl
  have hunits : (evalOf row w lay).units.toList =
      row.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single) := rfl
  have hruns : (evalOf row w lay).runs.toList = [] := rfl
  have hforms : (evalOf row w lay).forms.toList = [] := rfl
  rw [Row.coefficient_val, hterms, hunits, hruns, hforms]
  have h1 : ([(⟨w, .main, lay.onTable (Tensor.eq row.psi)⟩ : Term)].map fun t =>
      if t.oracle = o ∧ t.part = part then ρg.val (t.v.entry idx) else 0).sum = 0 := by
    refine OnBytes.Means.sum_map_zero _ _ fun t ht => ?_
    obtain rfl := List.mem_singleton.1 ht
    by_cases h : w = o ∧ OnBytes.Part.main = part
    · obtain ⟨hi, hge⟩ := hT h.1 h.2
      rw [if_pos h]
      show ρg.val ((lay.onTable (Tensor.eq row.psi)).entry idx) = 0
      rw [entry_onTable ρg lay (Tensor.eq row.psi) rfl (by rw [vars_eqTensor]; exact hb) idx hi,
        vars_eqTensor, if_neg (not_lt.2 hge)]
    · rw [if_neg h]
  have h2 : ((row.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).map fun u =>
      if u.oracle = o ∧ u.part = part then (if u.index = idx then ρg.val u.coeff else 0)
      else 0).sum = 0 := by
    refine OnBytes.Means.sum_map_zero _ _ fun u hu => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
    by_cases h : t.1.oracle = o ∧ OnBytes.Part.mask = part
    · rw [if_pos h, if_neg fun e => hU t ht ⟨h.1, h.2, e⟩]
    · rw [if_neg h]
  rw [h1, h2]
  simp

/-- **(Eval) has no coefficient on a pad**, from two conditions on places. -/
theorem sentAtM4_pad {row : TensorRow} {w : ℕ} {lay : VectorLay} {St : Statement}
    (hb : row.psi.length ≤ lay.bits)
    (hW : ∀ x : OnBytes.Oracle, St.oracles[w]? = some x → ∀ q ∈ x.pad, q.1 = .main →
      q.2 < 2 ^ lay.bits ∧ 2 ^ row.psi.length ≤ lay.entryAt q.2)
    (hM : ∀ t ∈ row.masks, ∀ x : OnBytes.Oracle, St.oracles[t.1.oracle]? = some x →
      (OnBytes.Part.mask, t.1.index) ∉ x.pad) :
    ∀ (o : ℕ) (x : OnBytes.Oracle), St.oracles[o]? = some x → ∀ q ∈ x.pad,
      ρg.val ((evalOf row w lay).coefficient o q.1 q.2) = 0 := by
  intro o x hx q hq
  refine evalOf_val_zero hb ?_ ?_
  · rintro rfl hp
    exact hW x hx q hq hp.symm
  · rintro t ht ⟨rfl, hp, hi⟩
    refine hM t ht x hx ?_
    have e : q = (OnBytes.Part.mask, t.1.index) := Prod.ext hp.symm hi.symm
    rw [← e]
    exact hq

/-- Where W's pad is the one that the codes and W's shape give: each of its places in the main table
holds an entry of the vector with a number from 2^kCol on. -/
theorem w_pad_behind {codes : Codes} {Sh : LinShape}
    (h : VerifiableInference.Desc.Own.linFits codes Sh = true) {places : List PadPlace}
    (hp : Send.pad codes Sh.w = some places) :
    ∀ q ∈ places.map fun p => (p.part, p.index), q.1 = OnBytes.Part.main →
      2 ^ Sh.kCol ≤ (linLayW codes Sh).entryAt q.2 := by
  obtain ⟨hS, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes Sh).1 h
  obtain ⟨_, _, _, _, _, _, _, hW, _⟩ := hS
  have ha : Sh.w.answers ≠ 0 := by
    have := hW.2.2.2
    omega
  have hp' : VerifiableInference.Desc.Own.padMade codes Sh.w = some places := hp
  intro q hq hmain
  obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hq
  exact (VerifiableInference.Desc.Own.w_has_room codes Sh h).2.2 p
    (by
      rw [if_neg (by simpa using ha), hp']
      exact hpm) hmain

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.evalOf_val_zero
#print axioms VerifiableInference.Desc.K13.Honest.sentAtM4_pad
#print axioms VerifiableInference.Desc.K13.Honest.w_pad_behind
