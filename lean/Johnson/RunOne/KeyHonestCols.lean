-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyHonestCols.lean: THEOREMS. BOOK-KEEPING ON LISTS: **every word of symbols of the right lengths is the committed word of some strings, at any told tenant; and every row of symbols is read off some list of raw words.**
OBJECT: Oracle.cut | wordOf (Johnson/Desc/Msg.lean) · rowAt (Johnson/Desc/Sound/MsgSig.lean). USER: Johnson/RunOne/KeyHonestStrs.lean calls strs_onto (meant: «strings whose word at a seat is the word sent exist»). LETTERS: F · (j₀, t₀) · oo · n · the word c.
  take_sum_le     the numbers in front of a member of a list, with the member, are at most the list's sum
  cut_col         the column «zeros · the main words · zeros · the mask words · zeros» is cut into just these words
  strs_onto       **told · the tenant · the tenants' words add up to the tree's · the word has the tenant's numbers of words ⊢ there are strings with that committed word, at every leaf**
  rows_onto       **every family of R symbols (over the base field: one word each; over the extension field: three) is read by rowAt off a list of R or 3 R raw words**
What is not claimed. More than one tenant at a time. Nothing on the stored table's cells. Nothing on soundness.

-/
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Johnson.Pack OnBytes.Slice

theorem take_sum_le (l : List ℕ) (t a : ℕ) (h : l[t]? = some a) : (l.take t).sum + a ≤ l.sum := by
  obtain ⟨ht, rfl⟩ := List.getElem?_eq_some_iff.1 h
  have e : l.drop t = l[t] :: l.drop (t + 1) := List.drop_eq_getElem_cons ht
  have s : (l.take t).sum + (l.drop t).sum = l.sum := by rw [← List.sum_append, List.take_append_drop]
  rw [e, List.sum_cons] at s
  omega

/-- The column. -/
def colOf (a b w : ℕ) (x : Sym) : List UInt64 :=
  (List.replicate a 0 ++ x.main ++ List.replicate (b - (a + x.main.length)) 0) ++ (x.mask ++ List.replicate (w - (b + x.mask.length)) 0)

theorem colOf_length (a b w : ℕ) (x : Sym) (h1 : a + x.main.length ≤ b) (h2 : b + x.mask.length ≤ w) : (colOf a b w x).length = w := by
  unfold colOf
  simp only [List.length_append, List.length_replicate]
  omega

theorem colOf_main (a b w : ℕ) (x : Sym) : ((colOf a b w x).drop a).take x.main.length = x.main := by
  unfold colOf
  have e : (List.replicate a (0 : UInt64) ++ x.main ++ List.replicate (b - (a + x.main.length)) 0) ++ (x.mask ++ List.replicate (w - (b + x.mask.length)) 0)
      = List.replicate a (0 : UInt64) ++ (x.main ++ (List.replicate (b - (a + x.main.length)) 0 ++ (x.mask ++ List.replicate (w - (b + x.mask.length)) 0))) := by
    simp only [List.append_assoc]
  rw [e, List.drop_left' (List.length_replicate ..), List.take_left' rfl]

theorem colOf_mask (a b w : ℕ) (x : Sym) (h1 : a + x.main.length ≤ b) : ((colOf a b w x).drop b).take x.mask.length = x.mask := by
  unfold colOf
  have l : (List.replicate a (0 : UInt64) ++ x.main ++ List.replicate (b - (a + x.main.length)) 0).length = b := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [List.drop_left' l, List.take_left' rfl]

theorem cut_col (oo : Oracle) (t : ℕ) (n : SymbolComponent) (hn : oo.tenants[t]? = some n)
    (hsum : (oo.tenants.map (·.main)).sum + (oo.tenants.map (·.mask)).sum = oo.words)
    (x : Sym) (h1 : x.main.length = n.main) (h2 : x.mask.length = n.mask) :
    oo.cut t (colOf (oo.mainSkip t) (oo.maskSkip t) oo.words x) = some x := by
  have a1 : ((oo.tenants.map (·.main)).take t).sum + n.main ≤ (oo.tenants.map (·.main)).sum :=
    take_sum_le _ t _ (by rw [List.getElem?_map, hn]; rfl)
  have a2 : ((oo.tenants.map (·.mask)).take t).sum + n.mask ≤ (oo.tenants.map (·.mask)).sum :=
    take_sum_le _ t _ (by rw [List.getElem?_map, hn]; rfl)
  have e1 : oo.mainSkip t = ((oo.tenants.map (·.main)).take t).sum := by unfold Oracle.mainSkip; rw [List.map_take]
  have e2 : oo.maskSkip t = (oo.tenants.map (·.main)).sum + ((oo.tenants.map (·.mask)).take t).sum := by unfold Oracle.maskSkip; rw [List.map_take]
  have g1 : oo.mainSkip t + x.main.length ≤ oo.maskSkip t := by rw [e1, e2, h1]; omega
  have g2 : oo.maskSkip t + x.mask.length ≤ oo.words := by rw [e2, h2]; omega
  unfold Oracle.cut
  rw [hn, Option.bind_some, if_pos (colOf_length _ _ _ x g1 g2), ← h1, ← h2, colOf_main, colOf_mask _ _ _ x g1]

/-- **Every word of the tenant's lengths is the committed word of some strings.** -/
theorem strs_onto {Xi : Type} (F : FileDescription Xi) (j₀ t₀ : ℕ) (oo : Oracle) (n : SymbolComponent) (ho : F.oracleAt j₀ = some oo) (hn : oo.tenants[t₀]? = some n)
    (hsum : (oo.tenants.map (·.main)).sum + (oo.tenants.map (·.mask)).sum = oo.words)
    (c : ℕ → Sym) (hc : ∀ k, (c k).main.length = n.main ∧ (c k).mask.length = n.mask) :
    ∃ y : Strs, ∀ k, wordOf F y j₀ t₀ k = some (c k) :=
  ⟨⟨fun _ => none, fun _ k => colOf (oo.mainSkip t₀) (oo.maskSkip t₀) oo.words (c k)⟩, fun k => by
    unfold wordOf
    rw [ho, Option.bind_some]
    exact cut_col oo t₀ n hn hsum (c k) (hc k).1 (hc k).2⟩

/-- **Every row of symbols is read off some raw words.** -/
theorem rows_onto : ∀ (b : Bool) (R : ℕ) (g : Fin R → RowTy b), ∃ ws : List UInt64, ws.length = R * (if b then 1 else 3) ∧ ∀ k : Fin R, rowAt b ws k.val = g k
  | true, R, g => ⟨List.ofFn fun k : Fin R => ofF (g k), by simp, fun k => by
      show toF ((List.ofFn fun k : Fin R => ofF (g k)).getD k.val 0) = g k
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      exact toF_ofF _⟩
  | false, R, g => by
    let w : Fin (R * 3) → UInt64 := fun i =>
      have hi : i.val / 3 < R := by have := i.isLt; omega
      if i.val % 3 = 0 then ofF (g ⟨i.val / 3, hi⟩ : Cb.Gl.E).c0 else if i.val % 3 = 1 then ofF (g ⟨i.val / 3, hi⟩ : Cb.Gl.E).c1 else ofF (g ⟨i.val / 3, hi⟩ : Cb.Gl.E).c2
    refine ⟨List.ofFn w, by simp, fun k => ?_⟩
    have h0 : 3 * k.val < R * 3 := by have := k.isLt; omega
    have h1 : 3 * k.val + 1 < R * 3 := by have := k.isLt; omega
    have h2 : 3 * k.val + 2 < R * 3 := by have := k.isLt; omega
    show toE ((List.ofFn w).getD (3 * k.val) 0, (List.ofFn w).getD (3 * k.val + 1) 0, (List.ofFn w).getD (3 * k.val + 2) 0) = g k
    rw [List.getD_eq_getElem _ _ (by simpa using h0), List.getD_eq_getElem _ _ (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h2),
      List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
    have d0 : (3 * k.val) / 3 = k.val := by omega
    have d1 : (3 * k.val + 1) / 3 = k.val := by omega
    have d2 : (3 * k.val + 2) / 3 = k.val := by omega
    have m0 : (3 * k.val) % 3 = 0 := by omega
    have m1 : (3 * k.val + 1) % 3 = 1 := by omega
    have m2 : (3 * k.val + 2) % 3 = 2 := by omega
    have w0 : w ⟨3 * k.val, h0⟩ = ofF (g k : Cb.Gl.E).c0 := by
      show (if (3 * k.val) % 3 = 0 then _ else _) = _
      rw [if_pos m0]
      simp only [d0]
    have w1 : w ⟨3 * k.val + 1, h1⟩ = ofF (g k : Cb.Gl.E).c1 := by
      show (if (3 * k.val + 1) % 3 = 0 then _ else if (3 * k.val + 1) % 3 = 1 then _ else _) = _
      rw [if_neg (by omega), if_pos m1]
      simp only [d1]
    have w2 : w ⟨3 * k.val + 2, h2⟩ = ofF (g k : Cb.Gl.E).c2 := by
      show (if (3 * k.val + 2) % 3 = 0 then _ else if (3 * k.val + 2) % 3 = 1 then _ else _) = _
      rw [if_neg (by omega), if_neg (by omega)]
      simp only [d2]
    rw [w0, w1, w2]
    show (⟨toF (ofF _), toF (ofF _), toF (ofF _)⟩ : Cb.Gl.E) = g k
    rw [toF_ofF, toF_ofF, toF_ofF]
    rfl

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.take_sum_le
#print axioms Johnson.RunOne.KeyLetters.cut_col
#print axioms Johnson.RunOne.KeyLetters.strs_onto
#print axioms Johnson.RunOne.KeyLetters.rows_onto
