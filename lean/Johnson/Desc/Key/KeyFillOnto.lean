-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillOnto.lean: THE READER OF A WORD OF SYMBOLS (Johnson/Desc/Key/KeyFill.lean: symsW) IS ONTO: every word as sent of the library's oracle message is the reading of a RAW word every leaf of which is shown. SO AN HONEST WORD IS A MEMBER.
  wordsOfRows b n g   n rows' symbols written as raw words: one word a row over the base field, three over the extension field: the canonical ones (OnBytes.Slice.ofF | ofE)
  rowAt_wordsOfRows   rowAt (Johnson/Desc/Sound/MsgSig.lean) reads them back
  rawOf f             the raw word of a word as sent
  symsW_rawOf         (hm) → symsW (rawOf f) = f ; rawOf_shown
  inList_of_sent      a word as sent whose lift IS an encoding of m₀ has m₀ in its list (at distance 0)
  honest_far          **(hm) → upW f = C.enc m₀ r₀ → ∃ c u, every leaf of c is shown ∧ symsW c = f ∧ EncAt (ofU m₀) u ∧ far (aOf cs s) c u ≤ e**: THE HONEST MESSAGE's TABLE IS NEAR THE HONEST RAW WORD IN Msg.lean's OWN COUNT
  honest_member       **AN HONEST WORD IS A MEMBER** of fillG's list (through member_of_cand); that such raw words EXIST for every word as sent is symsW_rawOf | rawOf_shown
OBJECT: none: a filling of letters · USER: Johnson/Desc/Key/KeyFillStrs.lean (meant: with member_of_cand and a sender's «upW f = enc m₀ r₀»: an honest run's word is a Member) · LETTERS: cs · s · e.
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob

/-- n rows' symbols, as raw words. -/
def wordsOfRows : (b : Bool) → (n : ℕ) → (Fin n → RowTy b) → List UInt64
  | true, n, g => List.ofFn fun i : Fin n => ofF (g i)
  | false, n, g => List.ofFn fun k : Fin (3 * n) =>
      let t := ofE (g ⟨k.val / 3, by have := k.isLt; omega⟩)
      if k.val % 3 = 0 then t.1 else if k.val % 3 = 1 then t.2.1 else t.2.2

theorem getD_ofFn {n : ℕ} (f : Fin n → UInt64) (i : Fin n) : (List.ofFn f).getD i.val 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl

theorem rowAt_wordsOfRows : ∀ (b : Bool) (n : ℕ) (g : Fin n → RowTy b) (i : Fin n), rowAt b (wordsOfRows b n g) i.val = g i
  | true, n, g, i => by
    show toF ((List.ofFn fun i : Fin n => ofF (g i)).getD i.val 0) = g i
    rw [getD_ofFn]
    exact toF_ofF (g i)
  | false, n, g, i => by
    have h0 : 3 * i.val < 3 * n := by have := i.isLt; omega
    have h1 : 3 * i.val + 1 < 3 * n := by have := i.isLt; omega
    have h2 : 3 * i.val + 2 < 3 * n := by have := i.isLt; omega
    show toE ((wordsOfRows false n g).getD (3 * i.val) 0, (wordsOfRows false n g).getD (3 * i.val + 1) 0, (wordsOfRows false n g).getD (3 * i.val + 2) 0) = g i
    unfold wordsOfRows
    rw [getD_ofFn _ ⟨3 * i.val, h0⟩, getD_ofFn _ ⟨3 * i.val + 1, h1⟩, getD_ofFn _ ⟨3 * i.val + 2, h2⟩]
    have d0 : (3 * i.val) / 3 = i.val := by omega
    have d1 : (3 * i.val + 1) / 3 = i.val := by omega
    have d2 : (3 * i.val + 2) / 3 = i.val := by omega
    have m0 : (3 * i.val) % 3 = 0 := by omega
    have m1 : (3 * i.val + 1) % 3 = 1 := by omega
    have m2 : (3 * i.val + 2) % 3 = 2 := by omega
    simp only [d0, d1, d2, m0, m1, m2, if_true, Fin.eta]
    simp only [show (1 : ℕ) ≠ 0 from by omega, show (2 : ℕ) ≠ 0 from by omega, show (2 : ℕ) ≠ 1 from by omega, if_false, if_true]
    exact toE_ofE (g i)

variable (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e : ℕ)

open Classical in
/-- The raw word of a word as sent. -/
def rawOf (f : (portOmZ cs s e).Str) : ℕ → Option Sym := fun k =>
  if h : k < 2 ^ aOf cs s then
    some ⟨if ha : (cMain cs s).a = aOf cs s then wordsOfRows _ s.mainRows (fun i => f (.inl ⟨k, by rw [ha]; exact h⟩) (i, ())) else [],
      wordsOfRows _ s.maskRows (fun i => f (.inr ⟨k, h⟩) (i, ()))⟩
  else none

theorem rawOf_shown (f : (portOmZ cs s e).Str) (k : ℕ) (h : k < 2 ^ aOf cs s) : (rawOf cs s e f k).isSome = true := by
  unfold rawOf
  rw [dif_pos h]
  rfl

theorem symsW_rawOf (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) (f : (portOmZ cs s e).Str) : symsW cs s e (rawOf cs s e f) = f := by
  funext p
  match p with
  | .inl x =>
    funext r
    obtain ⟨i, ⟨⟩⟩ := r
    rcases hm with h0 | ha
    · exact (Nat.not_lt_zero _ (lt_of_lt_of_eq i.isLt h0)).elim
    · have hx : x.val < 2 ^ aOf cs s := by rw [← ha]; exact x.isLt
      simp only [symsW, rawOf, dif_pos hx, dif_pos ha, Option.map_some, Option.getD_some]
      exact rowAt_wordsOfRows _ s.mainRows _ i
  | .inr x =>
    funext r
    obtain ⟨i, ⟨⟩⟩ := r
    simp only [symsW, rawOf, dif_pos x.isLt, Option.map_some, Option.getD_some]
    exact rowAt_wordsOfRows _ s.maskRows _ i

/-- A word as sent whose lift is an encoding of m₀ has m₀ in its list. -/
theorem inList_of_sent (f : (portOmZ cs s e).Str) (m₀ : (portOmZ cs s e).Msg) (r₀ : (portOmZ cs s e).Rnd)
    (h : (portOmZ cs s e).upW f = (portOmZ cs s e).C.enc m₀ r₀) : (portOmZ cs s e).InList f m₀ := by
  refine ⟨r₀, ?_⟩
  show cnt (fun x => (portOmZ cs s e).C.T ((portOmZ cs s e).upW f) x ≠ (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc m₀ r₀) x) ≤ _
  rw [h]
  have : cnt (fun x : (portOmZ cs s e).P => (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc m₀ r₀) x ≠ (portOmZ cs s e).C.T ((portOmZ cs s e).C.enc m₀ r₀) x) = 0 := by
    unfold cnt
    exact Nat.card_eq_zero.2 (Or.inl ⟨fun x => x.2 rfl⟩)
  rw [this]
  exact Nat.zero_le _

/-- **The honest message's table is near the honest raw word, in Msg.lean's own count.** -/
theorem honest_far (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s) (f : (portOmZ cs s e).Str) (m₀ : (portOmZ cs s e).Msg) (r₀ : (portOmZ cs s e).Rnd)
    (h : (portOmZ cs s e).upW f = (portOmZ cs s e).C.enc m₀ r₀) :
    ∃ c u, (∀ k, k < 2 ^ aOf cs s → (c k).isSome = true) ∧ symsW cs s e c = f ∧ EncAt cs s e (ofU cs s e m₀) u ∧ far (aOf cs s) c u ≤ e := by
  have hs := symsW_rawOf cs s e hm f
  obtain ⟨u, hE, hfar⟩ := far_of_inList cs s e hm (rawOf cs s e f) (rawOf_shown cs s e f) m₀ (by rw [hs]; exact inList_of_sent cs s e f m₀ r₀ h)
  exact ⟨rawOf cs s e f, u, rawOf_shown cs s e f, hs, hE, hfar⟩

section
variable {A Cells Rec XI : Type} (j₀ t₀ : ℕ) (seedIs : A → (portOmZ cs s e).Z.D → ((portOmZ cs s e).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (lay : ℕ → ℕ → Tab → Tab → Tab) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec) (F : FileDescription XI)

/-- **AN HONEST WORD IS A MEMBER**: where the tenant's committed word reads as a word as sent whose lift is an encoding of m₀, every leaf is shown, and the record's sample holds the library's answers of m₀ at its seed: the table of m₀ is a Member of
fillG's list that meets the record's sample. -/
theorem honest_member (hlog : ∀ o, F.oracleAt j₀ = some o → o.logLength = aOf cs s) (hm : s.mainRows = 0 ∨ (cMain cs s).a = aOf cs s)
    (uniq : ∀ a ρ v ρ' v', seedIs a ρ v → seedIs a ρ' v' → (portOmZ cs s e).Z.val ρ = (portOmZ cs s e).Z.val ρ' ∧ v = v')
    (a : A) (y : Strs) (o : Oracle) (z : (portOmZ cs s e).Smp) (m₀ : (portOmZ cs s e).Msg) (r₀ : (portOmZ cs s e).Rnd) (ρ : (portOmZ cs s e).Z.D)
    (ho : F.oracleAt j₀ = some o) (hz : (fillG cs s e j₀ t₀ seedIs arr lay decT recOf).smp a j₀ t₀ = some z)
    (hs : seedIs a ρ ((portOmZ cs s e).Z.val ρ m₀))
    (hsh : ∀ k, k < 2 ^ aOf cs s → (wordOf F y j₀ t₀ k).isSome = true)
    (hw : (portOmZ cs s e).upW (symsW cs s e (wordOf F y j₀ t₀)) = (portOmZ cs s e).C.enc m₀ r₀) :
    Member F (fillG cs s e j₀ t₀ seedIs arr lay decT recOf) o j₀ t₀ y z (ofU cs s e m₀) :=
  member_of_cand cs s e j₀ t₀ seedIs arr lay decT recOf F hlog hm uniq a y o z m₀ ρ _ ho hz hs hsh
    ⟨inList_of_sent cs s e _ m₀ r₀ hw, rfl⟩

end

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.honest_member
#print axioms VerifiableInference.Desc.Key.Fill.symsW_rawOf
#print axioms VerifiableInference.Desc.Key.Fill.honest_far
