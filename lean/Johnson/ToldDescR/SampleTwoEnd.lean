-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SampleTwoEnd.lean: no soundness is claimed.
sampleTwoB cs V (RcLastCode.lean: rcLastB's fourth conjunct) at the first chain's reached ends: the join of the walk (SmpWalk.lean) with the earning at the two sendings, which stands here as two named premises.
  **sampleTwoB_last_end**   Rc 358 (z, s), in a family that hands back along a list whose sub-protocols keep SmpStay · ownSitsB V s · bookFitsB s.book · the messages number idx and nW sit at V.index and V.w in s.book · E₁: behind the sub-protocol number j the test accepts the message idx at V.indexShape · E₂: at border 357 it accepts nW at V.wShape ⇒ sampleTwoB cs V s = true
  **sampleTwoB_h4**         the same in the letters of h₄, the premise of five_at_end_in (Johnson/Desc/Sound/RcOfFold.lean, a file that is not in this library) at B₄ := sampleTwoB cs V
Why the numbers. ownSitsB says where the own group's two members sit; in a book that fits, two messages at one place are one (places_inj): so the members are idx and nW.
Does not show. E₁ · E₂ · the four facts at the last state. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.SmpWalk
import Johnson.Desc.Last.OwnSits
import Johnson.Desc.Sound.BookTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open Meaning.K2
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Fits)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.Book (BookFits places_inj)

/-- **At the first chain's last reached state.** -/
theorem sampleTwoB_last_end {Cl Pp : Type} {bs : List (Block S Cl)} {Rc : ℕ → Pp × S → Prop}
    (hb : HandsBack bs Rc) (hf : ∀ b ∈ bs, b.planOk = true → Fits (ByS SmpStay) b)
    (hp : ∀ b ∈ bs, b.planOk = true) {z : Pp} {s : S} (h : Rc 358 (z, s)) {cs : Codes}
    {V : OwnSeats} {idx nW : ℕ} (hO : ownSitsB V s = true) (hB : bookFitsB s.book = true)
    (hI : s.book.place[idx]? = some V.index) (hW : s.book.place[nW]? = some V.w)
    (j : ℕ) (hj : j + 1 ≤ 358)
    (E₁ : ∀ s', Rc (j + 1) (z, s') → sampleAtB cs V.indexShape s'.st idx = true)
    (E₂ : ∀ s', Rc 357 (z, s') → sampleAtB cs V.wShape s'.st nW = true) :
    sampleTwoB cs V s = true := by
  have a1 : sampleAtB cs V.indexShape s.st idx = true := by
    obtain ⟨m, hm⟩ : ∃ m, 358 = j + 1 + m := ⟨358 - (j + 1), by omega⟩
    rw [hm] at h
    obtain ⟨s₀, r0, w⟩ := back_smpStay hb hf hp (j + 1) m s h
    exact sampleAtB_stay (E₁ s₀ r0) w
  have a2 : sampleAtB cs V.wShape s.st nW = true := by
    obtain ⟨s₀, r0, w⟩ := back_smpStay hb hf hp 357 1 s h
    exact sampleAtB_stay (E₂ s₀ r0) w
  unfold sampleTwoB
  cases hF : firstOfS s with
  | none => rfl
  | some f =>
    obtain ⟨G, i₁, i₂, hG, hm, p1, p2, -, -⟩ := (ownSitsB_iff V s).1 hO f hF
    have eb : f.book = s.book ∧ f.st = s.st := by
      unfold firstOfS at hF
      obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hF
      exact ⟨rfl, rfl⟩
    have hFit : BookFits f.book := by
      rw [eb.1]
      exact (bookFitsB_iff _).1 hB
    obtain rfl : idx = i₁ := places_inj hFit (by rw [eb.1]; exact hI) p1
    obtain rfl : nW = i₂ := places_inj hFit (by rw [eb.1]; exact hW) p2
    rw [eb.2] at hG
    simp only [eb.2, hG, hm, a1, a2, Bool.and_self]

/-- **In the letters of the premise h₄ of `five_at_end_in`** (B₄ := sampleTwoB cs V). -/
theorem sampleTwoB_h4 {Cl Pp : Type} {bs : List (Block S Cl)} {Rch : ℕ → Pp × S → Prop}
    (hb : HandsBack bs Rch) (hf : ∀ b ∈ bs, b.planOk = true → Fits (ByS SmpStay) b)
    (hp : ∀ b ∈ bs, b.planOk = true) {cs : Codes} {V : OwnSeats} {idx nW : ℕ}
    (hEnd : ∀ z s, Rch 358 (z, s) → s.failed = none → ownSitsB V s = true ∧
      bookFitsB s.book = true ∧ s.book.place[idx]? = some V.index ∧
      s.book.place[nW]? = some V.w)
    (j : ℕ) (hj : j + 1 ≤ 358)
    (E₁ : ∀ z s', Rch (j + 1) (z, s') → sampleAtB cs V.indexShape s'.st idx = true)
    (E₂ : ∀ z s', Rch 357 (z, s') → sampleAtB cs V.wShape s'.st nW = true)
    {Q P₀ : Type} (get : Q → P₀ × S) (Oc : Q → Strs → Prop) (Rc : Q → Prop)
    (hE : ∀ q y, Oc q y → Rc q → ∃ z, Rch 358 (z, (get q).2)) :
    ∀ q y, Oc q y → Rc q → (get q).2.failed = none → sampleTwoB cs V (get q).2 = true := by
  intro q y ho hq hm
  obtain ⟨z, hz⟩ := hE q y ho hq
  obtain ⟨k1, k2, k3, k4⟩ := hEnd z _ hz hm
  exact sampleTwoB_last_end hb hf hp hz k1 k2 k3 k4 j hj (E₁ z) (E₂ z)

end ToldDesc

#print axioms ToldDesc.sampleTwoB_last_end
#print axioms ToldDesc.sampleTwoB_h4
