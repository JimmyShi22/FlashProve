-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsConstr.lean: THE ITEM constr k p AT THE COMPOSED MEANING: ITS SENTENCE READS
ONLY WHAT THE TABLE BOOKS, FROM FIVE NAMED CONGRUENCES ON THE MEANING's LETTERS. One abbreviation,
one structure, three theorems.

Why. An item `constr k p` rides past 344 of the first chain's 358 sub-protocols; each one's fifth
tie asks `ReadsItemQR` of it (Johnson/Desc/Sound/ReadsItems.lean). At `mgAll 𝔇 Mg` its sentence is
`P5J.constrQAt` (Johnson/P5J/MeansQ.lean): it reads the witness through five letters alone: the
digits' part; "the committed symbols pack small integers" (base); the output head's part; a group of
layers' share; an attention sub-proof's share. The decoded matrix and its index come of the
statement, not of the witness.

What is said. `SameAt 𝔇 links k p w w'`: two witnesses agree on every component that the table books
for `constr k p`. `HidReads 𝔇 links`: for each of the five letters, at a segment k of the list:
under `SameAt` the letter's sentence passes from w to w'. `readsAt_constr`: under it, `ReadsAt` at
`constr k p`, under no condition on the statement. `readsItem_constr`: so `ReadsItemQR`.
`partG_congr`: a group of layers' share reads the hidden integers of its own group alone, and the
request only in the parts idn and rider: what the payer of the fourth field will call.

Limits. `HidReads` is paid by nobody here. Whether the hidden integers of a segment read a pad at
another segment's seat is NOT settled here: if they do, the fourth or fifth field is false as typed.
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp)
open VerifiableInference.OnPublicFiles (headLink)
open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms

/-- A group of layers' share reads its own group's hidden integers, and the request in two parts. -/
theorem partG_congr {X : OnBytes.Model.Verify.Public} {i : IdxQ}
    {x x' : Instance ppref} {MG MG' : ℕ → Mats ℤ} {g : ℕ}
    {p : P5J.TPart} (hM : MG g = MG' g) (hx : p = .idn ∨ p = .rider → x = x')
    (h : P5J.partG X i x MG g p) : P5J.partG X i x' MG' g p := by
  cases p with
  | small =>
    unfold P5J.partG at h ⊢
    rw [← hM]
    exact h
  | idn =>
    unfold P5J.partG at h ⊢
    rw [← hM, ← hx (Or.inl rfl)]
    exact h
  | rider =>
    unfold P5J.partG at h ⊢
    rw [← hM, ← hx (Or.inr rfl)]
    exact h
  | lookCalls =>
    unfold P5J.partG at h ⊢
    rw [← hM]
    exact h
  | _ => exact h

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (links : List ModelPart)

/-- Two witnesses agree on what the table books for `constr k p`. -/
abbrev SameAt (k : ℕ) (p : P5J.TPart) (w w' : Wit (CellsQ rows cols) Tok MsgT) : Prop :=
  ∀ c ∈ (Item.constr k p).reads 𝔇.arr 𝔇.N links, sameQ c w w'

/-- **The five letters through which `constr` reads the witness read only what is booked.** -/
structure HidReads : Prop where
  digits : ∀ k a y w w', k < links.length → SameAt 𝔇 links k .lookDigits w w' →
    𝔇.digitsPart k a y w → 𝔇.digitsPart k a y w'
  base : ∀ k w w', k < links.length → SameAt 𝔇 links k .small w w' →
    𝔇.H.base k w → 𝔇.H.base k w'
  head : ∀ p i a y w w', p ≠ .lookDigits → SameAt 𝔇 links (headLink X) p w w' →
    𝔇.headPart p i a y w → 𝔇.headPart p i a y w'
  lay : ∀ k p i a w w', k < links.length → k ≠ headLink X → k % 2 = 0 → p ≠ .lookDigits →
    SameAt 𝔇 links k p w w' →
    P5J.partG X i (𝔇.put (𝔇.H.req a) (𝔇.H.hid w).tok).val (𝔇.H.hid w).MG (k / 2) p →
    P5J.partG X i (𝔇.put (𝔇.H.req a) (𝔇.H.hid w').tok).val (𝔇.H.hid w').MG (k / 2) p
  att : ∀ k p w w', k < links.length → k ≠ headLink X → k % 2 ≠ 0 → p ≠ .lookDigits →
    SameAt 𝔇 links k p w w' →
    P5J.partA (Hd.shapeA X (k / 2)) ((𝔇.H.hid w).MA (k / 2)) p →
    P5J.partA (Hd.shapeA X (k / 2)) ((𝔇.H.hid w').MA (k / 2)) p

variable (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The item constr k p**, at a segment of the list. -/
theorem readsAt_constr (R : HidReads 𝔇 links) (k : ℕ) (hk : k < links.length) (p : P5J.TPart) :
    ReadsAt (fun _ _ => True) (fun j => j.reads 𝔇.arr 𝔇.N links) 𝔇.N (mgAll 𝔇 Mg)
      (.constr k p) := by
  intro a y w w' _ hc hw
  have hw0 : P5J.constrQAt (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart k p a y
      w := hw
  show P5J.constrQAt (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart k p a y w'
  unfold P5J.constrQAt at hw0 ⊢
  by_cases hp : p = .lookDigits
  · rw [if_pos hp] at hw0 ⊢
    subst hp
    exact R.digits k a y w w' hk hc hw0
  · rw [if_neg hp] at hw0 ⊢
    refine ⟨fun e => ?_, fun M i hM hH => ?_⟩
    · subst e
      exact R.base k w w' hk hc (hw0.1 rfl)
    · have h1 := hw0.2 M i hM hH
      by_cases h24 : k = headLink X
      · rw [if_pos h24] at h1 ⊢
        subst h24
        exact R.head p i a y w w' hp hc h1
      · rw [if_neg h24] at h1 ⊢
        by_cases he : k % 2 = 0
        · rw [if_pos he] at h1 ⊢
          exact R.lay k p i a w w' hk h24 he hp hc h1
        · rw [if_neg he] at h1 ⊢
          exact R.att k p w w' hk h24 he hp hc h1

theorem readsItem_constr {A : Type} {Fr : Frame} (R : HidReads 𝔇 links) (ps : List Place)
    (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (j k : ℕ) (hk : k < links.length)
    (p : P5J.TPart) : ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch j (.constr k p) :=
  readsItem_of_readsAt _ _ _ _ _ _ _ _ _ (readsAt_constr 𝔇 links Mg R k hk p)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.partG_congr
#print axioms VerifiableInference.Desc.Sound.readsAt_constr
#print axioms VerifiableInference.Desc.Sound.readsItem_constr
