-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SwitchTab.lean: the two tables of an honest prover's new message at a code
switch of the proximity test, at typed indices and over any type of entries. Three definitions with
code, and their laws.

Why. `gMain` and `gMask` (Johnson/Prover/Link/SwitchMsg.lean) are functions of a natural number
into the field, without code. Here an index is typed at its table's number of entries, so no arm
needs a default value; and the entries' type is a letter α, so one text serves words (`OnBytes.E`)
and field elements.

The layout is the library's (`csAt`, `free_at`, OnBytes/Slice/CsData.lean): the folded main message
fills the new main table; the new mask table holds the two folded mask messages, the three folded
tails, then free room.

Main names (namespace `Johnson.Prover.Link`).
  `maskUsed s`   how many entries of the new mask table the old full message fills
  `gMainT s μ'`   the new main table: `Fin s.C.l → α`
  `gMaskT s n μ' tl fr`   the new mask table: `Fin (maskUsed s + n) → α`; `fr : Fin n → α` stands in
      the free room. The sixth arm's index is proved to lie in `Fin n`
  `main_len`, `mask_len`, `fill_pos`   under `CsFit s s'`: the two tables have the next stage's
      numbers of entries, at n := `Fmt.M1.fillOf s.st s'.st` (Fmt/M1All.lean), which is at least 1
  `gMainT_map`, `gMaskT_map`   the tables commute with every map of entries
  `gMainT_csAt`, `gMaskT_csAt`, `gMaskT_free`   the layout, entry by entry
  `gMain_eq`, `gMask_eq`   the tie to the tables of SwitchMsg.lean
  `gMain_words`, `gMask_words`   so the tables of words, read in the field, are these tables

Limits. Definitions and equations on a layout. Outside `CsFit` the mask table still has
`maskUsed s + n` entries: that this is the next stage's number is `mask_len`, under `CsFit` by name.
The pad of the sample is the free room's last entry: no statement here names it. Who fills `fr` and
the tails is not said, and nothing is said of how they are chosen. Nothing on the tests of form, on
trees or on hashes. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchMsg
import Fmt.M1All

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- How many entries of the new mask table the old full message fills. -/
def maskUsed (s : Sg) : ℕ := 2 * s.Z.l + s.C.r + 2 * s.Z.r

/-- The new main table: entry i is the folded main message's entry i. -/
def gMainT {α : Type} (s : Sg) (μ' : s.cMid.J → α) : Fin s.C.l → α := fun i => μ' (.inl i)

/-- The new mask table, of `maskUsed s + n` entries: the two folded mask messages, the three folded
tails, then the n entries of free room. -/
def gMaskT {α : Type} (s : Sg) (n : ℕ) (μ' : s.cMid.J → α) (tl : s.cMid.Q → α) (fr : Fin n → α) :
    Fin (maskUsed s + n) → α := fun i =>
  if h1 : i.val < s.Z.l then μ' (.inr (.inl ⟨i.val, h1⟩))
  else if h2 : i.val - s.Z.l < s.Z.l then μ' (.inr (.inr ⟨i.val - s.Z.l, h2⟩))
  else if h3 : i.val - 2 * s.Z.l < s.C.r then tl (.inl ⟨i.val - 2 * s.Z.l, h3⟩)
  else if h4 : i.val - (2 * s.Z.l + s.C.r) < s.Z.r then
    tl (.inr (.inl ⟨i.val - (2 * s.Z.l + s.C.r), h4⟩))
  else if h5 : i.val - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r then
    tl (.inr (.inr ⟨i.val - (2 * s.Z.l + s.C.r + s.Z.r), h5⟩))
  else fr ⟨i.val - maskUsed s, by
    have := i.isLt
    unfold maskUsed at this ⊢
    omega⟩

section Sizes
variable {s s' : Sg}

/-- The new main table has the next stage's number of entries. -/
theorem main_len (hf : CsFit s s') : s.C.l = 2 ^ (s'.h + s'.g) * s'.C.l := hf.main.symm

/-- The new mask table has the next stage's number of entries. -/
theorem mask_len (hf : CsFit s s') :
    maskUsed s + Fmt.M1.fillOf s.st s'.st = 2 ^ s'.h * s'.Z.l := by
  have h := hf.mask
  show maskUsed s + (2 ^ s'.h * s'.Z.l - (2 * s.Z.l + s.C.r + 2 * s.Z.r)) = _
  unfold maskUsed
  omega

/-- The free room has an entry. -/
theorem fill_pos (hf : CsFit s s') : 1 ≤ Fmt.M1.fillOf s.st s'.st := by
  have h := hf.mask
  show 1 ≤ 2 ^ s'.h * s'.Z.l - (2 * s.Z.l + s.C.r + 2 * s.Z.r)
  omega

end Sizes

section Laws
variable {α β : Type} (s : Sg) (n : ℕ) (μ' : s.cMid.J → α) (tl : s.cMid.Q → α) (fr : Fin n → α)

theorem gMainT_map (f : α → β) :
    (fun i => f (gMainT s μ' i)) = gMainT s fun j => f (μ' j) := rfl

/-- **The mask table commutes with every map of entries.** -/
theorem gMaskT_map (f : α → β) :
    (fun i => f (gMaskT s n μ' tl fr i)) =
      gMaskT s n (fun j => f (μ' j)) (fun q => f (tl q)) fun k => f (fr k) := by
  funext i
  unfold gMaskT
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

/-- The main table at the index of an entry of the old full message. -/
theorem gMainT_csAt (x : CsK s) (i : ℕ) (hx : csAt s x = .inl i) (hi : i < s.C.l) :
    gMainT s μ' ⟨i, hi⟩ = Sum.elim μ' tl x := by
  rcases x with (j | j | j) | (q | q | q)
  · have e : j.val = i := Sum.inl.inj hx
    show μ' (.inl ⟨i, hi⟩) = μ' (.inl j)
    exact congrArg (fun z => μ' (.inl z)) (Fin.ext e.symm)
  all_goals cases hx

/-- **The mask table at the index of an entry of the old full message.** -/
theorem gMaskT_csAt (x : CsK s) (i : ℕ) (hx : csAt s x = .inr i) (hi : i < maskUsed s + n) :
    gMaskT s n μ' tl fr ⟨i, hi⟩ = Sum.elim μ' tl x := by
  rcases x with (j | j | j) | (q | q | q)
  · cases hx
  · obtain rfl : j.val = i := Sum.inr.inj hx
    unfold gMaskT
    rw [dif_pos j.isLt]
    rfl
  · obtain rfl : s.Z.l + j.val = i := Sum.inr.inj hx
    have n1 : ¬ s.Z.l + j.val < s.Z.l := by omega
    have e : s.Z.l + j.val - s.Z.l = j.val := by omega
    have p2 : s.Z.l + j.val - s.Z.l < s.Z.l := by rw [e]; exact j.isLt
    unfold gMaskT
    rw [dif_neg n1, dif_pos p2]
    exact congrArg (fun z => μ' (.inr (.inr z))) (Fin.ext e)
  · obtain rfl : 2 * s.Z.l + q.val = i := Sum.inr.inj hx
    have n1 : ¬ 2 * s.Z.l + q.val < s.Z.l := by omega
    have n2 : ¬ 2 * s.Z.l + q.val - s.Z.l < s.Z.l := by omega
    have e : 2 * s.Z.l + q.val - 2 * s.Z.l = q.val := by omega
    have p3 : 2 * s.Z.l + q.val - 2 * s.Z.l < s.C.r := by rw [e]; exact q.isLt
    unfold gMaskT
    rw [dif_neg n1, dif_neg n2, dif_pos p3]
    exact congrArg (fun z => tl (.inl z)) (Fin.ext e)
  · obtain rfl : 2 * s.Z.l + s.C.r + q.val = i := Sum.inr.inj hx
    have n1 : ¬ 2 * s.Z.l + s.C.r + q.val < s.Z.l := by omega
    have n2 : ¬ 2 * s.Z.l + s.C.r + q.val - s.Z.l < s.Z.l := by omega
    have n3 : ¬ 2 * s.Z.l + s.C.r + q.val - 2 * s.Z.l < s.C.r := by omega
    have e : 2 * s.Z.l + s.C.r + q.val - (2 * s.Z.l + s.C.r) = q.val := by omega
    have p4 : 2 * s.Z.l + s.C.r + q.val - (2 * s.Z.l + s.C.r) < s.Z.r := by rw [e]; exact q.isLt
    unfold gMaskT
    rw [dif_neg n1, dif_neg n2, dif_neg n3, dif_pos p4]
    exact congrArg (fun z => tl (.inr (.inl z))) (Fin.ext e)
  · obtain rfl : 2 * s.Z.l + s.C.r + s.Z.r + q.val = i := Sum.inr.inj hx
    have hq := q.isLt
    have n1 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val < s.Z.l := by omega
    have n2 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val - s.Z.l < s.Z.l := by omega
    have n3 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val - 2 * s.Z.l < s.C.r := by omega
    have n4 : ¬ 2 * s.Z.l + s.C.r + s.Z.r + q.val - (2 * s.Z.l + s.C.r) < s.Z.r := by omega
    have e : 2 * s.Z.l + s.C.r + s.Z.r + q.val - (2 * s.Z.l + s.C.r + s.Z.r) = q.val := by omega
    have p5 : 2 * s.Z.l + s.C.r + s.Z.r + q.val - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r := by
      rw [e]; exact hq
    unfold gMaskT
    rw [dif_neg n1, dif_neg n2, dif_neg n3, dif_neg n4, dif_pos p5]
    exact congrArg (fun z => tl (.inr (.inr z))) (Fin.ext e)

/-- **Behind the last tail: the free room, entry by entry.** -/
theorem gMaskT_free (k : Fin n) :
    gMaskT s n μ' tl fr ⟨maskUsed s + k.val, Nat.add_lt_add_left k.isLt _⟩ = fr k := by
  have n1 : ¬ maskUsed s + k.val < s.Z.l := by unfold maskUsed; omega
  have n2 : ¬ maskUsed s + k.val - s.Z.l < s.Z.l := by unfold maskUsed; omega
  have n3 : ¬ maskUsed s + k.val - 2 * s.Z.l < s.C.r := by unfold maskUsed; omega
  have n4 : ¬ maskUsed s + k.val - (2 * s.Z.l + s.C.r) < s.Z.r := by unfold maskUsed; omega
  have n5 : ¬ maskUsed s + k.val - (2 * s.Z.l + s.C.r + s.Z.r) < s.Z.r := by
    unfold maskUsed; omega
  unfold gMaskT
  rw [dif_neg n1, dif_neg n2, dif_neg n3, dif_neg n4, dif_neg n5]
  exact congrArg fr (Fin.ext (Nat.add_sub_cancel_left _ _))

end Laws

section Tie
variable (s : Sg) (n : ℕ) (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE)

theorem gMain_eq (i : Fin s.C.l) : gMain s μ' i.val = gMainT s μ' i := by
  unfold gMain
  rw [dif_pos i.isLt]
  rfl

/-- **The tie to the mask table of SwitchMsg.lean.** -/
theorem gMask_eq (fr : ℕ → GE) (i : Fin (maskUsed s + n)) :
    gMask s μ' tl fr i.val = gMaskT s n μ' tl (fun k => fr (maskUsed s + k.val)) i := by
  unfold gMask gMaskT
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · refine congrArg fr ?_
            show i.val = maskUsed s + (i.val - maskUsed s)
            unfold maskUsed
            omega

theorem gMain_words (μW : s.cMid.J → E) (i : Fin s.C.l) :
    gMain s (fun j => readE (μW j)) i.val = readE (gMainT s μW i) :=
  gMain_eq s _ i

/-- **The mask table of words, read in the field.** -/
theorem gMask_words (μW : s.cMid.J → E) (tW : s.cMid.Q → E) (fW : Fin n → E) (fr : ℕ → GE)
    (hfr : ∀ k : Fin n, fr (maskUsed s + k.val) = readE (fW k)) (i : Fin (maskUsed s + n)) :
    gMask s (fun j => readE (μW j)) (fun q => readE (tW q)) fr i.val =
      readE (gMaskT s n μW tW fW i) := by
  rw [gMask_eq s n, funext hfr]
  exact (congrFun (gMaskT_map s n μW tW fW readE) i).symm

end Tie

end Johnson.Prover.Link
