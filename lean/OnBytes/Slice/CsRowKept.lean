-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/CsRowKept.lean: the rows of the generator of the folded rows where main rows are kept
beside the folded one.

OnBytes/Slice/CsRow.lean gives the library's row of the generator (`Cb.LdCode.row`) in closed form
for the three rows that a fold hands on: one under the main code, two under the mask code
(`Sg.cMid`; `midRow`, `row_mid`). A fold of a group in which some members' main rows are kept hands
on more: the folded main row, the kept main rows, each under the main code, and the two mask rows.
Here the same closed form is given for that complex. The proof leans on `row_mid`: a kept row has
the folded main row's weights, on its own entries alone. Definitions, statements and proofs.
Main names (K: the names of the kept rows; `none`: the folded main row):
  `Sg.cKept s K`: the complex: `(s.cM.il (Option K)).pair (s.cZ.pair s.cZ)`.
  `keptRow s K x`: the weight of an entry of the messages or of the tails in a coordinate of the
    long symbol at the position x, by `midRow`.
  `row_kept`: `(s.cKept K).row x α e = keptRow s K x.val α e`.
  `keptRow_msg`, `keptRow_tail`, `keptRow_maskMsg`, `keptRow_maskTail`: the weights written out, in
    `wM` and `wT` (OnBytes/Slice/SimCs.lean): powers of the position's point.
Limits: nothing on a protocol. Nothing on where an entry lies in a new message.

-/
import OnBytes.Slice.CsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K]

/-- The folded complex with kept slots: the folded main row and the kept main rows; the carried
mask; the fresh mask. -/
abbrev Sg.cKept : LdCode GE s.Ps := (s.cM.il (Option K)).pair (s.cZ.pair s.cZ)

/-- The weight of an entry in a coordinate of the long symbol at the position x. -/
def keptRow (x : ℕ) : (s.cKept K).Aa → (s.cKept K).J ⊕ (s.cKept K).Q → GE
  | .inl (k, _), .inl (.inl (k', j)) => if k' = k then midRow s x (.inl ()) (.inl (.inl j)) else 0
  | .inl (k, _), .inr (.inl (k', q)) => if k' = k then midRow s x (.inl ()) (.inr (.inl q)) else 0
  | .inr a, .inl (.inr j) => midRow s x (.inr a) (.inl (.inr j))
  | .inr a, .inr (.inr q) => midRow s x (.inr a) (.inr (.inr q))
  | _, _ => 0

/-- The library's row of the generator of the folded complex with kept slots. -/
theorem row_kept (x : s.Ps) (α : (s.cKept K).Aa) (e : (s.cKept K).J ⊕ (s.cKept K).Q) :
    (s.cKept K).row x α e = keptRow s K x.val α e := by
  rcases α with ⟨k, ⟨⟩⟩ | a
  · rcases e with (⟨k', j⟩ | j) | (⟨k', q⟩ | q)
    · show _ = if k' = k then midRow s x.val (.inl ()) (.inl (.inl j)) else 0
      rw [← row_mid]
      by_cases h : k' = k
      · subst h
        simp [LdCode.row, Pi.single_apply]
      · have h' : ¬ k = k' := fun e => h e.symm
        simp [LdCode.row, h, h']
    · simp [LdCode.row, keptRow]
    · show _ = if k' = k then midRow s x.val (.inl ()) (.inr (.inl q)) else 0
      rw [← row_mid]
      by_cases h : k' = k
      · subst h
        simp [LdCode.row, Pi.single_apply]
      · have h' : ¬ k = k' := fun e => h e.symm
        simp [LdCode.row, h, h']
    · simp [LdCode.row, keptRow]
  · rcases e with (⟨k', j⟩ | j) | (⟨k', q⟩ | q)
    · rcases a with ⟨⟩ | ⟨⟩ <;> simp [LdCode.row, keptRow]
    · show _ = midRow s x.val (.inr a) (.inl (.inr j))
      rw [← row_mid]
      rcases a with ⟨⟩ | ⟨⟩ <;> rcases j with j | j <;> simp [LdCode.row, Pi.single_apply]
    · rcases a with ⟨⟩ | ⟨⟩ <;> simp [LdCode.row, keptRow]
    · show _ = midRow s x.val (.inr a) (.inr (.inr q))
      rw [← row_mid]
      rcases a with ⟨⟩ | ⟨⟩ <;> rcases q with q | q <;> simp [LdCode.row, Pi.single_apply]

/-- An entry of a main row's message has a weight in its own row's coordinate alone. -/
theorem keptRow_msg (x : ℕ) (k k' : Option K) (j : Fin s.C.l) :
    keptRow s K x (.inl (k, ())) (.inl (.inl (k', j))) = if k' = k then wM s.C x j.val else 0 :=
  rfl

/-- The same of an entry of a main row's tail. -/
theorem keptRow_tail (x : ℕ) (k k' : Option K) (q : Fin s.C.r) :
    keptRow s K x (.inl (k, ())) (.inr (.inl (k', q))) = if k' = k then wT s.C x q.val else 0 :=
  rfl

/-- The carried mask row's and the fresh mask row's messages. -/
theorem keptRow_maskMsg (x : ℕ) (j : Fin s.Z.l) :
    keptRow s K x (.inr (.inl ())) (.inl (.inr (.inl j))) = wM s.Z (Fmt.M1.cp s.Z x) j.val ∧
      keptRow s K x (.inr (.inr ())) (.inl (.inr (.inr j))) = wM s.Z (Fmt.M1.cp s.Z x) j.val :=
  ⟨rfl, rfl⟩

/-- Their tails. -/
theorem keptRow_maskTail (x : ℕ) (q : Fin s.Z.r) :
    keptRow s K x (.inr (.inl ())) (.inr (.inr (.inl q))) = wT s.Z (Fmt.M1.cp s.Z x) q.val ∧
      keptRow s K x (.inr (.inr ())) (.inr (.inr (.inr q))) = wT s.Z (Fmt.M1.cp s.Z x) q.val :=
  ⟨rfl, rfl⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.row_kept
#print axioms OnBytes.Slice.keptRow_msg
#print axioms OnBytes.Slice.keptRow_maskTail
