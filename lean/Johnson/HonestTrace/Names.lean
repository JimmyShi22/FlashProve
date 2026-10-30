-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Names.lean

Names for the segments of a proof and for a segment's matrices of cells, with their numbers.

The byte format's pages on the three sorts of segment (docs/format/11-2, 11-3, 11-4) give each
segment a fixed list of matrices of cells, in this order: af, ad, ar, b, qa, xbO, xbI in a
feed-forward segment; as, ah, ao, bA, qa in an attention segment; hf, hd, hr, bH, xbL in the output
head. The matrices af, ad, as and hf lie in NAf, NAd, NAs and NHf parts (one or more), and each part
has a number of its own in the list. This file types these names, says which number a name has, and
spells a name as a string. It reads no file. The number of groups and the four numbers of parts are
arguments, but for one theorem at the reference model's four numbers (3, 1, 1, 4); that these are
the numbers of the public files in the goals' scope is "parts_in_scope"
(Johnson/Goal/HonestTrace/FullInScope.lean).

Main definitions and theorems:
* "Seg", "Seg.no", "Seg.ofNo": a segment; its number among the sub-proofs, from 0 (group g's
  feed-forward segment 2 g, its attention segment 2 g + 1, the head 2 G at G groups); the way back.
* "MatName", "MatName.no?": a matrix's name, a part being named with its number from 0; its number
  in the list of a segment. There is no number ("none") for a name that is not of the segment's
  sort, and none for a part beyond the parts.
* "MatName.label": the name as a string: a part is spelt by the name followed by the part's number
  in decimal digits ("af0", "af1", "as0", "hf3"), the others as above.
* "MatName.all", "MatName.ofLabel?": the names that have a number in a segment, in the order of
  their numbers; the first of them with a given label.
* "Seg.ofNo_no", "Seg.of_ofNo": "Seg.ofNo" undoes "Seg.no" at a group below G and at the head, and
  returns such segments alone, with the number asked for.
* "Seg.no_inj": two such segments with one number are one segment.
* "MatName.no?_inj": in one segment two names with one number are one name.
* "MatName.mem_all_of_no?": a name with a number in a segment's list is in "MatName.all".
* "MatName.ofLabel?_label_ref": at the reference model's numbers of parts (3, 1, 1, 4) every name of
  a segment's list is found by its own label.

Limits. The format's pages name the whole matrices alone, and the arrays that hold the parts by the
letter M and the number mu. The spelling of a part is that of the names which this library's
verifier gives the entries of its lists for the smallness test (OnBytes/Model/LayerPlan.lean,
AttentionPlan.lean, HeadPlan.lean). By a reading of its source the C++ verifier spells the parts of
af, ad, as and hf so too (verifier/src/cp_verify.cpp, vf_attention_check.h,
vf_output_head_plan.inc). No theorem of this file compares the labels with any of these
texts; for public files in the goals' scope Johnson/Goal/HonestTrace/FullInScope.lean shows that the
entries of the library's plans bear them ("planName_ff_in_scope" and its two like). That two names
of one list have two labels is shown at the reference model's numbers of parts alone.

Not claimed: anything on a proof, a prover or a verifier.

-/

set_option autoImplicit false

namespace OnBytes.HonestTrace

/-! ## Segments -/

/-- **A segment of the proof**: the feed-forward segment of a group of layers, the attention segment
of a group, or the output head. No bound is asked of the group's number. -/
inductive Seg
  | ff (g : Nat)
  | att (g : Nat)
  | head
  deriving DecidableEq, Repr

/-- The segment's number among the sub-proofs, from 0, in a proof with G groups of layers. -/
def Seg.no (G : Nat) : Seg → Nat
  | .ff g => 2 * g
  | .att g => 2 * g + 1
  | .head => 2 * G

/-- The segment is one of a proof with G groups of layers. -/
def Seg.Below (G : Nat) : Seg → Prop
  | .ff g => g < G
  | .att g => g < G
  | .head => True

/-- The segment with the number k in a proof with G groups of layers; "none" beyond the head. -/
def Seg.ofNo (G k : Nat) : Option Seg :=
  if k = 2 * G then some .head
  else if 2 * G < k then none
  else if k % 2 = 0 then some (.ff (k / 2))
  else some (.att (k / 2))

/-- "Seg.ofNo" undoes "Seg.no" at every segment of a proof with G groups. -/
theorem Seg.ofNo_no {G : Nat} {σ : Seg} (h : σ.Below G) : Seg.ofNo G (σ.no G) = some σ := by
  cases σ with
  | ff g =>
    have hg : g < G := h
    show Seg.ofNo G (2 * g) = _
    unfold Seg.ofNo
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]
  | att g =>
    have hg : g < G := h
    show Seg.ofNo G (2 * g + 1) = _
    unfold Seg.ofNo
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * g + 1) / 2 = g by omega]
  | head => exact if_pos rfl

/-- Two segments of a proof with G groups that have one number are one segment. -/
theorem Seg.no_inj {G : Nat} {σ τ : Seg} (hσ : σ.Below G) (hτ : τ.Below G)
    (h : σ.no G = τ.no G) : σ = τ :=
  Option.some.inj ((Seg.ofNo_no hσ).symm.trans ((congrArg (Seg.ofNo G) h).trans (Seg.ofNo_no hτ)))

/-- What "Seg.ofNo" returns is a segment of a proof with G groups, and has the number asked for. -/
theorem Seg.of_ofNo {G k : Nat} {σ : Seg} (h : Seg.ofNo G k = some σ) :
    σ.Below G ∧ σ.no G = k := by
  unfold Seg.ofNo at h
  by_cases h1 : k = 2 * G
  · rw [if_pos h1] at h
    obtain rfl := Option.some.inj h
    exact ⟨trivial, h1.symm⟩
  · rw [if_neg h1] at h
    by_cases h2 : 2 * G < k
    · rw [if_pos h2] at h
      exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : k % 2 = 0
      · rw [if_pos h3] at h
        obtain rfl := Option.some.inj h
        exact ⟨show k / 2 < G by omega, show 2 * (k / 2) = k by omega⟩
      · rw [if_neg h3] at h
        obtain rfl := Option.some.inj h
        exact ⟨show k / 2 < G by omega, show 2 * (k / 2) + 1 = k by omega⟩

/-! ## Matrices -/

/-- **The name of a matrix of cells in a segment's list.** A part of af, ad, as or hf is named with
its number, from 0. The name qa serves in a feed-forward segment, which owns that matrix, and in an
attention segment, which borrows it. xbI is the stream that enters a group (from group 1 on it is
borrowed), xbL the stream that the head borrows. -/
inductive MatName
  | af (part : Nat) | ad (part : Nat) | ar | b | qa | xbO | xbI
  | as (part : Nat) | ah | ao | bA
  | hf (part : Nat) | hd | hr | bH | xbL
  deriving DecidableEq, Repr

/-- **The number of a name in the list of a segment**, where af, ad, as and hf lie in NAf, NAd, NAs
and NHf parts. "none" for a name that is not of the segment's sort and for a part beyond the parts.
-/
def MatName.no? (NAf NAd NAs NHf : Nat) : Seg → MatName → Option Nat
  | .ff _, .af p => if p < NAf then some p else none
  | .ff _, .ad p => if p < NAd then some (NAf + p) else none
  | .ff _, .ar => some (NAf + NAd)
  | .ff _, .b => some (NAf + NAd + 1)
  | .ff _, .qa => some (NAf + NAd + 2)
  | .ff _, .xbO => some (NAf + NAd + 3)
  | .ff _, .xbI => some (NAf + NAd + 4)
  | .att _, .as p => if p < NAs then some p else none
  | .att _, .ah => some NAs
  | .att _, .ao => some (NAs + 1)
  | .att _, .bA => some (NAs + 2)
  | .att _, .qa => some (NAs + 3)
  | .head, .hf p => if p < NHf then some p else none
  | .head, .hd => some NHf
  | .head, .hr => some (NHf + 1)
  | .head, .bH => some (NHf + 2)
  | .head, .xbL => some (NHf + 3)
  | _, _ => none

/-- In one segment two names with one number are one name: no part runs into the next matrix. -/
theorem MatName.no?_inj {NAf NAd NAs NHf : Nat} {σ : Seg} {μ ν : MatName} {a : Nat}
    (hμ : MatName.no? NAf NAd NAs NHf σ μ = some a)
    (hν : MatName.no? NAf NAd NAs NHf σ ν = some a) : μ = ν := by
  cases σ <;> cases μ <;> cases ν <;> simp only [MatName.no?] at hμ hν <;>
    first
      | rfl
      | (exfalso; split at hμ <;> split at hν <;> simp at hμ hν <;> omega)
      | (exfalso; split at hμ <;> simp at hμ hν <;> omega)
      | (exfalso; split at hν <;> simp at hμ hν <;> omega)
      | (exfalso; simp at hμ hν <;> omega)
      | (split at hμ <;> split at hν <;> simp at hμ hν ⊢ <;> omega)

/-- **The name as a string.** A part is spelt by the matrix's name followed by the part's number in
decimal digits. -/
def MatName.label : MatName → String
  | .af p => "af" ++ toString p
  | .ad p => "ad" ++ toString p
  | .ar => "ar"
  | .b => "b"
  | .qa => "qa"
  | .xbO => "xbO"
  | .xbI => "xbI"
  | .as p => "as" ++ toString p
  | .ah => "ah"
  | .ao => "ao"
  | .bA => "bA"
  | .hf p => "hf" ++ toString p
  | .hd => "hd"
  | .hr => "hr"
  | .bH => "bH"
  | .xbL => "xbL"

/-- The names that have a number in the list of a segment, in the order of their numbers. -/
def MatName.all (NAf NAd NAs NHf : Nat) : Seg → List MatName
  | .ff _ => (List.range NAf).map .af ++ (List.range NAd).map .ad ++ [.ar, .b, .qa, .xbO, .xbI]
  | .att _ => (List.range NAs).map .as ++ [.ah, .ao, .bA, .qa]
  | .head => (List.range NHf).map .hf ++ [.hd, .hr, .bH, .xbL]

/-- The first name of a segment's list that has the label s; "none" if none has. -/
def MatName.ofLabel? (NAf NAd NAs NHf : Nat) (σ : Seg) (s : String) : Option MatName :=
  (MatName.all NAf NAd NAs NHf σ).find? fun μ => μ.label == s

/-- At the reference model's numbers of parts (3, 1, 1, 4) every name of a segment's list is found
by its own label: no two names of one list have one label there. -/
theorem MatName.ofLabel?_label_ref (σ : Seg) :
    ∀ μ ∈ MatName.all 3 1 1 4 σ, MatName.ofLabel? 3 1 1 4 σ μ.label = some μ := by
  cases σ with
  | ff g =>
    exact (by decide : ∀ μ ∈ MatName.all 3 1 1 4 (.ff 0),
      MatName.ofLabel? 3 1 1 4 (.ff 0) μ.label = some μ)
  | att g =>
    exact (by decide : ∀ μ ∈ MatName.all 3 1 1 4 (.att 0),
      MatName.ofLabel? 3 1 1 4 (.att 0) μ.label = some μ)
  | head => decide

/-- A name that has a number in a segment's list is a member of "MatName.all". -/
theorem MatName.mem_all_of_no? {NAf NAd NAs NHf : Nat} {σ : Seg} {μ : MatName} {a : Nat}
    (h : MatName.no? NAf NAd NAs NHf σ μ = some a) : μ ∈ MatName.all NAf NAd NAs NHf σ := by
  cases σ <;> cases μ <;> simp only [MatName.no?] at h <;>
    first
      | (simp [MatName.all]; done)
      | (split at h <;> simp_all [MatName.all]; done)
      | (simp at h; done)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.MatName.ofLabel?_label_ref
#print axioms OnBytes.HonestTrace.MatName.mem_all_of_no?
#print axioms OnBytes.HonestTrace.Seg.ofNo_no
#print axioms OnBytes.HonestTrace.Seg.no_inj
#print axioms OnBytes.HonestTrace.Seg.of_ofNo
#print axioms OnBytes.HonestTrace.MatName.no?_inj
