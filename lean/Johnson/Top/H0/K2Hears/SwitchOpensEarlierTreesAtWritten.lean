-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/SwitchOpensEarlierTreesAtWritten.lean: the code switch: the field "old" of the switch's premise
on the keys (ColsAtStageFirst.lean's hOld: the stretch's data open trees below the stretch's base
alone), and "the base is at most the first chain's number of trees", at every piece of a row that
tiles the first chain of the written data of the full size. A test with code, its law, its value at
the written data by Lean's kernel, and two controls.

How. The switch declares two rounds, named "SEND seed" and "LOC". `oldFrom n ds` walks a chain's
data with the number of trees sent so far, and asks at each such pair that neither round opens a
tree which is not sent in front of the pair. A row of pieces that tiles the chain cuts its data into
stretches, and a piece's base is the number of trees sent in front of its stretch (`tiled_split`).

  `oldFrom`        the test · `pairsFrom`: how many pairs it looks at
  `oldFrom_tail`, `oldFrom_split`: what its yes says at a pair, wherever the pair stands in the list
  `tiled_split`    a piece of a tiling row: its stretch's place in the row's data, and its base
  `old_of_tiled`   THE LAW: from the test's yes on the row's data
  `old_proofFull`, `old_written`: THE VALUE: yes, at the written data of the full size
  `pairs_proofFull`: it looks at 25 pairs there · `old_can_fail`: begun in the midst of that list,
                   with no tree counted, it says no
  `old_in_scope`   in the goals' scope, at the laid data D
Limits. The premise that the row's first piece has the base 0 is not shown here. That a place's
block declares the switch's two rounds is another file's. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.FrameInScope
import Johnson.Desc.Sound.ChainRule
import Johnson.Desc.Sound.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (Frame Piece Tiled rowData nTrees)
open _root_.Run.PQ (CK)
open Johnson.G (force force_eq writtenPFull dProofFull writtenPFull_eq)
open LPFD.Full (proofDataAndDecisionOfPublicFiles laidPOf_written RunPF)

/-- **The test.** n: the number of trees sent in front of the list. -/
def oldFrom : Nat → List RDT → Bool
  | _, [] => true
  | n, d :: ds =>
    (match ds with
      | d' :: _ =>
        !(d.entry.name == "SEND seed" && d'.entry.name == "LOC") ||
          (d.opens.all (fun j => decide (j < n)) && d'.opens.all fun j => decide (j < n))
      | [] => true) &&
    force (n + d.trees.length) fun v => oldFrom v ds

/-- How many pairs the test looks at. -/
def pairsFrom : Nat → List RDT → Nat
  | a, [] => a
  | a, d :: ds =>
    force (match ds with
      | d' :: _ => if d.entry.name == "SEND seed" && d'.entry.name == "LOC" then a + 1 else a
      | [] => a) fun v => pairsFrom v ds

/-- The test's yes goes on behind the first round, with that round's trees counted. -/
theorem oldFrom_tail (n : Nat) (d : RDT) (ds : List RDT) (h : oldFrom n (d :: ds) = true) :
    oldFrom (n + d.trees.length) ds = true := by
  cases ds with
  | nil => rfl
  | cons d' ds =>
    rw [oldFrom, Bool.and_eq_true, force_eq] at h
    exact h.2

/-- **What the test's yes says at a pair.** -/
theorem oldFrom_split : ∀ (pre : List RDT) (n : Nat) (d₁ d₂ : RDT) (post : List RDT),
    oldFrom n (pre ++ d₁ :: d₂ :: post) = true → d₁.entry.name = "SEND seed" →
    d₂.entry.name = "LOC" → ∀ d ∈ [d₁, d₂], ∀ j ∈ d.opens, j < n + nTrees pre
  | [], n, d₁, d₂, post, h, h1, h2 => by
    rw [List.nil_append, oldFrom, Bool.and_eq_true] at h
    have h3 := h.1
    simp only [h1, h2, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
      Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h3
    intro d hd j hj
    have e : nTrees ([] : List RDT) = 0 := rfl
    rw [e, Nat.add_zero]
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h3.1 j hj
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact h3.2 j hj
      · cases hd
  | d :: pre, n, d₁, d₂, post, h, h1, h2 => by
    rw [List.cons_append] at h
    have ih := oldFrom_split pre (n + d.trees.length) d₁ d₂ post (oldFrom_tail n d _ h) h1 h2
    have e : nTrees (d :: pre) = d.trees.length + nTrees pre := by
      unfold nTrees
      rw [List.map_cons, List.sum_cons]
    intro x hx j hj
    have := ih x hx j hj
    rw [e]
    omega

variable {C : CK} {F : Frame} {S Cl W : Type}

theorem nTrees_append (a b : List RDT) : nTrees (a ++ b) = nTrees a + nTrees b := by
  unfold nTrees
  rw [List.map_append, List.sum_append]

/-- **A piece of a tiling row**: where its stretch stands in the row's data, and its base. -/
theorem tiled_split : ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W), Tiled p l →
    ∀ (k : Nat) (q : Piece C F S Cl W), (p :: l)[k]? = some q →
      ∃ pre post, rowData p l = pre ++ (q.ds ++ post) ∧ q.base = p.base + nTrees pre
  | l, p, _, 0, q, hq => by
    obtain rfl : p = q := by simpa using hq
    exact ⟨[], l.flatMap (·.ds), by simp [rowData], rfl⟩
  | [], _, _, k + 1, q, hq => by simp at hq
  | q' :: l, p, ht, k + 1, q, hq => by
    obtain ⟨-, -, -, hb, ht'⟩ := ht
    have hq' : (q' :: l)[k]? = some q := by simpa using hq
    obtain ⟨pre, post, e, eb⟩ := tiled_split l q' ht' k q hq'
    refine ⟨p.ds ++ pre, post, ?_, ?_⟩
    · have e0 : rowData p (q' :: l) = p.ds ++ rowData q' l := by simp [rowData]
      rw [e0, e, List.append_assoc]
    · rw [eb, hb, nTrees_append]
      have : p.trees = nTrees p.ds := rfl
      omega

/-- **The law.** -/
theorem old_of_tiled (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ht : Tiled p l)
    (hb : p.base = 0) (hO : oldFrom 0 (rowData p l) = true) {k : Nat} {q : Piece C F S Cl W}
    (hq : (p :: l)[k]? = some q) {d₁ d₂ : RDT} (hds : q.ds = [d₁, d₂])
    (h1 : d₁.entry.name = "SEND seed") (h2 : d₂.entry.name = "LOC") :
    (∀ d ∈ q.ds, ∀ j ∈ d.opens, j < q.base) ∧ q.base ≤ nTrees (rowData p l) := by
  obtain ⟨pre, post, e, eb⟩ := tiled_split l p ht k q hq
  rw [hb, Nat.zero_add] at eb
  rw [hds] at e
  refine ⟨?_, ?_⟩
  · rw [e] at hO
    have h := oldFrom_split pre 0 d₁ d₂ post hO h1 h2
    rw [hds, eb]
    intro d hd j hj
    have := h d hd j hj
    omega
  · rw [e, nTrees_append, eb]
    omega

/-! ### The value at the written data of the full size -/

set_option maxRecDepth 1000000 in
theorem old_proofFull : oldFrom 0 dProofFull.ds₁ = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test is not idle there: it looks at 25 pairs. -/
theorem pairs_proofFull : pairsFrom 0 dProofFull.ds₁ = 25 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: begun at the first pair's round with no tree counted, it says no. -/
theorem old_can_fail : oldFrom 0 (dProofFull.ds₁.drop 1980) = false := by decide +kernel

theorem old_written : oldFrom 0 writtenPFull.ds₁ = true := by
  rw [writtenPFull_eq]
  exact old_proofFull

/-- **In the goals' scope, at the laid data.** -/
theorem old_in_scope {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : RunPF}
    (hZ : VerifierAndGoals.InScope Z = true) (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r))
    (p : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ht : Tiled p l) (hb : p.base = 0)
    (hd : rowData p l = D.ds₁) {k : Nat} {q : Piece C F S Cl W} (hq : (p :: l)[k]? = some q)
    {d₁ d₂ : RDT} (hds : q.ds = [d₁, d₂]) (h1 : d₁.entry.name = "SEND seed")
    (h2 : d₂.entry.name = "LOC") :
    (∀ d ∈ q.ds, ∀ j ∈ d.opens, j < q.base) ∧ q.base ≤ 83 := by
  have hO : oldFrom 0 (rowData p l) = true := by
    rw [hd, laidPOf_written hZ h]
    exact old_written
  obtain ⟨a, b⟩ := old_of_tiled p l ht hb hO hq hds h1 h2
  refine ⟨a, ?_⟩
  have e : nTrees (rowData p l) = D.t₁ := by
    rw [hd]
    rfl
  rw [e, t₁_in_scope hZ h] at b
  exact b

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.oldFrom_split
#print axioms VerifiableInference.Desc.First.K2.tiled_split
#print axioms VerifiableInference.Desc.First.K2.old_of_tiled
#print axioms VerifiableInference.Desc.First.K2.old_proofFull
#print axioms VerifiableInference.Desc.First.K2.pairs_proofFull
#print axioms VerifiableInference.Desc.First.K2.old_can_fail
#print axioms VerifiableInference.Desc.First.K2.old_written
#print axioms VerifiableInference.Desc.First.K2.old_in_scope
