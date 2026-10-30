-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/RowsAtPlan.lean: THE FIRST PROOF CHAIN'S ROWS (P5T.firstRows of
Johnson.G.sendRowsOf's value) HAVE, SENDING BY SENDING AND PLACE BY PLACE, THE SHAPES OF THE PLAN'S
SEATS WITH A SAMPLE (P5T.mineAt of P5T.planSeats): by the two texts, where the list of sendings'
one chain of the file "proof" with number 0 is the public part's own Z.made.proof.1. Theorems. No
value is evaluated; no scope; no pin.

  filter_key, flat_filter, range_getD, filter_idx   four facts on lists
  first_rows_shapes the first chain's rows' sampled shapes are that chain's sendings' sampled shapes
  mine_shapes       the plan's seats with a sample of sending k have the shapes of the sampled
                    messages of the k-th sending of Z.made.proof.1, in order
  rows_at_plan      THE END: at every sending k that has a seat with a sample: the k-th row of the
                    first chain is there, and its sampled shapes are these seats' shapes

Limits. Two premises stay: that sendRowsOf returns, and hP: of the list of sendings' chains just
Z.made.proof.1 bears ("proof", 0). Nothing on the radii. No soundness statement.

-/
import Johnson.Top.H0.Opts.RowsShapes
import Johnson.P5T.MembersByMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts

open OnBytes OnBytes.Params
open Johnson.G (Sending ChainSends SendRow sendsOf sendRowsOf)
open P5T (PSeat planSeats mineAt firstRows)

theorem filter_key {α β κ ν : Type} (key : α → κ) (v : α → ν) (key' : β → κ) (v' : β → ν)
    (P : κ → Bool) : ∀ (a : List α) (b : List β),
    a.map (fun r => (key r, v r)) = b.map (fun c => (key' c, v' c)) →
      (a.filter fun r => P (key r)).map v = (b.filter fun c => P (key' c)).map v'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := filter_key key v key' v' P a b h3
    simp only [List.filter_cons, h1]
    split
    · simp only [List.map_cons, h2, ih]
    · exact ih

theorem flat_filter (P : ChainSends → Bool) : ∀ l : List ChainSends,
    ((l.flatMap fun c => c.sends.map fun x => (c, x)).filter fun cx => P cx.1) =
      (l.filter P).flatMap fun c => c.sends.map fun x => (c, x)
  | [] => rfl
  | c :: l => by
    rw [List.flatMap_cons, List.filter_append, flat_filter P l, List.filter_cons]
    cases h : P c with
    | true =>
      rw [if_pos rfl, List.flatMap_cons]
      congr 1
      refine List.filter_eq_self.2 fun cx hcx => ?_
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hcx
      exact h
    | false =>
      rw [if_neg (by simp)]
      have : ((c.sends.map fun x => (c, x)).filter fun cx => P cx.1) = [] := by
        refine List.filter_eq_nil_iff.2 fun cx hcx => ?_
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 hcx
        simp [h]
      rw [this, List.nil_append]

theorem range_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Of a list made entry by entry, each entry's members bearing the entry's number: the members
that bear the number k are the k-th entry's. -/
theorem filter_idx {α : Type} (f : α × ℕ → List PSeat) (hf : ∀ s, ∀ p ∈ f s, p.send = s.2)
    (k : ℕ) : ∀ (l : List α) (n : ℕ),
    ((l.zipIdx n).flatMap f).filter (fun p => p.send == k && p.smpd) =
      if n ≤ k then ((l[k - n]?).map fun x => (f (x, k)).filter (·.smpd)).getD [] else []
  | [], n => by simp
  | x :: l, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, filter_idx f hf k l (n + 1)]
    rcases Nat.lt_trichotomy n k with h | h | h
    · have e1 : (f (x, n)).filter (fun p => p.send == k && p.smpd) = [] := by
        refine List.filter_eq_nil_iff.2 fun p hp => ?_
        have := hf (x, n) p hp
        have hne : p.send ≠ k := by
          rw [this]
          exact Nat.ne_of_lt h
        simp [hne]
      rw [e1, List.nil_append, if_pos (by omega), if_pos (by omega)]
      rw [show k - n = (k - (n + 1)) + 1 by omega, List.getElem?_cons_succ]
    · subst h
      have e1 : (f (x, n)).filter (fun p => p.send == n && p.smpd) =
          (f (x, n)).filter (·.smpd) := by
        refine List.filter_congr fun p hp => ?_
        rw [hf (x, n) p hp]
        simp
      rw [e1, if_neg (by omega), if_pos (Nat.le_refl n), Nat.sub_self, List.append_nil]
      rfl
    · have e1 : (f (x, n)).filter (fun p => p.send == k && p.smpd) = [] := by
        refine List.filter_eq_nil_iff.2 fun p hp => ?_
        have := hf (x, n) p hp
        have hne : p.send ≠ k := by
          rw [this]
          exact Nat.ne_of_gt h
        simp [hne]
      rw [e1, List.nil_append, if_neg (by omega), if_neg (by omega)]

/-- **The first chain's rows' sampled shapes.** -/
theorem first_rows_shapes {pol lay KL : ByteArray} {rows : List SendRow} {sends : List ChainSends}
    {p0 : ChainSends} (hr : sendRowsOf pol lay KL = .ok rows) (hs : sendsOf pol lay KL = .ok sends)
    (hP : sends.filter (fun c => c.file == "proof" && c.chain == 0) = [p0]) :
    (firstRows rows).map (fun r => r.sampled.map fun z => z.1) = p0.sends.map sampledOf := by
  have h := filter_key (fun r : SendRow => (r.file, r.chain)) (fun r => r.sampled.map fun z => z.1)
    (fun cx : ChainSends × Sending => (cx.1.file, cx.1.chain)) (fun cx => sampledOf cx.2)
    (fun q => q.1 == "proof" && q.2 == 0) _ _ (rows_shapes hr hs)
  have e := flat_filter (fun c => c.file == "proof" && c.chain == 0) sends
  rw [hP] at e
  unfold firstRows
  refine h.trans ?_
  rw [e]
  simp [List.map_map, Function.comp_def]

/-- **The plan's seats with a sample of sending k.** -/
theorem mine_shapes (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (k : ℕ)
    (hne : mineAt (planSeats Z dl) k ≠ []) :
    ∃ x, Z.made.proof.1.sends[k]? = some x ∧
      (mineAt (planSeats Z dl) k).map (·.shape) = sampledOf x := by
  unfold mineAt planSeats at hne ⊢
  dsimp only at hne ⊢
  rw [filter_idx _ (by
    rintro ⟨x, n⟩ p hp
    dsimp only at hp
    split at hp
    · cases hp
    · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp
      rfl) k _ 0] at hne ⊢
  simp only [Nat.zero_le, if_true, Nat.sub_zero] at hne ⊢
  cases hx : Z.made.proof.1.sends[k]? with
  | none =>
    rw [hx] at hne
    exact absurd rfl hne
  | some x =>
    rw [hx] at hne
    refine ⟨x, rfl, ?_⟩
    simp only [Option.map_some, Option.getD_some] at hne ⊢
    cases hl : OnBytes.layTrees Z.made.proof.1.codes x.sent.toArray with
    | none =>
      rw [hl] at hne
      exact absurd rfl hne
    | some lay =>
      dsimp only
      unfold sampledOf
      conv_rhs => rw [← range_getD x.sent default]
      simp only [List.filter_map, List.map_map, List.length_map, List.length_range]
      rfl

/-- **THE END.** -/
theorem rows_at_plan {pol lay KL : ByteArray} {rows : List SendRow} {sends : List ChainSends}
    (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (hr : sendRowsOf pol lay KL = .ok rows)
    (hs : sendsOf pol lay KL = .ok sends)
    (hP : sends.filter (fun c => c.file == "proof" && c.chain == 0) = [Z.made.proof.1]) (k : ℕ)
    (hne : mineAt (planSeats Z dl) k ≠ []) :
    ((firstRows rows)[k]?).map (fun r => r.sampled.map fun z => z.1) =
      some ((mineAt (planSeats Z dl) k).map (·.shape)) := by
  obtain ⟨x, hx, e⟩ := mine_shapes Z dl k hne
  rw [e, ← List.getElem?_map, first_rows_shapes hr hs hP, List.getElem?_map, hx]
  rfl

end P1Opts

#print axioms P1Opts.first_rows_shapes
#print axioms P1Opts.mine_shapes
#print axioms P1Opts.rows_at_plan
