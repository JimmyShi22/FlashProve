-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchRowsAt.lean: the closing of a segment (K10): where the lot's job returns the group's
rows, member number i of them, in one sentence: it is `memberOf` of the shape that the segment's public data have at that
number, with a mark "kept", and of the rows that the shared text of a message's rows (`messageRows`,
Honest/K2/Sending.lean) returned at that shape, at the member's data, and at the carried stretch of the number
(the stretches of the segments in front) + i. For the field tie of `CarryOwed` (Honest/K10/Xch/CarryTop.lean).

  `mapM_len`         `mapM` returns as many as it was given
  `rowsCore_flags`   where the text of a segment's group's rows returns, there is one mark "kept" for each member
  `seg_member_at`    member number i of what that text returns without the fresh mask
  **`lot_member_at`**  member number i of what the lot's job returns

Limits. Implications from "the job returns". What a member's data are is a letter of the sentence (a.2): it is not read here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchRowsInv
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchCongr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K2.Honest (GroupMember Left)
open Johnson.Prover.Send (Rows)
open ProofFile.Honest.K2 (SegmentPub GroupRows Stretch FreshTable groupRowsOf segmentGroupRows closingFrom messageRows freshTable)
open ProofFile.Honest.K2.Law (Laid rowsCore inFirstOf laterOf segmentRows_eq)
open ProofFile.Honest.K2.Reads (bind_ok bind_ok' ite_eq)

/-- `mapM` returns as many as it was given. -/
theorem mapM_len {α β : Type} (g : α → Except String β) : ∀ (l : List α) (r : List β),
    l.mapM g = .ok r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, _, h⟩ := bind_ok h
    obtain ⟨r', h2, h⟩ := bind_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    rw [List.length_cons, List.length_cons, mapM_len g l r' h2]

/-- Where the text returns, there is one mark "kept" for each member. -/
theorem rowsCore_flags {table : FreshTable} {S : SegmentPub} {ps : Bool} {prevKept : List OnBytes.OracleShape}
    {A : List Laid} {B : List Laid × Nat} {k : Nat → Except String Stretch} {base : Nat} {wf : Bool} {GR : GroupRows}
    (h : rowsCore table S ps prevKept A B k base wf = .ok GR) :
    (segFlags S ps).length = A.length + B.1.length := by
  unfold rowsCore at h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  rcases ite_eq h with ⟨_, h⟩ | ⟨h5, _⟩
  · cases h
  exact Decidable.byContradiction fun hx => h5 (bne_iff_ne.2 hx)

/-- Member number i of what the text of a segment's group's rows returns without the fresh mask. -/
theorem seg_member_at {table : FreshTable} {S : SegmentPub} {ps : Bool} {prevKept : List OnBytes.OracleShape}
    {A : List Laid} {B : List Laid × Nat} {k : Nat → Except String Stretch} {base : Nat} {GR : GroupRows}
    (h : rowsCore table S ps prevKept A B k base false = .ok GR) (hA : A.length = (S.sent.headD #[]).size - 1)
    {i : Nat} {a : Laid} (hi : (A ++ B.1)[i]? = some a) :
    ∃ (flag : Bool) (Rr : Rows) (kk : Stretch), GR.members[i]? = some ⟨a.1, flag⟩ ∧ GR.rows[i]? = some Rr ∧
      k (base + i) = .ok kk ∧ messageRows table S.sizes.codes a.1 none a.2 kk = .ok Rr := by
  obtain ⟨rows₀, rows₁, h0, h1, hm, hr⟩ := rowsCore_inv h
  have hfl := rowsCore_flags h
  have l0 : rows₀.length = A.length := by rw [mapM_len _ _ _ h0, List.length_zipIdx]
  have hlt : i < (A ++ B.1).length := (List.getElem?_eq_some_iff.1 hi).1
  have hltf : i < (segFlags S ps).length := by
    rw [hfl, ← List.length_append]
    exact hlt
  have hmem : GR.members[i]? = some ⟨a.1, (segFlags S ps)[i]⟩ := by
    have hz : (((A ++ B.1).map (·.1)).zip (segFlags S ps))[i]? = some (a.1, (segFlags S ps)[i]) :=
      List.getElem?_zip_eq_some.2 ⟨by rw [List.getElem?_map, hi]; rfl, List.getElem?_eq_getElem hltf⟩
    rw [hm, List.getElem?_map, hz]
    rfl
  by_cases c : i < A.length
  · have hiA : A[i]? = some a := by rwa [List.getElem?_append_left c] at hi
    obtain ⟨Rr, e1, e2⟩ := rows_at_first (rows₁ := rows₁) h0 hiA
    have e2' : (k (base + i)).bind (messageRows table S.sizes.codes a.1 none a.2) = .ok Rr := e2
    obtain ⟨kk, hk, hmsg⟩ := bind_ok' e2'
    exact ⟨_, Rr, kk, hmem, by rw [hr]; exact e1, hk, hmsg⟩
  · have hle : A.length ≤ i := Nat.le_of_not_lt c
    have hiB : B.1[i - A.length]? = some a := by rwa [List.getElem?_append_right hle] at hi
    obtain ⟨Rr, e1, e2⟩ := rows_at_later (rows₀ := rows₀) l0 h1 hiB
    have e2' : (k (base + ((S.sent.headD #[]).size - 1) + 0 + (i - A.length))).bind
        (messageRows table S.sizes.codes a.1 none a.2) = .ok Rr := e2
    have en : base + ((S.sent.headD #[]).size - 1) + 0 + (i - A.length) = base + i := by
      rw [← hA]
      omega
    rw [en] at e2'
    obtain ⟨kk, hk, hmsg⟩ := bind_ok' e2'
    have ei : A.length + (i - A.length) = i := by omega
    rw [ei] at e1
    exact ⟨_, Rr, kk, hmem, by rw [hr]; exact e1, hk, hmsg⟩

variable {W₀ Rc Xi Tr : Type}

/-- **Member number i of what the lot's job returns.** -/
theorem lot_member_at (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (w : Local W₀ Rc Xi Tr) (front : List Fmt.Drawn)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Z G Q).pub)) {R : GroupData}
    (h : (lotJob readers rows stAt Z G Q).rows w front ca = .ok R) :
    ∃ (S : SegmentPub) (x : Option (Left × List OnBytes.OracleShape) × Nat),
      (lotSegs Z G Q).getLast? = some S ∧ R.codes = S.sizes.codes ∧
      closingFrom freshTable (lotOwn readers rows Z G Q w front) front (Stretch.carried _ ca)
        (lotSegs Z G Q).dropLast 0 0 none = .ok x ∧
      ∀ (i : Nat) (a : Laid),
        (inFirstOf S (x.1.map (·.1)) (lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1)) ++
          (laterOf S (x.1.map (·.1)).isSome
            (lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1))).1)[i]? = some a →
        ∃ (flag : Bool) (Rr : Rows) (kk : Stretch), R.members[i]? = some (memberOf ⟨a.1, flag⟩ Rr) ∧
          Stretch.carried _ ca (x.2 + i) = .ok kk ∧ messageRows freshTable R.codes a.1 none a.2 kk = .ok Rr := by
  obtain ⟨S, GR, hL, hG, rfl⟩ := lot_rows_inv readers rows stAt Z G Q w front ca h
  obtain ⟨x, hx, hS⟩ := groupRows_inv hL hG
  refine ⟨S, x, hL, rfl, hx, fun i a hi => ?_⟩
  rw [segmentRows_eq] at hS
  obtain ⟨flag, Rr, kk, h1, h2, h3, h4⟩ := seg_member_at hS (inFirst_length S _ _) hi
  exact ⟨flag, Rr, kk, out_at S GR h1 h2, h3, h4⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mapM_len
#print axioms ProofFile.Honest.K10.rowsCore_flags
#print axioms ProofFile.Honest.K10.seg_member_at
#print axioms ProofFile.Honest.K10.lot_member_at
