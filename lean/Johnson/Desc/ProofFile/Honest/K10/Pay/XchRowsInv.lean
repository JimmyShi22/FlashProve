-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchRowsInv.lean: the closing of a segment (K10): where the lot's job returns the group's
rows, what these rows are: read back through the job's text, stage by stage, down to the one call of the shared text of a
message's rows (`messageRows`, Honest/K2/Sending.lean) that made each member's rows. For the field tie of `CarryOwed`
(Honest/K10/Xch/CarryTop.lean).

  `lot_rows_inv`     the job's rows are `rowsOut` (Pay/MadeParts.lean) of what `groupRowsOf` (Honest/K2/Closing.lean) returned
  `groupRows_inv`    that is what `segmentGroupRows` returned at the last segment, behind the steps over the segments in front
  `segFlags`, `rowsCore_inv`   what `segmentGroupRows`' text (`rowsCore`, Honest/K2/Law/SegmentAlike.lean) returns without the fresh
                   mask: the members; the rows of the first sending's members and of the later sendings' members, each list
                   made by one `mapM`
  `rows_at_first`, `rows_at_later`   the rows of member number i: the shared text's return at the carried stretch of its number
  `out_at`           member number i of `rowsOut` is `memberOf` of member number i and its rows

Limits. Implications from "the job returns". What the data in a member's main rows are is not read here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeParts
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K2.Honest (GroupMember Left)
open Johnson.Prover.Send (Rows)
open ProofFile.Honest.K2 (SegmentPub GroupRows Stretch FreshTable groupRowsOf segmentGroupRows closingFrom messageRows freshTable
  ownReady)
open ProofFile.Honest.K2.Law (Laid rowsCore)
open ProofFile.Honest.K2.Reads (bind_ok bind_ok' ite_eq map_ok mapM_at)

variable {W₀ Rc Xi Tr : Type}

/-- Where the lot's job returns rows, they are `rowsOut` of what the shared text returned. -/
theorem lot_rows_inv (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (w : Local W₀ Rc Xi Tr) (front : List Fmt.Drawn)
    (ca : CsAll (closeCarries (lotJob readers rows stAt Z G Q).pub)) {R : GroupData}
    (h : (lotJob readers rows stAt Z G Q).rows w front ca = .ok R) :
    ∃ (S : SegmentPub) (GR : GroupRows), (lotSegs Z G Q).getLast? = some S ∧
      groupRowsOf freshTable (lotSegs Z G Q) (lotOwn readers rows Z G Q w front) front
        (Stretch.carried _ ca) = .ok GR ∧ R = rowsOut S GR := by
  have h1 : (ownReady (rows w.x) G.first.layout (askPlace (addrsAt Z G)) (lotSegs Z G Q) front).bind
      (fun _ => (heardAll (lotSegs Z G Q) front).bind fun _ =>
        (jobBare (addrsAt Z G) (lotSegs Z G Q) (fun i => i.st Q) ⟨Q, borneAt Z Q⟩).rows
          (closeIn readers rows stAt w) front ca) = .ok R := h
  obtain ⟨_, -, h2⟩ := bind_ok' h1
  obtain ⟨_, -, h3⟩ := bind_ok' h2
  unfold jobBare jobRows at h3
  cases hL : (lotSegs Z G Q).getLast? with
  | none =>
    simp only [hL] at h3
    cases h3
  | some S =>
    simp only [hL] at h3
    rcases ite_eq h3 with ⟨_, h3⟩ | ⟨_, h3⟩
    · cases h3
    rcases ite_eq h3 with ⟨_, h3⟩ | ⟨_, h3⟩
    · cases h3
    rcases ite_eq h3 with ⟨_, h3⟩ | ⟨_, h3⟩
    · cases h3
    obtain ⟨GR, hGR, e⟩ := map_ok h3
    exact ⟨S, GR, rfl, hGR, e.symm⟩

/-- What `groupRowsOf` returns is what `segmentGroupRows` returned at the last segment. -/
theorem groupRows_inv {table : FreshTable} {segs : List SegmentPub} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {GR : GroupRows} {S : SegmentPub}
    (hL : segs.getLast? = some S) (h : groupRowsOf table segs own heard k = .ok GR) :
    ∃ x, closingFrom table own heard k segs.dropLast 0 0 none = .ok x ∧
      segmentGroupRows table S (x.1.map (·.1)) ((x.1.map (·.2)).getD []) (own (segs.length - 1)) k x.2 false =
        .ok GR := by
  unfold groupRowsOf at h
  rw [hL] at h
  exact bind_ok' h

/-- The marks "kept" of a segment's members, in the order of sending. ps: a fold stands in front. -/
def segFlags (S : SegmentPub) (ps : Bool) : List Bool :=
  (if ps then false :: S.sizes.target.kept.toList.map (·.keptAgain) else []) ++ S.ownKept

/-- What the text of `segmentGroupRows` returns where the fresh mask's stretch is not among the stretches. -/
theorem rowsCore_inv {table : FreshTable} {S : SegmentPub} {ps : Bool} {prevKept : List OnBytes.OracleShape}
    {A : List Laid} {B : List Laid × Nat} {k : Nat → Except String Stretch} {base : Nat} {GR : GroupRows}
    (h : rowsCore table S ps prevKept A B k base false = .ok GR) :
    ∃ rows₀ rows₁ : List Rows,
      (A.zipIdx.mapM fun x => (k (base + x.2)).bind (messageRows table S.sizes.codes x.1.1 none x.1.2)) =
        .ok rows₀ ∧
      (B.1.zipIdx.mapM fun x => (k (base + ((S.sent.headD #[]).size - 1) + 0 + x.2)).bind
        (messageRows table S.sizes.codes x.1.1 none x.1.2)) = .ok rows₁ ∧
      GR.members = (((A ++ B.1).map (·.1)).zip (segFlags S ps)).map (fun x => ⟨x.1, x.2⟩) ∧
      GR.rows = rows₀ ++ rows₁ := by
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
  rcases ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨rows₀, h0, h⟩ := bind_ok h
  obtain ⟨rows₁, h1, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  exact ⟨rows₀, rows₁, h0, h1, rfl, rfl⟩

/-- The rows of a member of the first sending. -/
theorem rows_at_first {g : Laid × Nat → Except String Rows} {A : List Laid} {rows₀ rows₁ : List Rows}
    (h0 : A.zipIdx.mapM g = .ok rows₀) {i : Nat} {a : Laid} (hi : A[i]? = some a) :
    ∃ Rr, (rows₀ ++ rows₁)[i]? = some Rr ∧ g (a, i) = .ok Rr := by
  have hz : (A.zipIdx)[i]? = some (a, i) := by
    rw [List.getElem?_zipIdx, hi]
    simp
  obtain ⟨b, hb, hg⟩ := mapM_at g _ _ h0 i (a, i) hz
  refine ⟨b, ?_, hg⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hb).1]
  exact hb

/-- The rows of a member of a later sending. n₀: how many members the first sending has. -/
theorem rows_at_later {g : Laid × Nat → Except String Rows} {B : List Laid} {rows₀ rows₁ : List Rows} {n₀ : Nat}
    (hlen : rows₀.length = n₀) (h1 : B.zipIdx.mapM g = .ok rows₁) {i : Nat} {a : Laid} (hi : B[i]? = some a) :
    ∃ Rr, (rows₀ ++ rows₁)[n₀ + i]? = some Rr ∧ g (a, i) = .ok Rr := by
  have hz : (B.zipIdx)[i]? = some (a, i) := by
    rw [List.getElem?_zipIdx, hi]
    simp
  obtain ⟨b, hb, hg⟩ := mapM_at g _ _ h1 i (a, i) hz
  refine ⟨b, ?_, hg⟩
  rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]
  exact hb

/-- Member number i of `rowsOut`. -/
theorem out_at (S : SegmentPub) (GR : GroupRows) {i : Nat} {g : GroupMember} {Rr : Rows}
    (hg : GR.members[i]? = some g) (hr : GR.rows[i]? = some Rr) :
    (rowsOut S GR).members[i]? = some (memberOf g Rr) := by
  show ((GR.members.zip GR.rows).map fun x => memberOf x.1 x.2)[i]? = _
  have hz : (GR.members.zip GR.rows)[i]? = some (g, Rr) := List.getElem?_zip_eq_some.2 ⟨hg, hr⟩
  rw [List.getElem?_map, hz]
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.lot_rows_inv
#print axioms ProofFile.Honest.K10.groupRows_inv
#print axioms ProofFile.Honest.K10.segFlags
#print axioms ProofFile.Honest.K10.rowsCore_inv
#print axioms ProofFile.Honest.K10.rows_at_first
#print axioms ProofFile.Honest.K10.rows_at_later
#print axioms ProofFile.Honest.K10.out_at
