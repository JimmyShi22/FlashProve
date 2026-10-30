-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchGData.lean: the closing of a segment (K10): the clause on data in the field stand of `TieByShared` (Pay/XchTieByShared.lean), at
a member that a sending of the shared kind (K1) has sent: the shape and the data that the closing's job takes for the member are
the sender's own. General: brought down to public facts on the last segment's list of sendings, one address, one shape, and
the count of challenges that the message's data read. No head, no thread.

  `closingFrom_some`  behind a walk over segments something is left just where something was handed in or a segment was walked
  `ownBase`           the number, among a segment's own messages, of the first message of its later sendings
  `later_two`         the members in two later sendings of one message each
  `first_at`          the members in the first sending of the first segment
  `member_later`, `member_first`   what `LotMember` (Pay/XchOwedMembers.lean) holds at such a place of the list
  **`data_later`**, **`data_first`**   the clause, with `ownBy_job` (Pay/XchData.lean)
  `job_data`          what a job made by `placeJob` (Honest/K1/PlaceJob.lean) reads is one call of its filling

Limits. The public facts are premises here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchOwedMembers
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchData
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieKit
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchCongr
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K2.Honest (Left)
open ProofFile.Honest.K2 (SegmentPub Stretch FreshTable closingFrom freshTable ownBy asRow)
open ProofFile.Honest.K2.Law (Laid inFirstOf laterOf)
open ProofFile.Honest.K2.Reads (bind_ok')

/-- Behind a walk over segments something is left just where something was handed in or a segment
was walked. -/
theorem closingFrom_some {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape))
      (x : Option (Left × List OnBytes.OracleShape) × Nat),
      closingFrom table own heard k segs j base prev = .ok x →
      x.1.isSome = (prev.isSome || !segs.isEmpty)
  | [], _, base, prev, x, h => by
    obtain rfl : (prev, base) = x := Except.ok.inj h
    simp
  | S :: rest, j, base, prev, x, h => by
    have h' : (K2.segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k
        base).bind
        (fun W => closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)) =
        .ok x := h
    obtain ⟨W, -, h2⟩ := bind_ok' h'
    rw [closingFrom_some rest (j + 1) (base + S.messages) (some W) x h2]
    simp

/-- The number, among a segment's own messages, of the first message of its later sendings. ps: a
fold stands in front. -/
def ownBase (S : SegmentPub) (ps : Bool) : Nat :=
  (S.sent.headD #[]).size - 1 - if ps then 1 + S.sizes.kept.length else 0

/-- The members in two later sendings of one message each. -/
theorem later_two {S : SegmentPub} {o₁ o₂ : OnBytes.OracleNotice}
    (hs : S.sent.drop 1 = [#[o₁], #[o₂]]) (ps : Bool) (own : Nat → Nat → Nat → Cb.Gl.E) :
    (laterOf S ps own).1 = [(o₁.shape, own (ownBase S ps + 0)), (o₂.shape, own (ownBase S ps + 1 + 0))] := by
  unfold laterOf
  rw [hs]
  rfl

/-- The members in the first sending of the first segment. -/
theorem first_at (S : SegmentPub) (own : Nat → Nat → Nat → Cb.Gl.E) (i : Nat) :
    (inFirstOf S none own)[i]? =
      (((S.sent.headD #[]).toList.take ((S.sent.headD #[]).size - 1))[i]?).map fun o =>
        (o.shape, own i) := by
  unfold inFirstOf
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases ((S.sent.headD #[]).toList.take ((S.sent.headD #[]).size - 1))[i]? with
  | none => rfl
  | some o =>
    show some (o.shape, own (0 + i)) = some (o.shape, own i)
    rw [Nat.zero_add]

variable {W₀ Rc Xi Tr : Type}

/-- What `LotMember` holds at the place of a later sending's message. -/
theorem member_later {readers : Local W₀ Rc Xi Tr → Readers} {rows : RowDataOf Xi} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {Q : Par} {w : Local W₀ Rc Xi Tr} {front : List Fmt.Drawn}
    {ca : CsAll (closeCarries ⟨Q, borneAt Z Q⟩)} {S : SegmentPub}
    (hLast : (lotSegs Z G Q).getLast? = some S) {o₁ o₂ : OnBytes.OracleNotice}
    (hs : S.sent.drop 1 = [#[o₁], #[o₂]]) {t : Nat} {a : Laid} {nn : Nat}
    (hL : LotMember readers rows Z G Q w front ca ((S.sent.headD #[]).size - 1 + t) a nn) :
    [(o₁.shape, lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1)
        (ownBase S (!(lotSegs Z G Q).dropLast.isEmpty) + 0)),
      (o₂.shape, lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1)
        (ownBase S (!(lotSegs Z G Q).dropLast.isEmpty) + 1 + 0))][t]? = some a := by
  obtain ⟨S', x, hLast', hx, hget, -⟩ := hL
  obtain rfl : S = S' := Option.some.inj (hLast.symm.trans hLast')
  have hps : (x.1.map (·.1)).isSome = !(lotSegs Z G Q).dropLast.isEmpty := by
    rw [Option.isSome_map, closingFrom_some _ _ _ _ _ hx]
    rfl
  rw [hps, List.getElem?_append_right (by rw [inFirst_length]; exact Nat.le_add_right _ _),
    inFirst_length, Nat.add_sub_cancel_left, later_two hs] at hget
  exact hget

/-- What `LotMember` holds at a place of the first segment's first sending. -/
theorem member_first {readers : Local W₀ Rc Xi Tr → Readers} {rows : RowDataOf Xi} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {Q : Par} {w : Local W₀ Rc Xi Tr} {front : List Fmt.Drawn}
    {ca : CsAll (closeCarries ⟨Q, borneAt Z Q⟩)} {S : SegmentPub}
    (hLast : (lotSegs Z G Q).getLast? = some S) (hOne : (lotSegs Z G Q).dropLast = []) {i : Nat}
    (hi : i < (S.sent.headD #[]).size - 1) {a : Laid} {nn : Nat}
    (hL : LotMember readers rows Z G Q w front ca i a nn) :
    ∃ o, (S.sent.headD #[])[i]? = some o ∧
      a = (o.shape, lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1) i) := by
  obtain ⟨S', x, hLast', hx, hget, -⟩ := hL
  obtain rfl : S = S' := Option.some.inj (hLast.symm.trans hLast')
  rw [hOne] at hx
  obtain rfl : ((none : Option (Left × List OnBytes.OracleShape)), 0) = x := Except.ok.inj hx
  rw [List.getElem?_append_left (by rw [inFirst_length]; exact hi)] at hget
  have hget' : (inFirstOf S none
      (lotOwn readers rows Z G Q w front ((lotSegs Z G Q).length - 1)))[i]? = some a := hget
  rw [first_at, List.getElem?_take_of_lt hi] at hget'
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hget'
  exact ⟨o, by rw [← Array.getElem?_toList]; exact ho, rfl⟩

/-- **The clause on data at a later sending's message.** D': the sender's own filling; ad: the message's
address; sh: its shape; fr: how many challenges had been heard when it was sent. -/
theorem data_later {readers : Local W₀ Rc Xi Tr → Readers} {rows : RowDataOf Xi} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {Q : Par} {w : Local W₀ Rc Xi Tr} {front : List Fmt.Drawn}
    {ca : CsAll (closeCarries ⟨Q, borneAt Z Q⟩)} {S : SegmentPub}
    (hLast : (lotSegs Z G Q).getLast? = some S) {o₁ o₂ : OnBytes.OracleNotice}
    (hs : S.sent.drop 1 = [#[o₁], #[o₂]]) {t : Nat} (ht : t < 2) {a : Laid} {nn : Nat}
    (hL : LotMember readers rows Z G Q w front ca ((S.sent.headD #[]).size - 1 + t) a nn)
    {D' : RowData} {ad : MsgAddr} {sh : OnBytes.OracleShape} {fr : Nat}
    (ho : ([o₁, o₂].getD t default).shape = sh)
    (ha : addrsAt Z G ((lotSegs Z G Q).length - 1)
      (ownBase S (!(lotSegs Z G Q).dropLast.isEmpty) + t) = some ad)
    (hsh : ((((lotSegs Z G Q)[(lotSegs Z G Q).length - 1]?).map
      (·.ownShapes ((lotSegs Z G Q).length - 1 == 0))).getD []).getD
        (ownBase S (!(lotSegs Z G Q).dropLast.isEmpty) + t) {} = sh)
    (hD : ∀ hd r j, (rows w.x).at_ (readers w) hd ad r j = D'.at_ (readers w) hd ad r j)
    (hle : D'.heardAt ad ≤ fr) (hfr : fr ≤ front.length) :
    a.1 = sh ∧ a.2 = fun r j => asRow (sh.mainDeg == 3) (D'.at_ (readers w) (front.take fr) ad r j) := by
  have hm := member_later hLast hs hL
  have key := ownBy_job (rows w.x) D' (readers w) (addrsAt Z G)
    (fun s m => ((((lotSegs Z G Q)[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) front fr
    ((lotSegs Z G Q).length - 1) (ownBase S (!(lotSegs Z G Q).dropLast.isEmpty) + t) ha hsh hD hle hfr
  obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
  · obtain rfl := Option.some.inj hm
    exact ⟨ho, key⟩
  · obtain rfl := Option.some.inj hm
    exact ⟨ho, key⟩

/-- **The clause on data at a message of the first segment's first sending.** -/
theorem data_first {readers : Local W₀ Rc Xi Tr → Readers} {rows : RowDataOf Xi} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {Q : Par} {w : Local W₀ Rc Xi Tr} {front : List Fmt.Drawn}
    {ca : CsAll (closeCarries ⟨Q, borneAt Z Q⟩)} {S : SegmentPub}
    (hLast : (lotSegs Z G Q).getLast? = some S) (hOne : (lotSegs Z G Q).dropLast = []) {i : Nat}
    (hi : i < (S.sent.headD #[]).size - 1) {a : Laid} {nn : Nat}
    (hL : LotMember readers rows Z G Q w front ca i a nn)
    {D' : RowData} {ad : MsgAddr} {sh : OnBytes.OracleShape} {fr : Nat}
    (ho : ∀ o, (S.sent.headD #[])[i]? = some o → o.shape = sh)
    (ha : addrsAt Z G ((lotSegs Z G Q).length - 1) i = some ad)
    (hsh : ((((lotSegs Z G Q)[(lotSegs Z G Q).length - 1]?).map
      (·.ownShapes ((lotSegs Z G Q).length - 1 == 0))).getD []).getD i {} = sh)
    (hD : ∀ hd r j, (rows w.x).at_ (readers w) hd ad r j = D'.at_ (readers w) hd ad r j)
    (hle : D'.heardAt ad ≤ fr) (hfr : fr ≤ front.length) :
    a.1 = sh ∧ a.2 = fun r j => asRow (sh.mainDeg == 3) (D'.at_ (readers w) (front.take fr) ad r j) := by
  obtain ⟨o, hoo, rfl⟩ := member_first hLast hOne hi hL
  exact ⟨ho o hoo, ownBy_job (rows w.x) D' (readers w) (addrsAt Z G)
    (fun s m => ((((lotSegs Z G Q)[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) front fr
    ((lotSegs Z G Q).length - 1) i ha hsh hD hle hfr⟩

/-- What a job made by `placeJob` reads is one call of its filling. -/
theorem job_data {X : Type} (P : VerifiableInference.Desc.K1.Par) (first : Nat)
    (fold : Option (Nat × OnBytes.FoldShape)) (D : RowDataOf Xi) (v : K1.PlaceIn Xi)
    (hd : List Fmt.Drawn) (own₀ : X) (n r i : Nat) :
    (K1.placeJob (X := X) P first fold D).data v { heard := hd, own := own₀, seen := .bare [] } n r i =
      (D v.x).at_ v.R hd ⟨⟨P.place, 0⟩, n⟩ r i := rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closingFrom_some
#print axioms ProofFile.Honest.K10.later_two
#print axioms ProofFile.Honest.K10.first_at
#print axioms ProofFile.Honest.K10.member_later
#print axioms ProofFile.Honest.K10.member_first
#print axioms ProofFile.Honest.K10.data_later
#print axioms ProofFile.Honest.K10.data_first
#print axioms ProofFile.Honest.K10.job_data
