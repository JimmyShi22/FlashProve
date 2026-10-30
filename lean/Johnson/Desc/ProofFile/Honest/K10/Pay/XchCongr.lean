-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchCongr.lean: the closing of a segment (K10): the shared text that walks the folds of
the segments in front (`closingFrom`, Honest/K2/Closing.lean) returns the same at two callers that agree in what the text
reads. The closing's job and the code switch into the same segment both call it, over the same segments, with three arguments
of their own: the segments' own main rows, the challenges heard, the carried stretches. For the field tie of `CarryOwed`
(Honest/K10/Xch/CarryTop.lean): the carrying message's main rows are made of what this text returns.

  `mapM_zipIdx_congr`   two functions that agree at a list's members, each with its number, give one `mapM`
  `later_length`, `inFirst_length`, `messages_count`   the counts: a segment whose first sending holds a message has as many
                      messages as the first sending's members, the fresh mask, and the later sendings' members together
  `rowsCore_congr`      the text of a segment's group's rows, at two ways to hand out stretches that agree at the numbers asked
  `segmentLeft_congr`   so one segment's step
  **`closingFrom_congr`**   so the steps from a segment on, from:
      hFirst  each segment's first sending holds a message
      hOwn    the two callers' own main rows are one function at each of these segments
      hGam    the folds' challenges, as the text reads them, are the same
      hK      the two ways to hand out stretches agree at the numbers of these segments' messages

Limits. A congruence: it says nothing on whether the text returns, nor on what. The four premises are shown here of no caller.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.K2.Honest (Left)
open ProofFile.Honest.K2 (SegmentPub GroupRows Stretch FreshTable segmentGroupRows segmentLeft closingFrom challengesOr0)
open ProofFile.Honest.K2.Law (Laid rowsCore inFirstOf laterOf laterStep segmentRows_eq)

/-- Two functions that agree at a list's members, each with its number, give one `mapM`. -/
theorem mapM_zipIdx_congr {α β : Type} (f g : α × Nat → Except String β) : ∀ (l : List α) (n : Nat),
    (∀ i a, l[i]? = some a → f (a, n + i) = g (a, n + i)) → (l.zipIdx n).mapM f = (l.zipIdx n).mapM g
  | [], _, _ => rfl
  | a :: l, n, h => by
    have h0 : f (a, n) = g (a, n) := h 0 a rfl
    have hr : (l.zipIdx (n + 1)).mapM f = (l.zipIdx (n + 1)).mapM g :=
      mapM_zipIdx_congr f g l (n + 1) fun i a' hi => by
        have e := h (i + 1) a' hi
        rwa [show n + (i + 1) = n + 1 + i by omega] at e
    rw [List.zipIdx_cons, List.mapM_cons, List.mapM_cons, h0, hr]

/-- How many members the later sendings have. -/
theorem later_length (own : Nat → Nat → Nat → Cb.Gl.E) : ∀ (l : List (Array OnBytes.OracleNotice)) (s : List Laid × Nat),
    (l.foldl (laterStep own) s).1.length = s.1.length + (l.map (·.size)).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, later_length own l, List.map_cons, List.sum_cons]
    unfold laterStep
    simp only [List.length_append, List.length_map, List.length_zipIdx, Array.length_toList]
    omega

/-- How many members the first sending has: all its messages but the last. -/
theorem inFirst_length (S : SegmentPub) (prev : Option Left) (own : Nat → Nat → Nat → Cb.Gl.E) :
    (inFirstOf S prev own).length = (S.sent.headD #[]).size - 1 := by
  unfold inFirstOf
  simp only [List.length_map, List.length_zipIdx, List.length_take, Array.length_toList]
  omega

theorem foldl_sizes : ∀ (l : List (Array OnBytes.OracleNotice)) (n : Nat),
    l.foldl (fun n a => n + a.size) n = n + (l.map (·.size)).sum
  | [], n => by simp
  | a :: l, n => by
    rw [List.foldl_cons, foldl_sizes l, List.map_cons, List.sum_cons]
    omega

/-- A segment's number of messages, where its first sending holds one. -/
theorem messages_count (S : SegmentPub) (h : 0 < (S.sent.headD #[]).size) :
    S.messages = (S.sent.headD #[]).size + ((S.sent.drop 1).map (·.size)).sum := by
  unfold SegmentPub.messages
  cases hs : S.sent with
  | nil =>
    rw [hs] at h
    exact absurd h (by simp)
  | cons a l =>
    rw [foldl_sizes]
    simp

/-- The text of a segment's group's rows, at two ways to hand out stretches that agree at the numbers asked. -/
theorem rowsCore_congr (table : FreshTable) (S : SegmentPub) (ps : Bool) (prevKept : List OnBytes.OracleShape)
    (A : List Laid) (B : List Laid × Nat) {k k' : Nat → Except String Stretch} (base : Nat) (wf : Bool)
    (hA : ∀ i, i < A.length → k (base + i) = k' (base + i))
    (hF : k (base + ((S.sent.headD #[]).size - 1)) = k' (base + ((S.sent.headD #[]).size - 1)))
    (hB : ∀ i, i < B.1.length →
      k (base + ((S.sent.headD #[]).size - 1) + (if wf = true then 1 else 0) + i) =
        k' (base + ((S.sent.headD #[]).size - 1) + (if wf = true then 1 else 0) + i)) :
    rowsCore table S ps prevKept A B k base wf = rowsCore table S ps prevKept A B k' base wf := by
  have e0 : (A.zipIdx.mapM fun x =>
        (k (base + x.2)).bind (K2.messageRows table S.sizes.codes x.1.1 none x.1.2)) =
      (A.zipIdx.mapM fun x =>
        (k' (base + x.2)).bind (K2.messageRows table S.sizes.codes x.1.1 none x.1.2)) :=
    mapM_zipIdx_congr _ _ A 0 fun i a hi => by
      show (k (base + (0 + i))).bind _ = (k' (base + (0 + i))).bind _
      rw [Nat.zero_add, hA i (List.getElem?_eq_some_iff.1 hi).1]
  have e1 : (B.1.zipIdx.mapM fun x =>
        (k (base + ((S.sent.headD #[]).size - 1) + (if wf = true then 1 else 0) + x.2)).bind
          (K2.messageRows table S.sizes.codes x.1.1 none x.1.2)) =
      (B.1.zipIdx.mapM fun x =>
        (k' (base + ((S.sent.headD #[]).size - 1) + (if wf = true then 1 else 0) + x.2)).bind
          (K2.messageRows table S.sizes.codes x.1.1 none x.1.2)) :=
    mapM_zipIdx_congr _ _ B.1 0 fun i a hi => by
      show (k (base + ((S.sent.headD #[]).size - 1) + (if wf = true then 1 else 0) + (0 + i))).bind _ =
        (k' (base + ((S.sent.headD #[]).size - 1) + (if wf = true then 1 else 0) + (0 + i))).bind _
      rw [Nat.zero_add, hB i (List.getElem?_eq_some_iff.1 hi).1]
  unfold rowsCore
  dsimp only
  rw [e0, e1, hF]

/-- One segment's step, at two callers that agree in what it reads. -/
theorem segmentLeft_congr (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape) (own : Nat → Nat → Nat → Cb.Gl.E) {heard heard' : List Fmt.Drawn}
    {k k' : Nat → Except String Stretch} (base : Nat) (hFirst : 0 < (S.sent.headD #[]).size)
    (hGam : challengesOr0 heard S.gamma = challengesOr0 heard' S.gamma)
    (hK : ∀ n, base ≤ n → n < base + S.messages → k n = k' n) :
    segmentLeft table S prev prevKept own heard k base = segmentLeft table S prev prevKept own heard' k' base := by
  have hc := messages_count S hFirst
  have lA := inFirst_length S prev own
  have lB : (laterOf S prev.isSome own).1.length = ((S.sent.drop 1).map (·.size)).sum := by
    unfold laterOf
    rw [later_length]
    simp
  have hR : segmentGroupRows table S prev prevKept own k base true = segmentGroupRows table S prev prevKept own k' base true := by
    rw [segmentRows_eq, segmentRows_eq]
    refine rowsCore_congr table S _ prevKept _ _ base true (fun i hi => hK _ (by omega) (by omega))
      (hK _ (by omega) (by omega)) fun i hi => hK _ (by omega) ?_
    rw [if_pos rfl]
    omega
  unfold segmentLeft
  dsimp only
  rw [hR, hGam]

/-- **The steps from a segment on, at two callers that agree in what the text reads.** -/
theorem closingFrom_congr (table : FreshTable) {own own' : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard heard' : List Fmt.Drawn} {k k' : Nat → Except String Stretch} :
    ∀ (segs : List SegmentPub) (j base : Nat) (prev : Option (Left × List OnBytes.OracleShape)),
      (∀ S ∈ segs, 0 < (S.sent.headD #[]).size) →
      (∀ i S, segs[i]? = some S → own (j + i) = own' (j + i)) →
      (∀ S ∈ segs, challengesOr0 heard S.gamma = challengesOr0 heard' S.gamma) →
      (∀ n, base ≤ n → n < base + (segs.map (·.messages)).sum → k n = k' n) →
      closingFrom table own heard k segs j base prev = closingFrom table own' heard' k' segs j base prev
  | [], _, _, _, _, _, _, _ => rfl
  | S :: rest, j, base, prev, hFirst, hOwn, hGam, hK => by
    have hs : ((S :: rest).map (·.messages)).sum = S.messages + (rest.map (·.messages)).sum := by
      rw [List.map_cons, List.sum_cons]
    have e0 : own j = own' j := hOwn 0 S rfl
    have e1 := segmentLeft_congr table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own' j) (heard := heard)
      (heard' := heard') (k := k) (k' := k') base (hFirst S (List.mem_cons_self ..))
      (hGam S (List.mem_cons_self ..)) fun n h1 h2 => hK n h1 (by rw [hs]; omega)
    show (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k base).bind
        (fun W => closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)) =
      (segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own' j) heard' k' base).bind
        (fun W => closingFrom table own' heard' k' rest (j + 1) (base + S.messages) (some W))
    rw [e0, e1]
    congr 1
    funext W
    exact closingFrom_congr table rest (j + 1) (base + S.messages) (some W)
      (fun T hT => hFirst T (List.mem_cons_of_mem _ hT))
      (fun i T hi => by
        have e := hOwn (i + 1) T hi
        rwa [show j + (i + 1) = j + 1 + i by omega] at e)
      (fun T hT => hGam T (List.mem_cons_of_mem _ hT))
      (fun n h1 h2 => hK n (by omega) (by rw [hs]; omega))

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mapM_zipIdx_congr
#print axioms ProofFile.Honest.K10.later_length
#print axioms ProofFile.Honest.K10.inFirst_length
#print axioms ProofFile.Honest.K10.foldl_sizes
#print axioms ProofFile.Honest.K10.messages_count
#print axioms ProofFile.Honest.K10.rowsCore_congr
#print axioms ProofFile.Honest.K10.segmentLeft_congr
#print axioms ProofFile.Honest.K10.closingFrom_congr
