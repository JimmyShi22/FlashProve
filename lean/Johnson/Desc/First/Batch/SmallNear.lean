-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/SmallNear.lean: THE HALF ON PRESENCE OF THE NAMED TEST ON THE SMALLNESS
TEST's SINGLE EQUATIONS (`nearA`, Johnson/Desc/First/Batch/SmallBehindDraw.lean), AND THE TWO HALVES
JOINED: THE PUBLIC TEST BEHIND A YES OF THE DRAW. A definition, and theorems.

Why. The single equations name three sorts of arrays: each matrix's array of symbols and the third
vector of reads, which the drawn matrix multiplies: these are sent in front of the draw; and the
digits' array, which the segment's third sending brings: it is ahead. Of the first two sorts the
smallness test has a test with code at the state in front of the draw: `Named.namedAt`
(Johnson/Desc/First/K8/Named.lean).
  `whereIs_of_namedNow`, `reqArray_of_liesAt`: the readings of that test are the frame's and the
    layout's own. `msgNow_spec`: so an array with a message now is in the link's list and the
    layout, and the frame finds its message.
  `SeatsOwn own p s`: WHAT IS LEFT: the seat at which the book has the message of an array that the
    matrix multiplies, in a tree that the place names, is one of own.
  `arrayIn_of_named`, `near_of_named`: **a yes of `namedAt`, with `SeatsOwn`: each such array is
    there.**
  `whereIs_none`: the frame finds no message of the link under way beyond its list of own messages.
  `near_of_unsent`: **an array of the link under way whose message is not yet in that list, has a
    moment other than 0, and has by the plan a seat of own, is ahead.**
  `smallFitsAt_front`: the named test at a state from which the draw says yes, from: the test on the
    plan `smallSizesB` (Johnson/Desc/First/Batch/SmallSizesPlan.lean) with its premises; `namedAt`
    and `SeatsOwn`; one number of a symbol array a matrix; a third vector of reads; the digits'
    array unsent.
  `formsInA_row`: **SO THE PUBLIC TEST AT THE STATE BEHIND THE DRAW.**
Limits: (1) EVERY PREMISE IS A PREMISE: none is shown of a reached state here, and the premises have
been evaluated together at no state and no plan: THAT THEY CAN HOLD TOGETHER IS NOT SHOWN. (2) One
way. (3) Nothing on what the equations are worth. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.SmallSizesPlan
import Johnson.Desc.First.K8.Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Order.Lies Order.liesAt Order.namedNow Named.arrays
  Named.msgNow Named.memberAt Named.partAt Named.namedB Named.namedAt)
open VerifiableInference.Desc.First.K8.Ready (seven)

/-! ## 1 The readings of the smallness test's own test -/

/-- "Under which number the statement has the message now" is the frame's own reading. -/
theorem whereIs_of_namedNow (f : ReqFrame) (w : Order.Lies) (o : Nat)
    (h : Order.namedNow f w = some o) : f.whereIs w.born w.message = some o := by
  unfold Order.namedNow at h
  unfold ReqFrame.whereIs
  split at h
  · rename_i hn
    rw [hn, if_neg (by simp)]
    split at h
    · rename_i hb
      rw [if_pos hb]
      exact h
    · rename_i hb
      rw [if_neg hb]
      split at h
      · exact nomatch h
      · rename_i i hi
        rw [hi]
        exact h
  · exact nomatch h

/-- "Where an array lies" reads the link's list and the layout as `reqArray` does. -/
theorem reqArray_of_liesAt (L : LinkCtx) (t : Nat) (w : Order.Lies)
    (h : Order.liesAt L t = some w) :
    ∃ b A, L.arrayOf[t]? = some b ∧ reqArray L.check.rows.layout b.1 b.2 = some A ∧
      w.born = b.1 ∧ w.message = A.message := by
  simp only [Order.liesAt, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨named, hn, laid, hl, sh, _, m, _, rfl⟩ := h
  refine ⟨named, laid, hn, ?_, rfl, rfl⟩
  unfold reqArray
  cases e : L.check.rows.layout.link[named.1]? with
  | none =>
    rw [List.getD_eq_getElem?_getD, e] at hl
    exact nomatch hl
  | some arrays =>
    rw [List.getD_eq_getElem?_getD, e] at hl
    exact hl

theorem msgNow_spec (L : LinkCtx) (t o : Nat) (h : Named.msgNow L t = some o) :
    ∃ b A, L.arrayOf[t]? = some b ∧ reqArray L.check.rows.layout b.1 b.2 = some A ∧
      L.check.frame.whereIs b.1 A.message = some o := by
  unfold Named.msgNow at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨b, A, e1, e2, e3, e4⟩ := reqArray_of_liesAt L t w hw
  refine ⟨b, A, e1, e2, ?_⟩
  rw [← e3, ← e4]
  exact whereIs_of_namedNow _ w o h

/-! ## 2 What the matrix multiplies is there -/

section
variable (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))

/-- **What is left beside the smallness test's own test**: the seats are seats of own. -/
def SeatsOwn (p : First.K8.Par) (s : S) : Prop :=
  ∀ tl L, s.tl? = some tl → s.link? = some L → ∀ t ∈ Named.arrays tl, ∀ (o : Nat) (jt : Nat × Nat),
    Named.msgNow L t = some o → s.book.place[o]? = some jt → jt.1 ∈ p.matsIn ++ p.readsIn →
    Named.partAt s.book jt.1 jt.2 = some o → jt ∈ own

/-- **Each array that the matrix multiplies is there.** -/
theorem arrayIn_of_named (p : First.K8.Par) (s : S) (a : Part) (tl : HTailF2)
    (ha : segAt? s = some a) (ht : s.tl? = some tl) (hN : Named.namedAt p s = true)
    (hO : SeatsOwn own p s) (t : Nat) (hm : t ∈ Named.arrays tl) :
    (arrayIn own a t).isSome = true := by
  obtain ⟨hL, _, hb, _⟩ := segAt_reads s a ha
  unfold Named.namedAt at hN
  rw [ht, hL] at hN
  have h1 := List.all_eq_true.1 hN t hm
  cases e1 : Named.msgNow a.L t with
  | none =>
    rw [e1] at h1
    exact nomatch h1
  | some o =>
    rw [e1] at h1
    replace h1 : (match Named.memberAt s.st s.book o with
      | none => false
      | some m => (p.matsIn ++ p.readsIn).contains m.2.1 &&
          Named.partAt s.book m.2.1 m.2.2 == some o) = true := h1
    cases e2 : Named.memberAt s.st s.book o with
    | none =>
      rw [e2] at h1
      exact nomatch h1
    | some m =>
      rw [e2] at h1
      have h1' : ((p.matsIn ++ p.readsIn).contains m.2.1 &&
          Named.partAt s.book m.2.1 m.2.2 == some o) = true := h1
      obtain ⟨g1, g2⟩ := Eq.mp (Bool.and_eq_true _ _) h1'
      have hp : s.book.place[o]? = some m.2 := by
        unfold Named.memberAt at e2
        cases x1 : s.st.oracles[o]? with
        | none =>
          rw [x1] at e2
          exact nomatch e2
        | some x =>
          cases x2 : s.book.place[o]? with
          | none =>
            rw [x1, x2] at e2
            exact nomatch e2
          | some jt =>
            rw [x1, x2] at e2
            rw [← Option.some.inj e2]
      have hin : m.2 ∈ own := hO tl a.L ht hL t hm o m.2 e1 hp (by simpa using g1)
        (by simpa using g2)
      obtain ⟨b, A, c1, c2, c3⟩ := msgNow_spec a.L t o e1
      unfold arrayIn seatAt
      rw [c1, Option.bind_some, c2, Option.bind_some, c3, Option.bind_some, hb, hp,
        Option.bind_some, if_pos (by simpa using hin)]
      rfl

theorem near_of_named (p : First.K8.Par) (s : S) (a : Part) (tl : HTailF2)
    (ha : segAt? s = some a) (ht : s.tl? = some tl) (hN : Named.namedAt p s = true)
    (hO : SeatsOwn own p s) (t : Nat) (hm : t ∈ Named.arrays tl) :
    nearA sent own a t = true := by
  unfold nearA
  rw [arrayIn_of_named own p s a tl ha ht hN hO t hm]
  rfl

/-! ## 3 The digits' array is ahead -/

omit sent own in
/-- The frame finds no message of the link under way beyond its list of own messages. -/
theorem whereIs_none (f : ReqFrame) (j : Nat) (h : f.own.size ≤ j) :
    f.whereIs f.link j = none := by
  unfold ReqFrame.whereIs
  split
  · rfl
  · rw [if_pos (by simp)]
    exact Array.getElem?_eq_none h

/-- **An array of the link under way that is not yet sent is ahead.** -/
theorem near_of_unsent (a : Part) (t : Nat) (name : String) (A : Params.ReqArray)
    (sh : Params.ReqLink) (M : Params.ReqMessage) (x : Nat × Nat)
    (h1 : a.L.arrayOf[t]? = some (a.L.check.frame.link, name))
    (h2 : reqArray a.L.check.rows.layout a.L.check.frame.link name = some A)
    (h3 : a.L.check.frame.own.size ≤ A.message)
    (h4 : a.L.check.frame.shape.link[a.L.check.frame.link]? = some sh)
    (h5 : sh.messages[A.message]? = some M) (h6 : M.moment ≠ 0)
    (h7 : (sent M.moment)[((sh.messages.take A.message).filter fun y =>
      y.moment == M.moment).length]? = some x)
    (h8 : x ∈ own) : nearA sent own a t = true := by
  have e : aheadIn sent own a (a.L.check.frame.link, name) = some ⟨A, x, M.shape⟩ := by
    unfold aheadIn aheadOf
    simp only [beq_self_eq_true, if_true, h2, Option.bind_some, whereIs_none _ _ h3, h4,
      Option.map_some, h5, h7]
    rw [if_neg (by simpa using h6)]
    simp [h8]
  unfold nearA
  rw [h1, Option.bind_some, e]
  simp

/-! ## 4 The two halves joined -/

/-- **The named test at a state from which the draw says yes.** -/
theorem smallFitsAt_front {Cl : Type} (p : First.K8.Par) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok t)
    (a : Part) (tl tlP : HTailF2) (funs : Array HFun) (u : Nat)
    (ha : segAt? s = some a) (ht : s.tl? = some tl) (hf : s.funs? = some funs)
    (hFA : First.K8.FunsAre s) (h3 : ∀ Fn ∈ funs.toList, Fn.tree = 2)
    (h7 : seven tl = seven tlP)
    (hP : smallSizesB a.L.arrayOf a.L.check.rows.layout tlP p = true)
    (hN : Named.namedAt p s = true) (hO : SeatsOwn own p s)
    (hg : tl.gtTree.size = tl.NM) (hU : tl.ix.U.getD 2 none = some u)
    (hZ : nearA sent own a tl.ix.ZZ = true) : smallFitsAt sent own s = true := by
  refine smallFitsAt_of_split sent own s a tl funs ha ht hf
    (sizes_of_plan p s t rs gs h a.L tl tlP funs ht hf hFA h3 h7 hP) hZ ?_ ?_
  · intro mu hmu
    refine near_of_named sent own p s a tl ha ht hN hO _ ?_
    unfold Named.arrays
    refine List.mem_append_left _ ?_
    have hlt : mu < tl.gtTree.size := by rw [hg]; exact hmu
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
    exact Array.getElem_mem_toList hlt
  · intro Fn hFn _
    refine near_of_named sent own p s a tl ha ht hN hO _ ?_
    rw [h3 Fn hFn, hU, Option.getD_some]
    unfold Named.arrays
    refine List.mem_append_right _ (List.mem_filterMap.2 ⟨2, by simp, hU⟩)

/-- **THE PUBLIC TEST ON THE SINGLE EQUATIONS AT THE STATE BEHIND A YES OF THE DRAW.** -/
theorem formsInA_row {Cl : Type} (Rd : Readers) (b : Nat) (p : First.K8.Par) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hRd : Rd.forms b "K8.equations" t = smallReader t)
    (h : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok t)
    (a : Part) (tl tlP : HTailF2) (funs : Array HFun) (u : Nat)
    (ha : segAt? s = some a) (ht : s.tl? = some tl) (hf : s.funs? = some funs)
    (hFA : First.K8.FunsAre s) (h3 : ∀ Fn ∈ funs.toList, Fn.tree = 2)
    (h7 : seven tl = seven tlP)
    (hP : smallSizesB a.L.arrayOf a.L.check.rows.layout tlP p = true)
    (hN : Named.namedAt p s = true) (hO : SeatsOwn own p s)
    (hg : tl.gtTree.size = tl.NM) (hU : tl.ix.U.getD 2 none = some u)
    (hZ : nearA sent own a tl.ix.ZZ = true) :
    formsInA Rd sent own b "K8.equations" t = true :=
  formsInA_behind_draw sent own Rd b p s t rs gs hRd h
    (smallFitsAt_front sent own p s t rs gs h a tl tlP funs u ha ht hf hFA h3 h7 hP hN hO hg hU hZ)

end

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.whereIs_of_namedNow
#print axioms VerifiableInference.Desc.K9.reqArray_of_liesAt
#print axioms VerifiableInference.Desc.K9.msgNow_spec
#print axioms VerifiableInference.Desc.K9.arrayIn_of_named
#print axioms VerifiableInference.Desc.K9.near_of_named
#print axioms VerifiableInference.Desc.K9.whereIs_none
#print axioms VerifiableInference.Desc.K9.near_of_unsent
#print axioms VerifiableInference.Desc.K9.smallFitsAt_front
#print axioms VerifiableInference.Desc.K9.formsInA_row
