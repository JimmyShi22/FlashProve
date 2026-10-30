-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Walk/Shape/ClearRow.lean: THE FRAME's "cleared" (clearWith,
Johnson/Desc/First/Walk/Frame.lean: one text for all links) AT A LINK THAT LEAVES A ROW, against the
shape of the first chain's state (chainSh, Johnson/Desc/First/Shape/Chain.lean): one step on the
shape, general in the link's own counts and in what its sub-proof left; and the two laws. Then the
two fillings: a layers' link; the head's link. General laws; nothing is evaluated. NO TEST OF THIS
TEXT READS A VALUE.

  `leaveAll`: the link's part is dropped, whichever sort the link is; the live state of the calls is
    taken back. `chainSh_leave`: it is the shape behind the leaving, wherever a ledger is open.
  `leave_iff`: the leaving's own form: it returns just where no mark of failure stands.
  `chainSh_kept`: the row laid at the pile's end and the messages behind: two components turn.
  **`clearG X lay lin countsB leftSh`**: THE STEP: a link's context and a ledger are there · no mark
    · the counts · the link is handed and done · the plan's sizes · then, where the link's public
    record says that it leaves a row: what was left is there, and the pending row on shapes returns
    (pendS, Johnson/Desc/First/Pend/Shape/PendShape.lean): the row's shape goes to the pile's end,
    the shape of statement, book and roots is laid, the link is left; where the record says that it
    leaves none: the link is left.
  **`clear_carries`**, **`clear_returns`**: under premises on the fillings. Both ask that what was
    left has the shape that leftSh reads. "Returns" also asks that the counts' text accepts wherever
    countsB accepts at the shape (one way).
  `countsLayB`, `leftLaySh`, `countsLay_sh`, `leftLay_sh` · `countsHeadB`, `leftHeadSh`,
    `countsHead_sh`, `leftHead_sh`: the two fillings, with their premises paid.
  **`clearLayG`**, **`clearHeadG`** with `clearLay_carries | _returns`, `clearHead_carries |
    _returns`.

Limits. The bare texts: in a seated chain they stand under the comparison of the reply. That a step
returns at a shape that the chain reaches is not shown. FrameEnds.lean's clearAttG is a second text
of this step for attention; no law ties the two. clear_carries is another law than the library's
Walk.Law.clear_carries. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Walk.Shape.FrameEnds
import Johnson.Desc.First.Pend.Shape.PendShape
import Johnson.Desc.First.Close.Law.TailMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Shape
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.Pend.Shape (pendS pend_carries pend_returns)
open VerifiableInference.Desc.First.Close (countsHead leftHead tailHead)
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Props

/-! ## 1 The leaving -/

/-- The link's part is dropped, whichever sort the link is. -/
def leaveAll (a : ChainSh) : ChainSh := ((leaveSh a).layOwn none).layHead none

/-- leaveAll at a shape that is written out and has a link's context. -/
theorem leaveAll_mk (m : Bool) (h : Nat) (tl : Option TailSh) (led : Option LedSh)
    (tb : Option (List FunSh)) (ro : Option Nat) (core : Ground.Sh.CoreSh) (rp : Bool) (im : Nat)
    (pile : List K13.Honest.RowSh) (e : Option EndSh) (ck : CheckSh) (L : LinkSh)
    (look lh : Option HeardAll) (own : Option OwnSh) (hd : Option HeadSh)
    (att : Option AttOwnSh) (fin : Option FinSh) :
    leaveAll (ChainSh.mk m h tl led tb ro core rp im pile e ck (some L) look lh own hd att fin) =
      ChainSh.mk m 0 none none none ro core rp im pile e L.check none none none none none none
        fin :=
  rfl

theorem chainSh_leave (s : S) (C : LinkCtx) (F : Fork) (hC : s.link? = some C)
    (h : s.fork? = some F) :
    chainSh { s with check := s.live, here := .between } = leaveAll (chainSh s) := by
  have he : endSh s.here = none := by
    cases hh : s.here with
    | mem a =>
      have : s.fork? = none := by
        unfold S.fork?
        rw [hh]
      rw [this] at h
      exact nomatch h
    | _ => rfl
  have hn : finOf s.here = none := by
    cases hh : s.here with
    | fin a =>
      have : s.fork? = none := by
        unfold S.fork?
        rw [hh]
      rw [this] at h
      exact nomatch h
    | _ => rfl
  have hl : s.live = C.check := by
    unfold S.live
    rw [hC]
  unfold chainSh
  rw [hC, he, hn, Option.map_some, leaveAll_mk, hl]
  rfl

theorem leave_iff {s : S} {F : Fork} (h : s.fork? = some F) (t : S) : s.leaveLink? = .ok t ↔
    t = { s with check := s.live, here := .between } ∧ s.failed = none := by
  have hi : s.inLink = true := by
    unfold S.inLink
    rw [h]
    rfl
  unfold S.leaveLink? S.leaveLink
  rw [if_pos hi, S.unmarked_ok]
  constructor
  · rintro ⟨rfl, hf⟩
    exact ⟨rfl, hf⟩
  · rintro ⟨rfl, hf⟩
    exact ⟨rfl, hf⟩

theorem chainSh_kept (s : S) (q : TensorRow) (os : Array OnBytes.Oracle) :
    chainSh { s with out := pendingKept s.out q, st := { s.st with oracles := os } } =
      ((chainSh s).setPile ((chainSh s).pile ++ [K13.Honest.rowSh q])).setCore
        (Ground.Sh.coreSh ⟨{ s.st with oracles := os }, s.book, s.roots⟩) := by
  show ChainSh.mk _ _ _ _ _ _ _ _ _ ((s.out.pending ++ [q]).map K13.Honest.rowSh) _ _ _ _ _ _ _ _
    _ = _
  rw [List.map_append]
  rfl

/-! ## 2 The step -/

/-- The tests in front of the row. -/
def clearB (X : LinkPub) (countsB : ChainSh → Bool) (a : ChainSh) (C : LinkSh) (L : LedSh) : Bool :=
  !a.marked && countsB a && C.handed && C.done && samePlanSh X L C.list

/-- **THE STEP ON THE SHAPE.** -/
def clearG (X : LinkPub) (lay : WsLay) (lin : LinShape) (countsB : ChainSh → Bool)
    (leftSh : ChainSh → Option MergeSh) (a : ChainSh) : Except String ChainSh :=
  match a.link, a.led with
  | some C, some L =>
    if clearB X countsB a C L then
      if X.fv then
        match leftSh a with
        | none => .error "W5: nothing is left for the row"
        | some w =>
          match pendS lay lin a.indexMasks w X.NCL a.core with
          | none => .error "ROW: the shape"
          | some y => .ok (leaveAll ((a.setPile (a.pile ++ [y.1])).setCore y.2))
      else .ok (leaveAll a)
    else .error "cleared: the shape"
  | _, _ => .error "N: no link with its ledger is open"

variable {X : LinkPub} {lay : WsLay} {lin : LinShape} {counts : S → Except String Unit}
  {left : S → Option WsForkOut} {countsB : ChainSh → Bool} {leftSh : ChainSh → Option MergeSh}

theorem clear_carries (hl : ∀ s, (left s).map mergeSh = leftSh (chainSh s)) (s t : S)
    (u : ChainSh)
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hg : clearG X lay lin countsB leftSh (chainSh s) = .ok u) : u = chainSh t := by
  obtain ⟨C, F, hC, hF, -, k, r, hb, hq⟩ := clearWith_iff.1 h
  have l1 : (chainSh s).link = some (linkSh C) := by
    show s.link?.map linkSh = _
    rw [hC]
    rfl
  have l2 : (chainSh s).led = some (ledSh F) := by
    show s.fork?.map ledSh = _
    rw [hF]
    rfl
  unfold clearG at hg
  rw [l1, l2] at hg
  simp only at hg
  split at hg
  · cases hv : X.fv with
    | false =>
      rw [hv] at hg
      obtain rfl := hb.2.2.2.2.1 hv
      rcases hq with ⟨-, hq⟩ | ⟨w, _, _, e, -⟩
      · obtain ⟨rfl, -⟩ := (leave_iff hF t).1 hq
        rw [chainSh_leave s C F hC hF]
        exact (Except.ok.inj hg).symm
      · exact nomatch e
    | true =>
      rw [hv] at hg
      obtain ⟨rfl, -⟩ := hb.2.2.2.2.2 hv
      rcases hq with ⟨e, -⟩ | ⟨w, q, os, e, hr, hq⟩
      · have := (hb.2.2.2.2.2 hv).2
        rw [e] at this
        exact nomatch this
      · have e' : leftSh (chainSh s) = some (mergeSh w) := by
          rw [← hl, e]
          rfl
        simp only [if_true] at hg
        rw [e'] at hg
        simp only at hg
        have c := pend_carries lay lin s.out.indexMasks w X.NCL s.st s.book s.roots os q hr
        have c' : pendS lay lin (chainSh s).indexMasks (mergeSh w) X.NCL (chainSh s).core =
            some (K13.Honest.rowSh q,
              Ground.Sh.coreSh ⟨{ s.st with oracles := os }, s.book, s.roots⟩) := c
        rw [c'] at hg
        have hF' : ({ s with out := pendingKept s.out q, st := { s.st with oracles := os } } :
            S).fork? = some F := hF
        have hC' : ({ s with out := pendingKept s.out q, st := { s.st with oracles := os } } :
            S).link? = some C := hC
        obtain ⟨rfl, -⟩ := (leave_iff hF' t).1 hq
        rw [chainSh_leave _ C F hC' hF', chainSh_kept]
        exact (Except.ok.inj hg).symm
  · exact nomatch hg

theorem clear_returns (hc : ∀ s, countsB (chainSh s) = true → counts s = .ok ())
    (hl : ∀ s, (left s).map mergeSh = leftSh (chainSh s)) (s : S) (u : ChainSh)
    (hg : clearG X lay lin countsB leftSh (chainSh s) = .ok u) :
    ∃ t, clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t := by
  unfold clearG at hg
  cases hC : s.link? with
  | none =>
    have l1 : (chainSh s).link = none := by
      show s.link?.map linkSh = _
      rw [hC]
      rfl
    rw [l1] at hg
    exact nomatch hg
  | some C =>
    have l1 : (chainSh s).link = some (linkSh C) := by
      show s.link?.map linkSh = _
      rw [hC]
      rfl
    cases hF : s.fork? with
    | none =>
      have l2 : (chainSh s).led = none := by
        show s.fork?.map ledSh = _
        rw [hF]
        rfl
      rw [l1, l2] at hg
      exact nomatch hg
    | some F =>
      have l2 : (chainSh s).led = some (ledSh F) := by
        show s.fork?.map ledSh = _
        rw [hF]
        rfl
      rw [l1, l2] at hg
      simp only at hg
      by_cases hB : clearB X countsB (chainSh s) (linkSh C) (ledSh F) = true
      · rw [if_pos hB] at hg
        unfold clearB at hB
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hB
        obtain ⟨⟨⟨⟨m, c0⟩, w1⟩, w2⟩, w3⟩ := hB
        have hf : s.failed = none := by
          have : s.failed.isSome = false := m
          simpa using this
        have w3' : SamePlan X F C.list := (samePlan_iff _ _ _).1 (by rw [samePlan_sh]; exact w3)
        cases hv : X.fv with
        | false =>
          exact ⟨_, clearWith_iff.2 ⟨C, F, hC, hF, hc s c0, C.check, none,
            ⟨w1, w2, w3', rfl, fun _ => rfl, fun e => by rw [hv] at e; exact nomatch e⟩,
            Or.inl ⟨rfl, (leave_iff hF _).2 ⟨rfl, hf⟩⟩⟩⟩
        | true =>
          rw [hv] at hg
          simp only [if_true] at hg
          cases hw : left s with
          | none =>
            have e' : leftSh (chainSh s) = none := by
              rw [← hl, hw]
              rfl
            rw [e'] at hg
            exact nomatch hg
          | some w =>
            have e' : leftSh (chainSh s) = some (mergeSh w) := by
              rw [← hl, hw]
              rfl
            rw [e'] at hg
            simp only at hg
            cases hp : pendS lay lin (chainSh s).indexMasks (mergeSh w) X.NCL (chainSh s).core with
            | none => rw [hp] at hg; exact nomatch hg
            | some z =>
              obtain ⟨⟨q, os⟩, hy⟩ :=
                pend_returns lay lin s.out.indexMasks w X.NCL s.st s.book s.roots z hp
              have hF' : ({ s with out := pendingKept s.out q, st := { s.st with oracles := os } } :
                  S).fork? = some F := hF
              exact ⟨_, clearWith_iff.2 ⟨C, F, hC, hF, hc s c0, C.check, some w,
                ⟨w1, w2, w3', rfl, (fun e => by rw [hv] at e; exact nomatch e),
                  fun _ => ⟨hw.symm, by rw [hw]; rfl⟩⟩,
                Or.inr ⟨w, q, os, rfl, hy, (leave_iff hF' _).2 ⟨rfl, hf⟩⟩⟩⟩
      · rw [if_neg hB] at hg
        exact nomatch hg

/-! ## 3 The filling at a layers' link -/

/-- The four counts at a layers' link's end, on shapes. -/
def countsLayB (NM : Nat) (a : ChainSh) : Bool :=
  match a.here, a.tl, a.led with
  | 1, some t, some L =>
    t.NM == NM && L.claims == L.planClaims &&
      (L.handed.length == L.planClaims && L.handed.all id) &&
      (t.foldTakenF.size == t.NM && t.foldTakenF.all id)
  | _, _, _ => false

/-- What a layers' sub-proof left for its row, on shapes. -/
def leftLaySh (a : ChainSh) : Option MergeSh := a.own.map (·.wo)

theorem countsLay_sh (NM : Nat) (s : S) (h : countsLayB NM (chainSh s) = true) :
    countsLay NM s = .ok () := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay a =>
    have h' : (a.tl.NM == NM && a.F.nClaim == a.F.planClaimsF &&
      (a.F.kapMapF.toList.length == a.F.planClaimsF && a.F.kapMapF.toList.all id) &&
      (a.tl.foldTakenF.size == a.tl.NM && a.tl.foldTakenF.all id)) = true := h
    rw [Array.length_toList, Array.all_toList] at h'
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩ := h'
    exact countsLay_iff.2 ⟨a, rfl, c0, c1,
      (weightsOut_iff _).1 (by
        unfold weightsOut
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact c2),
      (foldsOut_iff _).1 (by
        unfold foldsOut
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact c3)⟩
  | between => exact nomatch h
  | att a => exact nomatch h
  | head a =>
    exfalso
    cases ho : a.opened <;>
      simp [countsLayB, chainSh, ChainSh.mk, ChainSh.here, hereNo, ho] at h
  | fin a => exact nomatch h
  | mem a => exact nomatch h

theorem leftLay_sh (s : S) : (leftLay s).map mergeSh = leftLaySh (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay a =>
    show (a.own.map (·.wo)).map mergeSh = (a.own.map ownSh).map (·.wo)
    cases a.own <;> rfl
  | _ => rfl

/-- **The step at a layers' link.** -/
def clearLayG (X : LinkPub) (lay : WsLay) (lin : LinShape) (NM : Nat) :
    ChainSh → Except String ChainSh := clearG X lay lin (countsLayB NM) leftLaySh

theorem clearLay_carries (X : LinkPub) (lay : WsLay) (lin : LinShape) (NM : Nat) (s t : S)
    (u : ChainSh)
    (h : clearWith X (countsLay NM) leftLay (fun im w n os => pendingRowO lay im w n lin os) s =
      .ok t) (hg : clearLayG X lay lin NM (chainSh s) = .ok u) : u = chainSh t :=
  clear_carries leftLay_sh s t u h hg

theorem clearLay_returns (X : LinkPub) (lay : WsLay) (lin : LinShape) (NM : Nat) (s : S)
    (u : ChainSh) (hg : clearLayG X lay lin NM (chainSh s) = .ok u) :
    ∃ t, clearWith X (countsLay NM) leftLay (fun im w n os => pendingRowO lay im w n lin os) s =
      .ok t :=
  clear_returns (countsLay_sh NM) leftLay_sh s u hg

/-! ## 4 The filling at the head's link -/

/-- The four counts at the head's link's end, on shapes: 3 is "in the head's link, its sub-proof
opened". -/
def countsHeadB (a : ChainSh) : Bool :=
  match a.here, a.tl, a.led with
  | 3, some t, some L =>
    L.claims == L.planClaims && (L.handed.length == L.planClaims && L.handed.all id) &&
      (t.foldTakenF.size == t.NM && t.foldTakenF.all id)
  | _, _, _ => false

/-- What the head's sub-proof left for its row, on shapes. -/
def leftHeadSh (a : ChainSh) : Option MergeSh := a.head.bind (·.wo)

theorem countsHead_sh (s : S) (h : countsHeadB (chainSh s) = true) : countsHead s = .ok () := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head a =>
    cases ho : a.opened with
    | false =>
      exfalso
      simp [countsHeadB, chainSh, ChainSh.mk, ChainSh.here, hereNo, ho] at h
    | true =>
      have h' : (a.F.nClaim == a.F.planClaimsF &&
          (a.F.kapMapF.toList.length == a.F.planClaimsF && a.F.kapMapF.toList.all id) &&
          (a.tl.foldTakenF.size == a.tl.NM && a.tl.foldTakenF.all id)) = true := by
        simpa [countsHeadB, chainSh, ChainSh.mk, ChainSh.here, ChainSh.tl, ChainSh.led, hereNo,
          S.tl?, S.fork?, ho, tailSh, ledSh, LedSh.mk, LedSh.claims, LedSh.planClaims,
          LedSh.handed] using h
      rw [Array.length_toList, Array.all_toList] at h'
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem, id] at h'
      obtain ⟨⟨c1, c2⟩, c3⟩ := h'
      exact (VerifiableInference.Desc.First.Close.countsHead_iff _).2
        ⟨a, rfl, ho, c1, c2, c3⟩
  | between => exact nomatch h
  | lay a => exact nomatch h
  | att a => exact nomatch h
  | fin a => exact nomatch h
  | mem a => exact nomatch h

theorem leftHead_sh (s : S) : (leftHead s).map mergeSh = leftHeadSh (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

/-- **The step at the head's link.** -/
def clearHeadG (X : LinkPub) (lay : WsLay) (lin : LinShape) : ChainSh → Except String ChainSh :=
  clearG X lay lin countsHeadB leftHeadSh

theorem clearHead_carries (X : LinkPub) (lay : WsLay) (lin : LinShape) (s t : S) (u : ChainSh)
    (h : tailHead X lay lin s = .ok t) (hg : clearHeadG X lay lin (chainSh s) = .ok u) :
    u = chainSh t :=
  clear_carries leftHead_sh s t u h hg

theorem clearHead_returns (X : LinkPub) (lay : WsLay) (lin : LinShape) (s : S) (u : ChainSh)
    (hg : clearHeadG X lay lin (chainSh s) = .ok u) : ∃ t, tailHead X lay lin s = .ok t :=
  clear_returns countsHead_sh leftHead_sh s u hg

end Johnson.Desc.First.Walk.Shape

#print axioms Johnson.Desc.First.Walk.Shape.clearLay_carries
#print axioms Johnson.Desc.First.Walk.Shape.clearLay_returns
#print axioms Johnson.Desc.First.Walk.Shape.clearHead_carries
#print axioms Johnson.Desc.First.Walk.Shape.clearHead_returns
#print axioms Johnson.Desc.First.Walk.Shape.chainSh_leave
#print axioms Johnson.Desc.First.Walk.Shape.clear_carries
#print axioms Johnson.Desc.First.Walk.Shape.clear_returns
#print axioms Johnson.Desc.First.Walk.Shape.leaveAll
#print axioms Johnson.Desc.First.Walk.Shape.leaveAll_mk
#print axioms Johnson.Desc.First.Walk.Shape.leave_iff
#print axioms Johnson.Desc.First.Walk.Shape.chainSh_kept
#print axioms Johnson.Desc.First.Walk.Shape.clearB
#print axioms Johnson.Desc.First.Walk.Shape.clearG
#print axioms Johnson.Desc.First.Walk.Shape.countsLayB
#print axioms Johnson.Desc.First.Walk.Shape.leftLaySh
#print axioms Johnson.Desc.First.Walk.Shape.countsLay_sh
#print axioms Johnson.Desc.First.Walk.Shape.leftLay_sh
#print axioms Johnson.Desc.First.Walk.Shape.clearLayG
#print axioms Johnson.Desc.First.Walk.Shape.countsHeadB
#print axioms Johnson.Desc.First.Walk.Shape.leftHeadSh
#print axioms Johnson.Desc.First.Walk.Shape.countsHead_sh
#print axioms Johnson.Desc.First.Walk.Shape.leftHead_sh
#print axioms Johnson.Desc.First.Walk.Shape.clearHeadG
