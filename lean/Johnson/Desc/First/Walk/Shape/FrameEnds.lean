-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Walk/Shape/FrameEnds.lean: the link's frame (Johnson/Desc/First/Walk/Frame.lean,
FrameZero.lean) against the shape of the first chain's state (chainSh,
Johnson/Desc/First/Shape/Chain.lean), continued: "opened" at link 0 (openLayZero), and "cleared" at
an attention link (clearWith with attention's counts, where the link leaves no row): ONE STEP ON THE
SHAPE each, and the two laws "carries" and "returns" of FrameChain.lean. General laws; nothing is
evaluated. No test on values stands in these texts.

  `imOf room a`: the index-mask message's number, read off the shape: just one message at the
    chain's start; it has a ledger; the ledger has room. `imOf_iff`: it is the library's
    IndexMasksAt.
  `openZeroG P fvs kCol`: the step at link 0: openB at link 0; imOf; that number is laid; then the
    plan's numbers enter as at every layers' link. **`openZero_carries`**, **`openZero_returns`**
    (under the sub-protocol's own test on the plan, planLayZero).
  `samePlanSh`, `countsAttB`: the library's samePlan and attention's six counts, on shapes.
    `clearAttB`: an attention link is open; no mark; the counts; the sub-proof has drawn its last
    challenge and closed its link; it has worked on the plan. `leaveSh`: an attention link's part is
    dropped, the live state of the calls taken back.
  `clearAttG X nLin`: the step. **`clearAtt_carries`**, **`clearAtt_returns`** (under X.fv = false:
    the link leaves no row).

Limits. "cleared" at a layers' link and at the head's link lays a row on the pile by a function of
its own (pendingRowO; tailHead): not here. The texts are the bare ones: in a seated chain they are
asked together with "no mark" and the wrapper's comparison. That a step returns at a shape that the
chain reaches is not shown. openZero_returns asks the whole of planLayZero and spends three of its
six clauses (the group's number, the list, the sizes). Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Walk.Shape.FrameChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Props

/-! ## 1 "opened" at link 0 -/

/-- The index-mask message's number, off the shape. -/
def imOf (room : Nat) (a : ChainSh) : Option Nat :=
  if a.check.frame.atStart.size == 1 then
    (a.check.frame.atStart[0]?).bind fun im =>
      match a.ledgers[im]? with
      | some (some l) => if room ≤ (if l.closed then 0 else l.left) then some im else none
      | _ => none
  else none

theorem ledgers_sh (s : S) (im : Nat) :
    (chainSh s).ledgers[im]? = (s.st.oracles[im]?).map (·.ledger) := by
  rw [chainSh_ledgers, Array.getElem?_map]

theorem imOf_iff (room : Nat) (s : S) (im : Nat) :
    imOf room (chainSh s) = some im ↔ IndexMasksAt room s.check s.st.oracles im := by
  unfold imOf IndexMasksAt
  show (if (s.check.frame.atStart.size == 1) = true then
    (s.check.frame.atStart[0]?).bind fun im =>
      match (chainSh s).ledgers[im]? with
      | some (some l) => if room ≤ (if l.closed then 0 else l.left) then some im else none
      | _ => none
    else none) = some im ↔ _
  by_cases h1 : s.check.frame.atStart.size = 1
  · rw [if_pos (by simpa using h1)]
    cases h2 : s.check.frame.atStart[0]? with
    | none => simp [h1]
    | some j =>
      show (match (chainSh s).ledgers[j]? with
        | some (some l) => if room ≤ (if l.closed then 0 else l.left) then some j else none
        | _ => none) = some im ↔ _
      rw [ledgers_sh]
      cases h3 : s.st.oracles[j]? with
      | none =>
        constructor
        · intro h; exact nomatch h
        · rintro ⟨-, e, x, l, hx, -⟩
          obtain rfl := Option.some.inj e
          rw [h3] at hx
          exact nomatch hx
      | some x =>
        cases h4 : x.ledger with
        | none =>
          constructor
          · intro h
            simp [h4] at h
          · rintro ⟨-, e, y, l, hy, hl, -⟩
            obtain rfl := Option.some.inj e
            rw [h3] at hy
            obtain rfl := Option.some.inj hy
            rw [h4] at hl
            exact nomatch hl
        | some l =>
          simp only [Option.map_some, h4]
          by_cases h5 : room ≤ (if l.closed then 0 else l.left)
          · rw [if_pos h5]
            constructor
            · intro h
              obtain rfl := Option.some.inj h
              exact ⟨h1, rfl, x, l, h3, h4, h5⟩
            · rintro ⟨-, e, -⟩
              exact e
          · rw [if_neg h5]
            constructor
            · intro h; exact nomatch h
            · rintro ⟨-, e, y, l', hy, hl, hr⟩
              obtain rfl := Option.some.inj e
              rw [h3] at hy
              obtain rfl := Option.some.inj hy
              rw [h4] at hl
              obtain rfl := Option.some.inj hl
              exact absurd hr h5
  · rw [if_neg (by simpa using h1)]
    constructor
    · intro h; exact nomatch h
    · rintro ⟨e, -⟩
      exact absurd e h1

/-- **The step at link 0.** -/
def openZeroG (P : LayPar) (fvs : List Bool) (kCol : Nat) (a : ChainSh) : Except String ChainSh :=
  if openB 0 P.X.kind a then
    match imOf (roomOf fvs kCol) a with
    | some im =>
      .ok (enterSh 1 (tailSh P.tl₀) ((ledSh P.X.Fp).fresh P.ns) P.X 0 (a.setIndexMasks im))
    | none => .error "opened: the index-mask message"
  else .error "opened: the shape"

theorem chainSh_layZero (s : S) (hB : s.atBetween = true) (X : LinkPub) (n im : Nat)
    (tl : HTailF2) :
    chainSh { s with out := { s.out with indexMasks := im }, here := (.lay
      { L := { check := s.check, link := 0, arrayOf := X.arrayOf, list := X.Tp },
        F := startFork X n, tl := tl }) } =
      enterSh 1 (tailSh tl) ((ledSh X.Fp).fresh n) X 0 ((chainSh s).setIndexMasks im) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | between =>
    rw [← ledSh_startFork]
    rfl
  | _ => exact nomatch hB

theorem openZero_lays {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) :
    s.atBetween = true ∧ ∃ im, IndexMasksAt (roomOf fvs kCol) s.check s.st.oracles im ∧
      t = { s with out := { s.out with indexMasks := im }, here := (.lay
        { L := { check := s.check, link := 0, arrayOf := P.X.arrayOf, list := P.X.Tp },
          F := startFork P.X P.ns, tl := P.tl₀ }) } := by
  obtain ⟨hB, -, a, ⟨im, hi, ⟨-, -, hL, ho⟩, -, -, -, hF⟩, he⟩ := openLayZero_iff.1 h
  refine ⟨hB, im, hi, ?_⟩
  have hu := ((S.unmarked_ok _ _).1 he).1
  have hb' : ({ s with out := a.out } : S).atBetween = true := hB
  rw [← hu]
  unfold S.enterLay
  rw [if_pos hb', hL, hF, ho]

theorem openZero_carries (P : LayPar) (fvs : List Bool) (kCol : Nat) (s t : S) (u : ChainSh)
    (h : openLayZero P fvs kCol s = .ok t) (hg : openZeroG P fvs kCol (chainSh s) = .ok u) :
    u = chainSh t := by
  obtain ⟨hB, im, hi, rfl⟩ := openZero_lays h
  unfold openZeroG at hg
  by_cases hb : openB 0 P.X.kind (chainSh s) = true
  · rw [if_pos hb, (imOf_iff _ s im).2 hi] at hg
    rw [chainSh_layZero s hB]
    exact (Except.ok.inj hg).symm
  · rw [if_neg hb] at hg
    exact nomatch hg

theorem openZero_returns {shape : Params.ReqShape} (P : LayPar) (fvs : List Bool) (kCol : Nat)
    (hp : planLayZero shape P = true) (s : S) (u : ChainSh)
    (hg : openZeroG P fvs kCol (chainSh s) = .ok u) : ∃ t, openLayZero P fvs kCol s = .ok t := by
  unfold openZeroG at hg
  by_cases hb : openB 0 P.X.kind (chainSh s) = true
  · rw [if_pos hb] at hg
    cases hi : imOf (roomOf fvs kCol) (chainSh s) with
    | none => rw [hi] at hg; exact nomatch hg
    | some im =>
      obtain ⟨hB, hR, hf, h1, h2⟩ := (openB_iff _ _ s).1 hb
      obtain ⟨-, -, q1, q2, q3, -⟩ := (planLayZero_iff shape P).1 hp
      refine ⟨_, openLayZero_iff.2 ⟨hB, hR,
        ⟨{ check := s.check, link := 0, arrayOf := P.X.arrayOf, list := P.X.Tp },
          { s.out with indexMasks := im }, startFork P.X P.ns⟩,
        ⟨im, (imOf_iff _ s im).1 hi, ⟨h1, h2, rfl, rfl⟩, q1, q2, q3, rfl⟩,
        (S.unmarked_ok _ _).2 ⟨rfl, ?_⟩⟩⟩
      have hb' : ({ s with out := { s.out with indexMasks := im } } : S).atBetween = true := hB
      unfold S.enterLay
      rw [if_pos hb']
      exact hf
  · rw [if_neg hb] at hg
    exact nomatch hg

/-! ## 2 "cleared" where no row is left -/

/-- samePlan, on shapes. -/
def samePlanSh (X : LinkPub) (L : LedSh) (list : Tail2) : Bool :=
  list.nt == X.Tp.nt &&
    (List.range X.Tp.nt.size).all fun t =>
      match L.trees[t]?, X.Fp.trees[t]? with
      | some a, some b => a.R == b.R && a.K == b.K
      | _, _ => false

theorem samePlan_sh (X : LinkPub) (F : Fork) (list : Tail2) :
    samePlan X F list = samePlanSh X (ledSh F) list := by
  unfold samePlan samePlanSh
  congr 1
  refine List.all_congr rfl ?_
  intro t
  show _ = (match (F.trees.toList.map treeSh)[t]?, X.Fp.trees[t]? with
    | some a, some b => a.R == b.R && a.K == b.K
    | _, _ => false)
  rw [List.getElem?_map, Array.getElem?_toList]
  cases F.trees[t]? <;> cases X.Fp.trees[t]? <;> rfl

/-- Attention's six counts, on shapes. -/
def countsAttB (nLin : Nat) (t : TailSh) (L : LedSh) : Bool :=
  L.claims == L.planClaims && (L.handed.length == L.planClaims && L.handed.all id) &&
    (t.foldTakenF.size == t.NM && t.foldTakenF.all id) && L.claims == nLin && t.foldDrawn == 1 &&
    t.heard.isSome

/-- What an ATTENTION link holds is dropped (tl, led, tables, link, look, lookHeard, att); the live
state of the calls is taken back. own and head stay: for the other links see ClearRow.lean's
leaveAll. -/
def leaveSh (a : ChainSh) : ChainSh :=
  ((((((((a.setCheck a.live).setHere 0).layTl none).layLed none).layTables none).layLink
    none).layLook none).layLookHeard none).layAtt none

/-- The test. -/
def clearAttB (X : LinkPub) (nLin : Nat) (a : ChainSh) : Bool :=
  match a.link, a.led, a.tl with
  | some C, some L, some t =>
    a.here == 2 && !a.marked && countsAttB nLin t L && C.handed && C.done &&
      samePlanSh X L C.list
  | _, _, _ => false

/-- **The step.** -/
def clearAttG (X : LinkPub) (nLin : Nat) (a : ChainSh) : Except String ChainSh :=
  if clearAttB X nLin a then .ok (leaveSh a) else .error "cleared: the shape"

theorem countsAtt_sh (nLin : Nat) (tl : HTailF2) (F : Fork) :
    countsAttB nLin (tailSh tl) (ledSh F) =
      (F.nClaim == F.planClaimsF && weightsOut F && foldsOut tl && F.nClaim == nLin &&
        tl.foldDrawn == 1 && tl.heard.isSome) := by
  unfold countsAttB weightsOut foldsOut
  show (F.nClaim == F.planClaimsF &&
    (F.kapMapF.toList.length == F.planClaimsF && F.kapMapF.toList.all id) &&
    (tl.foldTakenF.size == tl.NM && tl.foldTakenF.all id) && F.nClaim == nLin &&
    tl.foldDrawn == 1 && (tl.heard.map heardAll).isSome) = _
  rw [Array.length_toList, Array.all_toList, Option.isSome_map]

/-- The shape behind the leaving of an attention link. -/
theorem chainSh_leaveAtt (s : S) (a : VerifiableInference.Desc.First.AttOwn)
    (h : s.here = .att a) :
    chainSh { s with check := s.live, here := .between } = leaveSh (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  obtain rfl : here = .att a := h
  rfl

theorem clearAttB_iff (X : LinkPub) (nLin : Nat) (s : S) :
    clearAttB X nLin (chainSh s) = true ↔
      s.failed = none ∧ CountsAtt nLin s ∧
        ∃ C F, s.link? = some C ∧ s.fork? = some F ∧ C.handed = true ∧ C.done = true ∧
          SamePlan X F C.list := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | att a =>
    show (((2 : Nat) == 2) && !failed.isSome && countsAttB nLin (tailSh a.tl) (ledSh a.F) &&
      a.L.handed && a.L.done && samePlanSh X (ledSh a.F) a.L.list) = true ↔ _
    rw [countsAtt_sh, ← samePlan_sh]
    simp only [Bool.and_eq_true, beq_self_eq_true, true_and, Bool.not_eq_true',
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, beq_iff_eq, samePlan_iff,
      weightsOut_iff, foldsOut_iff]
    constructor
    · rintro ⟨⟨⟨⟨hf, ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩⟩, w1⟩, w2⟩, w3⟩
      exact ⟨hf, ⟨a, rfl, c1, c2, c3, c4, c5, c6⟩, a.L, a.F, rfl, rfl, w1, w2, w3⟩
    · rintro ⟨hf, ⟨a', e, c1, c2, c3, c4, c5, c6⟩, C, F, eC, eF, w1, w2, w3⟩
      obtain rfl : a = a' := by injection e
      obtain rfl : a.L = C := Option.some.inj eC
      obtain rfl : a.F = F := Option.some.inj eF
      exact ⟨⟨⟨⟨hf, ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩⟩, w1⟩, w2⟩, w3⟩
  | between =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨-, ⟨a', e, -⟩, -⟩; exact nomatch e
  | lay a =>
    constructor
    · intro h
      have h' : (((1 : Nat) == 2) && !failed.isSome && countsAttB nLin (tailSh a.tl) (ledSh a.F) &&
        a.L.handed && a.L.done && samePlanSh X (ledSh a.F) a.L.list) = true := h
      simp at h'
    · rintro ⟨-, ⟨a', e, -⟩, -⟩; exact nomatch e
  | head a =>
    constructor
    · intro h
      exfalso
      cases ho : a.opened with
      | false =>
        have h' : clearAttB X nLin (chainSh ⟨st, book, roots, rowsOwed, failed, check, out,
          .head a, req⟩) = true := h
        simp [clearAttB, chainSh, ChainSh.mk, ChainSh.link, ChainSh.led, ChainSh.tl, S.link?,
          S.fork?, S.tl?, ho] at h'
      | true =>
        have h' : clearAttB X nLin (chainSh ⟨st, book, roots, rowsOwed, failed, check, out,
          .head a, req⟩) = true := h
        simp [clearAttB, chainSh, ChainSh.mk, ChainSh.link, ChainSh.led, ChainSh.tl, ChainSh.here,
          S.link?, S.fork?, S.tl?, hereNo, ho] at h'
    · rintro ⟨-, ⟨a', e, -⟩, -⟩; exact nomatch e
  | fin a =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨-, ⟨a', e, -⟩, -⟩; exact nomatch e
  | mem a =>
    constructor
    · intro h; exact nomatch h
    · rintro ⟨-, ⟨a', e, -⟩, -⟩; exact nomatch e

theorem leave_att {s : S} {a : VerifiableInference.Desc.First.AttOwn} (h : s.here = .att a)
    (t : S) : s.leaveLink? = .ok t ↔
      t = { s with check := s.live, here := .between } ∧ s.failed = none := by
  have hi : s.inLink = true := by
    unfold S.inLink S.fork?
    rw [h]
    rfl
  unfold S.leaveLink? S.leaveLink
  rw [if_pos hi, S.unmarked_ok]
  constructor
  · rintro ⟨rfl, hf⟩
    exact ⟨rfl, hf⟩
  · rintro ⟨rfl, hf⟩
    exact ⟨rfl, hf⟩

theorem clearAtt_carries (X : LinkPub) (nLin : Nat) (left : S → Option WsForkOut) (row : RowFn)
    (hv : X.fv = false) (s t : S) (u : ChainSh)
    (h : clearWith X (countsAtt nLin) left row s = .ok t)
    (hg : clearAttG X nLin (chainSh s) = .ok u) : u = chainSh t := by
  obtain ⟨C, F, -, -, hc, k, r, hb, hr⟩ := clearWith_iff.1 h
  obtain ⟨a, ha, -⟩ := countsAtt_iff.1 hc
  have hn : r = none := hb.2.2.2.2.1 hv
  subst hn
  rcases hr with ⟨-, hl⟩ | ⟨w, q, os, e, -⟩
  · obtain ⟨rfl, -⟩ := (leave_att ha t).1 hl
    unfold clearAttG at hg
    by_cases hB : clearAttB X nLin (chainSh s) = true
    · rw [if_pos hB] at hg
      rw [chainSh_leaveAtt s a ha]
      exact (Except.ok.inj hg).symm
    · rw [if_neg hB] at hg
      exact nomatch hg
  · exact nomatch e

theorem clearAtt_returns (X : LinkPub) (nLin : Nat) (left : S → Option WsForkOut) (row : RowFn)
    (hv : X.fv = false) (s : S) (u : ChainSh) (hg : clearAttG X nLin (chainSh s) = .ok u) :
    ∃ t, clearWith X (countsAtt nLin) left row s = .ok t := by
  unfold clearAttG at hg
  by_cases hB : clearAttB X nLin (chainSh s) = true
  · obtain ⟨hf, hc, C, F, eC, eF, w1, w2, w3⟩ := (clearAttB_iff X nLin s).1 hB
    obtain ⟨a, ha, -⟩ := id hc
    refine ⟨_, clearWith_iff.2 ⟨C, F, eC, eF, countsAtt_iff.2 hc, C.check, none,
      ⟨w1, w2, w3, rfl, fun _ => rfl, fun h => absurd (hv.symm.trans h) (by decide)⟩,
      Or.inl ⟨rfl, (leave_att ha _).2 ⟨rfl, hf⟩⟩⟩⟩
  · rw [if_neg hB] at hg
    exact nomatch hg

end Johnson.Desc.First.Walk.Shape

#print axioms Johnson.Desc.First.Walk.Shape.clearAttB_iff
#print axioms Johnson.Desc.First.Walk.Shape.clearAtt_carries
#print axioms Johnson.Desc.First.Walk.Shape.clearAtt_returns
#print axioms Johnson.Desc.First.Walk.Shape.imOf_iff
#print axioms Johnson.Desc.First.Walk.Shape.openZero_carries
#print axioms Johnson.Desc.First.Walk.Shape.openZero_returns
#print axioms Johnson.Desc.First.Walk.Shape.imOf
#print axioms Johnson.Desc.First.Walk.Shape.ledgers_sh
#print axioms Johnson.Desc.First.Walk.Shape.openZeroG
#print axioms Johnson.Desc.First.Walk.Shape.chainSh_layZero
#print axioms Johnson.Desc.First.Walk.Shape.openZero_lays
#print axioms Johnson.Desc.First.Walk.Shape.samePlanSh
#print axioms Johnson.Desc.First.Walk.Shape.samePlan_sh
#print axioms Johnson.Desc.First.Walk.Shape.countsAttB
#print axioms Johnson.Desc.First.Walk.Shape.leaveSh
#print axioms Johnson.Desc.First.Walk.Shape.clearAttB
#print axioms Johnson.Desc.First.Walk.Shape.clearAttG
#print axioms Johnson.Desc.First.Walk.Shape.countsAtt_sh
#print axioms Johnson.Desc.First.Walk.Shape.chainSh_leaveAtt
#print axioms Johnson.Desc.First.Walk.Shape.leave_att
