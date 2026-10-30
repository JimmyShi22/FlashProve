-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/HonestAtClosing.lean: the kind "the code switch" (K2): THE
FIELD honest OF `MadeAsks` (ExchangeAtMade.lean of this folder) AT THE PLACE's OWN SIZES: where the
part's laying returns V and the lot's closing returns W: off the pads' places the main rows of the
carrying message and of the kept copies in V are `mainRows` at W (`HonestMain`,
Johnson/Desc/K2/Honest/Inner/Statement.lean): UNDER A RECORD OF PUBLIC PREMISES ON THE PLACE AND THE
SEGMENT IN FRONT. One structure: premises' forms; statements with their proofs.

  `filter_range_map`   a law on lists: the numbers below a list's length at which a test says yes,
                    mapped to the entries, are the entries at which it says yes
  `shape_keptNo`    the shape at the number of the kept member number a is entry a of the kept
                    members' shapes; an empty shape on both sides beyond the last
  `lotClosingAt_kept`   where the lot's closing returns W, the walk over the segments has handed on
                    W WITH THE PLACE's OWN KEPT SHAPES: the closing's own test
  `kept_base`       WHAT THE CLOSING RETURNS AT A KEPT MEMBER OVER THE BASE FIELD LIES IN THE BASE
                    FIELD: in range, the entry is the image of its first coordinate
  `laid_off_pad`    one message of a laid sending, off the pads' places, in both fields
  `HonestPublic`    THE PUBLIC PREMISES, at a place and the segment in front
  `honestMain_at_closing`   THE END

By: `rowsLaid_inv` (SenderOwn.lean) · `laidMain_e`, `laidMain_f` (MainTxt.lean) ·
`foldEnd_kept_main` (KeptAtClosing.lean) · `closingFrom_last` (ClosingLast.lean) ·
`segmentLeft_inv` (SegmentLeftInv.lean) · `frozen_kept` (ClaimFrozen.lean), all of this folder ·
`padInMain_pad` (Honest/Law/LaysRoom.lean, of other authors).

Limits. AT THE PLACE's SIZES p.sizes: THE FIELD ASKS IT AT `sizesAt` OF THE STATEMENT AT A YES: that
these are one is not said here. `HonestPublic` IS SHOWN OF NO PLACE HERE. Both returns are premises.
WHAT IS WRITTEN WHERE: an equation at each run's coins between two texts' values: nothing on what an
entry is for. Off the pads alone. Nothing on the tails, the mask rows or the own messages. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.Law.LaysRoom
import Johnson.Desc.K2.Honest.Inner.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left GroupMember HonestMain mainRows zeroG keptNo)
open OnBytes.Slice (GE GF)

variable {W₀ Rc Xi Tr : Type}

/-! ## 1 Lists -/

/-- The numbers below a list's length at which a test says yes, mapped to the entries. -/
theorem filter_range_map {α β : Type} (p : α → Bool) (f : α → β) (d : β) : ∀ l : List α,
    ((List.range l.length).filter fun w => ((l[w]?).map p).getD false).map
      (fun w => ((l[w]?).map f).getD d) = (l.filter p).map f
  | [] => rfl
  | a :: l => by
    have ih := filter_range_map p f d l
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map,
      List.filter_cons]
    have e : ((List.range l.length).filter
        ((fun w => (((a :: l)[w]?).map p).getD false) ∘ Nat.succ)) =
        (List.range l.length).filter fun w => ((l[w]?).map p).getD false := rfl
    rw [e]
    have h0 : ((((a :: l)[0]?).map p).getD false) = p a := rfl
    rw [h0]
    cases p a
    · simp only [Bool.false_eq_true, if_false, List.map_map]
      exact ih
    · simp only [if_true, List.map_cons, List.map_map]
      exact congrArg (f a :: ·) ih

/-- The shape at the number of the kept member number a. -/
theorem shape_keptNo (ms : List GroupMember) (a : Nat) :
    VerifiableInference.Desc.K2.Honest.shapeOf ms (keptNo ms a) =
      ((ms.filter (·.kept)).map (·.shape)).getD a {} := by
  rw [← filter_range_map (·.kept) (·.shape) {} ms]
  have hn : VerifiableInference.Desc.K2.Honest.shapeOf ms ms.length = {} := by
    show ((ms[ms.length]?).map (·.shape)).getD {} = {}
    rw [List.getElem?_eq_none (Nat.le_refl _)]
    rfl
  have e : (((List.range ms.length).filter fun w => ((ms[w]?).map (·.kept)).getD false).map
      fun w => VerifiableInference.Desc.K2.Honest.shapeOf ms w).getD a
        (VerifiableInference.Desc.K2.Honest.shapeOf ms ms.length) =
      VerifiableInference.Desc.K2.Honest.shapeOf ms (keptNo ms a) := List.getD_map _ _ _
  rw [hn] at e
  exact e.symm

/-! ## 2 What the closing returns at a kept member -/

/-- **The closing's own test**: the walk has handed on W with the place's own kept shapes. -/
theorem lotClosingAt_kept {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub}
    {p : SwitchPlace} {D : RowData} {Rd : Readers} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {W : Left}
    (h : lotClosingAt lay segs p D Rd heard k = .ok W) :
    ∃ x, closingFrom freshTable (lotOwn segs p D Rd heard) heard k (segs.take p.link) 0 0 none =
        .ok x ∧ x.1 = some (W, p.sizes.kept) := by
  obtain ⟨x, kept, hx, ex⟩ := lotClosingAt_inv h
  refine ⟨x, hx, ?_⟩
  unfold lotClosingAt at h
  cases ho : ownLaid D lay p (segs.take p.link) with
  | error e =>
    rw [ho] at h
    cases h
  | ok u =>
    rw [ho] at h
    have h' : closingFor freshTable (segs.take p.link) p.sizes.kept (lotOwn segs p D Rd heard) heard
        k = .ok W := h
    unfold closingFor at h'
    rw [hx] at h'
    have h2 : (match x.1 with
      | some Wk =>
        if Wk.2 != p.sizes.kept then
          (.error "a switch's kept members are not those that the fold in front left" :
            Except String Left)
        else .ok Wk.1
      | none => .error "no segment stands in front of the switch") = .ok W := h'
    rw [ex] at h2
    have h3 : (if kept != p.sizes.kept then
        (.error "a switch's kept members are not those that the fold in front left" :
          Except String Left)
      else .ok W) = .ok W := h2
    by_cases hk : (kept != p.sizes.kept) = true
    · rw [if_pos hk] at h3
      cases h3
    · have e : kept = p.sizes.kept := by
        simpa using hk
      rw [ex, e]

/-- **WHAT THE CLOSING RETURNS AT A KEPT MEMBER OVER THE BASE FIELD LIES IN THE BASE FIELD**, in
range. -/
theorem kept_base {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub}
    {p : SwitchPlace} {D : RowData} {Rd : Readers} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {W : Left}
    (hW : lotClosingAt lay segs p D Rd heard k = .ok W) {A : List SegmentPub} {Sg : SegmentPub}
    (hA : segs.take p.link = A ++ [Sg]) {a b j : Nat} (ha : a < p.sizes.kept.length)
    (hb : b < (p.sizes.kept.getD a {}).mainRows)
    (hj : j < (Sg.sizes.codes.base.getD Sg.sizes.code default).ell)
    (h3 : ((p.sizes.kept.getD a {}).mainDeg == 3) = false) :
    algebraMap GF GE ((W.kept a).main b j).c0 = (W.kept a).main b j := by
  obtain ⟨x, hx, ex⟩ := lotClosingAt_kept hW
  rw [hA] at hx
  obtain ⟨y, Wk, -, hs, e2, -⟩ := closingFrom_last hx
  obtain rfl : Wk = (W, p.sizes.kept) := Option.some.inj (e2.symm.trans ex)
  obtain ⟨R, -, hk, hWe⟩ := segmentLeft_inv hs
  rw [hWe, frozen_kept _ _ _ _ a b j ha hb hj, foldEnd_kept_main, shape_keptNo, ← hk, h3]
  rfl

/-! ## 3 One message of a laid sending -/

/-- **One message, off the pads' places, in both fields.** hbase: over the base field the datum
lies in the base field. -/
theorem laid_off_pad {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
    {fresh : Option (Nat × Nat)} {data : Nat → Nat → Nat → Cb.Gl.E}
    {c : Cs (sendingDue codes sent fresh)} {V : Nat → Johnson.Prover.Send.Rows}
    (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n : Nat} (hn : n < sent.size) {s : OnBytes.OracleShape}
    (hs : (sent.getD n default).shape = s) {b j : Nat} (hb : b < s.mainRows)
    (hj : j < (codes.base.getD s.code default).ell) (ha : s.answers ≠ 0)
    (hpad : (OnBytes.Send.pad codes s).isSome = true)
    (hnp : (b + j * 2 ^ OnBytes.ceilLog2 s.mainRows) ∉
      ((OnBytes.padPlaces codes s).filter fun q => q.part == .main).map (·.index))
    (hbase : (s.mainDeg == 3) = false → algebraMap GF GE (data n b j).c0 = data n b j) :
    (V n).main (s.mainDeg == 3) b j = data n b j := by
  subst hs
  obtain ⟨pad, hpd⟩ := Option.isSome_iff_exists.1 hpad
  have hp : (b, j) ∉ padInMain (codes.base.getD (sent.getD n default).shape.code default).ell
      (sent.getD n default).shape := by
    intro hin
    obtain ⟨q, hq, hqm, hqi⟩ := padInMain_pad codes _ hpd hin
    apply hnp
    unfold OnBytes.padPlaces
    rw [hpd]
    exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by rw [hqm]; rfl⟩, hqi⟩
  unfold Johnson.Prover.Send.Rows.main
  cases h3 : ((sent.getD n default).shape.mainDeg == 3)
  · rw [if_neg Bool.false_ne_true, laidMain_f hw h hn h3 hb hj ha hp]
    exact hbase h3
  · rw [if_pos rfl, laidMain_e hw h hn h3 hb hj ha hp]

/-! ## 4 The end -/

/-- **THE PUBLIC PREMISES**, at a place and the segment in front. A structure of premises' forms:
public data alone. Nothing here proves that it can be met. -/
structure HonestPublic (p : SwitchPlace) (Sg : SegmentPub) : Prop where
  /-- every message of the sending with a main row is sampled -/
  noWord : NoWord (switchSent p.sizes p.others)
  /-- the sending holds the carrying message and a copy for each kept member -/
  size : 1 + p.sizes.kept.length ≤ (switchSent p.sizes p.others).size
  /-- message 0 has the target's shape -/
  first : ((switchSent p.sizes p.others).getD 0 default).shape = p.sizes.target.shape
  /-- message 1 + a has the kept member's shape -/
  copies : ∀ a, a < p.sizes.kept.length →
    ((switchSent p.sizes p.others).getD (1 + a) default).shape = p.sizes.kept.getD a {}
  /-- the carrying message is over the extension field -/
  overE : (p.sizes.target.shape.mainDeg == 3) = true
  /-- each of these messages is sampled, and the programs' pad returns at its shape -/
  firstAns : p.sizes.target.shape.answers ≠ 0
  firstPad : (OnBytes.Send.pad p.sizes.codes p.sizes.target.shape).isSome = true
  copyAns : ∀ a, a < p.sizes.kept.length → (p.sizes.kept.getD a {}).answers ≠ 0
  copyPad : ∀ a, a < p.sizes.kept.length →
    (OnBytes.Send.pad p.sizes.codes (p.sizes.kept.getD a {})).isSome = true
  /-- a kept member's code is no longer than the closed group's main code -/
  room : ∀ a, a < p.sizes.kept.length →
    (p.sizes.codes.base.getD (p.sizes.kept.getD a {}).code default).ell ≤
      (Sg.sizes.codes.base.getD Sg.sizes.code default).ell

/-- hV, hW AND hP ARE PREMISES. **THE FIELD honest, AT THE PLACE's OWN SIZES.** An equation at each
run's coins: what is written where. -/
theorem honestMain_at_closing {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
    {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub} {p : SwitchPlace}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {V : Nat → Johnson.Prover.Send.Rows} {Wl : Left}
    (hV : switchRowsLaid D readers (lotClosingAt lay segs) p c w hd = .ok V)
    (hW : lotClosingAt lay segs p (D w.x) (readers w) (hd.take (hd.length - 0))
      (Stretch.carried p.carries c.2.2) = .ok Wl)
    {A : List SegmentPub} {Sg : SegmentPub} (hA : segs.take p.link = A ++ [Sg])
    (hP : HonestPublic p Sg) : HonestMain p.sizes Wl V := by
  obtain ⟨Wl', hW', hR⟩ := rowsLaid_inv hV
  obtain rfl : Wl' = Wl := Except.ok.inj (hW'.symm.trans hW)
  intro k hk
  by_cases h0 : k = 0
  · subst h0
    simp only [if_true]
    intro b j hb hj hnp
    exact laid_off_pad hP.noWord hR (by have := hP.size; omega) hP.first hb hj hP.firstAns
      hP.firstPad hnp (fun h3 => by rw [hP.overE] at h3; cases h3)
  · simp only [if_neg h0]
    intro b j hb hj hnp
    have ha : k - 1 < p.sizes.kept.length := by omega
    have ek : 1 + (k - 1) = k := by omega
    have hs := hP.copies (k - 1) ha
    rw [ek] at hs
    have hm : ∀ own, mainRows p.sizes Wl' own k = (Wl'.kept (k - 1)).main := by
      intro own
      have h1 : ¬ ((k == 0) = true) := by simpa using h0
      simp only [mainRows, if_neg h1, if_pos hk]
    rw [hm]
    have t := laid_off_pad hP.noWord hR (by have := hP.size; omega) hs hb hj (hP.copyAns _ ha)
      (hP.copyPad _ ha) hnp (fun h3 => by
        rw [hm]
        exact kept_base hW hA ha hb (Nat.lt_of_lt_of_le hj (hP.room _ ha)) h3)
    rw [hm] at t
    exact t

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.filter_range_map
#print axioms ProofFile.Honest.K2.Law.shape_keptNo
#print axioms ProofFile.Honest.K2.Law.lotClosingAt_kept
#print axioms ProofFile.Honest.K2.Law.kept_base
#print axioms ProofFile.Honest.K2.Law.laid_off_pad
#print axioms ProofFile.Honest.K2.Law.HonestPublic
#print axioms ProofFile.Honest.K2.Law.honestMain_at_closing
