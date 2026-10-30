-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AsksLaw.lean: A YES OF THE LOOKUPS' LIGHT TESTS ON PUBLIC DATA
(Johnson/Desc/First/Look/K3Asks.lean) GIVES THE TESTS THAT THE LAWS NAME, AND SO THE LAWS' PREMISES:
the digits' row gives DigOK at every link, at every radius; the row of the guards gives readsB at
every attention link, at every radius, and so AttReadsOK under its fourth field. Statements and
proofs. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: the functions digRow and readsRow of K3Asks.lean.
USER: K3AsksDoorLaw.lean (asks_dig, asks_reads), K3AsksPlan.lean (digB_up),
  Johnson/P5T/DigAtHead.lean (asks_dig), Johnson/Desc/First/Link/Law/K9Row11.lean (port_up).
LETTERS: X : Verify.Public, D : K3Asks.Sent free; rad free in the conclusions.
Compiled with the whole library.


Main names:
  `Sent.up`: the light record as the record of the laws' files: the same four fields.
  `shape_up`: shapeB's yes gives the library's shapeTest2 (`tail_up`, `row_up`, `call_up`,
    `port_up`: its four parts).
  `digB_up`, `readsB_up`: a yes of the light test at a link gives the laws' test there.
  `asks_dig`: digRow X D = true: DigOK at every link, at D.up, at every radius, at the prime.
  `asks_reads`, `asks_attReads`: readsRow X D = true: readsB at every attention link; AttReadsOK
    there under its fourth field.

Limits. One way: a yes here gives the laws' yes; that the two say the same is not shown.
AttReadsOK's fourth field (every valid name of a cell has a cell) is no Bool and stays a premise.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Asks
import Johnson.Desc.First.Look.K3CallerTests
import Johnson.Desc.First.Look.K3CallerAttReads
import OnBytes.Tie.Pv.Lookup.Forest.FoLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks
open OnBytes OnBytes.Model OnBytes.DgP
open VerifiableInference.Desc.First.Look (Place P lookAt tlAt)

/-- The light record as the record of the laws' files. -/
def Sent.up (D : Sent) : First.Look.Sent := ⟨D.codes, D.shape, D.layout, D.arrayOf⟩

/-! ## 1 The lists -/

theorem sigList_up (D : Sent) (rad : OracleShape → Nat) (i mom : ℕ) :
    (First.Look.sigList D.up rad i mom).map (·.1) = sigList D i mom := by
  unfold First.Look.sigList sigList
  rw [List.map_map]
  rfl

theorem sigListCalls_up (D : Sent) (rad : OracleShape → Nat) (i : ℕ) :
    (First.Look.sigListCalls D.up rad i).map (·.1) = sigListCalls D i := by
  unfold First.Look.sigListCalls sigListCalls
  rw [List.map_append, sigList_up, List.map_map]
  rfl

/-- A test on the shape of a member that may lack, at a list of pairs and at its shapes. -/
theorem pick_up (l : List (OracleShape × Nat)) (k : ℕ) (f : OracleShape → Bool) :
    (match l[k]? with
      | some o => f o.1
      | none => false) =
    (match (l.map (·.1))[k]? with
      | some o => f o
      | none => false) := by
  rw [List.getElem?_map]
  cases l[k]? <;> rfl

theorem all_up (l : List (OracleShape × Nat)) (f : OracleShape → Bool) :
    (l.all fun o => f o.1) = (l.map (·.1)).all f := by
  rw [List.all_map]
  rfl

/-! ## 2 The arrays -/

theorem trees_up (x : Place) (t : ℕ) :
    x.arrays.arrays[t]? = (x.base.trees[t]?).map fun T => ⟨T.name, T.R, T.K, T.owner⟩ := by
  show (List.map _ x.base.trees.toList)[t]? = _
  rw [List.getElem?_map, Array.getElem?_toList]

theorem arrB_up (x : Place) (D : Sent) (l : List (OracleShape × Nat)) (i t : ℕ) :
    First.Look.arrB x.arrays D.up l i t = arrB x.base.trees D (l.map (·.1)) i t := by
  obtain ⟨codes, shape, layout, arrayOf⟩ := D
  unfold First.Look.arrB arrB
  rw [trees_up]
  dsimp only [Sent.up]
  cases x.base.trees[t]? with
  | none => rfl
  | some T =>
    cases (arrayOf.getD i #[])[t]? with
    | none => rfl
    | some bn =>
      show (bn.1 == i && _) = (bn.1 == i && _)
      congr 1
      cases reqArray layout i bn.2 with
      | none => rfl
      | some a =>
        exact pick_up l a.message fun o => blocksB a.blocks T.R T.K o.mainRows (mainEll codes o)

theorem maskB_up (D : Sent) (l : List (OracleShape × Nat)) (i upTo : ℕ) :
    First.Look.maskB D.up l i upTo = maskB D (l.map (·.1)) i upTo := by
  unfold First.Look.maskB maskB
  show (match (messagesAt D i).findIdx? fun x => x.shape.maskRows != 0 with
    | some m => _
    | none => false) = _
  cases ((messagesAt D i).findIdx? fun x => x.shape.maskRows != 0) with
  | none => rfl
  | some m =>
    exact pick_up l m fun o => decide (0 < o.maskRows) && decide (upTo ≤ maskEll D.codes o)

theorem symArrB_up (D : Sent) (l : List (OracleShape × Nat)) (i t R K : ℕ) :
    First.Look.symArrB D.up l i t R K = symArrB D (l.map (·.1)) i t R K := by
  obtain ⟨codes, shape, layout, arrayOf⟩ := D
  unfold First.Look.symArrB symArrB
  dsimp only [Sent.up]
  cases (arrayOf.getD i #[])[t]? with
  | none => rfl
  | some bn =>
    dsimp only
    cases reqArray layout bn.1 bn.2 with
    | none => rfl
    | some a =>
      dsimp only
      have em : First.Look.msgIn ⟨codes, shape, layout, arrayOf⟩ i bn.1 a.message =
          msgIn ⟨codes, shape, layout, arrayOf⟩ i bn.1 a.message := rfl
      rw [em]
      cases msgIn ⟨codes, shape, layout, arrayOf⟩ i bn.1 a.message with
      | none => rfl
      | some k =>
        exact pick_up l k fun o => blocksB a.blocks R K o.mainRows (mainEll codes o)

theorem maskCallsB_up (D : Sent) (l : List (OracleShape × Nat)) (i upTo : ℕ) :
    First.Look.maskCallsB D.up l i upTo = maskCallsB D (l.map (·.1)) i upTo := by
  unfold First.Look.maskCallsB maskCallsB
  show (match (messagesAt D i).findIdx? fun x => x.shape.maskRows != 0 with
    | some m => _
    | none => false) = _
  cases ((messagesAt D i).findIdx? fun x => x.shape.maskRows != 0) with
  | none => rfl
  | some m =>
    exact pick_up l ((keptAt D i).length + m) fun o =>
      decide (0 < o.maskRows) && decide (upTo ≤ maskEll D.codes o)

/-! ## 3 The test on the smallness test's record -/

theorem countBelow_eq (p : ℕ → Prop) [DecidablePred p] :
    ∀ n, countBelow (fun y => decide (p y)) n = Nat.count p n
  | 0 => rfl
  | n + 1 => by
    rw [countBelow, countBelow_eq p n, Nat.count_succ]
    by_cases h : p n <;> simp [h]

theorem tail_up {tl : HTailF2} (h : tailB tl = true) : tailTest tl = true := by
  simp only [tailB, shapeOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [tailTest, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, fun c hc => ?_⟩
  rw [← countBelow_eq]
  exact h6 c hc

theorem row_up {tl : HTailF2} (h : rowB tl.f9 (2 ^ 10) (2 ^ 8) = true) :
    testRow (portQ tl) (2 ^ t2D0) (2 ^ t2D1) = true := by
  simp only [rowB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [testRow, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h1, h2⟩, h3⟩

theorem call_up {tl : HTailF2} {pp : ℕ} (h : callB tl.f9 pp = true) :
    testCall (portQ tl) pp = true := by
  simp only [callB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [testCall, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun c hc => ⟨(h1 c hc).1, (h1 c hc).2.1, fun _ _ e => e, (h1 c hc).2.2⟩, h2⟩

theorem port_up {tl : HTailF2} (h : portB tl = true) : portTest tl = true := by
  simp only [portB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [portTest, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

/-- **The light test on the record gives the library's.** -/
theorem shape_up {tl : HTailF2} {pp : ℕ} (h : shapeB tl pp = true) : shapeTest2 tl pp = true := by
  simp only [shapeB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp only [shapeTest2, shapeTest, Bool.and_eq_true]
  exact ⟨⟨⟨tail_up h1, row_up h2⟩, call_up h3⟩, port_up h4⟩

/-! ## 4 The digits -/

theorem digAddrB_up (x : Place) (tl : HTailF2) (D : Sent) (l : List (OracleShape × Nat)) :
    First.Look.digAddrB x tl D.up l = digAddrB x tl D (l.map (·.1)) := by
  unfold First.Look.digAddrB digAddrB
  rw [arrB_up, arrB_up, maskB_up, trees_up, trees_up, _root_.FoLedger.elems_eq]
  cases x.base.trees[tl.ix.ZZ]? <;> cases x.base.trees[tl.ix.BZ]? <;> rfl

/-- **A yes of the light test at a link gives the laws' test there**, at every radius. -/
theorem digB_up {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    (h : digB set x tl D = true) (rad : OracleShape → Nat) :
    First.Look.digB set x tl D.up rad Cb.Gl.p = true := by
  simp only [digB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have ep : prime = Cb.Gl.p := Code.pGold_eq.symm
  rw [ep] at h2
  have e : (First.Look.digList x D.up rad).map (·.1) = sigList D x.link (lastMoment D x.link) :=
    sigList_up D rad _ _
  simp only [First.Look.digB, Bool.and_eq_true]
  refine ⟨⟨⟨h1, shape_up h2⟩, ?_⟩, ?_⟩
  · rw [all_up (First.Look.digList x D.up rad) fun o => o.answers == 1, e]
    exact h3
  · rw [digAddrB_up, e]
    exact h4

/-- **THE DIGITS' ROW GIVES DigOK AT EVERY LINK, AT EVERY RADIUS.** -/
theorem asks_dig {X : Verify.Public} {D : Sent} (h : digRow X D = true)
    (rad : OracleShape → Nat) :
    ∀ i < linksOf X, ∃ x tl, First.Look.digAt X i = some (x, tl) ∧
      First.Look.DigOK (Params.settingOf X.P.frame) x tl D.up rad Cb.Gl.p := by
  intro i hi
  have h0 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  have e0 : First.Look.digAt X i = digAt X i := rfl
  cases e : digAt X i with
  | none =>
    rw [e] at h0
    exact absurd h0 (by simp)
  | some xt =>
    rw [e] at h0
    have h1 : digB (Params.settingOf X.P.frame) xt.1 xt.2 D = true := h0
    exact ⟨xt.1, xt.2, e0.trans e,
      First.Look.digOK_at (x := xt.1) (tl := xt.2) (e0.trans e) (digB_up h1 rad)⟩

/-! ## 5 The guards of the reading -/

/-- **A yes of the light guards at a link gives the laws' guards there**, at every radius. -/
theorem readsB_up {x : Place} {tl : HTailF2} {D : Sent} (h : readsB x tl D = true)
    (rad : OracleShape → Nat) : First.Look.readsB x tl D.up rad = true := by
  simp only [readsB, sampledB, seatsB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have e := sigListCalls_up D rad x.link
  simp only [First.Look.readsB, First.Look.sampledB, First.Look.seatsB, Bool.and_eq_true]
  refine ⟨⟨?_, h2⟩, ?_, ?_⟩
  · rw [all_up (First.Look.sigListCalls D.up rad x.link) fun o => o.answers == 1, e]
    exact h1
  · refine List.all_eq_true.2 fun mu hmu => ?_
    rw [symArrB_up, e]
    exact List.all_eq_true.1 h3 mu hmu
  · rw [maskCallsB_up, e, _root_.FoLedger.elems_eq]
    exact h4

/-- **THE ROW OF THE GUARDS GIVES readsB AT EVERY ATTENTION LINK, AT EVERY RADIUS.** -/
theorem asks_reads {X : Verify.Public} {D : Sent} (h : readsRow X D = true)
    (rad : OracleShape → Nat) :
    ∀ i ∈ attLinks X, ∃ x tl, lookAt X i false = some x ∧ tlAt X i = some tl ∧
      First.Look.readsB x tl D.up rad = true := by
  intro i hi
  have h0 := List.all_eq_true.1 h i hi
  cases e : lookAt X i false with
  | none =>
    rw [e] at h0
    exact absurd h0 (by simp)
  | some x =>
    rw [e] at h0
    have h1 : ((tlAt X i).any fun tl => readsB x tl D) = true := h0
    cases e' : tlAt X i with
    | none =>
      rw [e'] at h1
      exact absurd h1 (by simp)
    | some tl =>
      rw [e'] at h1
      exact ⟨x, tl, rfl, rfl, readsB_up h1 rad⟩

/-- **So AttReadsOK there, under its fourth field.** -/
theorem asks_attReads {X : Verify.Public} {D : Sent} (h : readsRow X D = true)
    (rad : OracleShape → Nat) {i : ℕ} (hi : i ∈ attLinks X) :
    ∃ x tl, lookAt X i false = some x ∧ tlAt X i = some tl ∧
      ∀ S : Attention.Shape,
        (∀ r : Inst.Model.AttSeg.Raw, r.Valid (Road.L5.dimOf S) →
          (First.Look.cellJ (First.Look.szOf tl) (Road.L5.addrA S r).1 (Road.L5.addrA S r).2.1
            (Road.L5.addrA S r).2.2).isSome = true) → First.Look.AttReadsOK x S tl D.up rad := by
  obtain ⟨x, tl, e1, e2, e3⟩ := asks_reads h rad i hi
  exact ⟨x, tl, e1, e2, fun S hc => First.Look.attReadsOK_of e3 hc⟩

end VerifiableInference.Desc.K3Asks

#print axioms VerifiableInference.Desc.K3Asks.shape_up
#print axioms VerifiableInference.Desc.K3Asks.digB_up
#print axioms VerifiableInference.Desc.K3Asks.asks_dig
#print axioms VerifiableInference.Desc.K3Asks.readsB_up
#print axioms VerifiableInference.Desc.K3Asks.asks_reads
#print axioms VerifiableInference.Desc.K3Asks.asks_attReads
