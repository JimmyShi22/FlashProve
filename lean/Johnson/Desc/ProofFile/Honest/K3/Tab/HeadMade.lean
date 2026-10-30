-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/HeadMade.lean: what follows for the places of the output head's
lookup where the verifier's own makers return: the head's layout, and a request's covered
positions. Conditional. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the maker of the layout is `Head.layout`, the maker of
the covered positions `Head.coveredOf` (OnBytes/Model/HeadLayout.lean), of the checked tokens
`Head.winOf` (OnBytes/Model/HeadHeard.lean); the letter `so` is of the library's structure
`Head.StOwn` (OnBytes/Model/HeadLayout.lean): what the verifier keeps of the caller's request and
reply; a place is a number below a call's 2 ^ n;
`H.colH` (OnBytes/Tie/Pv/Lookup/Ends/H.lean) says which entry of which segment stands in a column;
`padH` (Johnson/HonestTrace/CountsHeadPub.lean) says whether a place is a padding place.

Why. Whoever holds a program's keys against the library's `H.kvH` needs, at a place: that the
column's segment is one of the nine, that the entry lies in it, that the position lies below T; and
of the request: which positions are covered, which token is checked there, and that it is an entry
of the vocabulary. Each follows from a step or a test of a maker, and the library's lemmas on the
makers give these steps and tests. Here they stand in the form in which a place needs them.

What is shown.
  `madeH_of_public`: what `Verify.publicOf` returns has a head's layout that the maker returns.
  `padH_false`: what "no padding place" says. No hypothesis.
  Under hy : Head.layout h tau = .ok L:
  `nH_made`: a call's n is lJ + lt.
  `posSize_made`: a segment lists one column for each entry. Its proof repeats, step for step, that
    of the library's `sizes_of_layout` (Johnson/Road/Ends/HeadInSeam.lean), which is stated of the
    layout of a `Head.Run` (OnBytes/Model/HeadTables.lean); here the layout stands by itself. Five
    steps in its middle are, to the sign, those of the library's `member_of_layout`
    (Johnson/Road/HeadFound.lean). The library's `sizes_of_layout` holds at every q; this one is
    stated at the q of `hq`, below the number of the layout's calls.
  `colH_made`: what `H.colH` finds has the name of one of the nine segments of `Head.segments h L`,
    and the entry lies below that segment's length.
  `placeH_lt`: at a place below 2 ^ n the column lies below 2 ^ lJ and the position below T.
  Under hc : Head.coveredOf so T V = .ok cov, at t < T, r and e being the two words behind the
  tokens:
  `hOn_made`, `hOnC_made`: covered: r ≤ t < e; with a cost: besides t + 1 < T.
  `win_made`: the checked token at a covered position: the next word; at the last position the
    reply.
  `win_lt`: at a covered position the checked token is below V.

Hypotheses that remain.
  `h`, in `madeH_of_public`: `Verify.publicOf` returns X.
  `hy`: `Head.layout h tau` returns L. `madeH_of_public` shows it at what `Verify.publicOf` returns.
  `hq`: the call is below NC; in `posSize_made`: below the number of the layout's calls.
  `hg`, in `posSize_made`: g is a segment of the call.
  `hc`: in `colH_made`: `H.colH` names the segment sn and the entry x; in the last four theorems:
    `Head.coveredOf so T V` returns cov.
  `hY`, in `placeH_lt`: the place is below the call's 2 ^ n.
  `ht`, in the last four theorems: the position is below T.
  `hon`, in `win_made` and `win_lt`: the position is covered.
  `padH_false` has none.

Imported. Johnson/Road/Ends/HeadInSeam.lean; Johnson/Road/Ends/HeadForIn.lean;
Johnson/Road/Ends/HeadBack.lean; Johnson/Road/HeadReply.lean;
Johnson/HonestTrace/CountsHeadPub.lean. As in the first four of these, the instance
`Inst.Model.Scl.ref` (Inst/Model/Scl.lean: the reference scales) is taken out for this file.

Kin. The library's `reqFits_of_covered` (Johnson/Road/HeadLaid.lean) shows the facts of `hOn_made`,
`hOnC_made` and `win_made` in the form of its structure `ReqFits`, at a `Head.Run` and at whichever
token is named. A step inside the proof of its `forInH_iff_inTables`
(Johnson/Road/Ends/HeadForIn.lean) is `nH_made` at a `Head.Run`. Its `win_lt`
(Johnson/Desc/Kinds/Law/Ints.lean, another namespace) has the short name and the sentence of this
file's, of another model's `win`.


Limits. Nothing on what a cell holds. The third argument of `Head.winOf` is, in the library's words,
the token that the prover has named; `win_made` and `win_lt` speak of it at the reply so.y. That the
named token is the reply is not said here. No request at which `Head.coveredOf` returns is exhibited
in this file, and no public file at which `Verify.publicOf` returns.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Road.Ends.HeadInSeam
import Johnson.Road.Ends.HeadForIn
import Johnson.Road.Ends.HeadBack
import Johnson.Road.HeadReply
import Johnson.HonestTrace.CountsHeadPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.AtInt

open OnBytes OnBytes.Model OnBytes.Ends
open OnBytes.HonestTrace (padH)

/-- What `Verify.publicOf` returns has a head's layout that the maker returns at its own shape. -/
theorem madeH_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL lay = .ok X) : ∃ tau, Head.layout X.hS tau = .ok X.HLy := by
  obtain ⟨_, y, -, -, e⟩ := OnBytes.Road.Hd.layout_of_public h
  exact ⟨y.tauFC, e⟩

/-- What "no padding place" says. -/
theorem padH_false (h : Head.Shape) (L : Head.HL) (q i : ℕ) :
    padH h L q i = false ↔ ∃ (sn : String) (x : ℕ), H.colH L q (i / h.T) = some (sn, x) ∧
      (Head.perEntry sn && decide (h.V ≤ Head.firstEntry L sn + x)) = false := by
  unfold padH
  cases hc : H.colH L q (i / h.T) with
  | none => simp
  | some a =>
    obtain ⟨sn, x⟩ := a
    constructor
    · intro e
      exact ⟨sn, x, rfl, e⟩
    · rintro ⟨sn', x', e1, e2⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e1)
      exact e2

section Layout

variable {h : Head.Shape} {tau : Array F} {L : Head.HL}

/-- A call's n is lJ + lt. -/
theorem nH_made (hy : Head.layout h tau = .ok L) {q : ℕ} (hq : q < L.fs.NC) :
    (L.fs.calls.getD q {}).n = (L.calls.getD q default).lJ + h.lt := by
  have hq' : q < L.calls.size := by rw [← OnBytes.Road.Hd.fsNC_of_layout hy]; exact hq
  obtain ⟨e1, e2⟩ := OnBytes.Road.Hd.clN_of_layout hy
  have hq2 : q < L.cl.size := by rw [e1]; exact hq'
  have e3 := e2 q hq'
  rw [OnBytes.Road.Hd.fsCalls_of_layout hy, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hq2]
  rw [Array.getElem?_eq_getElem hq2] at e3
  exact e3

/-- Every segment of every call lists one column for each entry. (The library's `sizes_of_layout`,
Johnson/Road/Ends/HeadInSeam.lean, says it of the layout of a `Head.Run`, at every q; here of the
layout itself; the proof repeats that lemma's, step for step.) -/
theorem posSize_made (hy : Head.layout h tau = .ok L) {q : ℕ} (hq : q < L.calls.size) {g : Seg}
    (hg : g ∈ (L.calls.getD q default).segs) : g.pos.size = g.n := by
  have A := OnBytes.Road.Hd.admittedH_of_layout hy
  obtain ⟨cs, hc, -, hL⟩ := A.calls
  obtain ⟨c1, -⟩ := OnBytes.Road.Hd.callsOf_spec hc
  rw [hL] at hq hg
  have hq' : q < cs.length := by simpa using hq
  have e : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
  rw [e] at hg
  obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cs[q] (List.getElem_mem hq')
  rw [e1, OnBytes.Road.Hd.place_segs_eq] at hg
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
  exact (OnBytes.Road.Hd.segAt_rising asks (fun a ha => by
    obtain ⟨x, f1, f2⟩ := e2 a ha
    rw [f2]
    exact OnBytes.Road.Hd.segments_lt A x (List.mem_of_find?_eq_some f1)) z hz).1

/-- **What `H.colH` finds is an entry of one of the nine segments.** -/
theorem colH_made (hy : Head.layout h tau = .ok L) {q j x : ℕ} {sn : String} (hq : q < L.fs.NC)
    (hc : H.colH L q j = some (sn, x)) : ∃ m ∈ Head.segments h L, sn = m.1 ∧ x < m.2.2 := by
  have hq' : q < L.calls.size := by rw [← OnBytes.Road.Hd.fsNC_of_layout hy]; exact hq
  obtain ⟨g, hg, e1, e2⟩ := OnBytes.Road.Hd.colH_some hc
  obtain ⟨m, hm, f1, f2⟩ := OnBytes.Road.Hd.member_of_layout hy hq' hg
  have hs := posSize_made hy hq' hg
  exact ⟨m, hm, e1.symm.trans f1, by rw [← f2, ← hs]; exact e2⟩

/-- **The column and the position of a place below the call's 2 ^ n.** -/
theorem placeH_lt (hy : Head.layout h tau = .ok L) {q Y : ℕ} (hq : q < L.fs.NC)
    (hY : Y < 2 ^ (L.fs.calls.getD q {}).n) :
    Y / h.T < 2 ^ (L.calls.getD q default).lJ ∧ Y % h.T < h.T := by
  have hT : h.T = 2 ^ h.lt := rfl
  rw [nH_made hy hq, Nat.pow_add] at hY
  refine ⟨?_, Nat.mod_lt _ (by rw [hT]; exact Nat.pow_pos (by decide))⟩
  rw [hT]
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hY)

end Layout

section Request

variable {so : Head.StOwn} {T V : ℕ} {cov : Head.Covered}

/-- Covered: r ≤ t < e. -/
theorem hOn_made (hc : Head.coveredOf so T V = .ok cov) {t : ℕ} (ht : t < T) :
    cov.hOn.getD t false =
      (decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) := by
  obtain ⟨-, -, -, -, e, -, -⟩ := OnBytes.Road.Hd.coveredOf_ok hc
  rw [e, OnBytes.Road.Hd.getD_rangeMap _ _ _ ht]

/-- With a cost: covered, and t + 1 < T. -/
theorem hOnC_made (hc : Head.coveredOf so T V = .ok cov) {t : ℕ} (ht : t < T) :
    cov.hOnC.getD t false =
      ((decide ((so.req.getD T 0).toNat ≤ t) && decide (t < (so.req.getD (T + 1) 0).toNat)) &&
        decide (t + 1 < T)) := by
  obtain ⟨-, -, -, -, -, -, e⟩ := OnBytes.Road.Hd.coveredOf_ok hc
  rw [e, OnBytes.Road.Hd.getD_rangeMap _ _ _ ht]

/-- **The checked token at a covered position**: the next word; at the last position the reply. -/
theorem win_made (hc : Head.coveredOf so T V = .ok cov) {t : ℕ} (ht : t < T)
    (hon : cov.hOn.getD t false = true) :
    (Head.winOf cov T so.y).getD t 0 =
      if t + 1 < T then (so.req.getD (t + 1) 0).toNat else so.y := by
  obtain ⟨hs, -, -, -, -, e, -⟩ := OnBytes.Road.Hd.coveredOf_ok hc
  have hon' := hon
  rw [hOn_made hc ht] at hon'
  have hw : cov.hWin.getD t 0 =
      if t + 1 < T then (so.req.getD (t + 1) 0).toNat else so.y := by
    rw [e, OnBytes.Road.Hd.getD_rangeMap _ _ _ ht, if_pos hon']
    by_cases h1 : t + 1 < T
    · rw [if_pos h1, if_pos h1]
      have h2 : t + 1 < so.req.size := by omega
      simp [Array.getD, h1, h2]
    · rw [if_neg h1, if_neg h1]
  unfold Head.winOf
  split
  · by_cases h1 : t = T - 1
    · have hsz : T - 1 < cov.hWin.size := by
        rw [e]
        simp
        omega
      have h2 : ¬ t + 1 < T := by omega
      rw [if_neg h2, h1]
      simp [Array.getD, hsz]
    · have h3 : T - 1 ≠ t := fun e' => h1 e'.symm
      rw [← hw, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, if_neg h3]
  · exact hw

/-- **At a covered position the checked token is an entry of the vocabulary.** -/
theorem win_lt (hc : Head.coveredOf so T V = .ok cov) {t : ℕ} (ht : t < T)
    (hon : cov.hOn.getD t false = true) : (Head.winOf cov T so.y).getD t 0 < V := by
  rw [win_made hc ht hon]
  obtain ⟨hs, ha, -, -, -, -, -⟩ := OnBytes.Road.Hd.coveredOf_ok hc
  by_cases h1 : t + 1 < T
  · rw [if_pos h1]
    have h2 : t + 1 < so.req.size := by omega
    rw [Array.all_eq_true] at ha
    have h3 : t + 1 < ((so.req.extract 0 T).map (·.toNat)).size := by
      simp
      omega
    have h4 := ha (t + 1) h3
    simp at h4
    simpa [Array.getD, h2] using h4
  · rw [if_neg h1]
    exact OnBytes.Road.Hd.coveredOf_y hc

end Request

end ProofFile.Honest.K3.AtInt

#print axioms ProofFile.Honest.K3.AtInt.madeH_of_public
#print axioms ProofFile.Honest.K3.AtInt.padH_false
#print axioms ProofFile.Honest.K3.AtInt.nH_made
#print axioms ProofFile.Honest.K3.AtInt.posSize_made
#print axioms ProofFile.Honest.K3.AtInt.colH_made
#print axioms ProofFile.Honest.K3.AtInt.placeH_lt
#print axioms ProofFile.Honest.K3.AtInt.hOn_made
#print axioms ProofFile.Honest.K3.AtInt.hOnC_made
#print axioms ProofFile.Honest.K3.AtInt.win_made
#print axioms ProofFile.Honest.K3.AtInt.win_lt
