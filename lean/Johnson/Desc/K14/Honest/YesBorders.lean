--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesBorders.lean: the facts that the places of the linear claim's shared
rounds ask of the state in front of them, carried from place to place.

Each place's function, where it returns, leaves a state that the library describes field by field
(Johnson/Desc/Key/Laid/: PointLaid, SendLaid, RecLaid, LocLaid, Joined; these are general in the
parameters and in the state). This file takes from these the facts that the next place asks.

Main names:
  Carried p codes k d mU mO   the state's codes are the plan's; statement and book are in step; the
                      key is k; the shared point is noted; the two groups are there, apart, with the
                      members mU and mO
  HasU p d            o_u is noted with its layout and stands as its sending left it
  HasO p d            o_omega and o_sp are noted and stand as their sending left them, apart from
                      each other and from o_u; o_sp's ledger (the statement's field of that name,
                      which counts a message's free mask entries) is fresh; o_omega has a tree to
                      itself
  GroupIs.same, GroupIs.rows, GroupIs.enter, GroupIs.perm, MsgIs.same, MsgIs.marked, MsgIs.lt   how
                      the two small facts are carried
  behindSend          the state behind a sending and the kind's note
  carried_point, carried_send, msg_older, carried_rec, hasU_rec, carried_loc, hasU_loc,
  carried_joined, hasU_joined, hasO_joined   from place to place. (HasU and HasO behind the
                      sending that brings them: sendU_returns, sendO_returns in
                      Johnson/Desc/K14/Honest/YesChain.lean)
  frontU_of, front6_of, front8_of   the facts as the places ask them

What is not claimed. That a place's function returns: the files beside this one. Shapes with one
code are not served. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesSend
import Johnson.Desc.K14.Honest.YesJoins
import Johnson.Desc.K14.Honest.YesSplit
import Johnson.Desc.Key.Laid.Draws
import Johnson.Desc.Key.Laid.Rec
import Johnson.Desc.Key.Laid.Joined

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Own (linFits aloneIn)
open VerifiableInference.Desc.Key (PointLaid RecLaid LocLaid Joined entered noted)
open VerifiableInference.Desc.Key.LaidW (SendLaid inFrontOf)

/-! ## How the two small facts are carried -/

/-- The fact on a group is carried where the group is as it was. -/
theorem GroupIs.same {T T' : Statement} {g c m : Nat} {ms : List Nat} (h : GroupIs T g c m ms)
    (e : T'.groups[g]? = T.groups[g]?) : GroupIs T' g c m ms := by
  obtain ⟨G, hG, r⟩ := h
  exact ⟨G, e.trans hG, r⟩

/-- It is carried where the group's rows alone have turned. -/
theorem GroupIs.rows {T T' : Statement} {g c m : Nat} {ms : List Nat} (h : GroupIs T g c m ms)
    (e : ∀ G, T.groups[g]? = some G → ∃ rows, T'.groups[g]? = some { G with rows := rows }) :
    GroupIs T' g c m ms := by
  obtain ⟨G, hG, a1, a2, a3, a4⟩ := h
  obtain ⟨rows, e'⟩ := e G hG
  exact ⟨_, e', a1, a2, a3, a4⟩

/-- Where the message o has joined the group, not as a kept member: one member more. -/
theorem GroupIs.enter {T T' : Statement} {g c m : Nat} {ms : List Nat} (h : GroupIs T g c m ms)
    (o : Nat) (e : ∀ G, T.groups[g]? = some G →
      ∃ rows, T'.groups[g]? = some { entered G o false with rows := rows }) :
    GroupIs T' g c m (o :: ms) := by
  obtain ⟨G, hG, a1, a2, a3, a4⟩ := h
  obtain ⟨rows, e'⟩ := e G hG
  refine ⟨_, e', a1, a2, a3, fun a => ?_⟩
  show a ∈ (entered G o false).members ↔ _
  rw [mem_entered, List.mem_cons, a4]

/-- The list of members may be written in another order. -/
theorem GroupIs.perm {T : Statement} {g c m : Nat} {ms ms' : List Nat} (h : GroupIs T g c m ms)
    (e : ∀ a, a ∈ ms ↔ a ∈ ms') : GroupIs T g c m ms' := by
  obtain ⟨G, hG, a1, a2, a3, a4⟩ := h
  exact ⟨G, hG, a1, a2, a3, fun a => (a4 a).trans (e a)⟩

/-- The fact on a message is carried where the message and the codes are as they were. -/
theorem MsgIs.same {T T' : Statement} {o : Nat} {s : OracleShape} (h : MsgIs T o s)
    (e : T'.oracles[o]? = T.oracles[o]?) (hc : T'.codes = T.codes) : MsgIs T' o s := by
  obtain ⟨x, hx, a1, a2, a3⟩ := h
  exact ⟨x, e.trans hx, a1, a2, by rw [hc]; exact a3⟩

/-- It is carried where the message has noted groups more. -/
theorem MsgIs.marked {T T' : Statement} {o : Nat} {s : OracleShape} (h : MsgIs T o s)
    (gs : List Nat) (e : ∀ x, T.oracles[o]? = some x → T'.oracles[o]? = some (noted x gs))
    (hc : T'.codes = T.codes) : MsgIs T' o s := by
  obtain ⟨x, hx, a1, a2, a3⟩ := h
  exact ⟨noted x gs, e x hx, a1, a2, by rw [hc]; exact a3⟩

/-- A message that is there has a number below the number of messages. -/
theorem MsgIs.lt {T : Statement} {o : Nat} {s : OracleShape} (h : MsgIs T o s) :
    o < T.oracles.size := by
  obtain ⟨x, hx, _⟩ := h
  exact (Array.getElem?_eq_some_iff.1 hx).1

/-! ## The facts between two places -/

/-- What every place behind "LIN point" finds. mU, mO: the two groups' members. -/
structure Carried (p : Par) (codes : Codes) (k : TableKey) (d : St) (mU mO : List Nat) : Prop where
  codes : d.st.codes = codes
  step : d.st.oracles.size = d.book.place.size
  key : d.loc.key = k
  psi : d.loc.psiSh.length = p.S.kCol
  two : d.loc.gU ≠ d.loc.gOmega
  gU : GroupIs d.st d.loc.gU p.S.fold.u.code p.S.sharedMaskCode mU
  gO : GroupIs d.st d.loc.gOmega p.S.omega.code p.S.sharedMaskCode mO

/-- What every place behind o_u's sending finds. -/
structure HasU (p : Par) (d : St) : Prop where
  lay : d.loc.oU.lay = vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh
  u : MsgIs d.st d.loc.oU.oracle p.S.fold.u

/-- What every place behind o_omega's sending finds. -/
structure HasO (p : Par) (d : St) : Prop where
  omega : MsgIs d.st d.loc.oOmega p.S.omega
  sp : MsgIs d.st d.loc.oSp p.S.sharedSplit
  ledger : ∀ x, d.st.oracles[d.loc.oSp]? = some x →
    x.ledger = Slice.freshLedger d.st.codes p.S.sharedSplit
  apart : d.loc.oOmega ≠ d.loc.oSp
  apartU : d.loc.oSp ≠ d.loc.oU.oracle
  apartOU : d.loc.oOmega ≠ d.loc.oU.oracle
  alone : aloneIn d.book d.loc.oOmega = true

/-! ## Behind "LIN point" -/

/-- Behind "LIN point": the two groups are there, apart, without a member. -/
theorem carried_point (p : Par) (codes : Codes) (k : TableKey) (d d' : St) (r : Fmt.RoundView)
    (hc : d.st.codes = codes) (hstep : d.st.oracles.size = d.book.place.size)
    (hk : d.loc.key = k) (hr : (drawn r).length = p.S.kCol) (h : PointLaid p d d' r) :
    Carried p codes k d' [] [] := by
  have hl := h.loc
  have hg := h.groups
  refine ⟨h.codes.trans hc, by rw [h.oracles, h.book]; exact hstep, by rw [hl]; exact hk,
    by rw [hl]; exact hr, ?_, ?_, ?_⟩
  · rw [hl]
    show d.st.groups.size ≠ d.st.groups.size + 1
    omega
  · rw [hl]
    refine ⟨{ code := p.S.fold.u.code, maskCode := p.S.sharedMaskCode }, ?_, rfl, rfl, rfl,
      fun o => by simp⟩
    show d'.st.groups[d.st.groups.size]? = _
    have hlt : d.st.groups.size <
        (d.st.groups.push { code := p.S.fold.u.code, maskCode := p.S.sharedMaskCode }).size := by
      rw [Array.size_push]
      omega
    rw [hg, Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt, Array.getElem?_push_size]
  · rw [hl]
    refine ⟨{ code := p.S.omega.code, maskCode := p.S.sharedMaskCode }, ?_, rfl, rfl, rfl,
      fun o => by simp⟩
    show d'.st.groups[d.st.groups.size + 1]? = _
    have e : d.st.groups.size + 1 =
        (d.st.groups.push { code := p.S.fold.u.code, maskCode := p.S.sharedMaskCode }).size := by
      rw [Array.size_push]
    rw [hg, e, Array.getElem?_push_size]

/-! ## Behind a sending -/

/-- The state behind a sending and the kind's note. l': what the kind notes. -/
abbrev behindSend (x : DState (Array Nat)) (l' : Lin) : St :=
  { st := x.st, book := x.book, roots := x.roots, opened := x.opened, loc := l' }

/-- A sending and the kind's note behind it leave Carried, where the note leaves the point, the
groups' numbers and the key. -/
theorem carried_send (p : Par) (codes : Codes) (k : TableKey) (Q : VerifiableInference.Desc.K1.Par)
    (d : St) (x : DState (Array Nat)) (ids : Array Nat) (mU mO : List Nat) (l' : Lin)
    (hB : Carried p codes k d mU mO) (S : SendLaid Q (inFrontOf d) x ids)
    (e1 : l'.psiSh = d.loc.psiSh) (e2 : l'.gU = d.loc.gU) (e3 : l'.gOmega = d.loc.gOmega)
    (e4 : l'.key = d.loc.key) : Carried p codes k (behindSend x l') mU mO := by
  obtain ⟨lay, _, hbook⟩ := S.book
  have hg : x.st.groups = d.st.groups := S.groups
  refine ⟨S.codes.trans hB.codes, ?_, e4.trans hB.key,
    by show l'.psiSh.length = _; rw [e1]; exact hB.psi,
    by show l'.gU ≠ l'.gOmega; rw [e2, e3]; exact hB.two, ?_, ?_⟩
  · show x.st.oracles.size = x.book.place.size
    have h1 : x.st.oracles.size = d.st.oracles.size + Q.sent.size := S.size
    have h2 : x.book.place.size = d.book.place.size + Q.sent.size := hbook.count
    rw [h1, h2, hB.step]
  · show GroupIs x.st l'.gU _ _ _
    rw [e2]
    exact hB.gU.same (by rw [hg])
  · show GroupIs x.st l'.gOmega _ _ _
    rw [e3]
    exact hB.gO.same (by rw [hg])

/-- A message that stood in front of a sending stands behind it. -/
theorem msg_older {Q : VerifiableInference.Desc.K1.Par} {d : St} {x : DState (Array Nat)}
    {ids : Array Nat} (S : SendLaid Q (inFrontOf d) x ids) {o : Nat} {s : OracleShape}
    (h : MsgIs d.st o s) : MsgIs x.st o s :=
  h.same (S.older o h.lt) S.codes

/-! ## Behind "(rec_gamma)" and "LOC" -/

/-- Behind "(rec_gamma)": o_u is the one member of its group. -/
theorem carried_rec (p : Par) (codes : Codes) (k : TableKey) (d d' : St) (GU : Group)
    (rows : List Row) (mO : List Nat) (hB : Carried p codes k d [] mO)
    (h : RecLaid p d d' GU rows) : Carried p codes k d' [d.loc.oU.oracle] mO := by
  refine ⟨h.codes.trans hB.codes, by rw [h.size, h.book]; exact hB.step,
    by rw [h.loc]; exact hB.key, by rw [h.loc]; exact hB.psi, by rw [h.loc]; exact hB.two, ?_, ?_⟩
  · rw [h.loc]
    refine hB.gU.enter _ fun G hG => ⟨G.rows ++ rows.toArray, ?_⟩
    obtain rfl : GU = G := Option.some.inj (h.gU.symm.trans hG)
    exact h.gU'
  · rw [h.loc]
    exact hB.gO.same (h.other _ (Ne.symm hB.two))

/-- "(rec_gamma)" leaves HasU. -/
theorem hasU_rec (p : Par) (d d' : St) (GU : Group) (rows : List Row) (hU : HasU p d)
    (h : RecLaid p d d' GU rows) : HasU p d' := by
  refine ⟨by rw [h.loc, h.codes]; exact hU.lay, ?_⟩
  rw [h.loc]
  exact hU.u.marked _ h.u h.codes

/-- "LOC" leaves Carried. -/
theorem carried_loc (p : Par) (codes : Codes) (k : TableKey) (d d' : St) (r : Fmt.RoundView) (GU : Group)
    (rows : List Row) (mU mO : List Nat) (hB : Carried p codes k d mU mO)
    (h : LocLaid p d d' r GU rows) : Carried p codes k d' mU mO := by
  refine ⟨h.codes.trans hB.codes, by rw [h.oracles, h.book]; exact hB.step,
    by rw [h.loc]; exact hB.key, by rw [h.loc]; exact hB.psi, by rw [h.loc]; exact hB.two, ?_, ?_⟩
  · rw [h.loc]
    refine hB.gU.rows fun G hG => ⟨G.rows ++ rows.toArray, ?_⟩
    obtain rfl : GU = G := Option.some.inj (h.gU.symm.trans hG)
    exact h.gU'
  · rw [h.loc]
    exact hB.gO.same (h.other _ (Ne.symm hB.two))

/-- "LOC" leaves HasU. -/
theorem hasU_loc (p : Par) (d d' : St) (r : Fmt.RoundView) (GU : Group) (rows : List Row)
    (hU : HasU p d) (h : LocLaid p d d' r GU rows) : HasU p d' := by
  refine ⟨by rw [h.loc, h.codes]; exact hU.lay, ?_⟩
  rw [h.loc]
  exact hU.u.same (by rw [h.oracles]) h.codes

/-! ## Behind the joinings -/

/-- Behind the joinings: o_u and o_sp are the members of the one group, o_omega and o_sp of the
other. -/
theorem carried_joined (p : Par) (codes : Codes) (k : TableKey) (d d' : St) (GU GO : Group)
    (hB : Carried p codes k d [d.loc.oU.oracle] []) (h : Joined d d' GU GO) :
    Carried p codes k d' [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp] := by
  refine ⟨h.codes.trans hB.codes, by rw [h.size, h.book]; exact hB.step,
    by rw [h.loc]; exact hB.key, by rw [h.loc]; exact hB.psi, by rw [h.loc]; exact hB.two, ?_, ?_⟩
  · rw [h.loc]
    refine (hB.gU.enter d.loc.oSp fun G hG => ⟨G.rows, ?_⟩).perm fun a => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.comm
    obtain rfl : GU = G := Option.some.inj (h.gU.symm.trans hG)
    exact h.gU'
  · rw [h.loc]
    obtain ⟨G, hG, a1, a2, a3, a4⟩ := hB.gO
    obtain rfl : GO = G := Option.some.inj (h.gO.symm.trans hG)
    refine ⟨_, h.gO', a1, a2, a3, fun a => ?_⟩
    rw [mem_entered, mem_entered, a4]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact Or.comm

/-- The joinings leave HasU. -/
theorem hasU_joined (p : Par) (d d' : St) (GU GO : Group) (hU : HasU p d) (hO : HasO p d)
    (h : Joined d d' GU GO) : HasU p d' := by
  refine ⟨by rw [h.loc, h.codes]; exact hU.lay, ?_⟩
  rw [h.loc]
  exact hU.u.same (h.rest _ (Ne.symm hO.apartOU) (Ne.symm hO.apartU)) h.codes

/-- The joinings leave HasO. -/
theorem hasO_joined (p : Par) (d d' : St) (GU GO : Group) (hO : HasO p d)
    (h : Joined d d' GU GO) : HasO p d' := by
  refine ⟨by rw [h.loc]; exact hO.omega.marked _ h.omega h.codes,
    by rw [h.loc]; exact hO.sp.marked _ h.sp h.codes, ?_, by rw [h.loc]; exact hO.apart,
    by rw [h.loc]; exact hO.apartU, by rw [h.loc]; exact hO.apartOU,
    by rw [h.loc, h.book]; exact hO.alone⟩
  rw [h.loc, h.codes]
  intro x hx
  obtain ⟨y, hy, _⟩ := hO.sp
  obtain rfl : noted y [d.loc.gOmega, d.loc.gU] = x := Option.some.inj ((h.sp y hy).symm.trans hx)
  exact hO.ledger y hy

/-! ## The facts as the places ask them -/

/-- The facts in front of "(rec_gamma)" and of "LOC". -/
theorem frontU_of {p : Par} {codes : Codes} {k : TableKey} {d : St} {mU mO : List Nat}
    (hlin : linFits codes p.S = true) (hB : Carried p codes k d mU mO) (hU : HasU p d) :
    FrontU p d mU :=
  ⟨by rw [hB.codes]; exact hlin, hB.psi, hU.lay, hB.gU, hU.u⟩

/-- The facts in front of the joinings. -/
theorem front6_of {p : Par} {codes : Codes} {k : TableKey} {d : St}
    (hlin : linFits codes p.S = true) (hB : Carried p codes k d [d.loc.oU.oracle] [])
    (hO : HasO p d) : Front6 p d :=
  ⟨by rw [hB.codes]; exact hlin, hB.two, hB.gU, hB.gO, hO.omega, hO.sp, hO.apart, hO.apartU,
    hO.alone⟩

/-- The facts in front of "SPLIT". -/
theorem front8_of {p : Par} {codes : Codes} {k : TableKey} {d : St}
    (hlin : linFits codes p.S = true)
    (hB : Carried p codes k d [d.loc.oU.oracle, d.loc.oSp] [d.loc.oOmega, d.loc.oSp])
    (hU : HasU p d) (hO : HasO p d) (hz : d.loc.zFd.length = p.S.kRow)
    (hfree : 0 < Send.freeMaskEntries p.S.sharedSplit.maskRows
      (codes.mask.getD p.S.sharedSplit.maskCode default).ell p.S.sharedSplit.answers) :
    Front8 p d :=
  ⟨by rw [hB.codes]; exact hlin, hB.psi, hz, hU.lay, hB.two, hB.gU, hB.gO, hU.u, hO.omega, hO.sp,
    hO.ledger, hO.apart, hO.apartU, hO.apartOU, by rw [hB.codes]; exact hfree⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.GroupIs.same
#print axioms Desc.K14.Honest.GroupIs.rows
#print axioms Desc.K14.Honest.GroupIs.enter
#print axioms Desc.K14.Honest.GroupIs.perm
#print axioms Desc.K14.Honest.MsgIs.same
#print axioms Desc.K14.Honest.MsgIs.marked
#print axioms Desc.K14.Honest.MsgIs.lt
#print axioms Desc.K14.Honest.carried_point
#print axioms Desc.K14.Honest.carried_send
#print axioms Desc.K14.Honest.msg_older
#print axioms Desc.K14.Honest.carried_rec
#print axioms Desc.K14.Honest.hasU_rec
#print axioms Desc.K14.Honest.carried_loc
#print axioms Desc.K14.Honest.hasU_loc
#print axioms Desc.K14.Honest.carried_joined
#print axioms Desc.K14.Honest.hasU_joined
#print axioms Desc.K14.Honest.hasO_joined
#print axioms Desc.K14.Honest.frontU_of
#print axioms Desc.K14.Honest.front6_of
#print axioms Desc.K14.Honest.front8_of
