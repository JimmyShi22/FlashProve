-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/ShapesSend.lean: THE BOOK-KEEPING ON THE SHARED CHAIN's OWN RECORD IS EARNED AT
THE TWO SENDINGS. The third part of Johnson/Desc/K14/Law/Shapes.lean and ShapesOmega.lean.

  decideSend_kept, sendAt_groups, rows_of_groups   a yes of a sending leaves the statement's groups:
                  so every group's list of rows.
  sendAt_size     it brings just the place's messages.
  midB nO s       what rides from "LIN point" to o_omega's sending, as a test: the statement has nO
                  messages; G_omega has no open row; the two groups are two.
  midB_step       a step onward that leaves the small record, brings no message and lays rows on G_u
                  alone keeps it; so "(rec_gamma)" and "LOC" (midB_rec, midB_loc).
  shapeM          the test between the two sendings: shapeU and midB; earned at "(rec_gamma)" and at
                  "LOC" (shapeM_rec, shapeM_loc).
  shapeK          **the filling of "shape k"**, k = 2, …, 9, in one term.
  shapeP p nU s   the test in front of o_u's sending: shape2; the shape's conditions hold at the
                  record's codes; G_u has no open row; midB at nU.
  seatedUB_grows  o_u stays seated where the statement grows and what is noted of o_u stays.
  shapeU_sendU    **at a yes of "send o_u"**: shapeP at nU gives shapeU at nU and 0 rows, and midB
                  at nU + the number of messages sent.
  shapeO_sendO    **at a yes of "send o_omega"**: shapeU at nU, c and midB at nO give shapeO at nU,
                  nO, c, 0; two codes and nO ≠ nU are asked.
  shapes_at_b2, shapes_at_b5   the same at the second and the fifth of the kind's eight blocks.
  newGroupP_rows, point_extras   **at a yes of "LIN point"**, two codes: the shape's conditions hold
                  at the record's codes; the two groups are new, two, and have no open row; no
                  message comes: all of shapeP but shape2, which the piece's written round gives
                  (shape_hands, Johnson/Desc/K14/Law/PointCounts.lean).

What is not claimed. That any record passes a test. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.ShapesOmega
import Johnson.Desc.K1.Law.GoodSend5
import Johnson.Desc.Sound.FenceK14Sends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (Kept kept_behind decideSend decideSend_iff sendOwn size_of_same)

/-- A yes of the sending's decision, on whatever rounds, keeps what stood in the statement. -/
theorem decideSend_kept {L : Type} (Q : VerifiableInference.Desc.K1.Par) (owed : Option Nat)
    (d d' : DState L) (rs : List Fmt.RoundView) (ids : Array Nat)
    (h : decideSend Q owed d rs = .ok (ids, d')) : Kept d d' := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨_, _, rfl⟩ := (decideSend_iff Q owed d d' r₁ r₂ ids).1 h
    exact kept_behind Q d _ _

/-- A yes of a sending at this chain's state leaves the statement's groups. -/
theorem sendAt_groups (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    d'.st.groups = d.st.groups := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  have k := decideSend_kept Q none _ x2 rs ids hx
  rw [hb _ _ _ (named_some h)]
  exact k.2.1

/-- A yes of a sending leaves every elder message as it was. -/
theorem sendAt_elder (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∀ j, j < d.st.oracles.size → d'.st.oracles[j]? = d.st.oracles[j]? := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  have k := decideSend_kept Q none _ x2 rs ids hx
  rw [hb _ _ _ (named_some h)]
  exact k.2.2

/-- The same at the second and the fifth of the kind's eight blocks. -/
theorem elder_at_sends (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ b, b = b2 ∨ b = b5 → ∀ d rs gs d', b.decide d rs gs = .ok d' →
      ∀ j, j < d.st.oracles.size → d'.st.oracles[j]? = d.st.oracles[j]? := by
  intro b hb d rs gs d' h
  obtain ⟨n, Q, inFront, groups, behind, rfl, _, hbk⟩ :=
    Fence.sends_are P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb
  exact sendAt_elder P n Q inFront groups behind (fun a ids e he => (hbk a ids e he).1) d d' rs gs h

/-- Where the groups stay, every group's list of rows stays. -/
theorem rows_of_groups (d d' : St) (h : d'.st.groups = d.st.groups) (g : Nat) :
    rowsOn d' g = rowsOn d g := by
  unfold rowsOn
  rw [h]

/-- A yes of a sending brings just the place's messages. -/
theorem sendAt_size (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (hb : ∀ a ids e, behind a ids = some e → e.st = a.st ∧ e.book = a.book ∧ e.roots = a.roots)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    d'.st.oracles.size = d.st.oracles.size + Q.sent.size := by
  obtain ⟨_, _, _, h3, _, _⟩ := Fence.sendAt_received P n Q inFront groups behind hb d d' rs gs h
  exact h3

/-- **What rides from "LIN point" to o_omega's sending**, as a test. -/
def midB (nO : Nat) (s : St) : Bool :=
  decide (s.st.oracles.size = nO) && decide ((rowsOn s s.loc.gOmega).length = 0) &&
    decide (s.loc.gOmega ≠ s.loc.gU)

theorem midB_iff (nO : Nat) (s : St) : midB nO s = true ↔
    s.st.oracles.size = nO ∧ (rowsOn s s.loc.gOmega).length = 0 ∧ s.loc.gOmega ≠ s.loc.gU := by
  unfold midB
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- A step that leaves the small record, brings no message and leaves the rows of every group but
G_u keeps it. -/
theorem midB_step (nO : Nat) (a b : St) (l : b.loc = a.loc)
    (hs : b.st.oracles.size = a.st.oracles.size)
    (hr : ∀ g, g ≠ a.loc.gU → rowsOn b g = rowsOn a g) (h : midB nO a = true) :
    midB nO b = true := by
  obtain ⟨h1, h2, h3⟩ := (midB_iff nO a).1 h
  refine (midB_iff nO b).2 ⟨hs.trans h1, ?_, ?_⟩
  · rw [l, hr _ h3]
    exact h2
  · rw [l]
    exact h3

/-- "(rec_gamma)" keeps it. -/
theorem midB_rec (p : Par) (nO : Nat) (a b : St) (rs : List Fmt.RoundView)
    (k : laysRec p a rs = some b) (h : midB nO a = true) : midB nO b = true := by
  obtain ⟨_, l, _, _, _, hr⟩ := laysRecW p a b rs k
  exact midB_step nO a b l (size_of_same (msgs_rec p a b rs k)) hr h

/-- "LOC" keeps it. -/
theorem midB_loc (p : Par) (nO : Nat) (a b : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (k : loc p a [r] [cols] = some b) (h : midB nO a = true) : midB nO b = true := by
  obtain ⟨l, _, _, _, _, hr⟩ := laysLocW p a b r cols k
  exact midB_step nO a b l (size_of_same (msgs_loc p a b r cols k)) hr h

/-- **The test between the two sendings**: shapeU and midB. -/
def shapeM (p : Par) (nU nO c : Nat) (s : St) : Bool := shapeU p nU c s && midB nO s

theorem shapeM_iff (p : Par) (nU nO c : Nat) (s : St) : shapeM p nU nO c s = true ↔
    shapeU p nU c s = true ∧ midB nO s = true := by
  unfold shapeM
  simp only [Bool.and_eq_true]

/-- **At a yes of "(rec_gamma)".** -/
theorem shapeM_rec (p : Par) (nU nO c : Nat) (a b : St) (rs : List Fmt.RoundView)
    (k : laysRec p a rs = some b) (h : shapeM p nU nO c a = true) :
    shapeM p nU nO (c + p.S.fold.index.answers) b = true :=
  (shapeM_iff p nU nO _ b).2 ⟨shapeU_rec p nU c a b rs k ((shapeM_iff p nU nO c a).1 h).1,
    midB_rec p nO a b rs k ((shapeM_iff p nU nO c a).1 h).2⟩

/-- **At a yes of "LOC".** -/
theorem shapeM_loc (p : Par) (nU nO c : Nat) (a b : St) (r : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (k : loc p a [r] [cols] = some b)
    (h : shapeM p nU nO c a = true) : shapeM p nU nO (c + r.drawn.poss.length) b = true :=
  (shapeM_iff p nU nO _ b).2 ⟨shapeU_loc p nU c a b r cols k ((shapeM_iff p nU nO c a).1 h).1,
    midB_loc p nO a b r cols k ((shapeM_iff p nU nO c a).1 h).2⟩

/-- **The test in front of o_u's sending.** -/
def shapeP (p : Par) (nU : Nat) (s : St) : Bool :=
  shape2 p s && linOk s.st.codes p.S && decide ((rowsOn s s.loc.gU).length = 0) && midB nU s

theorem shapeP_iff (p : Par) (nU : Nat) (s : St) : shapeP p nU s = true ↔
    shape2 p s = true ∧ linOk s.st.codes p.S = true ∧ (rowsOn s s.loc.gU).length = 0 ∧
      midB nU s = true := by
  unfold shapeP
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- o_u stays seated where the statement grows and what is noted of o_u stays. -/
theorem seatedUB_grows (p : Par) (a b : St) (g : Grows a.st b.st) (hu : b.loc.oU = a.loc.oU)
    (h : seatedUB p a = true) : seatedUB p b = true := by
  obtain ⟨⟨x, hx, hs⟩, h2, h3⟩ := (seatedUB_iff p a).1 h
  obtain ⟨x', hx', gx⟩ := g.2.2 _ x hx
  refine (seatedUB_iff p b).2 ⟨⟨x', ?_, gx.1.trans hs⟩, ?_, ?_⟩
  · rw [hu]
    exact hx'
  · rw [hu, g.1]
    exact h2
  · rw [g.1]
    exact h3

/-- **At a yes of "send o_u".** -/
theorem shapeU_sendU (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (sentU : Array OracleNotice)
    (hU : withU P.par.S = some sentU) (hQ : Q.sent = sentU) (nU : Nat)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d rs gs = .ok d')
    (hs : shapeP P.par nU d = true) :
    shapeU P.par nU 0 d' = true ∧ midB (nU + sentU.size) d' = true := by
  obtain ⟨h2, hok, hr0, hm⟩ := (shapeP_iff P.par nU d).1 hs
  obtain ⟨hn, hrO, hne⟩ := (midB_iff nU d).1 hm
  obtain ⟨ids, a1, a2, rU, cU, la, k2⟩ := sendAt_inv P n Q inFront groups _ d d' rs gs h
  rw [hQ] at rU
  obtain ⟨oU1, lU1⟩ := onward_recvP _ d a1 sentU ids rU
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv P.par a2 d' ids k2
  obtain ⟨nN, sU0, shU⟩ := withU_first P.par.S sentU hU
  obtain ⟨eo, x, hx, sx⟩ := recvP_first _ d a1 sentU ids rU nN sU0 o ho
  obtain ⟨x2, hx2, gx2⟩ := cU.grows.2.2 _ x hx
  have hc : a2.st.codes = d.st.codes := (oU1.trans cU).grows.1
  have hg := sendAt_groups P n Q inFront groups _
    (fun a ids e k => (behindU_inv P.par a e ids k).1) d d' rs gs h
  have hsz := sendAt_size P n Q inFront groups _ (Fence.behindU_book P.par) d d' rs gs h
  have la2 : a2.loc = d.loc := la.trans lU1
  have ekey : d'.loc.key = d.loc.key := by rw [l2, ← la2]
  have epsi : d'.loc.psiSh = d.loc.psiSh := by rw [l2, ← la2]
  have egU : d'.loc.gU = d.loc.gU := by rw [l2, ← la2]
  have egO : d'.loc.gOmega = d.loc.gOmega := by rw [l2, ← la2]
  have eoU : d'.loc.oU = ⟨o, vectorLay a2.st.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩ := by
    rw [l2]
  refine ⟨(shapeU_iff P.par nU 0 d').2
    ⟨?_, (seatedUB_iff P.par d').2 ⟨⟨x2, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩,
    (midB_iff _ d').2 ⟨?_, ?_, ?_⟩⟩
  · unfold shape2 shape1 at h2 ⊢
    rw [ekey, epsi]
    exact h2
  · rw [s2, eoU]
    exact hx2
  · exact (gx2.1.trans sx).trans shU
  · rw [eoU, s2]
  · rw [s2, hc]
    exact hok
  · rw [eoU]
    exact eo.trans hn
  · rw [egU, rows_of_groups d d' hg]
    exact hr0
  · rw [hsz, hn, hQ]
  · rw [egO, rows_of_groups d d' hg]
    exact hrO
  · rw [egO, egU]
    exact hne

/-- **At a yes of "send o_omega".** -/
theorem shapeO_sendO (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (hQ : Q.sent = withOmega P.par.S) (hS : P.par.S.sharedSplitNeeded = true) (nU nO c : Nat)
    (hne : nO ≠ nU) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d rs gs = .ok d')
    (hs : shapeU P.par nU c d = true) (hm : midB nO d = true) :
    shapeO P.par nU nO c 0 d' = true := by
  obtain ⟨h2, hsU, hnU, hrU⟩ := (shapeU_iff P.par nU c d).1 hs
  obtain ⟨hn, hrO, _⟩ := (midB_iff nO d).1 hm
  obtain ⟨ids, a1, a2, rO, cO, la, k2⟩ := sendAt_inv P n Q inFront groups _ d d' rs gs h
  rw [hQ] at rO
  obtain ⟨oO1, lO1⟩ := onward_recvP _ d a1 _ ids rO
  obtain ⟨s2, o, sp, ho, l2⟩ := behindOmega_inv P.par a2 d' ids k2
  obtain ⟨nN, sO0, shO⟩ := withOmega_first P.par.S
  obtain ⟨eo, x, hx, sx⟩ := recvP_first _ d a1 _ ids rO nN sO0 o ho
  obtain ⟨x2, hx2, gx2⟩ := cO.grows.2.2 _ x hx
  have hg := sendAt_groups P n Q inFront groups _
    (fun a ids e k => (behindOmega_inv P.par a e ids k).1) d d' rs gs h
  have la2 : a2.loc = d.loc := la.trans lO1
  have ekey : d'.loc.key = d.loc.key := by rw [l2, ← la2]
  have epsi : d'.loc.psiSh = d.loc.psiSh := by rw [l2, ← la2]
  have egU : d'.loc.gU = d.loc.gU := by rw [l2, ← la2]
  have egO : d'.loc.gOmega = d.loc.gOmega := by rw [l2, ← la2]
  have eoU : d'.loc.oU = d.loc.oU := by rw [l2, ← la2]
  have eoO : d'.loc.oOmega = o := by rw [l2]
  have gr : Grows d.st d'.st := by
    rw [s2]
    exact (oO1.trans cO).grows
  refine (shapeO_iff P.par nU nO c 0 d').2 ⟨(shapeU_iff P.par nU c d').2
    ⟨?_, seatedUB_grows P.par d d' gr eoU hsU, ?_, ?_⟩, (shapedOB_iff P.par d').2 ⟨x2, ?_, ?_⟩,
    ?_, hne, ?_, hS⟩
  · unfold shape2 shape1 at h2 ⊢
    rw [ekey, epsi]
    exact h2
  · rw [eoU]
    exact hnU
  · rw [egU, rows_of_groups d d' hg]
    exact hrU
  · rw [s2, eoO]
    exact hx2
  · exact (gx2.1.trans sx).trans shO
  · rw [eoO]
    exact eo.trans hn
  · rw [egO, rows_of_groups d d' hg]
    exact hrO

/-- A new group has the next number and no open row; the older groups' rows stay. -/
theorem newGroupP_rows (d d' : St) (c mc n : Nat) (h : newGroupP d c mc = some (n, d')) :
    n = d.st.groups.size ∧ d'.st.groups.size = n + 1 ∧ rowsOn d' n = [] ∧
      ∀ g, g < n → rowsOn d' g = rowsOn d g := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, by simp [VerifiableInference.Desc.Ground.withGroup],
      by simp [rowsOn, VerifiableInference.Desc.Ground.withGroup], fun g hg => ?_⟩
    simp [rowsOn, VerifiableInference.Desc.Ground.withGroup, Array.getElem?_push,
      Nat.ne_of_lt hg]
  · cases h

/-- **At a yes of "LIN point"**, two codes. -/
theorem point_extras (p : Par) (hS : p.S.sharedSplitNeeded = true) (nU : Nat) (a b : St)
    (rs : List Fmt.RoundView) (k : linPoint p a rs = some b) (hn : a.st.oracles.size = nU) :
    linOk b.st.codes p.S = true ∧ (rowsOn b b.loc.gU).length = 0 ∧ midB nU b = true := by
  have hok := linPoint_ok p a b rs k
  obtain ⟨_, _, _, _, ho, hc⟩ := linPoint_inv p a b rs k
  refine ⟨by rw [hc]; exact hok, ?_⟩
  unfold linPoint at k
  split at k
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at k
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := k
    rw [if_pos hS] at h2
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
    obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
    obtain ⟨e1, s1, r1, _⟩ := newGroupP_rows a d1 _ _ gU h1
    obtain ⟨e2, _, r2, k2⟩ := newGroupP_rows d1 d2 _ _ gO h3
    have hlt : gU < gO := by rw [e2, s1]; exact Nat.lt_succ_self _
    refine ⟨?_, (midB_iff nU _).2 ⟨?_, ?_, ?_⟩⟩
    · show (rowsOn d2 gU).length = 0
      rw [k2 gU hlt, r1]
      rfl
    · rw [ho]
      exact hn
    · show (rowsOn d2 gO).length = 0
      rw [r2]
      rfl
    · show gO ≠ gU
      exact Nat.ne_of_gt hlt
  · cases k

/-- **At the second of the kind's eight blocks.** -/
theorem shapes_at_b2 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (sentU : Array OracleNotice)
    (hU : withU P.S = some sentU) (nU : Nat) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b2.decide d rs gs = .ok d')
    (hs : shapeP P.par nU d = true) :
    shapeU P.par nU 0 d' = true ∧ midB (nU + sentU.size) d' = true := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU', hU', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  obtain rfl : sentU' = sentU := Option.some.inj (hU'.symm.trans hU)
  exact shapeU_sendU P _ _ _ _ sentU' hU (parK1_sent _ _ _ _) nU d d' rs gs h hs

/-- **At the fifth.** -/
theorem shapes_at_b5 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (nU nO c : Nat) (hne : nO ≠ nU) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b5.decide d rs gs = .ok d')
    (hs : shapeU P.par nU c d = true) (hm : midB nO d = true) :
    shapeO P.par nU nO c 0 d' = true := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  exact shapeO_sendO P _ _ _ _ (parK1_sent _ _ _ _) hS nU nO c hne d d' rs gs h hs hm

/-- **THE FILLING OF "shape k"** at the borders 2, …, 9 of the shared chain (in front of block k).
nU, nO: o_u's and o_omega's numbers in the chain's statement, by the plan; n: the positions that
"LOC" draws. At the other borders: no test. -/
def shapeK (p : Par) (nU nO n : Nat) : Nat → St → Bool
  | 2 => shapeP p nU
  | 3 => shapeM p nU nO 0
  | 4 => shapeM p nU nO p.S.fold.index.answers
  | 5 => shapeM p nU nO (p.S.fold.index.answers + n)
  | 6 => shapeO p nU nO (p.S.fold.index.answers + n) 0
  | 7 => shapeO p nU nO (p.S.fold.index.answers + n) 0
  | 8 => shapeO p nU nO (p.S.fold.index.answers + n) 0
  | 9 => shapeO p nU nO (p.S.fold.index.answers + n + 1) (0 + 1)
  | _ => fun _ => true

end Desc.K14.Law
