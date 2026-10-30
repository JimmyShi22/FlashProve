--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesChain.lean: the decide functions of the eight sub-protocols of the linear
claim's shared rounds return .ok one behind the other.

From a state that has the plan's codes, with statement and book in step: "LIN point", the sending of
o_u, "(rec_gamma)", "LOC", the sending of o_omega and o_sp, the joinings, "LIN zeta", "SPLIT".

THIS IS TRUE OF EVERY PROVER. No premise speaks of a value that the prover sends, but for the form
of what is sent: the eight test no equation (Johnson/Desc/K14/Text.lean), so a cheating prover's
values of the right form are taken by the same theorem. What an honest prover's values add is in
Johnson/Desc/K14/Honest/ChainHolds.lean.

A decide function is no decision without the format's tests on the rounds and the columns in front
of it (Johnson/Desc/Block.lean: Block.step): see Johnson/Desc/K14/Honest/ChainSteps.lean.

Main names:
  PlanFacts p codes sentU layO   the public premises: on the codes and the shape alone
  Rounds8             the premises on a view's rounds and columns: how many elements were sampled;
                      no sampled seed has the factor 0 as machine words; the counts of seeds,
                      answers and pads fit; each sampled location has its column; "SPLIT"'s round
                      holds one scalar
  SentTo, SentTo.decides   what a sending and the kind's note behind it are made of
  sendU_returns, sendO_returns   the two sendings' decideSend returns .ok, the notes can be made,
                      and the facts that the next places ask hold behind them
  alone_behind        behind its sending o_omega has a tree to itself
  locU, locO, locZ    the part of the state that the kind itself notes (Lin), behind the two
                      sendings and in front of "SPLIT", written out
  Returned            the six places' functions and the two sendings have returned one behind the
                      other, with the facts at the states where a constraint is laid
  eight_return        **there are such states**. (Each place's file writes its state out; here the
                      states are bound by ∃ and read again by the library's laws on a place that has
                      returned)
  Returned.decides    **so the eight sub-protocols' own decide functions return .ok one behind the
                      other**

On the key. Two premises are on the instance's key: its sizes fit, and no seed of the key has the
factor 0 (hkey, hbeta). At a key that fails them the guard of "(rec_gamma)"'s function fails
whatever a prover sends (Johnson/Desc/K14/Text.lean: laysRec; no theorem here). In the release a
key's seeds follow from the committed table's name by the hash: so the second is no choice of an
honest committer's. A statement on honest provers above this file has to carry it among what a valid
instance is, or to bound the chance of it over the random oracle.

What is not claimed. That a decision accepts. That the public premises hold at any shape: they are
tests with code, evaluated in Johnson/Desc/K14/Honest/YesAt.lean. That a view's rounds meet Rounds8:
YesRounds.lean. That the laid constraints hold of what was sent. Shapes with one code, or whose
masks are not sent ahead, are not served. Nothing on the two proximity tests behind the eight.
Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesBorders
import Johnson.Desc.K14.Honest.YesPoint
import Johnson.Desc.K14.Honest.YesRecAt
import Johnson.Desc.K14.Honest.YesLocAt
import Johnson.Desc.Own.AloneMeans
import Johnson.Desc.K14.Law.LedgerRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground (groupOk ok sentL)
open VerifiableInference.Desc.Own (lengthsFit linFits keyFits allZero aloneIn)
open VerifiableInference.Desc.K1 (decideSend seedsOf answersIn shapesOf fitB)
open VerifiableInference.Desc.Key (laid_point laid_rec laid_loc joined_joins)
open VerifiableInference.Desc.Key.LaidW (send_laid inFrontOf)
open VerifiableInference.Desc.Book (cnt)
open Desc.K14.Law (parU parO)

/-- **The public premises**: on the codes and the shape alone. sentU: what goes out with o_u; layO:
how the trees of o_omega's sending are laid. -/
structure PlanFacts (p : Par) (codes : Codes) (sentU : Array OracleNotice)
    (layO : TreeLay) : Prop where
  lengths : lengthsFit codes = true
  lin : linFits codes p.S = true
  groupU : groupOk codes p.S.fold.u.code p.S.sharedMaskCode = true
  groupO : groupOk codes p.S.omega.code p.S.sharedMaskCode = true
  two : p.S.sharedSplitNeeded = true
  ahead : p.S.masksAhead = true
  goes : withU p.S = some sentU
  goesTwo : sentU.size = 2
  noticesU : ok (sentL codes sentU) = true
  noticesO : ok (sentL codes (withOmega p.S)) = true
  free : 0 < Send.freeMaskEntries p.S.sharedSplit.maskRows
    (codes.mask.getD p.S.sharedSplit.maskCode default).ell p.S.sharedSplit.answers
  trees : layTrees codes (withOmega p.S) = some layO
  /-- o_omega's notice gets a tree that o_sp's does not share -/
  own : layO.tree.getD 0 0 < layO.shapes.size ∧ layO.tree.getD 1 0 ≠ layO.tree.getD 0 0

/-- The first notice of o_u's sending. -/
theorem withU_zero {S : LinShape} {sentU : Array OracleNotice} (h : withU S = some sentU) :
    sentU[0]? = some ⟨S.fold.u, S.fold.leafClass⟩ := by
  obtain ⟨w, _, rfl⟩ := Option.map_eq_some_iff.1 h
  simp

/-- The two notices of o_omega's sending. -/
theorem withOmega_two {S : LinShape} (h : S.sharedSplitNeeded = true) :
    (withOmega S).size = 2 ∧ (withOmega S)[0]? = some ⟨S.omega, S.omegaLeafClass⟩ ∧
      (withOmega S)[1]? = some ⟨S.sharedSplit, S.sharedSplitLeafClass⟩ := by
  simp [withOmega, linMessageOmega, h]

/-- What a sending and the kind's note behind it are made of. x: the state behind the sending's own
decision; ids: the new messages' numbers. -/
structure SentTo (Q : VerifiableInference.Desc.K1.Par) (note : St → Array Nat → Option St)
    (d d' : St) (ra rb : Fmt.RoundView) (x : DState (Array Nat)) (ids : Array Nat) : Prop where
  sent : decideSend Q none (inFrontOf d) [ra, rb] = .ok (ids, x)
  noted : note { d with st := x.st, book := x.book, roots := x.roots, opened := x.opened } ids =
    some d'
  st : d'.st = x.st
  size : d'.st.oracles.size = d.st.oracles.size + 2

/-- The sub-protocol's decide function returns .ok, from what a sending is made of. -/
theorem SentTo.decides {Q : VerifiableInference.Desc.K1.Par} {note : St → Array Nat → Option St}
    {d d' : St} {ra rb : Fmt.RoundView} {x : DState (Array Nat)} {ids : Array Nat}
    (h : SentTo Q note d d' ra rb x ids) (P : P14) (n : String) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (gs : List (List (Nat × List UInt64))) :
    (sendAt P n Q inFront groups note).decide d [ra, rb] gs = .ok d' :=
  sendAt_returns P n Q inFront groups note d d' [ra, rb] gs ids x h.sent h.noted

/-- **The sending of o_u**: decideSend returns .ok, the note can be made, and what the next places
ask holds behind it. -/
theorem sendU_returns (p : Par) (codes : Codes) (k : TableKey)
    (Q : VerifiableInference.Desc.K1.Par)
    (sentU : Array OracleNotice) (layO : TreeLay) (hP : PlanFacts p codes sentU layO)
    (hQc : Q.codes = codes) (hQs : Q.sent = sentU) (d : St) (ra rb : Fmt.RoundView)
    (hB : Carried p codes k d [] [])
    (hnz : ∀ s ∈ seedsOf Q ra, isZeroE s.2 = false)
    (hfit : fitB Q.codes Q.seeds (shapesOf Q) (answersIn rb) = true) :
    ∃ d' x ids, SentTo Q (behindU p) d d' ra rb x ids ∧ Carried p codes k d' [] [] ∧ HasU p d' ∧
      d'.loc = { d.loc with
        oU := ⟨d.st.oracles.size, vectorLay codes p.S.fold.u p.S.fold.rowsHigh⟩
        firstMask := some (d.st.oracles.size + 1) } := by
  have hx := send_returns Q d ra rb (hB.codes.trans hQc.symm) hnz
    (by rw [hQc, hQs]; exact hP.noticesU) hB.step hfit
  have S := send_laid Q none (inFrontOf d) _ ra rb _ hx
  have i0 := ids_zero Q.sent.size d.st.oracles.size (by rw [hQs, hP.goesTwo]; omega)
  have i1 := ids_one Q.sent.size d.st.oracles.size (by rw [hQs, hP.goesTwo]; omega)
  have hb := behindU_is p ({ d with
      st := (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra) (answersIn rb)).st
      book := (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
        (answersIn rb)).book
      roots :=
        (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra) (answersIn rb)).roots
      opened :=
        (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
          (answersIn rb)).opened } :
      St) _ _ _ hP.ahead i0 i1
  have hc : (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
      (answersIn rb)).st.codes = Q.codes := S.codes.trans (hB.codes.trans hQc.symm)
  refine ⟨_, _, _, ⟨hx, hb, rfl, ?_⟩, ?_, ?_, ?_⟩
  · have h2 := S.size
    rw [hQs, hP.goesTwo] at h2
    exact h2
  · exact carried_send p codes k Q d _ _ [] [] _ hB S rfl rfl rfl rfl
  rotate_left
  · show ({ d.loc with
      oU := ⟨d.st.oracles.size, vectorLay (VerifiableInference.Desc.K1.behind Q (inFrontOf d)
        (seedsOf Q ra) (answersIn rb)).st.codes p.S.fold.u p.S.fold.rowsHigh⟩
      firstMask := some (d.st.oracles.size + 1) } : Lin) = _
    rw [hc, hQc]
  · refine ⟨rfl, ?_⟩
    obtain ⟨hsh, hf, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes p.S).1 hP.lin
    obtain ⟨y, hy, s1, s2, s3, _⟩ := send_left Q none (inFrontOf d) _ ra rb _ hx 0
      ⟨p.S.fold.u, p.S.fold.leafClass⟩ (by rw [hQs]; exact withU_zero hP.goes)
      (by have := hf.1.2.2.2.2.1; show p.S.fold.u.answers ≠ 0; omega)
    rw [Nat.add_zero] at hy
    refine ⟨y, hy, s1, s2, ?_⟩
    show y.pad = ((Send.pad (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
      (answersIn rb)).st.codes p.S.fold.u).getD []).map fun q => (q.part, q.index)
    rw [hc]
    exact s3

/-- An array of one member. -/
theorem one_member (a : Array Nat) (o : Nat) (h1 : a.size = 1) (h2 : a[0]? = some o) :
    a = #[o] := by
  obtain ⟨l⟩ := a
  match l, h1, h2 with
  | [b], _, h2 =>
    have : b = o := by simpa using h2
    rw [this]

/-- **Behind its sending o_omega has a tree to itself.** -/
theorem alone_behind (B B' : TreeBook) (n0 : Nat) (lay : TreeLay) (num : Nat → Nat)
    (src : Nat → Fmt.Src) (h : VerifiableInference.Desc.Book.Seated B B' 2 n0 lay num src)
    (h1 : lay.tree.getD 0 0 < lay.shapes.size) (h2 : lay.tree.getD 1 0 ≠ lay.tree.getD 0 0) :
    aloneIn B' n0 = true := by
  obtain ⟨t, ht, _, _, _, hsz, hpart⟩ := h.made _ h1
  have hp := h.new 0 (by omega)
  rw [Nat.add_zero] at hp
  have c2 : cnt lay.tree (lay.tree.getD 0 0) 2 = 1 := by
    show (0 + (if lay.tree.getD 0 0 = lay.tree.getD 0 0 then 1 else 0)) +
      (if lay.tree.getD 1 0 = lay.tree.getD 0 0 then 1 else 0) = 1
    rw [if_pos rfl, if_neg h2]
  have h0 := hpart 0 (by omega) rfl
  rw [Nat.add_zero] at h0
  exact (VerifiableInference.Desc.Own.aloneIn_iff B' n0).2
    ⟨_, t, hp, ht, one_member t.parts n0 (hsz.trans c2) h0⟩

/-- **The sending of o_omega and o_sp**: decideSend returns .ok, the note can be made, and what the
next places ask holds behind it. -/
theorem sendO_returns (p : Par) (codes : Codes) (k : TableKey)
    (Q : VerifiableInference.Desc.K1.Par)
    (sentU : Array OracleNotice) (layO : TreeLay) (hP : PlanFacts p codes sentU layO)
    (hQc : Q.codes = codes) (hQs : Q.sent = withOmega p.S) (d : St) (ra rb : Fmt.RoundView)
    (mU mO : List Nat) (hB : Carried p codes k d mU mO)
    (hU : HasU p d) (hnz : ∀ s ∈ seedsOf Q ra, isZeroE s.2 = false)
    (hfit : fitB Q.codes Q.seeds (shapesOf Q) (answersIn rb) = true) :
    ∃ d' x ids, SentTo Q (behindOmega p) d d' ra rb x ids ∧ Carried p codes k d' mU mO ∧
      HasU p d' ∧ HasO p d' ∧
      d'.loc = { d.loc with oOmega := d.st.oracles.size, oSp := d.st.oracles.size + 1 } := by
  obtain ⟨w2, w0, w1⟩ := withOmega_two hP.two
  have hx := send_returns Q d ra rb (hB.codes.trans hQc.symm) hnz
    (by rw [hQc, hQs]; exact hP.noticesO) hB.step hfit
  have S := send_laid Q none (inFrontOf d) _ ra rb _ hx
  have i0 := ids_zero Q.sent.size d.st.oracles.size (by rw [hQs, w2]; omega)
  have i1 := ids_one Q.sent.size d.st.oracles.size (by rw [hQs, w2]; omega)
  have hb := behindOmega_is p ({ d with
      st := (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra) (answersIn rb)).st
      book := (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
        (answersIn rb)).book
      roots :=
        (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra) (answersIn rb)).roots
      opened :=
        (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
          (answersIn rb)).opened } :
      St) _ _ _ hP.two i0 i1
  have hc : (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
      (answersIn rb)).st.codes = Q.codes := S.codes.trans (hB.codes.trans hQc.symm)
  obtain ⟨hsh, _⟩ := (VerifiableInference.Desc.Own.linFits_iff codes p.S).1 hP.lin
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits p.S.sharedSplit p.S.sharedMaskCode := by
    rcases hsh.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hP.two] at e
      cases e
    · exact e
  obtain ⟨y0, hy0, a1, a2, a3, _⟩ := send_left Q none (inFrontOf d) _ ra rb _ hx 0
    ⟨p.S.omega, p.S.omegaLeafClass⟩ (by rw [hQs]; exact w0)
    (by have := hsh.2.2.2.2.2.2.1.2.2.2; show p.S.omega.answers ≠ 0; omega)
  obtain ⟨y1, hy1, b1, b2, b3, b4⟩ := send_left Q none (inFrontOf d) _ ra rb _ hx 1
    ⟨p.S.sharedSplit, p.S.sharedSplitLeafClass⟩ (by rw [hQs]; exact w1)
    (by have := hSp.2.2.1; show p.S.sharedSplit.answers ≠ 0; omega)
  rw [Nat.add_zero] at hy0
  have hlt := hU.u.lt
  refine ⟨_, _, _, ⟨hx, hb, rfl, ?_⟩, ?_, ?_, ?_, rfl⟩
  · have h2 := S.size
    rw [hQs, w2] at h2
    exact h2
  · exact carried_send p codes k Q d _ _ mU mO _ hB S rfl rfl rfl rfl
  · refine ⟨?_, msg_older S hU.u⟩
    show d.loc.oU.lay = vectorLay (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
      (answersIn rb)).st.codes p.S.fold.u p.S.fold.rowsHigh
    rw [hc, hQc, ← hB.codes]
    exact hU.lay
  · refine ⟨⟨y0, hy0, a1, a2, ?_⟩, ⟨y1, hy1, b1, b2, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · show y0.pad = ((Send.pad (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
        (answersIn rb)).st.codes p.S.omega).getD []).map fun q => (q.part, q.index)
      rw [hc]
      exact a3
    · show y1.pad = ((Send.pad (VerifiableInference.Desc.K1.behind Q (inFrontOf d) (seedsOf Q ra)
        (answersIn rb)).st.codes p.S.sharedSplit).getD []).map fun q => (q.part, q.index)
      rw [hc]
      exact b3
    · intro z hz
      obtain rfl : y1 = z := Option.some.inj (hy1.symm.trans hz)
      show y1.ledger = Slice.freshLedger (VerifiableInference.Desc.K1.behind Q (inFrontOf d)
        (seedsOf Q ra) (answersIn rb)).st.codes p.S.sharedSplit
      rw [hc]
      exact b4
    · show d.st.oracles.size ≠ d.st.oracles.size + 1
      omega
    · show d.st.oracles.size + 1 ≠ d.loc.oU.oracle
      omega
    · show d.st.oracles.size ≠ d.loc.oU.oracle
      omega
    · obtain ⟨lay, hlay, hbook⟩ := S.book
      have e : lay = layO := by
        have h1 : layTrees codes (withOmega p.S) = some lay := by
          rw [← hQs, ← hB.codes]
          exact hlay
        exact Option.some.inj (h1.symm.trans hP.trees)
      subst e
      rw [hQs, w2] at hbook
      exact alone_behind _ _ _ _ _ _ hbook hP.own.1 hP.own.2

/-- **The premises on a view's rounds and columns.** QU, QO: the two sendings' parameters. -/
structure Rounds8 (p : Par) (QU QO : VerifiableInference.Desc.K1.Par)
    (r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView) (cols : List (Nat × List UInt64)) : Prop where
  point : (drawn r1).length = p.S.kCol
  seedsU : ∀ s ∈ seedsOf QU r2a, isZeroE s.2 = false
  fitU : fitB QU.codes QU.seeds (shapesOf QU) (answersIn r2b) = true
  columns : ∀ x ∈ r4.drawn.poss, ∃ col,
    cols.lookup (x % 2 ^ p.S.fold.index.code.logN) = some col ∧ col.length = p.S.fold.index.rows
  seedsO : ∀ s ∈ seedsOf QO r5a, isZeroE s.2 = false
  fitO : fitB QO.codes QO.seeds (shapesOf QO) (answersIn r5b) = true
  zeta : (drawn r7).length = p.S.kRow
  scalar : ∃ x, r8.vals = [.e x]

/-! ## What the kind itself notes, written out -/

/-- What the kind notes (Lin) behind o_u's sending. l0: what it notes in front of the eight; g0, n0:
the numbers of groups and of messages there; r1: the round of "LIN point". -/
def locU (p : Par) (codes : Codes) (l0 : Lin) (g0 n0 : Nat) (r1 : Fmt.RoundView) : Lin :=
  { l0 with
    psiSh := drawn r1, gU := g0, gOmega := g0 + 1
    oU := ⟨n0, vectorLay codes p.S.fold.u p.S.fold.rowsHigh⟩, firstMask := some (n0 + 1) }

/-- What the kind notes behind o_omega's sending. -/
def locO (p : Par) (codes : Codes) (l0 : Lin) (g0 n0 : Nat) (r1 : Fmt.RoundView) : Lin :=
  { locU p codes l0 g0 n0 r1 with oOmega := n0 + 2, oSp := n0 + 3 }

/-- What the kind notes in front of "SPLIT". r7: the round of "LIN zeta". -/
def locZ (p : Par) (codes : Codes) (l0 : Lin) (g0 n0 : Nat) (r1 r7 : Fmt.RoundView) : Lin :=
  { locO p codes l0 g0 n0 r1 with zFd := drawn r7 }

/-- **The eight have returned**: the six places' functions and the two sendings, one behind the
other; what the kind notes is written out; the facts at the states where a constraint is laid. -/
structure Returned (P : P14) (sentU : Array OracleNotice) (d0 : St)
    (r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (rs3 rs6 : List Fmt.RoundView) (d1 d2 d3 d4 d5 d6 d7 d8 : St) (x2 x5 : DState (Array Nat))
    (ids2 ids5 : Array Nat) : Prop where
  k1 : linPoint P.par d0 [r1] = some d1
  s2 : SentTo (parU P sentU) (behindU P.par) d1 d2 r2a r2b x2 ids2
  k3 : laysRec P.par d2 rs3 = some d3
  k4 : loc P.par d3 [r4] [cols] = some d4
  s5 : SentTo (parO P) (behindOmega P.par) d4 d5 r5a r5b x5 ids5
  k6 : joins P.par d5 rs6 = some d6
  k7 : linZeta d6 [r7] = some d7
  k8 : split P.par d7 [r8] = some d8
  l2 : d2.loc = locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1
  l3 : d3.loc = locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1
  l7 : d7.loc = locZ P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1 r7
  n1 : d1.st.oracles.size = d0.st.oracles.size
  n4 : d4.st.oracles.size = d0.st.oracles.size + 2
  c2 : d2.st.codes = P.codes
  c3 : d3.st.codes = P.codes
  c7 : d7.st.codes = P.codes
  f3 : FrontU P.par d3 [d3.loc.oU.oracle]
  f8 : Front8 P.par d7
  u2 : HasU P.par d2
  u3 : HasU P.par d3
  u7 : HasU P.par d7
  o7 : HasO P.par d7

/-- **The eight return, whatever values of the right form are sent.** d0: a state with the plan's
codes, statement and book in step. -/
theorem eight_return (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (d0 : St)
    (hc : d0.st.codes = P.codes) (hstep : d0.st.oracles.size = d0.book.place.size)
    (hkey : keyFits d0.loc.key P.par.S.fold.index = true)
    (hbeta : (d0.loc.key.seeds.all (!allZero ·.beta)) = true)
    (r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (hR : Rounds8 P.par (parU P sentU) (parO P) r1 r2a r2b r4 r5a r5b r7 r8 cols)
    (rs3 rs6 : List Fmt.RoundView) :
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5,
      Returned P sentU d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5
        ids2 ids5 := by
  -- "LIN point"
  obtain ⟨d1, k1⟩ : ∃ d1, linPoint P.par d0 [r1] = some d1 :=
    ⟨_, linPoint_returns P.par d0 r1 (by rw [hc]; exact hP.lengths) (by rw [hc]; exact hP.lin)
      (by rw [hc]; exact hP.groupU) (by rw [hc]; exact hP.groupO) hP.two⟩
  obtain ⟨r, hr, L1⟩ := laid_point P.par d0 d1 [r1] hP.two k1
  obtain rfl : r1 = r := by simpa using hr
  have B1 := carried_point P.par P.codes d0.loc.key d0 d1 r1 hc hstep rfl hR.point L1
  -- the sending of o_u
  obtain ⟨d2, x2, ids2, s2, B2, U2, l2⟩ := sendU_returns P.par P.codes d0.loc.key
    (parU P sentU) sentU layO hP rfl
    (Law.parK1_sent P 2 _ sentU) d1 r2a r2b B1 hR.seedsU hR.fitU
  have l2' : d2.loc = locU P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1 := by
    rw [l2, L1.loc, L1.oracles]
    rfl
  -- "(rec_gamma)"
  obtain ⟨d3, k3⟩ : ∃ d3, laysRec P.par d2 rs3 = some d3 := by
    obtain ⟨_, _, _, _, k⟩ := laysRec_returns P.par d2 rs3 (frontU_of hP.lin B2 U2)
      (by rw [B2.key]; exact hkey) (by rw [B2.key]; exact hbeta)
    exact ⟨_, k⟩
  obtain ⟨GU3, rows3, L3⟩ := laid_rec P.par d2 d3 rs3 k3
  have B3 := carried_rec P.par P.codes _ d2 d3 GU3 rows3 [] B2 L3
  have U3 := hasU_rec P.par d2 d3 GU3 rows3 U2 L3
  rw [← L3.loc] at B3
  -- "LOC"
  obtain ⟨d4, k4⟩ : ∃ d4, loc P.par d3 [r4] [cols] = some d4 := by
    obtain ⟨_, _, k⟩ := loc_returns P.par d3 r4 cols (frontU_of hP.lin B3 U3) hR.columns
    exact ⟨_, k⟩
  obtain ⟨r, cs, GU4, rows4, hr, hcs, L4⟩ := laid_loc P.par d3 d4 [r4] [cols] k4
  have B4 := carried_loc P.par P.codes _ d3 d4 r GU4 rows4 _ _ B3 L4
  have U4 := hasU_loc P.par d3 d4 r GU4 rows4 U3 L4
  rw [← L4.loc] at B4
  -- the sending of o_omega and o_sp
  obtain ⟨d5, x5, ids5, s5, B5, U5, O5, l5⟩ := sendO_returns P.par P.codes d0.loc.key
    (parO P) sentU layO hP rfl
    (Law.parK1_sent P 5 _ _) d4 r5a r5b _ _ B4 U4 hR.seedsO hR.fitO
  have e5 : d5.loc.oU = d4.loc.oU := by rw [l5]
  rw [← e5] at B5
  have n4 : d4.st.oracles.size = d0.st.oracles.size + 2 := by
    rw [L4.oracles, L3.size, s2.size, L1.oracles]
  have l5' : d5.loc = locO P.par P.codes d0.loc d0.st.groups.size d0.st.oracles.size r1 := by
    rw [l5, L4.loc, L3.loc, l2', n4]
    rfl
  -- the joinings
  obtain ⟨d6, k6⟩ : ∃ d6, joins P.par d5 rs6 = some d6 := by
    obtain ⟨_, _, _, _, k⟩ := joins_returns P.par d5 rs6 hP.two (front6_of hP.lin B5 O5)
    exact ⟨_, k⟩
  obtain ⟨GU6, GO6, L6⟩ := joined_joins P.par d5 d6 rs6 hP.two k6
  have B6 := carried_joined P.par P.codes _ d5 d6 GU6 GO6 B5 L6
  have U6 := hasU_joined P.par d5 d6 GU6 GO6 U5 O5 L6
  have O6 := hasO_joined P.par d5 d6 GU6 GO6 O5 L6
  rw [← L6.loc] at B6
  -- "LIN zeta" and "SPLIT"
  obtain ⟨x, hx⟩ := hR.scalar
  have U7 : HasU P.par { d6 with loc := { d6.loc with zFd := drawn r7 } } := ⟨U6.lay, U6.u⟩
  have O7 : HasO P.par { d6 with loc := { d6.loc with zFd := drawn r7 } } :=
    ⟨O6.omega, O6.sp, O6.ledger, O6.apart, O6.apartU, O6.apartOU, O6.alone⟩
  have F8 : Front8 P.par { d6 with loc := { d6.loc with zFd := drawn r7 } } :=
    front8_of hP.lin ⟨B6.codes, B6.step, B6.key, B6.psi, B6.two, B6.gU, B6.gO⟩ U7 O7 hR.zeta hP.free
  obtain ⟨d8, k8⟩ : ∃ d8, split P.par { d6 with loc := { d6.loc with zFd := drawn r7 } } [r8] =
      some d8 := by
    obtain ⟨_, _, _, _, _, _, k⟩ := split_returns P.par
      { d6 with loc := { d6.loc with zFd := drawn r7 } } r8 x hP.two F8 hx
    exact ⟨_, k⟩
  refine ⟨d1, d2, d3, d4, d5, d6, { d6 with loc := { d6.loc with zFd := drawn r7 } }, d8, x2, x5,
    ids2, ids5, k1, s2, k3, k4, s5, k6, linZeta_returns d6 r7, k8, l2', L3.loc.trans l2', ?_,
    by rw [L1.oracles], n4, B2.codes, B3.codes, B6.codes, frontU_of hP.lin B3 U3, F8,
    U2, U3, U7, O7⟩
  show ({ d6.loc with zFd := drawn r7 } : Lin) = _
  rw [L6.loc, l5']
  rfl

/-- Where a place's function returns, the sub-protocol's decide function returns .ok, under
whichever named tests. (The converse is the library's Desc.K14.why_ok.) -/
theorem why_of_some (l : VerifiableInference.Desc.Ground.Clauses) {x : Option St} {d : St}
    (h : x = some d) : why l x = .ok d := by
  rw [h]
  rfl

/-- **So the eight sub-protocols' own decide functions return .ok one behind the other.** -/
theorem Returned.decides {P : P14} {sentU : Array OracleNotice} {d0 : St}
    {r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView} {cols : List (Nat × List UInt64)}
    {rs3 rs6 : List Fmt.RoundView} {d1 d2 d3 d4 d5 d6 d7 d8 : St} {x2 x5 : DState (Array Nat)}
    {ids2 ids5 : Array Nat}
    (h : Returned P sentU d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5
      ids2 ids5) (hU : withU P.S = some sentU) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (gs1 gs2 gs3 gs5 gs6 gs7 gs8 : List (List (Nat × List UInt64))) :
    b1.decide d0 [r1] gs1 = .ok d1 ∧ b2.decide d1 [r2a, r2b] gs2 = .ok d2 ∧
      b3.decide d2 rs3 gs3 = .ok d3 ∧ b4.decide d3 [r4] [cols] = .ok d4 ∧
      b5.decide d4 [r5a, r5b] gs5 = .ok d5 ∧ b6.decide d5 rs6 gs6 = .ok d6 ∧
      b7.decide d6 [r7] gs7 = .ok d7 ∧ b8.decide d7 [r8] gs8 = .ok d8 := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU', hU', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hU.symm.trans hU')
  exact ⟨why_of_some (linPointL P.par d0) h.k1, h.s2.decides P _ _ _ gs2,
    why_of_some (laysRecL P.par d2.loc) h.k3, why_of_some [] h.k4, h.s5.decides P _ _ _ gs5,
    why_of_some (joinsL d5) h.k6, why_of_some [] h.k7,
    why_of_some (foldL P.par.S d7.loc ++
      (((fold P.par.S d7.loc (linLayOmega d7.st.codes P.par.S)).map (splitL d7)).getD [])) h.k8⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.withU_zero
#print axioms Desc.K14.Honest.withOmega_two
#print axioms Desc.K14.Honest.sendU_returns
#print axioms Desc.K14.Honest.one_member
#print axioms Desc.K14.Honest.alone_behind
#print axioms Desc.K14.Honest.sendO_returns
#print axioms Desc.K14.Honest.SentTo.decides
#print axioms Desc.K14.Honest.eight_return
#print axioms Desc.K14.Honest.why_of_some
#print axioms Desc.K14.Honest.Returned.decides
