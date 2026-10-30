--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ChainSteps.lean: the eight sub-protocols of the linear claim's shared
rounds, in terms of the format's own step: one statement with both halves.

A sub-protocol's decision is its step (Johnson/Desc/Block.lean: Block.step): the test on the rounds'
form (roundsFit), the test that the view's next columns are, in key, position and width, those that
the rounds read, and then the decide function, on the rounds without the sealed digest and on these
columns laid in groups. A chain's decision is the fold of the steps (foldBlocks).

The statement (eight_steps_hold), at the shared chain's first state and the eight sub-protocols that
the IOP as written in Lean makes (blocks P). FIRST HALF, TRUE OF EVERY PROVER: where the view's
rounds pass roundsFit and its next columns are those that "LOC" reads, the eight steps return .ok
one behind the other, and so does the fold; no premise speaks of a value sent, but for its form.
SECOND HALF, inside the conclusion, behind five hypotheses of its own: hRec and hCol on the
committed table (no committer is in Lean), and three equations that say that the OOD answers and the
scalar shown are the honest ones: then the statement behind the eighth is in order, and every open
row and every sample row in it holds of the honest tables (AllMet).

Main names:
  ReadsNone           a declared round that reads no column
  blocks_rounds       what the eight declare: six of them rounds that read no column ("(rec_gamma)"
                      and the joinings none at all); the two sendings their kind's two rounds; "LOC"
                      one round, which reads the committed table at all its locations
  step_plain          a sub-protocol whose rounds read no column: its step is roundsFit and decide,
                      whatever columns lie ahead (the library's step_of_decide,
                      Johnson/Desc/First/Att/K05SeamBack.lean, has it with no column ahead)
  lookup_some         a look-up finds something where the key occurs
  loc_groups          the one group of columns that "LOC" reads
  cols_of_step        **from the step's own test on the columns: each sampled location has its
                      column, of as many words as the committed table has rows**
  step_loc            the step of "LOC"
  eight_steps_hold    **the statement**

What is assumed, as premises of the theorem.
  Public: the IOP as written in Lean makes its eight sub-protocols (hb); PlanFacts; the two sendings
      pass their kind's test on the plan.
  On the key: its sizes fit; no seed has the factor 0 (no choice of an honest committer's).
  On the view: roundsFit at the six sub-protocols that have rounds; the columns' test at "LOC"
      (hcs).
  As hypotheses of the second half alone: hRec; hCol; what is shown is honest.

What stands between this theorem and a file's shared chain, and is not in it:
  the front sub-protocol, which has no round and leaves the state as it is; the two proximity tests
      and the chain's closing, which stand behind the eight (Johnson/Desc/K14/Blocks.lean)
  the chain laid flat, which turns each sub-protocol's test on the plan (a step reads none); the
      first tree's number 0; nothing left over at the chain's end (Johnson/Desc/Block.lean:
      Chain.blocksInOrder, chainAt)
  the file's tests on the plan, on the instance (the key's item is the plan's; its words are below
      the prime) and on the views (every word below the prime)
  The theorem is general in the rounds and columns that lie behind the eight's, and in the first
      tree's number, so that it can be joined. It is not joined.

What is not claimed. That the chain or a file accepts. That a committer's key and columns meet hRec
and hCol. That any program writes such a view. That the honest tables are what lies beneath the
roots that the verifier is sent. Shapes with one code, or whose masks are not sent ahead, are not
served. Nothing on soundness or on hiding. This is not completeness of the protocol, of the shared
chain or of a program.

-/
import Johnson.Desc.K14.Honest.ChainHolds
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.Sound.Gather
import Johnson.Desc.K15.SendOwnLaw
import Johnson.Desc.First.Att.K05SeamBack
import Johnson.Desc.K14.Law.StoredCols
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block OpenedColumn roundsFit noDigest groupsOf foldBlocks roundsFit_noDigest
  foldBlocks_ok)
open VerifiableInference.Desc.Sound (step_ok_iff groupsAt roundsFit_len)
open VerifiableInference.Desc.First.Att.P (groupsOf_none)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14.Law (locations genK parU parO entryAt mem_of_lookup)

/-- A declared round that reads no column. -/
def ReadsNone (r : Fmt.DeclaredRound) : Prop := r.stored = [] ∧ r.opens = []

/-- **What the eight declare.** -/
theorem blocks_rounds (P : P14) (sentU : Array OracleNotice)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU P.S = some sentU) :
    (∀ r ∈ b1.rounds, ReadsNone r) ∧
      b2.rounds = VerifiableInference.Desc.K1.rounds (parU P sentU) ∧ b3.rounds = [] ∧
      b4.rounds = [{ entry := entryAt P 1, stored := [readsAtLoc P.S.fold P.item] }] ∧
      b5.rounds = VerifiableInference.Desc.K1.rounds (parO P) ∧ b6.rounds = [] ∧
      (∀ r ∈ b7.rounds, ReadsNone r) ∧ ∀ r ∈ b8.rounds, ReadsNone r := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU', hU', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hU.symm.trans hU')
  have plain : ∀ l : List Fmt.Entry,
      ∀ r ∈ l.map (fun e => ({ entry := e } : Fmt.DeclaredRound)), ReadsNone r := by
    intro l r hr
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    exact ⟨rfl, rfl⟩
  refine ⟨plain _, rfl, rfl, ?_, rfl, rfl, plain _, plain _⟩
  show (((entries P).drop 1).take 1).map (fun e =>
    ({ entry := e, stored := [readsAtLoc P.S.fold P.item] } : Fmt.DeclaredRound)) = _
  unfold entryAt entries rounds whys
  split <;> rfl

/-- K1's two rounds read no column. -/
theorem send_plain (Q : VerifiableInference.Desc.K1.Par) :
    ∀ r ∈ VerifiableInference.Desc.K1.rounds Q, ReadsNone r := by
  intro r hr
  simp only [VerifiableInference.Desc.K1.rounds, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **A sub-protocol whose rounds read no column**: its step is roundsFit and decide, whatever
columns lie ahead. -/
theorem step_plain (b : Block St Unit) (hb : ∀ r ∈ b.rounds, ReadsNone r) (ft : Nat) (s s' : St)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hfit : roundsFit b.rounds rs = true)
    (hd : b.decide s (rs.map noDigest) [] = .ok s') : b.step ft s rs cols = .ok (s', 0) := by
  have hg := groupsOf_none ft b.rounds (rs.map (·.drawn)) hb
  refine (step_ok_iff ft b s s' rs cols 0).2 ⟨hfit, ?_, ?_, ?_⟩
  · rw [hg]
    rfl
  · rw [hg]
    rfl
  · unfold groupsAt
    rw [hg]
    exact hd

/-- A look-up finds something where the key occurs. -/
theorem lookup_some {β : Type} : ∀ (l : List (Nat × β)) (a : Nat), (∃ b, (a, b) ∈ l) →
    ∃ b, l.lookup a = some b
  | [], _, h => by
    obtain ⟨_, hb⟩ := h
    cases hb
  | (k, v) :: l, a, h => by
    by_cases hk : a = k
    · subst hk
      exact ⟨v, List.lookup_cons_self⟩
    · obtain ⟨b, hb⟩ := h
      have hb' : (a, b) ∈ l := by
        rcases List.mem_cons.1 hb with e | e
        · exact absurd (congrArg Prod.fst e) hk
        · exact e
      obtain ⟨c, hc⟩ := lookup_some l a ⟨b, hb'⟩
      refine ⟨c, ?_⟩
      have hne : (a == k) = false := by simpa using hk
      rw [List.lookup_cons, hne]
      exact hc

/-- **The one group of columns that "LOC" reads**: the committed table's, at the list of the sampled
locations, each of as many words as the table has rows. -/
theorem loc_groups (P : P14) (ft : Nat) (R : Fmt.Drawn) (hl : R.poss.length = P.S.fold.columns) :
    groupsOf ft [{ entry := entryAt P 1, stored := [readsAtLoc P.S.fold P.item] }] [R] =
      [(Fmt.listOf (R.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)] := by
  have hp : Fmt.partOf (readsAtLoc P.S.fold P.item) R.poss = R.poss := by
    show (R.poss.drop 0).take P.S.fold.columns = R.poss
    rw [List.drop_zero, ← hl, List.take_length]
  show [(Fmt.listOf ((Fmt.partOf (readsAtLoc P.S.fold P.item) R.poss).map
    (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
      (Fmt.storedKey P.item, x, P.S.fold.index.rows)] ++ [] ++ [] = _
  rw [hp]
  rfl

/-- **From the step's own test on the columns: each sampled location has its column, of as many
words as the committed table has rows.** cs: the view's next columns. -/
theorem cols_of_step (P : P14) (R : Fmt.Drawn) (cs : List OpenedColumn)
    (h : cs.map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (Fmt.listOf (R.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)) :
    ∀ x ∈ R.poss, ∃ col,
      (cs.map fun c => (c.2.1, c.2.2)).lookup (x % 2 ^ P.S.fold.index.code.logN) = some col ∧
        col.length = P.S.fold.index.rows := by
  intro x hx
  have h1 : x % 2 ^ P.S.fold.index.code.logN ∈
      Fmt.listOf (R.poss.map (· % 2 ^ P.S.fold.index.code.logN)) :=
    (Fmt.listOf_mem _ _).2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  have h2 : (Fmt.storedKey P.item, x % 2 ^ P.S.fold.index.code.logN, P.S.fold.index.rows) ∈
      cs.map (fun x => (x.1, x.2.1, x.2.2.length)) := by
    rw [h]
    exact List.mem_map.2 ⟨_, h1, rfl⟩
  obtain ⟨c, hc, e⟩ := List.mem_map.1 h2
  have e1 : c.2.1 = x % 2 ^ P.S.fold.index.code.logN := congrArg (fun y => y.2.1) e
  obtain ⟨col, hcol⟩ := lookup_some (cs.map fun c => (c.2.1, c.2.2))
    (x % 2 ^ P.S.fold.index.code.logN) ⟨c.2.2, List.mem_map.2 ⟨c, hc, by rw [e1]⟩⟩
  refine ⟨col, hcol, ?_⟩
  obtain ⟨c', hc', e'⟩ := List.mem_map.1 (mem_of_lookup _ _ _ hcol)
  have h3 : (c'.1, c'.2.1, c'.2.2.length) ∈ cs.map (fun x => (x.1, x.2.1, x.2.2.length)) :=
    List.mem_map.2 ⟨c', hc', rfl⟩
  rw [h] at h3
  obtain ⟨y, _, ey⟩ := List.mem_map.1 h3
  have e2 : P.S.fold.index.rows = c'.2.2.length := congrArg (fun z => z.2.2) ey
  have e3 : c'.2.2 = col := congrArg Prod.snd e'
  rw [← e3, e2]

/-- **The step of "LOC".** cs: the view's next columns, those that the round reads; cs': what lies
behind them. -/
theorem step_loc (P : P14) (b4 : Block St Unit)
    (hr : b4.rounds = [{ entry := entryAt P 1, stored := [readsAtLoc P.S.fold P.item] }])
    (ft : Nat) (s s' : St) (R4 : Fmt.RoundView) (cs cs' : List OpenedColumn)
    (hfit : roundsFit b4.rounds [R4] = true) (hl : R4.drawn.poss.length = P.S.fold.columns)
    (h : cs.map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (Fmt.listOf (R4.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows))
    (hd : b4.decide s [noDigest R4] [cs.map fun c => (c.2.1, c.2.2)] = .ok s') :
    b4.step ft s [R4] (cs ++ cs') = .ok (s', cs.length) := by
  have hg : groupsOf ft b4.rounds ([R4].map (·.drawn)) =
      [(Fmt.listOf (R4.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows)] := by
    rw [hr]
    exact loc_groups P ft R4.drawn hl
  have hlen : ((Fmt.listOf (R4.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
      (Fmt.storedKey P.item, x, P.S.fold.index.rows)).length = cs.length := by
    rw [← h, List.length_map]
  refine (step_ok_iff ft b4 s s' [R4] (cs ++ cs') cs.length).2 ⟨hfit, ?_, ?_, ?_⟩
  · rw [hg, List.take_left']
    · simpa using h
    · rfl
  · rw [hg]
    simpa using hlen.symm
  · unfold groupsAt
    rw [hg, List.take_left' rfl]
    simp only [List.map_cons, List.map_nil, hlen]
    show b4.decide s [noDigest R4] [(cs.take cs.length).map fun c => (c.2.1, c.2.2)] = .ok s'
    rw [List.take_length]
    exact hd

/-- **The eight sub-protocols' own steps return .ok one behind the other, and so does the fold,
whatever values of the right form are sent, by an honest prover or a cheating one; and, under hRec
and hCol, if the values shown are the honest ones, the statement behind the eighth is in order and
all that it claims holds of the honest words.** At the shared chain's first state. cs: the columns
that "LOC" reads; rest, cs': the rounds and the columns that lie behind the eight's. Not
completeness. -/
theorem eight_steps_hold (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : TableKey)
    (hkey : keyFits key P.par.S.fold.index = true)
    (hbeta : (key.seeds.all (!allZero ·.beta)) = true)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView) (cs cs' : List OpenedColumn) (rest : List Fmt.RoundView) (ft : Nat)
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hcs : cs.map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf ft b4.rounds [R4.drawn]).flatMap id) (H : Inputs) :
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 : St,
      b1.step ft (first P.codes key) [R1] (cs ++ cs') = .ok (d1, 0) ∧
      b2.step ft d1 [R2a, R2b] (cs ++ cs') = .ok (d2, 0) ∧
      b3.step ft d2 [] (cs ++ cs') = .ok (d3, 0) ∧
      b4.step ft d3 [R4] (cs ++ cs') = .ok (d4, cs.length) ∧
      b5.step ft d4 [R5a, R5b] cs' = .ok (d5, 0) ∧ b6.step ft d5 [] cs' = .ok (d6, 0) ∧
      b7.step ft d6 [R7] cs' = .ok (d7, 0) ∧ b8.step ft d7 [R8] cs' = .ok (d8, 0) ∧
      foldBlocks ft [b1, b2, b3, b4, b5, b6, b7, b8] (first P.codes key)
        ([R1, R2a, R2b, R4, R5a, R5b, R7, R8] ++ rest) (cs ++ cs') = .ok (d8, rest, cs') ∧
      ((∀ x ∈ key.seeds.zipIdx, ∀ r < P.par.S.fold.index.rows,
          RowAnswer P.par.S.fold.index (x.1.z.map rdE.val) (rdE.val x.1.beta)
            (fun t => rdE.val (thetaE t)) x.2 (H.Rw r)
            (rdE.val (key.record.getD (r * P.par.S.fold.index.answers + x.2) zeroE))) →
        (∀ x ∈ locations P.par R4, ∀ col,
          (cs.map fun c => (c.2.1, c.2.2)).lookup x = some col → ∀ q < P.par.S.fold.index.rows,
            rdE.val (ofF (col.toArray.getD q 0)) = genK rdE P.par.S.fold x (H.Rw q)) →
        R2b.vals = answersAt (parU P sentU) d1.st R2a H.w₀ (rowsU P (first P.codes key) R1 H) →
        R5b.vals = answersAt (parO P) d4.st R5a (words1 P sentU (first P.codes key) R1 H)
          (rowsO P (first P.codes key) R1 H) →
        R8.vals = [.e (Slice.ofE (muRun P (first P.codes key) R1 R7 H))] →
        Means.AllMet rdE d8.st (words2 P sentU (first P.codes key) R1 H)) := by
  obtain ⟨p1, e2, e3, e4, e5, e6, p7, p8⟩ :=
    blocks_rounds P sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hP.goes
  -- the form of the rounds, without the digest
  obtain ⟨r4, hr4, hl4, _, _, _⟩ := Law.loc_fits P b1 b2 b3 b4 b5 b6 b7 b8 hb [R4] f4
  obtain rfl : R4 = r4 := by simpa using hr4
  have g4 : cs.map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (Fmt.listOf (R4.drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN))).map fun x =>
        (Fmt.storedKey P.item, x, P.S.fold.index.rows) := by
    rw [hcs, e4, loc_groups P ft R4.drawn hl4]
    simp
  have n1 : roundsFit b1.rounds [noDigest R1] = true := (roundsFit_noDigest _ [R1]).trans f1
  have n2 : roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU))
      [noDigest R2a, noDigest R2b] = true := by
    rw [← e2]
    exact (roundsFit_noDigest _ [R2a, R2b]).trans f2
  have n5 : roundsFit (VerifiableInference.Desc.K1.rounds (parO P))
      [noDigest R5a, noDigest R5b] = true := by
    rw [← e5]
    exact (roundsFit_noDigest _ [R5a, R5b]).trans f5
  have n7 : roundsFit b7.rounds [noDigest R7] = true := (roundsFit_noDigest _ [R7]).trans f7
  have n8 : roundsFit b8.rounds [noDigest R8] = true := (roundsFit_noDigest _ [R8]).trans f8
  have hR := rounds8_of_fits P sentU layO hP b1 b2 b3 b4 b5 b6 b7 b8 hb hBU hBO (noDigest R1)
    (noDigest R2a) (noDigest R2b) (noDigest R4) (noDigest R5a) (noDigest R5b) (noDigest R7)
    (noDigest R8) (cs.map fun c : OpenedColumn => (c.2.1, c.2.2)) n1 n2 n5 n7 n8
    (cols_of_step P R4.drawn cs g4)
  -- the eight return
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, x2, x5, ids2, ids5, h⟩ := eight_return P sentU layO hP
    (first P.codes key) rfl rfl hkey hbeta _ _ _ _ _ _ _ _ _ hR [] []
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
    h.decides hP.goes b1 b2 b3 b4 b5 b6 b7 b8 hb [] [] [] [] [] [] []
  -- the eight steps
  have s1 := step_plain b1 p1 ft _ d1 [R1] (cs ++ cs') f1 k1
  have s2 := step_plain b2 (by rw [e2]; exact send_plain _) ft d1 d2 [R2a, R2b] (cs ++ cs') f2 k2
  have s3 := step_plain b3 (by rw [e3]; intro r hr; cases hr) ft d2 d3 [] (cs ++ cs')
    (by rw [e3]; rfl) k3
  have s4 := step_loc P b4 e4 ft d3 d4 R4 cs cs' f4 hl4 g4 k4
  have s5 := step_plain b5 (by rw [e5]; exact send_plain _) ft d4 d5 [R5a, R5b] cs' f5 k5
  have s6 := step_plain b6 (by rw [e6]; intro r hr; cases hr) ft d5 d6 [] cs' (by rw [e6]; rfl) k6
  have s7 := step_plain b7 p7 ft d6 d7 [R7] cs' f7 k7
  have s8 := step_plain b8 p8 ft d7 d8 [R8] cs' f8 k8
  refine ⟨d1, d2, d3, d4, d5, d6, d7, d8, s1, s2, s3, s4, s5, s6, s7, s8, ?_, ?_⟩
  · -- the fold
    have t1 := foldBlocks_ok ft b1 [b2, b3, b4, b5, b6, b7, b8] (first P.codes key) [R1]
      ([R2a, R2b, R4, R5a, R5b, R7, R8] ++ rest) (cs ++ cs') (roundsFit_len _ _ f1) d1 0 s1
    have t2 := foldBlocks_ok ft b2 [b3, b4, b5, b6, b7, b8] d1 [R2a, R2b]
      ([R4, R5a, R5b, R7, R8] ++ rest) (cs ++ cs') (roundsFit_len _ _ f2) d2 0 s2
    have t3 := foldBlocks_ok ft b3 [b4, b5, b6, b7, b8] d2 [] ([R4, R5a, R5b, R7, R8] ++ rest)
      (cs ++ cs') (by rw [e3]; rfl) d3 0 s3
    have t4 := foldBlocks_ok ft b4 [b5, b6, b7, b8] d3 [R4] ([R5a, R5b, R7, R8] ++ rest) (cs ++ cs')
      (roundsFit_len _ _ f4) d4 cs.length s4
    have t5 := foldBlocks_ok ft b5 [b6, b7, b8] d4 [R5a, R5b] ([R7, R8] ++ rest) cs'
      (roundsFit_len _ _ f5) d5 0 s5
    have t6 := foldBlocks_ok ft b6 [b7, b8] d5 [] ([R7, R8] ++ rest) cs' (by rw [e6]; rfl) d6 0 s6
    have t7 := foldBlocks_ok ft b7 [b8] d6 [R7] ([R8] ++ rest) cs' (roundsFit_len _ _ f7) d7 0 s7
    have t8 := foldBlocks_ok ft b8 [] d7 [R8] rest cs' (roundsFit_len _ _ f8) d8 0 s8
    rw [List.drop_zero] at t1 t2 t3 t5 t6 t7 t8
    rw [List.drop_left' rfl] at t4
    exact t1.trans (t2.trans (t3.trans (t4.trans (t5.trans (t6.trans (t7.trans t8))))))
  · intro hRec hCol ha2 ha5 hmu
    exact returned_holds P sentU layO hP (first P.codes key) _ _ _ _ _ _ _ _ _ [] []
      d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5 h H hBU hBO n2 n5
      (first_kept rdE P.codes key H.w₀) hRec hCol ha2 ha5 hmu

end Desc.K14.Honest

#print axioms Desc.K14.Honest.blocks_rounds
#print axioms Desc.K14.Honest.send_plain
#print axioms Desc.K14.Honest.step_plain
#print axioms Desc.K14.Honest.lookup_some
#print axioms Desc.K14.Honest.loc_groups
#print axioms Desc.K14.Honest.cols_of_step
#print axioms Desc.K14.Honest.step_loc
#print axioms Desc.K14.Honest.eight_steps_hold
