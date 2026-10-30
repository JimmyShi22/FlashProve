-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorAtFile.lean

What it proves. The door at the test on G_u, set against the proof file's own description under the
head P5J.AtMg: the term P5J.F0T o Zp Np cF (Johnson/P5J/AtTerm.lean). (1) Wherever the fold over its
shared chain's flat list returns from its own start at an instance, doorUF's state with the reader
colsLoc is the one with which that fold enters the test on G_u (doorUF_at_F0T); so wherever the
description says yes (doorUF_at_yes). (2) Its shared chain's declared rounds begin as cols_of_reads
(DoorReturns.lean) asks, so the columns that the frame's text lays for the shared view begin with
colsLoc's (cols_at_F0T). (3) The second of the two tests on the key that doorUF_returns takes as
premises is, like the first, one that "(rec_gamma)"'s function makes itself (laysRec_beta).

Names.
  doorUF_at_F0T, doorUF_at_yes   (1).
  decl_shared_F0T, cols_at_F0T   (2).
  laysRec_beta   (3).

By what. doorUF_of_carried_head (DoorOfFoldAt.lean); FileDescription.run_ok, chainAt_ok
(Johnson/Desc/RunLaws.lean); flat_retype_all (Johnson/Desc/K14/Law/SharedFlat.lean); blocks_rounds
(Johnson/Desc/K14/Honest/ChainSteps.lean); rounds_of_blocks, one_round (Johnson/Desc/K14/Law/);
blocks_head, facts_at_head (NearAtHead.lean); eight_of (MarksBehind.lean); cols_of_reads
(DoorReturns.lean).

Limits.
- One front and one view. The three ties hk, hr with hn, hc are premises here. At a run of the
  frame's walking prover, at a called part, the second and the third are shown, and the fold's
  return with them: DoorAtRun.lean; the first stays a premise on the prover.
- Nothing where the fold fails, or where the description says no. Its yes is three chains'
  acceptance and the tests on plan, instance and views: for an honest run that is completeness,
  which nobody has.
- cols_at_F0T: that the view's rounds have the challenges which readsOf is given, and that stored is
  the prover's own function at the input, is not said.
- The two tests on the key (its sizes fit; no seed has the factor 0) are on a field of the public
  instance. In the release a key's seeds follow from the committed table's name by the hash: a
  statement on honest provers has to carry the second among what a valid instance is, or to bound
  the chance of it over the random oracle (Johnson/Desc/K14/Honest/YesChain.lean's head).
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone. No example of the
  head is shown here.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorOfFoldAt
import Johnson.P5J.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks FileDescription.run_ok chainAt_ok)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (Seat.enter)
open VerifiableInference.Desc.Own (allZero)
open Desc.K14 (St blocks first readsAtLoc laysRec laysRecL)
open Desc.Plain (Par)
open Desc.K14.Honest (ReadsNone blocks_rounds)
open ProofFile.Honest (Read readsOf fillCols Table)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-! ## 1 At the description's own list and start -/

/-- **At the proof file's own description, under the head.** P5J.F0T o Zp Np cF
(Johnson/P5J/AtTerm.lean) is the seated description's own term. Wherever the fold over its shared
chain's flat list returns, from its own start at the instance x, at the view v, doorUF's state is
the one with which that fold enters the test on G_u, and doorUF is off its fall-back.
The ties, on one front and one view. hk: (α) the key that the prover's shared parts are given is the
instance's. hr, hn: (β) what the part has seen are the view's first rounds, as many as the eight
declare. hc: (γ) the reader's columns are the view's first columns.
hv: that fold returns: the very term on which the description's decision (runEnd, by chainAt) goes
at its shared chain. Where it fails nothing is said; through the ties it can narrow the input.
No SaysAt follows. The test on G_u alone. -/
theorem doorUF_at_F0T (h : P5J.AtMg o Z D r Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (key : W → TableKey) (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (x : ProofFile.Inst) (v : Fmt.View) (hk : key w = x.pub.key)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hn : fr.seen.rounds.length =
      ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length)
    (hc : ∃ more, v.opened = colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds ++ more)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 (P5J.F0T o Zp Np cF).shared.blocksInOrder
      ((P5J.F0T o Zp Np cF).start₂ ((P5J.F0T o Zp Np cF).pub x)) v.rounds v.opened = .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key) v.rounds
        v.opened = .ok (d8, rest, more) ∧
      foldBlocks 0 ((P5J.F0T o Zp Np cF).shared.blocksInOrder.drop 9) d8 rest more = .ok out ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes (key w))
        fr.seen.rounds (colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) w fr) :=
  doorUF_of_carried_head (Cl := ProofFile.Cl) h Zp.p.chains b1 b2 b3 b4 b5 b6 b7 b8 hb key stored w fr
    x.pub.key v hk hr hn hc (VerifiableInference.Desc.K12.Seat.tests Np)
    VerifiableInference.Desc.K12.Seat.last out hv

/-- **Wherever the proof file's description says yes**, at the instance x and three views of which v
is the shared chain's: as doorUF_at_F0T, less its conjunct on what lies behind the nine, and with
the fold's return no premise any more: the decision's yes gives it (FileDescription.run_ok, chainAt_ok,
Johnson/Desc/RunLaws.lean). The three ties stay premises. It says nothing of a run at which the
description says no; and its yes is three chains' acceptance and the tests on plan, instance and
views: for an honest run that is completeness, which nobody has. -/
theorem doorUF_at_yes (h : P5J.AtMg o Z D r Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (key : W → TableKey) (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (x : ProofFile.Inst) (v₁ v v₃ : Fmt.View) (hk : key w = x.pub.key)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hn : fr.seen.rounds.length =
      ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length)
    (hc : ∃ more, v.opened = colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds ++ more)
    (hy : (P5J.F0T o Zp Np cF).run x v₁ v v₃ = true) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key) v.rounds
        v.opened = .ok (d8, rest, more) ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes (key w))
        fr.seen.rounds (colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) w fr) := by
  obtain ⟨e₁, e₂, e₃, -, -, -, -, -, -, h2, -⟩ := (FileDescription.run_ok _ x v₁ v v₃).1 hy
  obtain ⟨d8, rest, more, g1, -, g3, g4⟩ := doorUF_at_F0T h b1 b2 b3 b4 b5 b6 b7 b8 hb key stored w
    fr x v hk hr hn hc (e₂, [], []) (chainAt_ok.1 h2).2
  exact ⟨d8, rest, more, g1, g3, g4⟩

/-! ## 2 The third tie at the description's declared rounds -/

/-- **The declared rounds of the proof file's shared chain begin as cols_of_reads asks**: three
rounds that read no column ("LIN point"'s one; the two of the sending of o_u), then "LOC"'s round,
which reads the committed table; then others. -/
theorem decl_shared_F0T (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry) (post : List Fmt.DeclaredRound),
      ReadsNone d0 ∧ ReadsNone d1 ∧ ReadsNone d2 ∧
      (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 = d0 :: d1 :: d2 ::
        { entry := e, stored := [readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item] } :: post :=
    by
  obtain ⟨bs, hbs⟩ := blocks_head h
  obtain ⟨B, rfl⟩ := eight_of _ bs hbs
  obtain ⟨p1, e2, e3, e4, -⟩ := blocks_rounds _ _ B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 hbs
    (facts_at_head h).2.2
  obtain ⟨d0, hd0, -⟩ := Desc.K14.Law.one_round
    (Desc.K14.Law.rounds_of_blocks _ B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 hbs).1
  have h0 : ReadsNone d0 := p1 d0 (by rw [hd0]; exact List.mem_cons_self)
  have eF : (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 =
      (((Desc.K14.chainOf Zp.p.chains (K1.qAt Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np)
        VerifiableInference.Desc.K12.Seat.last).retype (Cl' := ProofFile.Cl)).blocksInOrder).flatMap
          (·.rounds) := rfl
  rw [eF, Desc.K14.Law.flat_retype_all Zp.p.chains (K1.qAt Zp Np) B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7
    B.b8 _ _ hbs]
  simp only [List.flatMap_cons, List.flatMap_append, List.map_cons, List.map_nil,
    List.flatMap_nil]
  have key : ∀ T : List Fmt.DeclaredRound, ∃ post, [] ++ ((B.b1.rounds ++ (B.b2.rounds ++
          (B.b3.rounds ++ (B.b4.rounds ++ (B.b5.rounds ++ (B.b6.rounds ++ (B.b7.rounds ++
            (B.b8.rounds ++ [])))))))) ++ T) = d0 ::
      { entry := VerifiableInference.Desc.K1.seedEntry
          (Desc.K14.Law.parU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) } ::
      { entry := VerifiableInference.Desc.K1.answerEntry
          (Desc.K14.Law.parU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) } ::
      { entry := Desc.K14.Law.entryAt (K1.qAt Zp Np) 1,
        stored := [readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item] } :: post := by
    intro T
    rw [hd0, e2, e3, e4]
    exact ⟨_, rfl⟩
  obtain ⟨post, hpost⟩ := key _
  exact ⟨d0, _, _, _, post, h0, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hpost⟩

/-- **(γ) at the proof file's own description, under the head.** The frame's run lays the shared
view's columns as fillCols (readsOf 1 0 stored tree F.roundsDeclaredByBlocks.2.1 ‹the shared challenges›) ‹the stored
run's columns› (ProofFile/Honest/Frame.lean: run). Where no stored run is handed and that returns c,
c begins with colsLoc's columns, at the same function stored. rs: any rounds whose challenges are
those that readsOf is given. That the view's rounds have these challenges, and that stored is the
prover's storedWords at the input, is not said here. -/
theorem cols_at_F0T (h : P5J.AtMg o Z D r Zp Np cF) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (hf : fillCols (readsOf 1 0 stored tree (P5J.F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 (rs.map (·.drawn))) [] =
      .ok c) :
    ∃ more, c = colsLoc (K1.qAt Zp Np) stored rs ++ more := by
  obtain ⟨d0, d1, d2, e, post, h0, h1, h2, eq⟩ := decl_shared_F0T (o := o) h
  rw [eq] at hf
  exact cols_of_reads _ 1 0 stored tree d0 d1 d2 e post h0 h1 h2 rs c hf

/-! ## 3 The second test on the key -/

/-- Where "(rec_gamma)"'s function returns, no seed of the key has the factor 0: the second of its
three named tests (laysRecL, Johnson/Desc/K14/Text.lean). The like of laysRec_key
(ShapeBehind.lean), which has the first. -/
theorem laysRec_beta (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    (d.loc.key.seeds.all (!allZero ·.beta)) = true := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, hg, _⟩ := VerifiableInference.Desc.obind_ok h
  have hok : VerifiableInference.Desc.Ground.ok (laysRecL p d.loc) = true := by
    by_contra hno
    simp [guard, hno] at hg
  simp only [VerifiableInference.Desc.Ground.ok, laysRecL, List.all_cons, Bool.and_eq_true] at hok
  exact hok.2.1

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.doorUF_at_F0T
#print axioms ProofFile.Honest.K12.Light.doorUF_at_yes
#print axioms ProofFile.Honest.K12.Light.decl_shared_F0T
#print axioms ProofFile.Honest.K12.Light.cols_at_F0T
#print axioms ProofFile.Honest.K12.Light.laysRec_beta
