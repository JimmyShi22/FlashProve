--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ChainStepsMet.lean: an honest run of the eight sub-protocols of the linear
claim's shared rounds in terms of the format's own step and fold, written out: all premises of
eight_steps_hold (Johnson/Desc/K14/Honest/ChainSteps.lean), and the five hypotheses of its second
half, are met together at one member.

The run is that of Johnson/Desc/K14/Honest/ChainMet.lean: the committed table's rows are 0, with the
key and the column of ChainWitness.lean; the words in front and the random values of the four
messages are arbitrary; the OOD answers of a sending are chosen when the state in front of that
sending is there. The statement (HonestStepsW) shows the key, the challenges and the column written
out, the eight steps, the fold, and the three equations on what is shown.

Main names:
  fits_entry          when one round passes the format's test on its form
  entry_names, own_rounds   the entries of the kind's own four rounds, by field; which sub-protocol
                      declares which
  fits_point, fits_loc, fits_zeta, fits_split, colW, cols_met   the witness's rounds and column pass
                      the format's tests
  HonestStepsW        an honest run at the witness's key, challenges and column, in terms of the
                      format's step
  steps_met           **there is an honest run**
  eight_of_cond       the IOP as written in Lean makes its eight sub-protocols where K14Cond holds
  steps_key, steps_real   at the two typed shapes

What is assumed, as premises: PlanFacts; the two sendings pass their kind's test on the plan; the
IOP as written in Lean makes its eight sub-protocols. At the two typed shapes: nothing.
What is not claimed. More than "not empty": eight_steps_hold is general, this file is one member, at
a committed table that is 0, at one location, at challenges that are written and not sampled, at a
key that is no committer's (what ChainWitness.lean's head says of the witness holds here). That the
shared chain or a file accepts. Nothing on the two proximity tests and the chain's closing. Nothing
on soundness or on hiding. This is not completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.ChainSteps
import Johnson.Desc.K14.Honest.ChainMet
import Johnson.Desc.Key.KeyClaimFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G Desc.Plain
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block OpenedColumn roundsFit drawsMarkedNonzeroHaveNonzeroWords itemOf groupsOf foldBlocks)
open VerifiableInference.Desc.K1 (planOkOwn realSized)
open Lk6.AtPlan (keyFull)
open Desc.K14.Law (parU parO entryAt)

/-- **When one round passes the format's test on its form.** -/
theorem fits_entry (d : Fmt.DeclaredRound) (r : Fmt.RoundView) (k : Fmt.Kind)
    (hk : Fmt.kindOf d.entry.name = some k) (hs : k ≠ .seeds) (ha : d.entry.answers = 0)
    (hro : d.entry.roots = 0) (hnz : d.entry.drawNZ = 0)
    (hv : r.vals.map itemOf = List.replicate (d.entry.msg / 24) .e)
    (he : r.drawn.elems.length = d.entry.drawE) (hp : r.drawn.poss.length = d.entry.poss)
    (ht : r.drawn.trits = []) (ht0 : d.entry.trits = 0)
    (hlt : ∀ x ∈ r.drawn.poss, x < 2 ^ d.entry.logN) : roundsFit [d] [r] = true := by
  have i1 : d.items.filter (· != .root) = List.replicate (d.entry.msg / 24) .e := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, ha, hro]
  have n1 : drawsMarkedNonzeroHaveNonzeroWords d r = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk, Option.any_some, List.all_eq_true]
    intro x hx
    have h1 : x.1 ∈ Fmt.dsElems d.entry k := (List.of_mem_zip (a := x.1) (b := x.2) hx).1
    unfold Fmt.dsElems at h1
    rw [if_neg hs, hnz, List.replicate_zero, List.append_nil] at h1
    rw [List.eq_of_mem_replicate h1]
    rfl
  simp only [roundsFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    i1, n1, ht, ht0]
  exact ⟨⟨⟨⟨⟨⟨⟨hv, he⟩, hp⟩, rfl⟩, hlt⟩, fun _ h => nomatch h⟩, trivial⟩, trivial⟩

/-- The entries of the kind's own four rounds, by field, where the shape has two codes. -/
theorem entry_names (P : P14) (hS : P.S.sharedSplitNeeded = true) :
    (∃ w, entryAt P 0 = { name := "LIN point", work := w, drawE := P.S.kCol }) ∧
    (∃ w, entryAt P 1 =
      { name := "LOC", work := w, poss := P.S.fold.columns, logN := P.S.fold.index.code.logN }) ∧
    (∃ w, entryAt P 2 = { name := "LIN zeta", work := w, drawE := P.S.kRow }) ∧
    (∃ w, entryAt P 3 = { name := "SPLIT", work := w, msg := 24 }) := by
  unfold entryAt entries rounds whys
  rw [if_pos hS]
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Which sub-protocol declares which of the kind's own rounds. -/
theorem own_rounds (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hS : P.S.sharedSplitNeeded = true) :
    b1.rounds = [{ entry := entryAt P 0 }] ∧ b7.rounds = [{ entry := entryAt P 2 }] ∧
      b8.rounds = [{ entry := entryAt P 3 }] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · show (((entries P).drop 0).take 1).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) = _
    unfold entryAt entries rounds whys
    rw [if_pos hS]
    rfl
  · show (((entries P).drop 2).take 1).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) = _
    unfold entryAt entries rounds whys
    rw [if_pos hS]
    rfl
  · show (((entries P).drop 3).take (if P.S.sharedSplitNeeded then 1 else 0)).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound)) = _
    unfold entryAt entries rounds whys
    rw [if_pos hS, if_pos hS]
    rfl

/-- The witness's round of "LIN point" passes the format's test. -/
theorem fits_point (P : P14) (hS : P.S.sharedSplitNeeded = true) :
    roundsFit [{ entry := entryAt P 0 }] [pointW P] = true := by
  obtain ⟨⟨w, e⟩, _⟩ := entry_names P hS
  rw [e]
  exact fits_entry _ _ .elems (by show Fmt.kindOf "LIN point" = some .elems; decide) (by decide) rfl
    rfl rfl (by simp [rvElems]) List.length_replicate rfl rfl rfl (fun _ h => nomatch h)

/-- The witness's round of "LIN zeta" passes the format's test. -/
theorem fits_zeta (P : P14) (hS : P.S.sharedSplitNeeded = true) :
    roundsFit [{ entry := entryAt P 2 }] [zetaW P] = true := by
  obtain ⟨_, _, ⟨w, e⟩, _⟩ := entry_names P hS
  rw [e]
  exact fits_entry _ _ .elems (by show Fmt.kindOf "LIN zeta" = some .elems; decide) (by decide) rfl
    rfl rfl (by simp [rvElems]) List.length_replicate rfl rfl rfl (fun _ h => nomatch h)

/-- The witness's round of "SPLIT" passes the format's test, whatever scalar it shows. -/
theorem fits_split (P : P14) (hS : P.S.sharedSplitNeeded = true) (x : Fmt.Ext) :
    roundsFit [{ entry := entryAt P 3 }] [rvVals [.e x]] = true := by
  obtain ⟨_, _, _, ⟨w, e⟩⟩ := entry_names P hS
  rw [e]
  exact fits_entry _ _ .nothing (by show Fmt.kindOf "SPLIT" = some .nothing; decide) (by decide) rfl
    rfl rfl (by simp [rvVals, itemOf]) rfl rfl rfl rfl (fun _ h => nomatch h)

/-- The witness's round of "LOC" passes the format's test. -/
theorem fits_loc (P : P14) (hS : P.S.sharedSplitNeeded = true) :
    roundsFit [{ entry := entryAt P 1, stored := [readsAtLoc P.S.fold P.item] }]
      [rvPoss P.S.fold.columns] = true := by
  obtain ⟨_, ⟨w, e⟩, _⟩ := entry_names P hS
  rw [e]
  refine fits_entry _ _ .positions (by show Fmt.kindOf "LOC" = some .positions; decide) (by decide)
    rfl rfl rfl (by simp [rvPoss]) rfl List.length_replicate rfl rfl fun x hx => ?_
  rw [List.eq_of_mem_replicate hx]
  exact Nat.two_pow_pos _

/-- The witness's one column, as a view holds it. -/
def colW (P : P14) : List OpenedColumn := [(Fmt.storedKey P.item, 0, List.replicate P.S.fold.index.rows 0)]

/-- The witness's column is what "LOC" reads. -/
theorem cols_met (P : P14) (ft : Nat) (hc : 1 ≤ P.S.fold.columns) :
    (colW P).map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf ft [{ entry := entryAt P 1, stored := [readsAtLoc P.S.fold P.item] }]
        [(rvPoss P.S.fold.columns).drawn]).flatMap id := by
  rw [loc_groups P ft _ List.length_replicate]
  have e : (rvPoss P.S.fold.columns).drawn.poss.map (· % 2 ^ P.S.fold.index.code.logN) =
      List.replicate P.S.fold.columns 0 := by
    show (List.replicate P.S.fold.columns 0).map (· % 2 ^ P.S.fold.index.code.logN) = _
    rw [List.map_replicate, Nat.zero_mod]
  rw [e, VerifiableInference.Desc.Key.listOf_zeros _
    (fun h => by have := congrArg List.length h; simp at this; omega)
    (fun x hx => List.eq_of_mem_replicate hx)]
  simp [colW]

/-- **An honest run at the witness's key, challenges and column, in terms of the format's step**:
the eight steps and the fold return .ok; the OOD answers shown at the two sendings are the honest
ones at the states reached; the scalar shown is the honest one; and all that the statement claims
behind the eighth holds of the honest words. H: what the prover holds; rest, cs': the rounds and the
columns that lie behind the eight's. -/
def HonestStepsW (P : P14) (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (H : Inputs) (rest : List Fmt.RoundView) (cs' : List OpenedColumn) (ft : Nat) : Prop :=
  ∃ (R2b R5b R8 : Fmt.RoundView) (d1 d2 d3 d4 d5 d6 d7 d8 : St),
    b1.step ft (firstW P) [pointW P] (colW P ++ cs') = .ok (d1, 0) ∧
    b2.step ft d1 [seedsW (parU P sentU), R2b] (colW P ++ cs') = .ok (d2, 0) ∧
    b3.step ft d2 [] (colW P ++ cs') = .ok (d3, 0) ∧
    b4.step ft d3 [rvPoss P.par.S.fold.columns] (colW P ++ cs') = .ok (d4, (colW P).length) ∧
    b5.step ft d4 [seedsW (parO P), R5b] cs' = .ok (d5, 0) ∧ b6.step ft d5 [] cs' = .ok (d6, 0) ∧
    b7.step ft d6 [zetaW P] cs' = .ok (d7, 0) ∧ b8.step ft d7 [R8] cs' = .ok (d8, 0) ∧
    foldBlocks ft [b1, b2, b3, b4, b5, b6, b7, b8] (firstW P)
      ([pointW P, seedsW (parU P sentU), R2b, rvPoss P.par.S.fold.columns, seedsW (parO P), R5b,
        zetaW P, R8] ++ rest) (colW P ++ cs') = .ok (d8, rest, cs') ∧
    R2b.vals = answersAt (parU P sentU) d1.st (seedsW (parU P sentU)) H.w₀
      (rowsU P (firstW P) (pointW P) H) ∧
    R5b.vals = answersAt (parO P) d4.st (seedsW (parO P))
      (words1 P sentU (firstW P) (pointW P) H) (rowsO P (firstW P) (pointW P) H) ∧
    R8.vals = [.e (Slice.ofE (muRun P (firstW P) (pointW P) (zetaW P) H))] ∧
    Means.AllMet rdE d8.st (words2 P sentU (firstW P) (pointW P) H)

/-- **There is an honest run in terms of the format's step**, at rows that are 0, whatever words lie
in front and whatever the random values of the four messages are. -/
theorem steps_met (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (w₀ : Words Cb.Gl.E)
    (cU cMask cOmega cSp : MsgCoins) (rest : List Fmt.RoundView) (cs' : List OpenedColumn) (ft : Nat) :
    HonestStepsW P sentU b1 b2 b3 b4 b5 b6 b7 b8 (inputs0 w₀ cU cMask cOmega cSp) rest cs' ft := by
  obtain ⟨_, e2, _, e4, e5, _, _, _⟩ := blocks_rounds P sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hP.goes
  obtain ⟨e1, e7, e8⟩ := own_rounds P b1 b2 b3 b4 b5 b6 b7 b8 hb hP.two
  obtain ⟨_, hf, _⟩ := (VerifiableInference.Desc.Own.linFits_iff P.codes P.par.S).1 hP.lin
  have hcol : 1 ≤ P.S.fold.columns := hf.1.2.2.2.2.2
  have f1 : roundsFit b1.rounds [pointW P] = true := by
    rw [e1]; exact fits_point P hP.two
  have f4 : roundsFit b4.rounds [rvPoss P.par.S.fold.columns] = true := by
    rw [e4]; exact fits_loc P hP.two
  have f7 : roundsFit b7.rounds [zetaW P] = true := by
    rw [e7]; exact fits_zeta P hP.two
  have f8 : ∀ x, roundsFit b8.rounds [rvVals [.e x]] = true := fun x => by
    rw [e8]; exact fits_split P hP.two x
  have f2 : ∀ v, v.map itemOf = List.replicate (parU P sentU).answers .answer →
      roundsFit b2.rounds [seedsW (parU P sentU), rvVals v] = true := fun v hv => by
    rw [e2]; exact fits_send _ v hv
  have f5 : ∀ v, v.map itemOf = List.replicate (parO P).answers .answer →
      roundsFit b5.rounds [seedsW (parO P), rvVals v] = true := fun v hv => by
    rw [e5]; exact fits_send _ v hv
  have hcs : (colW P).map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf ft b4.rounds [(rvPoss P.par.S.fold.columns).drawn]).flatMap id := by
    rw [e4]; exact cols_met P ft hcol
  -- the state in front of the first sending
  obtain ⟨c1, _, _, _, _, _, _, _, sc1, _⟩ :=
    eight_steps_hold P sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb (keyW P.par.S.fold.index)
      (key_fits _) (key_beta _) _ _ _ _ _ _ _ _ (colW P) cs' rest ft f1 (f2 _ (items_zero _)) f4
      (f5 _ (items_zero _)) f7 (f8 (0, 0, 0)) hcs (inputs0 w₀ cU cMask cOmega cSp)
  -- a run with the first sending's honest answers
  have i2 := items_answersAt (parU P sentU) c1.st (seedsW (parU P sentU)) w₀
    (rowsU P (firstW P) (pointW P) (inputs0 w₀ cU cMask cOmega cSp))
  obtain ⟨a1, a2, a3, a4, _, _, _, _, sa1, sa2, sa3, sa4, _⟩ :=
    eight_steps_hold P sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb (keyW P.par.S.fold.index)
      (key_fits _) (key_beta _) _ _ _ _ _ _ _ _ (colW P) cs' rest ft f1 (f2 _ i2) f4
      (f5 _ (items_zero _)) f7 (f8 (0, 0, 0)) hcs (inputs0 w₀ cU cMask cOmega cSp)
  obtain rfl : c1 = a1 := congrArg Prod.fst (Except.ok.inj (sc1.symm.trans sa1))
  -- the honest run
  have i5 := items_answersAt (parO P) a4.st (seedsW (parO P))
    (words1 P sentU (firstW P) (pointW P) (inputs0 w₀ cU cMask cOmega cSp))
    (rowsO P (firstW P) (pointW P) (inputs0 w₀ cU cMask cOmega cSp))
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, s1, s2, s3, s4, s5, s6, s7, s8, hfold, hall⟩ :=
    eight_steps_hold P sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb (keyW P.par.S.fold.index)
      (key_fits _) (key_beta _) _ _ _ _ _ _ _ _ (colW P) cs' rest ft f1 (f2 _ i2) f4 (f5 _ i5) f7
      (f8 (Slice.ofE (muRun P (firstW P) (pointW P) (zetaW P) (inputs0 w₀ cU cMask cOmega cSp))))
      hcs (inputs0 w₀ cU cMask cOmega cSp)
  obtain rfl : d1 = c1 := congrArg Prod.fst (Except.ok.inj (s1.symm.trans sa1))
  obtain rfl : d2 = a2 := congrArg Prod.fst (Except.ok.inj (s2.symm.trans sa2))
  obtain rfl : d3 = a3 := congrArg Prod.fst (Except.ok.inj (s3.symm.trans sa3))
  obtain rfl : d4 = a4 := congrArg Prod.fst (Except.ok.inj (s4.symm.trans sa4))
  exact ⟨_, _, _, d1, d2, d3, d4, d5, d6, d7, d8, s1, s2, s3, s4, s5, s6, s7, s8, hfold, rfl, rfl,
    rfl, hall (rec_zero P.par.S.fold.index) (col_zero P.par _) rfl rfl rfl⟩

/-- The IOP as written in Lean makes its eight sub-protocols where K14Cond holds. -/
theorem eight_of_cond {f : Nat} {P : P14} {W : Rounds} (hC : Law.K14Cond f P W) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨bs, hb, hl, _⟩ := hC.blocks
  match bs, hl with
  | [b1, b2, b3, b4, b5, b6, b7, b8], _ => exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩

/-- **At the typed sizes of a key of full size.** -/
theorem steps_key : ∃ sentU : Array OracleNotice, withU keyFull.once.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] → ∃ b1 b2 b3 b4 b5 b6 b7 b8,
      blocks ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ =
        some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
      ∀ (w₀ : Words Cb.Gl.E) (cU cMask cOmega cSp : MsgCoins) (rest : List Fmt.RoundView)
        (cs' : List OpenedColumn) (ft : Nat),
        HonestStepsW ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
          b1 b2 b3 b4 b5 b6 b7 b8 (inputs0 w₀ cU cMask cOmega cSp) rest cs' ft := by
  obtain ⟨sentU, layO, hf⟩ := planFacts_key
  refine ⟨sentU, (hf 0 [(0, 0)] (by simp)).goes, fun item bp hbp => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (Law.k14_key item bp hbp) (hf item bp hbp).goes
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_of_cond (Law.k14_key item bp hbp)
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, fun w₀ cU cMask cOmega cSp rest cs' ft =>
    steps_met _ sentU layO (hf item bp hbp) hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb w₀ cU cMask cOmega
      cSp rest cs' ft⟩

/-- **At the typed sizes over a proof file's own codes.** -/
theorem steps_real : ∃ (x : LinSized) (sentU : Array OracleNotice),
    realSized = some (x, codesFull2) ∧ withU x.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] → ∃ b1 b2 b3 b4 b5 b6 b7 b8,
      blocks ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ =
        some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
      ∀ (w₀ : Words Cb.Gl.E) (cU cMask cOmega cSp : MsgCoins) (rest : List Fmt.RoundView)
        (cs' : List OpenedColumn) (ft : Nat),
        HonestStepsW ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ sentU
          b1 b2 b3 b4 b5 b6 b7 b8 (inputs0 w₀ cU cMask cOmega cSp) rest cs' ft := by
  obtain ⟨x, sentU, layO, a1, _, hf⟩ := planFacts_real
  obtain ⟨x', b1', _, hC⟩ := Law.k14_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (a1.symm.trans b1'))
  refine ⟨x, sentU, a1, (hf 0 [(0, 0)] (by simp)).goes, fun item bp hbp => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (hC item bp hbp) (hf item bp hbp).goes
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_of_cond (hC item bp hbp)
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, fun w₀ cU cMask cOmega cSp rest cs' ft =>
    steps_met _ sentU layO (hf item bp hbp) hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb w₀ cU cMask cOmega
      cSp rest cs' ft⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.fits_entry
#print axioms Desc.K14.Honest.entry_names
#print axioms Desc.K14.Honest.own_rounds
#print axioms Desc.K14.Honest.fits_point
#print axioms Desc.K14.Honest.fits_zeta
#print axioms Desc.K14.Honest.fits_split
#print axioms Desc.K14.Honest.fits_loc
#print axioms Desc.K14.Honest.cols_met
#print axioms Desc.K14.Honest.steps_met
#print axioms Desc.K14.Honest.eight_of_cond
#print axioms Desc.K14.Honest.steps_key
#print axioms Desc.K14.Honest.steps_real
