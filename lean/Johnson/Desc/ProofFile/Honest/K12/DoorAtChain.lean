-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorAtChain.lean

What it proves. The state that doorUF gives with the reader colsLoc (DoorReturns.lean), set against
a verifier's own text: the library's shared chain chainOf (Johnson/Desc/K14/Blocks.lean). Wherever
the fold over that chain's flat list returns, from the seat's start at an instance whose key is the
one that the prover's shared parts are given, at a view whose first rounds are those that the part
has seen and whose first columns are the reader's, it has passed through a state behind the eight of
which the seat's way in makes doorUF's state.

The same at every list of blocks that begins with that chain's front block and the eight, at
whatever type of claims (doorUF_at_flat), and so at the list that the proof file's description folds
over: the chain carried to the description's own type of claims (doorUF_at_carried).

Names.
  flat_chain   the flat list of chainOf, written out: each block with its test on the plan turned.
  doorUF_at_chain   at chainOf's own flat list.
  eight_of_flat   a fold over a list that begins with the front block and the eight, cut behind
      these nine.
  doorUF_at_flat, doorUF_at_carried   at every such list; at the description's.

By what. doorUF_at_ties (DoorReturns.lean); foldBlocks_planOk (Johnson/Desc/K15/K15Run.lean);
peel_front, fold_like (Johnson/Desc/K14/Honest/FlatSteps.lean); FlatOf, flatOf_carried
(FlatForm.lean, there); foldBlocks_append_ok (Johnson/Desc/RunLaws.lean).

Limits.
- One front and one view. The three ties hk, hr, hc are premises: nobody shows them at a run of the
  frame here.
- It is conditional on the fold's return (hv): nothing is said of a view at which a later block
  refuses.
- c, Q, tests, last and the type of claims are free in doorUF_at_carried: that they are the proof
  file's own under the head is not drawn here.
- The premises hW, hkey, hbeta read the input.
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorReturns
import Johnson.Desc.K14.Honest.FlatSteps
import Johnson.Desc.K15.K15Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey TreeLay)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks roundsFit foldBlocks_append_ok
  foldBlocks_planOk)
open VerifiableInference.Desc.K12 (Seat.enter)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14 (P14 St blocks blocksOr first readsAtLoc chainOf frontBlock)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (PlanFacts peel_front fold_like FlatOf flatOf_carried)

variable {W X : Type}

/-- The flat list of the library's shared chain: the front block, the eight, the tests and the
chain's end, each with its test on the plan turned and nothing else. -/
theorem flat_chain (c : OnBytes.Model.Verify.Chains) (Q : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) :
    (chainOf c Q tests last).blocksInOrder =
      (frontBlock c :: ((blocksOr Q ++ tests) ++ [last (blocksOr Q ++ tests)])).map fun b =>
        { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := by
  unfold chainOf VerifiableInference.Desc.Chain.blocksInOrder
  simp only [List.map_nil, List.flatMap_nil, List.append_nil, List.map_cons, List.map_append,
    List.cons_append, List.nil_append]

/-- **At the library's own shared chain.** chainOf c Q tests last (Johnson/Desc/K14/Blocks.lean) is
the chain that the proof file's description lays, carried to its own type of claims
(sharedSeatOf, Johnson/Desc/ProofFile/Lot/K14Seat.lean), and first Q.codes k is that seat's start at
an instance whose key is k. Wherever the verifier's fold over that chain's flat list returns, at the
view v, it has passed through a state d8 behind the eight of which the seat's way in makes doorUF's
state; and from there it is the fold over the blocks behind the eight.
The ties: hk: (α) the key that the prover's shared parts are given is the instance's. hr: (β) what
the part has seen are the view's first rounds. hc: (γ) the reader's columns are the view's first
columns. The other premises are doorUF_returns' own.
It speaks of one front and one view. It does not say that the fold returns. No SaysAt follows. -/
theorem doorUF_at_chain (c : OnBytes.Model.Verify.Chains) (Q : P14) (sentU : Array OracleNotice)
    (layO : TreeLay)
    (hP : PlanFacts Q.par Q.codes sentU layO) (hBU : planOkOwn (parU Q sentU) = true)
    (hBO : planOkOwn (parO Q) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : W → TableKey)
    (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView)
    (hfr : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hW : ∀ x < 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a,
      ((stored w Q.item x).getD []).length = Q.S.fold.index.rows)
    (hkey : keyFits (key w) Q.par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true)
    (k : TableKey) (v : Fmt.View) (hk : key w = k)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hc : ∃ more, v.opened = colsLoc Q (stored w) fr.seen.rounds ++ more)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 (chainOf c Q tests last).blocksInOrder (first Q.codes k) v.rounds v.opened =
      .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) v.rounds v.opened =
        .ok (d8, rest, more) ∧
      foldBlocks 0 (tests ++ [last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests)]) d8 rest more =
        .ok out ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) := by
  obtain ⟨d8, rest, more, hF, hE⟩ := doorUF_at_ties Q sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7
    b8 hb key stored w fr R1 R2a R2b R4 R5a R5b R7 R8 hfr f1 f2 f4 f5 f7 f8 hW hkey hbeta
    (first Q.codes k) v ⟨by rw [hk], hr, hc⟩
  have eB : blocksOr Q = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hb]
    rfl
  rw [flat_chain, foldBlocks_planOk, eB] at hv
  have h1 := peel_front c 0 _ _ _ _ _ hv
  rw [List.append_assoc] at h1
  obtain ⟨s', rs', cols', g1, g2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h1
  have e : (s', rs', cols') = (d8, rest, more) := Except.ok.inj (g1.symm.trans hF)
  obtain rfl : s' = d8 := (Prod.mk.inj e).1
  obtain rfl : rs' = rest := (Prod.mk.inj (Prod.mk.inj e).2).1
  obtain rfl : cols' = more := (Prod.mk.inj (Prod.mk.inj e).2).2
  exact ⟨s', rs', cols', hF, g2, hE⟩

/-- A fold that returns over a list which begins with the front block and the eight has returned
over the eight, from the same state at the same rounds and columns, and goes on from there over what
lies behind the nine. -/
theorem eight_of_flat {Cl : Type} (c : OnBytes.Model.Verify.Chains)
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (xs : List (Block St Cl))
    (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : St × List Fmt.RoundView × List OpenedColumn) (hv : foldBlocks 0 xs s rs cols = .ok out) :
    ∃ s' rs' cols', foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] s rs cols =
        .ok (s', rs', cols') ∧ foldBlocks 0 (xs.drop 9) s' rs' cols' = .ok out := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have hv' : foldBlocks 0 ([x0, x1, x2, x3, x4, x5, x6, x7, x8] ++ tl) s rs cols = .ok out := hv
  obtain ⟨s', rs', cols', g1, g2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 hv'
  have g1' := fold_like 0 _ [frontBlock c, b1, b2, b3, b4, b5, b6, b7, b8]
    (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 .nil))))))))) _ _ _ _ g1
  exact ⟨s', rs', cols', peel_front c 0 _ _ _ _ _ g1', g2⟩

/-- **At every list of blocks that begins with the shared chain's front block and the eight**
(FlatOf, Johnson/Desc/K14/Honest/FlatForm.lean), at whatever type of claims. Wherever a fold over
such a list returns from first Q.codes k at the view v, it has passed through a state d8 behind the
eight of which the seat's way in makes doorUF's state, and from there it is the fold over what lies
behind the ninth member. The ties hk, hr, hc and the other premises: as in doorUF_at_chain. -/
theorem doorUF_at_flat {Cl : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts Q.par Q.codes sentU layO) (hBU : planOkOwn (parU Q sentU) = true)
    (hBO : planOkOwn (parO Q) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : W → TableKey)
    (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView)
    (hfr : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hW : ∀ x < 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a,
      ((stored w Q.item x).getD []).length = Q.S.fold.index.rows)
    (hkey : keyFits (key w) Q.par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true)
    (k : TableKey) (v : Fmt.View) (hk : key w = k)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hc : ∃ more, v.opened = colsLoc Q (stored w) fr.seen.rounds ++ more)
    (xs : List (Block St Cl)) (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 xs (first Q.codes k) v.rounds v.opened = .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) v.rounds v.opened =
        .ok (d8, rest, more) ∧
      foldBlocks 0 (xs.drop 9) d8 rest more = .ok out ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) := by
  obtain ⟨d8, rest, more, hF, hE⟩ := doorUF_at_ties Q sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7
    b8 hb key stored w fr R1 R2a R2b R4 R5a R5b R7 R8 hfr f1 f2 f4 f5 f7 f8 hW hkey hbeta
    (first Q.codes k) v ⟨by rw [hk], hr, hc⟩
  obtain ⟨s', rs', cols', g1, g2⟩ := eight_of_flat c xs F _ _ _ out hv
  have e : (s', rs', cols') = (d8, rest, more) := Except.ok.inj (g1.symm.trans hF)
  obtain rfl : s' = d8 := (Prod.mk.inj e).1
  obtain rfl : rs' = rest := (Prod.mk.inj (Prod.mk.inj e).2).1
  obtain rfl : cols' = more := (Prod.mk.inj (Prod.mk.inj e).2).2
  exact ⟨s', rs', cols', hF, g2, hE⟩

/-- **At the list that the proof file's description folds over**: the library's shared chain carried
to the description's own type of claims: ((chainOf c Q tests last).retype).blocksInOrder (fileDescBy_shared,
Johnson/Desc/ProofFile/Law/OrderStated.lean; flatOf_carried, FlatForm.lean): doorUF_at_flat
there. -/
theorem doorUF_at_carried {Cl : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts Q.par Q.codes sentU layO) (hBU : planOkOwn (parU Q sentU) = true)
    (hBO : planOkOwn (parO Q) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : W → TableKey)
    (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView)
    (hfr : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hW : ∀ x < 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a,
      ((stored w Q.item x).getD []).length = Q.S.fold.index.rows)
    (hkey : keyFits (key w) Q.par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true)
    (k : TableKey) (v : Fmt.View) (hk : key w = k)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hc : ∃ more, v.opened = colsLoc Q (stored w) fr.seen.rounds ++ more)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 ((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder (first Q.codes k) v.rounds
      v.opened = .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) v.rounds v.opened =
        .ok (d8, rest, more) ∧
      foldBlocks 0 (((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder.drop 9) d8 rest more =
        .ok out ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) :=
  doorUF_at_flat c Q sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb key stored w fr R1 R2a R2b R4
    R5a R5b R7 R8 hfr f1 f2 f4 f5 f7 f8 hW hkey hbeta k v hk hr hc _
    (flatOf_carried c Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hb) out hv

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.flat_chain
#print axioms ProofFile.Honest.K12.Light.doorUF_at_chain
#print axioms ProofFile.Honest.K12.Light.eight_of_flat
#print axioms ProofFile.Honest.K12.Light.doorUF_at_flat
#print axioms ProofFile.Honest.K12.Light.doorUF_at_carried
