-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SealAtHead.lean: the last member of the proof file's own first chain (the
chain's end, with the sealing round) at its seat: one step on the chain's shape, with both laws at
the seated block's own decision. Under the head `P5J.AtMgA`; nothing is evaluated.

The member's text. `ChainEnd.chainEnd 1 5 true … First.endAsks` (Johnson/Desc/ChainEnd.lean,
Johnson/Desc/K13/FirstEnd.lean): it reads no round and no column, asks five named clauses of the
state, and hands the state on as it is: no count of claims is owed; the own group is the last group;
W is in the own group and in no other; a proximity test has begun on every group but the own one;
every sampled message but the own group's members is in a tested group.

Main names.
* `endOf a`: the own group's number and W's number, off the shape: there where the chain stands at
  the memory, something is laid for the last chain, and W's number is laid.
* `sealB a`: the five clauses as one test with code on the shape. `sealB_sh`: at a state's shape it
  is the text's own five clauses.
* `sealG`, `sealGS`: the step: (at the seat: no mark, then) the test; the shape stays.
* `seal_at`: the member b at number 357 of cF.blocksInOrder declares the one sealing round; a yes of b, on
  whatever rounds and columns, leaves the state as it is, and `sealGS` returns its shape; and where
  `sealGS` returns at a state's shape, b says yes on whatever rounds and columns. The step has no
  parameter.

How. `IM.seal_seated` (Johnson/IMR/SealSeat.lean: the chain's last block is that text, alone),
`IM.back_numbers` (Johnson/IMR/BackSeat.lean: its number), `IM.yes_alone`
(Johnson/IMR/SeatForm.lean), `ChainEnd.refuse_ok_iff` (Johnson/Desc/ChainEndLaw.lean).

Limits. The decision alone: the frame's tests on the round's form are not here. OF THE HEAD THE
PROOF SPENDS THREE FIELDS ALONE (scope, reads, laid.opened): the others are idle here, and the
letters Z, D, r, Np and x stand in no conclusion. No state is shown at which `sealGS` returns. At
the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.K13.FirstEnd
import Johnson.Desc.ChainEndLaw
import Johnson.IMR.SealSeat
import Johnson.IMR.BackSeat
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 The five clauses on the shape -/

/-- The own group's number and W's number, off the shape. Nothing in three cases: the chain does not
stand at the memory; nothing is laid for the last chain; W's number is not laid. -/
def endOf (a : ChainSh) : Option (Nat × Nat) :=
  a.atEnd.bind fun e => e.2.2.bind fun l => if l.w != noId then some (l.own, l.w) else none

/-- At a state's shape it is what the state's own reader gives. -/
theorem endOf_sh (s : S) : endOf (chainSh s) = s.firstEnd?.map fun e => (e.lin.own, e.lin.w) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | mem a =>
    show (a.lin.map VerifiableInference.Desc.K13.Honest.laidSh).bind _ = (a.lin.bind _).map _
    cases a.lin with
    | none => rfl
    | some l =>
      show (if l.w != noId then some (l.own, l.w) else none) =
        (if l.w != noId then some _ else none).map _
      split <;> rfl
  | _ => rfl

/-- **The five clauses, as one test on the shape.** -/
def sealB (a : ChainSh) : Bool :=
  (match a.rowsOwed with
    | none => true
    | some n => n == 0) &&
  ((endOf a).any fun e => e.1 + 1 == a.core.st.groups.length) &&
  ((endOf a).any fun e => (a.core.st.oracles[e.2]?).any fun x => x.groups == [e.1]) &&
  ((List.range a.core.st.groups.length).all fun g =>
    (endOf a).map (·.1) == some g || (a.core.st.groups[g]?).any (·.inRun)) &&
  ((List.range a.core.st.oracles.length).all fun o =>
    (a.core.st.oracles[o]?).all fun x =>
      !x.sampled ||
        ((endOf a).any fun e => (a.core.st.groups[e.1]?).any (·.members.contains o)) ||
        x.groups.any fun g => (a.core.st.groups[g]?).any (·.inRun))

/-- At a state's shape the test is the text's own five clauses. -/
theorem sealB_sh (s : S) :
    sealB (chainSh s) = (VerifiableInference.Desc.First.endAsks s).all (·.2) := by
  have hg : ∀ g, (chainSh s).core.st.groups[g]? =
      (s.st.groups[g]?).map VerifiableInference.Desc.Ground.Sh.grpSh :=
    VerifiableInference.Desc.Ground.Sh.grp_get s.st
  have ho : ∀ o, (chainSh s).core.st.oracles[o]? =
      (s.st.oracles[o]?).map VerifiableInference.Desc.Ground.Sh.orcSh :=
    VerifiableInference.Desc.Ground.Sh.orc_get s.st
  have lg : (chainSh s).core.st.groups.length = s.st.groups.size := by
    show (s.st.groups.toList.map _).length = _
    simp
  have lo : (chainSh s).core.st.oracles.length = s.st.oracles.size := by
    show (s.st.oracles.toList.map _).length = _
    simp
  have hr : (chainSh s).rowsOwed = s.rowsOwed := rfl
  unfold sealB
  simp only [endOf_sh, hg, ho, lg, lo, hr]
  simp only [VerifiableInference.Desc.First.endAsks,
    VerifiableInference.Desc.First.untestedButOwnL, List.all_cons, List.all_nil, Bool.and_true,
    S.closeOk, S.noneWaits, Option.any_map, Option.all_map, Option.map_map, Function.comp_def,
    VerifiableInference.Desc.Ground.Sh.grpSh, VerifiableInference.Desc.Ground.Sh.orcSh,
    Array.contains_toList, Bool.and_assoc]
  generalize s.rowsOwed = q
  cases q <;> rfl

/-- **The step on the shape.** -/
def sealG (a : ChainSh) : Except String ChainSh :=
  if sealB a then .ok a else .error "the chain's end: the shape does not pass"

/-- **The step at the seat.** -/
def sealGS (a : ChainSh) : Except String ChainSh :=
  if a.marked then .error "the chain's end: the state bears a mark" else sealG a

/-! ## 2 At the seat -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The text's refusal, by the test on the shape. -/
theorem refuse_iff (s : S) :
    VerifiableInference.Desc.ChainEnd.refuse (VerifiableInference.Desc.First.endAsks s) = .ok () ↔
      sealB (chainSh s) = true := by
  rw [VerifiableInference.Desc.ChainEnd.refuse_ok_iff, sealB_sh, List.all_eq_true]

/-- **The seal at its seat (member 357)**: the one sealing round is declared; a yes leaves the state
and gives the step's return at its shape; the step's return gives a yes, on whatever rounds and
columns. -/
theorem seal_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[357]? = some b ∧
      b.rounds = [VerifiableInference.Desc.ChainEnd.sealRound] ∧
      (∀ s rs gs t, b.decide s rs gs = .ok t → t = s ∧ sealGS (chainSh s) = .ok (chainSh t)) ∧
      ∀ s rs gs u, sealGS (chainSh s) = .ok u → b.decide s rs gs = .ok s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', -, rfl, la⟩ := IM.seal_seated O
  have hy := IM.yes_alone la (by intro k; cases k)
  have q := (IM.back_numbers h.scope h.reads O).2
  refine ⟨_, q, IM.alone_rounds la, fun s rs gs t hd => ?_, fun s rs gs u hg => ?_⟩
  · obtain ⟨h1, hf, -⟩ := (hy s t rs gs).1 hd
    have h2 : (VerifiableInference.Desc.ChainEnd.refuse
        (VerifiableInference.Desc.First.endAsks s)).map (fun _ => s) = .ok t := h1
    cases hr : VerifiableInference.Desc.ChainEnd.refuse
        (VerifiableInference.Desc.First.endAsks s) with
    | error e =>
      rw [hr] at h2
      cases h2
    | ok u =>
      rw [hr] at h2
      obtain rfl : s = t := Except.ok.inj h2
      refine ⟨rfl, ?_⟩
      have hm : (chainSh s).marked = false := by
        show s.failed.isSome = false
        rw [hf]
        rfl
      unfold sealGS sealG
      rw [hm, (refuse_iff s).1 hr]
      rfl
  · unfold sealGS at hg
    split at hg
    · cases hg
    · rename_i hm
      unfold sealG at hg
      split at hg
      · rename_i hB
        have hf : s.failed = none := by
          have h1 : (chainSh s).marked = false := by simpa using hm
          have h2 : s.failed.isSome = false := h1
          simpa using h2
        refine (hy s s rs gs).2 ⟨?_, hf, ?_⟩
        · show (VerifiableInference.Desc.ChainEnd.refuse
            (VerifiableInference.Desc.First.endAsks s)).map (fun _ => s) = .ok s
          rw [(refuse_iff s).2 hB]
          rfl
        · unfold ProofFile.sameReply
          exact beq_self_eq_true _
      · cases hg

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.endOf_sh
#print axioms Johnson.AtFull.Shape.sealB_sh
#print axioms Johnson.AtFull.Shape.refuse_iff
#print axioms Johnson.AtFull.Shape.seal_at
#print axioms Johnson.AtFull.Shape.endOf
#print axioms Johnson.AtFull.Shape.sealB
#print axioms Johnson.AtFull.Shape.sealG
#print axioms Johnson.AtFull.Shape.sealGS
