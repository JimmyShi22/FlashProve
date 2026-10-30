-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorReturnsAt.lean

What it proves. The public premises of doorUF_returns (DoorReturns.lean) hold under the head
P5J.AtMg at the proof file's shared chain: PlanFacts, and the two sendings' tests on the plan. So
under the head doorUF with the reader colsLoc is off its fall-back at every front of the declared
form, under the three premises that read the input (doorUF_returns_head). At the small made-up chain
P3 (SharedSmall.lean) guards evaluate the same at the honest values of PubAtSmallDoor.lean.

Names.
  own_of_planOk   where each of the eight blocks passes its test on the plan, the two sendings pass
      their kind's. A second text of the proof of planOwn_of
      (Johnson/Desc/K14/Honest/ChainWitness.lean), which takes the same from a wider premise
      (K14Cond).
  planFacts_head, own_head   the public premises under the head.
  doorUF_returns_head   the theorem.
  storedSmall, the guards   at P3: colsLoc at the honest table's columns gives PubAtSmallDoor.lean's
      columns; the fold returns; doorUF's state is not the fall-back; with a table of another width
      the fold fails and the state is the fall-back.

By what. doorUF_returns (DoorReturns.lean); planFacts_real (Johnson/Desc/K14/Honest/YesAt.lean);
planOk_head_eight (MarksAtHead.lean); eight_of (MarksBehind.lean); facts_at_head (NearAtHead.lean);
written_at_head, qAt_written (FitAtHead.lean).

Limits. Those of DoorReturns.lean: it moves no count; it gives no SaysAt; the three premises that
read the input (hW, hkey, hbeta) and the premises on the rounds seen stay premises, on one front;
the test on G_u alone. The full size alone; no example of the head is shown here. At P3: one list of
challenges; guards, no theorem. It stands over files that are not in the library yet, as
MarksBehind.lean does. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorReturns
import Johnson.Desc.ProofFile.Honest.K12.MarksAtHead
import Johnson.Desc.ProofFile.Honest.K12.DoorsAtSmall
import Johnson.Desc.K14.Honest.YesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey TreeLay)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks roundsFit)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14 (P14 St blocks first readsAtLoc withU)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (PlanFacts planFacts_real)

variable {W X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- Where each of the eight blocks passes its test on the plan, the two sendings pass their kind's
test on the plan. -/
theorem own_of_planOk (P : P14) (sentU : Array OracleNotice) (bs : List (Block St Unit))
    (hb : blocks P = some bs) (hplan : ∀ b ∈ bs, b.planOk = true) (hU : withU P.S = some sentU) :
    planOkOwn (parU P sentU) = true ∧ planOkOwn (parO P) = true := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hb
  obtain ⟨sentU', hU', rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hU.symm.trans hU')
  have p2 := hplan _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have p5 := hplan _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))
  have q2 : ((VerifiableInference.Desc.Block.inside _ _ _).planOk &&
      VerifiableInference.OnPublicFiles.OkD.At.sending P.codes
        (VerifiableInference.OnPublicFiles.OkD.At.withU P.S) && _) = true := p2
  have q5 : ((VerifiableInference.Desc.Block.inside _ _ _).planOk &&
      VerifiableInference.OnPublicFiles.OkD.At.sending P.codes (OnBytes.linMessageOmega P.S) && _) =
        true := p5
  simp only [Bool.and_eq_true] at q2 q5
  have u2 : (planOkOwn (parU P sentU) && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parU P sentU)).claims.isEmpty && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parU P sentU)).after.isEmpty) = true := q2.1.1
  have u5 : (planOkOwn (parO P) && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parO P)).claims.isEmpty && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parO P)).after.isEmpty) = true := q5.1.1
  simp only [Bool.and_eq_true] at u2 u5
  exact ⟨u2.1.1, u5.1.1⟩

/-- **The library's public premises on the shared rounds hold under the head.** -/
theorem planFacts_head (h : P5J.AtMg o Z D r Zp Np cF) : ∃ layO : TreeLay,
    PlanFacts (K1.qAt Zp Np).par (K1.qAt Zp Np).codes (sentOf (K1.qAt Zp Np).S) layO := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  obtain ⟨x', sentU, layO, hx', -, hF⟩ := planFacts_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (hx.symm.trans hx'))
  have k := hF 0 [(0, 0)] (by simp)
  have hw := (facts_at_head h).2.2
  rw [qAt_written Wr Np] at hw ⊢
  have e : sentU = sentOf x.shape := Option.some.inj (k.goes.symm.trans hw)
  exact ⟨layO, e ▸ k⟩

theorem own_head (h : P5J.AtMg o Z D r Zp Np cF) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) :
    planOkOwn (parU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S)) = true ∧
      planOkOwn (parO (K1.qAt Zp Np)) = true :=
  own_of_planOk _ _ bs hb (planOk_head_eight h bs hb) (facts_at_head h).2.2

/-- **Under the head, at the test on G_u, the fold in front returns and doorUF is off its
fall-back**, with the reader colsLoc. What stays asked: on the frame: what the part has seen are
eight rounds of the declared form (hfr, f1 … f8); on the input's form: hW, hkey; on values, one:
hbeta. As in doorUF_returns: no SaysAt follows, and that d8 is the state through which the
verifier's fold passes is not said here (DoorTies, DoorReturns.lean). -/
theorem doorUF_returns_head (h : P5J.AtMg o Z D r Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : W → TableKey)
    (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView)
    (hfr : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hW : ∀ x < 2 ^ (readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item).sh.a,
      ((stored w (K1.qAt Zp Np).item x).getD []).length = (K1.qAt Zp Np).S.fold.index.rows)
    (hkey : keyFits (key w) (K1.qAt Zp Np).par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true) :
    ∃ d8 : St,
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes (key w))
        fr.seen.rounds (colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      doorUF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc (K1.qAt Zp Np) (stored w) fr.seen.rounds) w fr =
        { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU, pass := .nothing
          mask := d8.loc.firstMask } := by
  obtain ⟨layO, hP⟩ := planFacts_head h
  obtain ⟨hBU, hBO⟩ := own_head h _ hb
  exact doorUF_returns _ _ layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb key stored w fr
    R1 R2a R2b R4 R5a R5b R7 R8 hfr f1 f2 f4 f5 f7 f8 hW hkey hbeta

end ProofFile.Honest.K12.Light

namespace ProofFile.Honest.K12.Light.SharedSmall
open ProofFile.Honest.K12.Light.SharedHonest (rows keyAt symbolAt)
open ProofFile.Honest.K12.Light.SharedToy (fr door)

/-! ## At P3 -/

/-- The honest table's columns at P3, as a function of item and position: the four rows' symbols. -/
def storedSmall (n : ℕ) (_ x : ℕ) : Option (List UInt64) :=
  some ((List.range n).map fun r => symbolAt (rows 0) r x)

-- the reader gives the columns that PubAtSmallDoor.lean lays by hand
#guard colsLoc P3 (storedSmall 4) fr.seen.rounds == colsU
-- with them the fold returns, and doorUF's state is not the fall-back: it has other right sides
#guard goes bs3 fr.seen.rounds (colsLoc P3 (storedSmall 4) fr.seen.rounds)
#guard targets (doorUF P3 sentU3 bs3 (fun _ : Unit => keyAt (rows 0))
    (fun _ fr => colsLoc P3 (storedSmall 4) fr.seen.rounds) () fr) == targets door
#guard targets (doorUF P3 sentU3 bs3 (fun _ : Unit => keyAt (rows 0))
    (fun _ fr => colsLoc P3 (storedSmall 4) fr.seen.rounds) () fr) != targets (fallU P3 sentU3)
-- with a table of another width the fold fails
#guard !goes bs3 fr.seen.rounds (colsLoc P3 (storedSmall 3) fr.seen.rounds)
#guard targets (doorUF P3 sentU3 bs3 (fun _ : Unit => keyAt (rows 0))
    (fun _ fr => colsLoc P3 (storedSmall 3) fr.seen.rounds) () fr) == targets (fallU P3 sentU3)

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.own_of_planOk
#print axioms ProofFile.Honest.K12.Light.planFacts_head
#print axioms ProofFile.Honest.K12.Light.own_head
#print axioms ProofFile.Honest.K12.Light.doorUF_returns_head
#print axioms ProofFile.Honest.K12.Light.SharedSmall.storedSmall
