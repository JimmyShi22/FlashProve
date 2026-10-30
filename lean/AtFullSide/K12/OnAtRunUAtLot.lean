-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the list of the test on G_u at a run, at a row of the lot's value.
/-
AtFullSide/K12/OnAtRunUAtLot.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together at a real run? NOT KNOWN. G with hP: a term lies at this G's own
type: `theGAtBase` with `theGAtBase_prover` (E2E/TheG.lean; not imported): its
prover at the return's prover is the return's; BUT its two arguments, the threads' parts and the
kinds' rows, have no known value. A value of `ThreadsP`, ready's and runC's return and that the part
is called have no term and no law known to us: where the part is never called the ends hold for
nothing. THE LIST IS NO LONGER A LETTER UNDER EQUATIONS OF THIS HOUSE's OWN: it takes its place,
parts, On and bud from a row of a value: under the head that lot has just one row at the public part
(the job is made: `realU_at_head`).

What is here. The tops of AtFullSide/K12/OnAtRunUPaid.lean and
AtFullSide/K12/OnAtRunUAtWrittenInstance.lean AT A LIST LAID OF A ROW OF THE LOT's VALUE AT G_u:
`lotU` (Johnson/M1/SlotsUW.lean, another house's) at the shared chain's face, whose list of halves
is what `halfU` lays (`lotU_halves`, there) and whose rows pay the body of bud₂ (`rowU_owes`,
Johnson/M1/SlotsSeat.lean). The four equations hpl, hr, hOn, hbud are the form in which `rowU_owes`
takes a list, with hOn besides; `Unlettered.lay` (Honest/Thread/Rows.lean) meets all four by its
text. So On at a run, bud₂ and the tie to the filling's list are said of one row. The eight
sub-protocols are no premise here (`eight_head`). No definition; four statements.

  `simAtU_is_head`   the lot's simulators' job is the head's, whole.
  `isListAtU_of_lot`   such a list is the list of `IsListAtU`, at the job that `halfU` lays.
  `onAtRun_U_at_lot`   `OnAtRun₂` there, from hAns.
  `onAtRun_U_at_lot_at_the_written_instance`   `OnAtRun₂` there, at the matrices and at an instance
      written of a sample, under hrc.

THE PREMISES, SORTED. PUBLIC: h. THE MAKER: hAr. THE RUN: T · hρ · hR · hrun: the rule's own
letters. WHICH OBJECTS: hP · hrow · hpl · hr · hOn · hbud. ON VALUES: hAns in the third statement
(it reads the index, the committer's pads and the key; it names no coin k that the book lends, no
challenge, no stand and no carried block); THE CROSSING: hrc in the fourth: a premise.

Limits. All limits of the four files beneath, the limit on the committer's randomness first
(AtFullSide/K12/OnAtRunUAtCommittersKey.lean's head), and of the two files of the lot:
"Nothing here says that the values meet Good." That `Good` holds at this row is `good_testOnU`'s,
under one premise on the book that is not called here. The rule moves the debt and pays none of it.
Rows stay at the wide filling's types. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.OnAtRunUAtWrittenInstance
import Johnson.M1.SlotsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (E TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.First (S)
open Johnson.G (codesFull2)
open Desc.K14 (St blocks)
open Desc.K14.Honest (OwnAnswers)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.K14 (randNow)
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open LPFD.Full (XF instanceAsPlainRecord)

variable {W₀ : Type}

/-- CONDITIONAL: on the head and the eight. **The lot's simulators' job at G_u is the head's**,
whole: all four fields. -/
theorem simAtU_is_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    simAtU Zp = simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold simAtU
  rw [h.laid.places]
  show (match blocks (K1.qAt Zp Np) with
    | some bs => simHeadU Zp Np bs
    | none => _) = _
  rw [hb]

/-- CONDITIONAL: on the head and the eight. **A list that takes its place, parts, On and bud from a
row of the lot's value at G_u (`lotU` at the shared chain's face) is the list of `IsListAtU`**, at
the job that `halfU` lays. -/
theorem isListAtU_of_lot {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (wt : ProofFile.Pub → W₀ → Weights)
    (enc : ProofFile.Pub → W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F))
    (Gd : ProofFile.Ground) (row : Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hrow : row ∈ (lotU Face.shared wt enc).rows Zp Gd) {Bk : ProverCoinCounts}
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hpl : L.place = row.place) (hr : L.row = row.row) (hOn : L.On = row.On)
    (hbud : L.bud = row.bud) :
    ∃ A, jobRealU (wt Zp) (enc Zp) Zp = some A ∧
      IsListAtU Np L A (simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]) := by
  have eA := jobRealU_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb (wt Zp) (enc Zp)
  have eJ := realU_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb (wt Zp) (enc Zp)
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hrow
  rw [eJ] at hJ
  obtain rfl := List.mem_singleton.1 hJ
  have eS := simAtU_is_head h b1 b2 b3 b4 b5 b6 b7 b8 hb
  refine ⟨_, eA, hpl, ?_, ?_, hbud⟩
  · rw [hr]
    show testPairs _ (simAtU Zp) = _
    rw [eS]
  · rw [hOn]
    show onFreeT Face.shared _ (simAtU Zp) codesFull2 1 _ = _
    rw [eS]
    rfl

/-- CONDITIONAL: see the head. **The clause of the rule at a list laid of a row of the lot's value
at G_u, at the maker's return at the wide filling and that return's own book**, from hAns. The
eight are no premise: under the head they are made. -/
theorem onAtRun_U_at_lot {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (I : WiderIn W₀) (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S' O) =
      .ok Ar)
    {H : Prover W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B W₀ IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {w₀ : W₀} {rc : IndexCommitterCoins}
    {x : ProofFile.Inst} {k : Coins Ar.B} {ρ : Draws}
    {R : Ready W₀ IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) w₀ rc x k ρ = .ok r)
    (Gd : ProofFile.Ground) (row : Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hrow : row ∈ (lotU Face.shared I.weights
      (fun Zq w => Bind.ForProver.encW Zq (I.weights Zq w))).rows Zp Gd)
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey)
    (hpl : L.place = row.place) (hr : L.row = row.row) (hOn : L.On = row.On)
    (hbud : L.bud = row.bud)
    (hAns : ∀ csU csO : Array E, OwnAnswers (K1.qAt Zp Np) x.pub.key
      (heldAt (K1.qAt Zp Np)
        (askOf ⟨K1.qAt Zp Np, 0⟩ (fun c => I.weights Zp c.w₀)
          (fun c => randNow (K1.qAt Zp Np) c.rc)
          (⟨w₀, rc, x.pub.key⟩ : Common W₀ IndexCommitterCoins TableKey)) csU csO)) :
    OnAtRun₂ T ρ r L := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_head h.toAtMg
  obtain ⟨A, hA, hL⟩ := isListAtU_of_lot h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb I.weights
    (fun Zq w => Bind.ForProver.encW Zq (I.weights Zq w)) Gd row hrow L hpl hr hOn hbud
  exact onAtRun_U_at_the_returns_book h b1 b2 b3 b4 b5 b6 b7 b8 hb I S' O hAr hP T hρ hR hrun A hA _
    rfl L hL hAns

/-- CONDITIONAL: see the head. **The same at the matrices and at an instance written of a sample,
under the crossing's one equation** (hrc). Beside it no clause on values is left. -/
theorem onAtRun_U_at_lot_at_the_written_instance {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀)
    (S' : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {Ar : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hAr : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S' O) = .ok Ar)
    {H : Prover FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit}
    (hP : G.prover H = Ar.H) {M : FullSizeMatrix} {rc : IndexCommitterCoins}
    (online : (protocolAtFiles Z).EncodingRandomness) (seed : (protocolAtFiles Z).OutOfDomainSeed) (request : XF)
    (hrc : rc = ProofFile.Honest.randOf (S := frS) (cut := 402653181) online)
    {k : Coins Ar.B} {ρ : Draws}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (T : ThreadsP (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k R)
    (hρ : ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k = .ok R)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Ar.B (G.prover H) M rc
      (instanceAsPlainRecord (request, (protocolAtFiles Z).recOf M online seed)) k ρ = .ok r)
    (Gd : ProofFile.Ground) (row : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hrow : row ∈ (lotU Face.shared matrixInput.weights
      (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows Zp Gd)
    (L : Lettered Ar.B St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hpl : L.place = row.place) (hr : L.row = row.row) (hOn : L.On = row.On)
    (hbud : L.bud = row.bud) :
    OnAtRun₂ T ρ r L := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ := eight_head h.toAtMg
  obtain ⟨A, hA, hL⟩ := isListAtU_of_lot h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb matrixInput.weights
    (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w)) Gd row hrow L hpl hr hOn hbud
  exact onAtRun_U_at_the_written_instance h b1 b2 b3 b4 b5 b6 b7 b8 hb S' O hAr hP online seed
    request hrc T hρ hR hrun A hA _ rfl L hL

end AtFullSide.K12

#print axioms AtFullSide.K12.simAtU_is_head
#print axioms AtFullSide.K12.isListAtU_of_lot
#print axioms AtFullSide.K12.onAtRun_U_at_lot
#print axioms AtFullSide.K12.onAtRun_U_at_lot_at_the_written_instance
