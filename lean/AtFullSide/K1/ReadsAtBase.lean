-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsAtBase.lean: the family TieReadsS of the item "tie l" at the base prover, at a
segment, from VecTie at that segment and that the record behind the reads names array 0.

  tieReadsS_of_tie   hF2 of exchangeAtS_tie_base at one segment

By what. tieReadsS_vec (K1/Law/TieReadsVecS.lean), vecPlanS_of_tie (AtFullSide/K1/ReadsCore.lean), the
record K1Seated at the reads' member (k1Seated_at_base), the seat of "U3" (reads_public).

Limits.
- VecTie and hix are hypotheses here: each sort pays them in its own file.
- At a Vd of which nothing holds the law is idle: it speaks under ThrS.
- Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K1.ReadsCore
import AtFullSide.K1.ReadsSizes
import AtFullSide.K1.RecordAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes OnBytes.Params
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Seat)
open OnBytes.HonestTrace.U3 (u3Seats)
open OnBytes.HonestTrace.U3.Fit (colsW first_at_head)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

set_option maxRecDepth 100000 in
/-- The reads' pieces are not the opening's. -/
theorem reads_piece : (List.range 25).all (fun l => IM.k1Ix l false + 1 != 1) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE SECOND FAMILY OF THE ITEM "tie l", AT THE BASE PROVER.** -/
theorem tieReadsS_of_tie (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (cells : LocB W₀ → CellsM OnBytes.Flat.numsFull) (tok : LocB W₀ → P5J.At.Tok)
    (Oth : Others A.B (LocB W₀)) (hO : OthersApart A Oth)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25)
    (hix : ∀ blk, (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd
        Rd Kp w).bs[K1.noL l false]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said (K1.noL l false) k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl → u3Of tl = 0)
    (T : ∀ st : OnBytes.HonestTrace.Seat, st ∈ u3Seats A.Z A.G → st.seg = l →
      VecTie (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd
        Kp w) Said (K1.noL l false) (witB I A.Z) A.Z A.G l (nReads (P5J.At.X A.Z) l) st.addr) :
    TieReadsS (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd
        Kp w) Said (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.ms A.Z Z.lay) (witB I A.Z)
      (ProofFile.Honest.K3.matsOwn (P5J.At.X A.Z) l) (K1.noL l false) l (nReads (P5J.At.X A.Z) l) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hG : ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G := by
    rw [eG]
    exact O.blank
  obtain ⟨e1, e2, e3⟩ := first_at_head h hG
  have hW : A.G.W = P5J.At.X A.Z := ProofFile.Law.blankBy_W hG
  have hFirst : A.G.first = A.Z.first := Meaning.K2.blank_first hG
  obtain ⟨-, hlater, -⟩ := k1Seated_at_base h hA cells tok Oth hO test carryX item n₁ n₂ b₀ Vd Rd Kp w
  obtain ⟨blk₁, R₀⟩ := hlater l hl false
  have R : K1Seated (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀
      Vd Rd Kp w) (K1.noL l false) blk₁ (witB I A.Z)
      (laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l false + 1) 1
        (lotNo OnBytes.secondHashFunction A.Z ⟨1, some l, IM.k1Ix l false + 1, .K1⟩) (lotData S A.Z A.G)) ()
      (.reads l) (P5J.At.arr A.Z) (P5J.At.seats A.Z) (P5J.At.ms A.Z Z.lay)
      (K1.radRec (3 * l + 1) (jobLaterAt S A.Z A.G l false).P) := R₀
  obtain ⟨st, n, hs, hseg, hsa, hn, hsh, hans, hdeg, hmom⟩ := reads_public h hG hl (K1.gpOf A.Z)
  obtain ⟨c1, -⟩ := seat_clauses h hG hs
  rw [hseg] at c1
  have hCn : nReads (P5J.At.X A.Z) l ≤ st.array.sizeC := by
    rw [← hW, nReads_at_head h hG hl]
    apply Nat.le_of_eq
    unfold colsW
    rw [← e3, c1]
    rfl
  have H := vecPlanS_of_tie h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd
    Kp w Said hSaid hG hl R hs hseg hsa hn hsh hCn hix (T st hs hseg)
  have hown : ((lettersHead h A.H (scriptAt I S Op A cF cells tok Oth) test carryX item n₁ n₂ b₀ Vd Rd
      Kp w).N.group l).contains (seatAtMember (lettersHead h A.H (scriptAt I S Op A cF cells tok Oth)
      test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs (K1.noL l false)
      (K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l false + 1) 1) n) = true := by
    have hmem := (R.seats _).2 ⟨n, hn, hans, rfl⟩
    exact List.contains_iff_mem.2
      (VerifiableInference.Desc.First.K8.sent_in_group _ l 1 (by simp) _ hmem)
  have hlen : A.G.first.codes.lengthsOk = true := by
    rw [e1]
    exact lengthsOk_full2
  have hpiece := List.all_eq_true.1 reads_piece l (List.mem_range.2 hl)
  have hne : (⟨(K1.parLater A.G.first (K1.gpOf A.Z) l (IM.k1Ix l false + 1) 1).place, 0⟩ : Addr) ≠
      firstAddr := by
    intro e
    have e' := congrArg (fun a : Addr => a.place.piece) e
    have hp : IM.k1Ix l false + 1 = 1 := e'
    simp only [bne_iff_ne, ne_eq] at hpiece
    exact hpiece hp
  have ok : reqLayoutOk A.G.first.codes A.G.first.shape A.G.first.layout = true := by
    rw [hFirst]
    exact Meaning.K2.pub_layoutOk h.laid.pub
  have hsg : l < A.G.first.shape.link.length := by
    rw [e2]
    have e : VerifiableInference.PlanWritten.proofSizedFull.request.link.length = 25 := by decide
    rw [e]
    exact hl
  have key := tieReadsS_vec R Said n hn hown hlen hne hmom (apart_at_head h hG) hs hsa ok hsg hdeg H
  have eC : A.G.first.codes = P5J.At.cs A.Z := by
    rw [hFirst]
    rfl
  rw [eC, hW] at key
  exact key

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieReadsS_of_tie
