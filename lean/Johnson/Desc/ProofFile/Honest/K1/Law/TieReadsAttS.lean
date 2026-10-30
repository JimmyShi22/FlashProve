-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsAttS.lean: THE SECOND
FAMILY OF "tie m" AT AN ATTENTION's SEGMENT: WHAT VecPlanS' LAST CLAUSE
(Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsVecS.lean) COMES DOWN TO THERE. One definition of a
premise's form, two statements and their proofs.

  valsAt_att       at a segment of attention's sort the filler's valsAt is attVals
                   (Johnson/HonestTrace/U3Rows.lean)
  AttPlanS         VecPlanS WITH THE PLAN's A.nW FOR nR AND ITS LAST TWO CLAUSES SWAPPED FOR ONE:
                   the state's tables are those that tablesP gives at the points that the honest
                   ptsOf makes of what was heard. MADE BY PROGRAM OFF THAT DEFINITION's TEXT.
                   Public in every clause. The sister of ReadsPlanS and HeadPlanS
  vecPlanS_of_att  AttPlanS gives VecPlanS at A.nW, under hb · hU · hY, hk (the built link has the
                   kind 1) · hA · hSame · AttTlS (TieStateAttPlan.lean)

OF THE FOUR THINGS THAT VecPlanS' LAST CLAUSE WANTS AT ATTENTION: (a) what the maker returns:
attVals_vec (Johnson/Desc/ProofFile/Honest/K5/Law/AttValsVec.lean): CALLED · (b)
attention's reading is readAt: u3Of_is_readAt (U3OfIsReadAt.lean): CALLED · (c) THE STATE's TABLES
ARE THE MAKER's: AttPlanS' LAST CLAUSE: A PREMISE: the quiet step makes its points off the state
(ptsFrom, lookOfO), the maker off what was heard (ptsOf, lookOf): the named premises PointsSame
and LookTie stand there · (d) the state's sizes are the plan's: AttTlS with the library's
tlLike_over_reads, and hSame; readAt_same, ParFits.same (Johnson/HonestTrace/Reads.lean).

With tieReadsS_vec: TieReadsS at an attention's segment, under the record at its reads, eleven
public premises, and what vecPlanS_of_att takes.

Limits. AttPlanS, AttTlS and hSame are paid by nobody. AttPlanS has no member and no negative test;
IT MAY HOLD EMPTILY. Its last clause is a sentence on the run. A law under "Stepped". Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsVecS
import Johnson.Desc.ProofFile.Honest.K1.Law.TieStateAttPlan
import Johnson.Desc.ProofFile.Honest.K1.Law.U3OfIsReadAt
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2 HFun)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (funBack)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.HonestTrace (seatsOf seatAt pairOf parOfMats parFits_parOfMats SameSizes ParFits.same
  readAt_same)
open OnBytes.HonestTrace.U3 (SegVals valsAt attVals covOf u3Seats placeIn sizesOf)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

/-- At a segment of attention's sort valsAt is attVals. The sister of valsAt_layers, valsAt_head. -/
theorem valsAt_att (Z : Pub) (G : Ground) (cov : OnBytes.Model.Head.Covered) {seg : ℕ}
    {SV : SegVals}
    (hv : valsAt Z G cov seg = .ok SV) {Y : OnBytes.Model.Stages.LinkH}
    (hY : G.built[seg]? = some Y) (hk : Y.kind = 1) :
    ∃ sps, spotsOf Z.cuts = some sps ∧ attVals Z G sps seg Y.g = .ok SV := by
  unfold valsAt at hv
  obtain ⟨sps, h1, hv⟩ := bind_eq_ok hv
  obtain ⟨Y', h2, hv⟩ := bind_eq_ok hv
  obtain ⟨_, -, hv⟩ := bind_eq_ok hv
  obtain ⟨_, -, hv⟩ := bind_eq_ok hv
  rw [hY] at h2
  obtain rfl : Y = Y' := Except.ok.inj h2
  refine ⟨sps, ?_, by simpa [hk] using hv⟩
  cases hs : spotsOf Z.cuts with
  | none => rw [hs] at h1; cases h1
  | some s => rw [hs] at h1; exact congrArg some (Except.ok.inj h1)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}

/-- **All that the law on the vector of reads asks of a run AT AN ATTENTION's SEGMENT sg, under the
thread's own binders.** The sister of ReadsPlanS (TieReadsAtS.lean) and HeadPlanS
(TieReadsHeadAtS.lean), clause for clause but for its last: there K4's makers, the head's; HERE
ATTENTION's: "the state's tables are those that the verifier's tablesP gives at the points that the
honest side's ptsOf makes of what was heard". g: the group; Ap: its plan: THE FORM ITSELF DOES NOT
TIE Ap TO g (Ap stands at "Ap.nW ≤ a.sizeC" alone): the law's hA does. No witness; no coin is read;
of the input: the instance, in one clause; of the run: what was heard, in two. WHERE covOf REFUSES
THE INSTANCE's REQUEST, "(covOf ...).toOption.getD default" IS Lean's DEFAULT COVER, IN SILENCE:
public data: at one place. IT MAY HOLD EMPTILY. A definition: a premise's form. NO MEMBER, NO
NEGATIVE TEST. -/
def AttPlanS (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b₁ : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (Z : Pub) (G : Ground) (n sg g : ℕ)
    (Ap : OnBytes.Attention.Plan) (A : MsgAddr) : Prop :=
  ∀ blk, L.bs[b₁]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b₁ k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl : HTailF2, s'.tl? = some tl →
    Book.BookFits s'.book ∧
    (∀ (z : ℕ) (T' : OnBytes.Tree), s'.book.trees[z]? = some T' → T'.number = z) ∧
    ∃ p : K9.Part, K9.segAt? s' = some p ∧
    ∃ (c₀ : ℕ × String) (a : ReqArray) (nm : String) (M : Params.ReqMessage) (SV : SegVals)
      (vec : Cells → ℕ → OnBytes.E),
      p.L.arrayOf[u3Of tl]? = some c₀ ∧
      reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a ∧
      p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n) ∧
      laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
        (p.d.st.placeBits (s.st.oracles.size + n) .main) = true ∧
      arrayOf G.first.layout sg nm = some a ∧
      Meaning.messageAt G.first.shape sg a.message = some M ∧ M.shape.answers ≠ 0 ∧
      pairOf (u3Seats Z G) A = some (sg, a.message) ∧ a.name = "U3" ∧ 0 < a.sizeI ∧
      Ap.nW ≤ a.sizeC ∧
      valsAt Z G ((covOf Z G (wit μ.st.input).x).toOption.getD default) sg = .ok SV ∧
      SV.vec (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok vec ∧
      ∀ (sps : List Spot) (A' : OnBytes.Attention.Plan) (k5 k3 : Spot × ℕ)
        (q : First.Att.P.Pts) (t : First.Att.P.TablesP),
        spotsOf Z.cuts = some sps → G.W.A[g]? = some A' →
        placeIn Z sps sg .K5 = .ok k5 → placeIn Z sps sg .K3 = .ok k3 →
        H2K5.Honest.ptsOf ⟨A'.S, A'.own⟩
          ⟨(k4LookOf A'.fs k3.2
              (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))).zk,
            (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)).drop k5.2⟩ = some q →
        First.Att.P.tablesP (⟨A'.S, A'.own⟩ : H2K5.Honest.Pub5).g (sizesOf A'.mats) A'.nW
          (First.Att.P.lookOf A'.S.cf.lmb (k4LookOf A'.fs k3.2
            (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)))) q = some t →
        tl.funs = t.funs.map funBack

variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b₁ : Nat}
  {blk₁ : Block S Cl} {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst}

/-- **AttPlanS gives VecPlanS at an attention's segment**, where the member lies under the library's
reads' block, the state in front has the plan's record (AttTlS), and the plan's two lists of
matrices have the same sizes (hSame). The sister of vecPlanS_of_layers, vecPlanS_of_head. -/
theorem vecPlanS_of_att {Z : Pub} {G : Ground} {pr sg n : ℕ}
    {Y : OnBytes.Model.Stages.LinkH} {reads : Option (List ℕ)} {Ap : OnBytes.Attention.Plan}
    {A : MsgAddr} {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop}
    (hb : L.bs[b₁]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G sg Y pr reads).retype : Block S Cl))
    (hY : G.built[sg]? = some Y) (hk : Y.kind = 1) (hA : G.W.A[Y.g]? = some Ap)
    (hSame : SameSizes Ap.mats Ap.seam.tl.mats) (hTl : AttTlS L Said b₁ Ap)
    (H : AttPlanS L Said b₁ wit Z G n sg Y.g Ap A) :
    VecPlanS L Said b₁ wit Z G n sg Ap.nW A := by
  intro blk' hb' k s μ E ds y cols s' hT hd hS tl htl
  obtain rfl : blk₁ = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hfuns⟩ := H _ hb' k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨r₁, r₂, gs, -, -, -, -, -, -, -, hdec, -, -, -, -, -, -, -, -, -⟩ :=
    att_record hk hA hU hS
  obtain ⟨a₀, hs0, hL0⟩ := hTl _ hb' k s μ E ds y cols s' hT hd hS
  obtain ⟨tl', htl', hL1⟩ :=
    K1.tlLike_over_reads Z G sg Y hY pr reads s s' [r₁, r₂] gs rfl hdec a₀ hs0
  obtain rfl : tl' = tl := Option.some.inj (htl'.symm.trans htl)
  have hL := hL0.trans hL1
  obtain ⟨sps, hsp, hH⟩ := valsAt_att Z G _ hv hY hk
  obtain ⟨A', k5, k3, hA', h5, h3, hn', HV⟩ := K5.attVals_vec hH
  obtain rfl : Ap = A' := Option.some.inj (hA.symm.trans hA')
  obtain ⟨q, t, hq, ht, hvecEq⟩ := HV _ _ hvec
  refine ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hn', fun C j _ => ?_⟩
  rw [hvecEq, u3Of_is_readAt Ap.mats (cellsAtOf C (matsOwn G.W sg)) t.funs j,
    hfuns sps _ k5 k3 q t hsp hA' h5 h3 hq ht]
  refine readAt_same (mats := tl'.mats) (ParFits.same ?_ (parFits_parOfMats Ap.mats))
    (parFits_parOfMats tl'.mats) _ _ _
  rw [hL.mats]
  exact hSame

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.valsAt_att
#print axioms ProofFile.Honest.K1.AttPlanS
#print axioms ProofFile.Honest.K1.vecPlanS_of_att
