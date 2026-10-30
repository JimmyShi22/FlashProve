-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHeadAtS.lean: THE
SECOND FAMILY OF TiePlanS, TieReadsS (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanSplit.lean), AT
THE OUTPUT HEAD's SEGMENT, UNDER THE KIND's RECORD AT THAT SEGMENT's READS ALONE. One definition of
a premise's form, two statements and their proofs. The sister of TieReadsAtS.lean.

  HeadPlanS            HeadReadsS (TieReadsHeadS.lean) LESS the letter T (the trace) and two
                       clauses: "the reader's cells are the trace's" · "tl has the plan's
                       matrices". MADE BY PROGRAM OFF THAT DEFINITION's TEXT. Public in every
                       clause; two clauses are sentences on the run: what the filler's maker
                       returns at the instance and at what was heard; that the state's tables are
                       those that the head's makers give off what was heard
  headPlanS_of_reads   HeadReadsS gives it
  tieReadsS_head       TieReadsS L Said G.first.codes arr ms wit (matsOwn G.W 24) b 24
                       (G.W.H.nU.getD 2 0), from: the record R at the reads' member · hU · thirteen
                       public premises · HeadPlanS

THE ROAD: tie_reads_headS' lift, with: "tl has the plan's matrices" PAID, off the member's own
accept: head_record (HeadRecord.lean) at the library's quiet_of_kind
(Johnson/Desc/K1/Law/OwnHeldAtSendings.lean) · tie_reads_headP (TieReadsHeadPlan.lean) for
tie_reads_head.

Limits. THE TIE OF THE SCRIPT TO OUR LOT's TEXTS (the record's fields msgs, pads) IS A PREMISE.
HeadPlanS has no member and no negative test. IT MAY HOLD EMPTILY: where the pair ThrS holds of
nothing at b, where the member accepts no step, or where the state behind has no record of the
smallness test, it asks nothing. A law under "Stepped": it holds of nothing at a book that does not
cover the reads' part's count. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsHeadS
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsHeadPlan
import Johnson.Desc.ProofFile.Honest.K1.Law.HeadRecord
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanSplit
import Johnson.Desc.K1.Law.OwnHeldAtSendings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (Reading HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Tr seatsOf seatAt pairOf)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats placeIn)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}

/-- **All that the law on the vector of reads asks of a run at the output head's segment, under the
thread's own binders.** HeadReadsS (TieReadsHeadS.lean) LESS the letter T and two clauses: "the
reader's cells are the trace's" and "tl has the plan's matrices". No witness; no coin is read; of
the input: the instance, in two clauses; of the run: what was heard, in two. WHERE covOf REFUSES THE
INSTANCE's REQUEST, "(covOf ...).toOption.getD default" IS Lean's DEFAULT COVER, IN SILENCE: public
data: HERE AT TWO PLACES (valsAt; ReadsQuiet.tables), where ReadsPlanS has one. IT MAY HOLD EMPTILY.
A definition: a premise's form. NO MEMBER, NO NEGATIVE TEST. -/
def HeadPlanS (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (Z : Pub) (G : Ground) (n sg : ℕ)
    (A : MsgAddr) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl : HTailF2, s'.tl? = some tl →
    Book.BookFits s'.book ∧
    (∀ (z : ℕ) (T' : OnBytes.Tree), s'.book.trees[z]? = some T' → T'.number = z) ∧
    ∃ (p : K9.Part) (c₀ : ℕ × String) (a : ReqArray) (nm : String) (M : Params.ReqMessage)
      (SV : SegVals) (vec : Cells → ℕ → OnBytes.E),
      K9.segAt? s' = some p ∧ p.L.arrayOf[u3Of tl]? = some c₀ ∧
      reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a ∧
      p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n) ∧
      laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
        (p.d.st.placeBits (s.st.oracles.size + n) .main) = true ∧
      arrayOf G.first.layout sg nm = some a ∧
      Meaning.messageAt G.first.shape sg a.message = some M ∧ M.shape.answers ≠ 0 ∧
      pairOf (u3Seats Z G) A = some (sg, a.message) ∧ a.name = "U3" ∧ 0 < a.sizeI ∧
      G.W.H.nU.getD 2 0 ≤ a.sizeC ∧
      valsAt Z G ((covOf Z G (wit μ.st.input).x).toOption.getD default) sg = .ok SV ∧
      SV.vec (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok vec ∧
      ∀ (sps : List Spot) (k6 k3 : Spot × ℕ) (x : OnBytes.Model.Head.Heard)
        (t : OnBytes.Model.Head.Tables), spotsOf Z.cuts = some sps →
        placeIn Z sps sg .K6 = .ok k6 → placeIn Z sps sg .K3 = .ok k3 →
        headHeardWholeAt (headParAt G) (Kinds.Head.requestOf Z.s₀) 0
          (k4LookOf G.W.HLy.fs k3.2
            (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))) k6.2
          (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok x →
        ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
          ((covOf Z G (wit μ.st.input).x).toOption.getD default) x = .ok t → tl.funs = t.funs

/-- **HeadReadsS gives it**: it asks less. -/
theorem headPlanS_of_reads {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop} {b : ℕ}
    {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {T : Local W₀ Rc ProofFile.Inst Tr' → Tr}
    {Z : Pub} {G : Ground} {n sg : ℕ} {A : MsgAddr} (H : HeadReadsS L Said b wit T Z G n sg A) :
    HeadPlanS L Said b wit Z G n sg A := by
  intro blk hb k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨hFits, hNum, p, c₀, a, nm, M, SV, vec, hp, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, -, -, hfuns⟩ := H blk hb k s μ E ds y cols s' hA hd hS tl htl
  exact ⟨hFits, hNum, p, c₀, a, nm, M, SV, vec, hp, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hfuns⟩

variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE SECOND FAMILY AT THE OUTPUT HEAD's SEGMENT, 24**: under
the kind's record at the segment's reads, ONE member of the kind K1. l (the sending's link, in R's
job) IS A LETTER: nothing here says that it is 24: a caller lays l := 24. -/
theorem tieReadsS_head {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
    {gp : _root_.Desc.Plain.GPar}
    {l piece first pr : ℕ} {Y : OnBytes.Model.Stages.LinkH} {reads : Option (List ℕ)}
    (R : K1Seated L b blk wit (laterJobAt G.first gp l piece 1 first (lotData Sz₀ Z G)) own₀ sort
      arr seats₀ ms rad)
    (hU : blk.UnderR ((IM.k1Reads Z G 24 Y pr reads).retype : Block S Cl))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (n : ℕ)
    (hn : n < (K1.parLater G.first gp l piece 1).sent.size)
    (hown : (L.N.group 24).contains
      (seatAtMember L.bs b (K1.parLater G.first gp l piece 1) n) = true)
    (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece 1).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t) → momentIs t 1 = true)
    (hap : apartOk Z G = true) {st : OnBytes.HonestTrace.Seat} (hs : st ∈ u3Seats Z G)
    (hsa : st.addr = ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (hsg : 24 < G.first.shape.link.length)
    (h3 : ((shapeAt (K1.parLater G.first gp l piece 1) n).mainDeg == 3) = true)
    (hY : G.built[24]? = some Y) (hk : Y.kind = 2)
    (H : HeadPlanS L Said b wit Z G n 24 st.addr) :
    TieReadsS L Said G.first.codes arr ms wit (matsOwn G.W 24) b 24 (G.W.H.nU.getD 2 0) := by
  intro blk' hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe
  obtain rfl : blk = blk' := Option.some.inj (R.member.symm.trans hb)
  obtain ⟨hFits, hNum, p, c₀, a, nm, M, SV, vec, hp, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hfuns⟩ := H _ hb k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmats, _, _⟩ :=
    head_record (K1.quiet_of_kind G 24 Y hY hk) hU hS htl
  obtain ⟨c, -, -, -, hc, -, -, -, -, hin, hheard⟩ := step_at_block R Said hA hd hS
  subst hAe
  have key := tie_reads_headP R Said hA hd hS hFits hNum c hc n hn ds' 24 hown p hp tl c₀ hc₀ a ha
    ho hok hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec h3 hY hk hI hC hmats
    hfuns (L.pubOf μ.st.input.x)
  rw [hin, hheard, List.append_assoc] at key
  exact key

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.HeadPlanS
#print axioms ProofFile.Honest.K1.headPlanS_of_reads
#print axioms ProofFile.Honest.K1.tieReadsS_head
