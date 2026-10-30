-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHeadS.lean:
tie_reads_head (Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHead.lean) LIFTED FROM ONE RUN TO THE
FORM OF TieRowsS (Johnson/Desc/ProofFile/Honest/K1/Law/TieShare.lean; tieRowsS_iff,
Johnson/Desc/ProofFile/Honest/K1/Law/TieRowsCore.lean): THE SECOND EQUATION OF TieRowsAt, BEHIND THE
PAIR AND THE MEMBER's STEP, AT THE STATE's RECORD, AT EVERY CONTINUATION, OF THE THREAD's OWN
WITNESS's TABLE. One definition of a premise's form, one statement and its proof.

  HeadReadsS        ALL THAT tie_reads_head ASKS OF A RUN, GATHERED UNDER THE THREAD's OWN BINDERS:
                    from the pair and the member's step, at the state's record tl: the two premises
                    on the verifier's book · an open part p, the array of reads' name c₀ in its
                    list, the layout's array a with its message, test and size · the segment's maker
                    accepts (SV) and its vec accepts what was heard (vec) · AND THE THREE THAT CARRY
                    THE WEIGHT: the reader's cells are the trace's · tl has the plan's matrices ·
                    THE STATE's TABLES ARE THE FILLER's
  tie_reads_headS   under R at the lot's own job, public premises and HeadReadsS: at A := cellsAt
                    ... of the thread's own witness at (heard ++ (ds ++ ds')), nR := the plan's
                    number of reads: THE FIRST EQUATION OF TieRowsAt AT A GIVES THE WHOLE OF
                    TieRowsAt G.W (T input) sg nR tl A: the second equation is paid here

THE LIFT: R.member (the block) · step_at_block (Johnson/Desc/ProofFile/Honest/K1/Law/
ExchangeAtPins.lean): the part's cut; the input rides; what was heard grows by ds ·
List.append_assoc.

Limits. HeadReadsS IS A DEFINITION: NO MEMBER IS GIVEN, AND NO NEGATIVE TEST; nothing is claimed of
it, and no goal file names it. It names the thread's reader of the input (wit) and the trace (T) in
one equation; no witness of the Script's stands in it. A law under "Stepped": it holds of nothing at
a book that does not cover the part's count. THE FIRST EQUATION OF TieRowsAt (the matrices' packed
cells) IS NOT HERE: so TieRowsS is not concluded. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (Reading HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Tr Sz seatsOf seatAt pairOf parOfMats cellsC cellOf packedCells matsOf
  PlanMarks PartsFit)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats placeIn)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}

/-- **All that tie_reads_head asks of a run, under the thread's own binders.** From the pair and the
member's step. A definition: a premise's form. -/
def HeadReadsS (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (T : Local W₀ Rc ProofFile.Inst Tr' → Tr)
    (Z : Pub) (G : Ground) (n sg : ℕ) (A : MsgAddr) : Prop :=
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
      (wit μ.st.input).R.cells = cellsC G.W (T μ.st.input) ∧ tl.mats = G.W.H.tl.mats ∧
      ∀ (sps : List Spot) (k6 k3 : Spot × ℕ) (x : OnBytes.Model.Head.Heard)
        (t : OnBytes.Model.Head.Tables), spotsOf Z.cuts = some sps →
        placeIn Z sps sg .K6 = .ok k6 → placeIn Z sps sg .K3 = .ok k3 →
        headHeardWholeAt (headParAt G) (Kinds.Head.requestOf Z.s₀) 0
          (k4LookOf G.W.HLy.fs k3.2
            (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))) k6.2
          (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok x →
        ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
          ((covOf Z G (wit μ.st.input).x).toOption.getD default) x = .ok t → tl.funs = t.funs

variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **In TieRowsS' own form, at the output head: whoever brings the
first equation of TieRowsAt has the whole.** -/
theorem tie_reads_headS {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
    {gp : _root_.Desc.Plain.GPar} {l piece first : ℕ}
    (R : K1Seated L b blk wit (laterJobAt G.first gp l piece 1 first (lotData Sz₀ Z G)) own₀ sort
      arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop)
    (T : Local W₀ Rc ProofFile.Inst Tr' → Tr) (n : ℕ)
    (hn : n < (K1.parLater G.first gp l piece 1).sent.size) {sg : ℕ}
    (hown : (L.N.group sg).contains
      (seatAtMember L.bs b (K1.parLater G.first gp l piece 1) n) = true)
    (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece 1).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t) → momentIs t 1 = true)
    (hap : apartOk Z G = true) {st : OnBytes.HonestTrace.Seat} (hs : st ∈ u3Seats Z G)
    (hsa : st.addr = ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (hsg : sg < G.first.shape.link.length)
    (h3 : ((shapeAt (K1.parLater G.first gp l piece 1) n).mainDeg == 3) = true)
    {Y : OnBytes.Model.Stages.LinkH} (hY : G.built[sg]? = some Y) (hk : Y.kind = 2)
    (hsg25 : sg < 25) (hMarks : PlanMarks G.W) (hParts : PartsFit G.W)
    (H : HeadReadsS L Said b wit T Z G n sg st.addr) :
    ∀ blk', L.bs[b]? = some blk' → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
      drawsFit blk'.rounds ds = true → L.thread.Stepped blk' k s μ E ds y cols s' →
      ∀ tl, s'.tl? = some tl → ∀ ds', ∀ A,
        A = cellsAt (K1.parLater G.first gp l piece 1).codes arr ms L.N sg
          (L.pubOf μ.st.input.x, s') (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds'))) →
        (∀ ν, ν < tl.NM → ∀ c, c < (Sz.ref.packedShape sg ν).2 →
          ∀ i', i' < (Sz.ref.packedShape sg ν).1 → A (tl.gtTree.getD ν 0) i' c =
            algebraMap Cb.Gl.F Cb.Gl.E
              (packedCells Sz.ref (cellOf G.W (T μ.st.input)) sg ν i' c)) →
        TieRowsAt G.W (T μ.st.input) sg (G.W.H.nU.getD 2 0) tl A := by
  intro blk' hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe h1
  obtain rfl : blk = blk' := Option.some.inj (R.member.symm.trans hb)
  obtain ⟨hFits, hNum, p, c₀, a, nm, M, SV, vec, hp, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hcells, hmats, hfuns⟩ := H _ hb k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨c, -, -, -, hc, -, -, -, -, hin, hheard⟩ := step_at_block R Said hA hd hS
  have key := tie_reads_head R Said hA hd hS hFits hNum c hc n hn ds' sg hown p hp tl c₀ hc₀ a ha
    ho hok hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec h3 hY hk hsg25 hMarks
    hParts hI hC (T μ.st.input) hcells hmats hfuns (L.pubOf μ.st.input.x)
  rw [hin, hheard, List.append_assoc, ← hAe] at key
  exact ⟨h1, key⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.HeadReadsS
#print axioms ProofFile.Honest.K1.tie_reads_headS
