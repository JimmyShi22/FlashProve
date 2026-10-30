-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsAtS.lean: THE SECOND
FAMILY OF TiePlanS, TieReadsS (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanSplit.lean), AT EVERY
LAYERS' SEGMENT, UNDER THE KIND's RECORD AT THAT SEGMENT's READS ALONE. One definition of a
premise's form, two statements and their proofs.

  ReadsPlanS            FirstPlanS (TiePlanFirstS.lean) LESS the clause on the codes and the group
                        on the matrices' arrays; a letter sg for the segment 0. MADE BY PROGRAM OFF
                        THAT DEFINITION's TEXT. Public in every clause; two clauses are sentences on
                        the run: what the filler's maker returns at the instance and at what was
                        heard; that the state's tables are those that K4's makers give off what was
                        heard
  readsPlanS_of_first   FirstPlanS gives it at sg = 0
  tieReadsS_layers      TieReadsS L Said G.first.codes arr ms wit (matsOwn G.W sg) b₁ sg
                        (hp₀.nU.getD 2 0), from: the record R at the reads' member · hU · fourteen
                        public premises · ReadsPlanS

THE ROAD is the second half of tiePlanS_first's proof, to the letter, with sg for 0: layers_record,
step_at_block, tie_reads_layersP (LayersRecord.lean, SendAtBlock.lean, TieReadsPlan.lean), which are
general in the segment.

WHAT IT IS FOR: of the two families of TiePlanS this one is the kind K1's own at all 25 segments.
HERE: the segments of a group of layers (hk : Y.kind = 0). NOT HERE: the attention's segments; the
output head.

Limits. THE TIE OF THE SCRIPT TO OUR LOT's TEXTS (the record's fields msgs, pads) IS A PREMISE.
ReadsPlanS has no member and no negative test. IT MAY HOLD EMPTILY: where the pair ThrS holds of
nothing at b₁, where the member accepts no step, or where the state behind has no record of the
smallness test, it asks nothing. l and sg are two letters: nothing here says that the sending's link
is the segment. A law under "Stepped": it holds of nothing at a book that does not cover the reads'
part's count. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanFirstS
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2 HFun)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.HonestTrace (Sz seatsOf seatAt pairOf)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats placeIn)
open OnBytes.Model.Layer (HPlan2 TableAsk TableAt layTables tableAsks funsOf)
open OnBytes.Desc.First.K4.Honest (ptsOf namedPts)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}

/-- **All that the law on the vector of reads asks of a run at a layers' segment sg, under the
thread's own binders.** FirstPlanS (TiePlanFirstS.lean) LESS its clause on the codes and its group
on the matrices' arrays, WITH A LETTER sg FOR THE SEGMENT 0. No witness; no coin is read; of the
input: the instance, in one clause; of the run: what was heard, in two. WHERE covOf REFUSES THE
INSTANCE's REQUEST, "(covOf ...).toOption.getD default" IS Lean's DEFAULT COVER, IN SILENCE: public
data. A definition: a premise's form. NO MEMBER, NO NEGATIVE TEST. -/
def ReadsPlanS (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b₁ : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (Z : Pub) (G : Ground) (n sg g : ℕ)
    (hp₀ : HPlan2) (A : MsgAddr) : Prop :=
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
      hp₀.nU.getD 2 0 ≤ a.sizeC ∧
      valsAt Z G ((covOf Z G (wit μ.st.input).x).toOption.getD default) sg = .ok SV ∧
      SV.vec (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok vec ∧
      ∀ (sps : List Spot) (pl : HPlan2) (k4 k3 : Spot × ℕ)
        (x : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (funs : Array HFun),
        spotsOf Z.cuts = some sps → G.W.G[g]? = some pl →
        placeIn Z sps sg .K4 = .ok k4 → placeIn Z sps sg .K3 = .ok k3 →
        layTables (OnBytes.Desc.First.K4.Honest.matsOf
            { P := G.W.layers, hp := pl, g := g, link := sg, piece := k4.1.place.piece,
              r0 := k4.2, seg := sg }) (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some x →
        funsOf G.W.layers.y
          (ptsOf
            { P := G.W.layers, hp := pl, g := g, link := sg, piece := k4.1.place.piece,
              r0 := k4.2, seg := sg }
            { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
              look := k4LookOf G.W.layers.y.fo k3.2 }
            (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))).fo
          (namedPts
            { P := G.W.layers, hp := pl, g := g, link := sg, piece := k4.1.place.piece,
              r0 := k4.2, seg := sg }
            (ptsOf
              { P := G.W.layers, hp := pl, g := g, link := sg, piece := k4.1.place.piece,
                r0 := k4.2, seg := sg }
              { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
                look := k4LookOf G.W.layers.y.fo k3.2 }
              (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))))
          x.2.1 = some funs →
        tl.funs = funs

/-- **FirstPlanS gives it at the segment 0**: it asks less. -/
theorem readsPlanS_of_first {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop} {b₀ b₁ : ℕ}
    {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {Sz₀ : Sz} {Z : Pub} {G : Ground}
    {gp : _root_.Desc.Plain.GPar} {n g : ℕ} {hp₀ : HPlan2} {A : MsgAddr}
    (H : FirstPlanS L Said b₀ b₁ wit Sz₀ Z G gp n g hp₀ A) :
    ReadsPlanS L Said b₁ wit Z G n 0 g hp₀ A := by
  intro blk hb k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨hFits, hNum, p, hp, -, -, hR⟩ := H blk hb k s μ E ds y cols s' hA hd hS tl htl
  exact ⟨hFits, hNum, p, hp, hR⟩

variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b₁ : Nat}
  {blk₁ : Block S Cl} {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₁ : X}
  {sort₁ : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE SECOND FAMILY AT A LAYERS' SEGMENT sg**: under the kind's
record at the segment's reads, ONE member of the kind K1. l (the sending's link, in R's job) AND sg
(the segment) ARE TWO LETTERS: nothing here says that they are one: a caller lays l := sg. -/
theorem tieReadsS_layers {Sz₀ : Sz} {Z : Pub} {G : Ground} {gp : _root_.Desc.Plain.GPar}
    {l piece first₁ pr sg : ℕ} {Y : OnBytes.Model.Stages.LinkH} {reads : Option (List ℕ)}
    {hp₀ : HPlan2}
    (R : K1Seated L b₁ blk₁ wit
      (laterJobAt G.first gp l piece 1 first₁ (lotData Sz₀ Z G)) own₁ sort₁ arr seats₀ ms rad)
    (hU : blk₁.UnderR ((IM.k1Reads Z G sg Y pr reads).retype : Block S Cl))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (n : ℕ)
    (hn : n < (K1.parLater G.first gp l piece 1).sent.size)
    (hown : (L.N.group sg).contains
      (seatAtMember L.bs b₁ (K1.parLater G.first gp l piece 1) n) = true)
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
    (hY : G.built[sg]? = some Y) (hk : Y.kind = 0) (hG : G.W.G[Y.g]? = some hp₀)
    (H : ReadsPlanS L Said b₁ wit Z G n sg Y.g hp₀ st.addr) :
    TieReadsS L Said G.first.codes arr ms wit (matsOwn G.W sg) b₁ sg (hp₀.nU.getD 2 0) := by
  intro blk' hb' k s μ E ds y cols s' hA hd hS tl htl ds' A hAe
  obtain rfl : blk₁ = blk' := Option.some.inj (R.member.symm.trans hb')
  obtain ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hfuns⟩ := H _ hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨_, _, hmats, _, _, _, _⟩ :=
    layers_record (quiet_layers_of_kind G sg Y hY hk hG) hU hS htl
  obtain ⟨c, -, -, -, hc, -, -, -, -, hin, hheard⟩ := step_at_block R Said hA hd hS
  subst hAe
  have key := tie_reads_layersP R Said hA hd hS hFits hNum c hc n hn ds' sg hown p hp tl c₀ hc₀ a
    ha ho hok hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec h3 hY hk
    hI hG hC hmats hfuns (L.pubOf μ.st.input.x)
  rw [hin, hheard, List.append_assoc] at key
  exact key

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ReadsPlanS
#print axioms ProofFile.Honest.K1.readsPlanS_of_first
#print axioms ProofFile.Honest.K1.tieReadsS_layers
