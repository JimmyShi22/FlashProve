-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanFirstS.lean: TiePlanS
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) AT THE FIRST SEGMENT, AT ANY SIZES, AT THE
READER's OWN CELLS, UNDER THE RECORD K1Seated AT TWO MEMBERS. One definition of a premise's form,
one statement and its proof.

  FirstPlanS       FirstRowsS (Johnson/Desc/ProofFile/Honest/K1/Law/TieRowsFirstS.lean) WITH A
                   LETTER Sz₀ FOR Sz.ref, LESS THE TRACE T AND ITS ONE CLAUSE (the reader's cells
                   are the trace's): all else to the sign. NO MEMBER IS GIVEN, AND NO NEGATIVE TEST
  tiePlanS_first   tieRowsS_first (the same file) likewise: Sz₀ in the two jobs; LESS T, hMarks,
                   hParts; its end: TiePlanS L Said G.first.codes arr ms Sz₀ wit (matsOwn G.W 0) b₁
                   0 (the plan's number of reads): THE LIST IS THE FILLER's OWN

MADE BY PROGRAM OFF THAT FILE's TEXT: the letter for the constant; the binders and the clause
struck; the two calls go to tie_mat_firstP (TieMatPlan.lean) and tie_reads_layersP
(TieReadsPlan.lean); nothing else. That file keeps its own.

THE MEMBER IS A LETTER (since […]). The blocks' class of claims Cl is a letter, and the
reads' member is a letter of the type Block S Cl, with ONE PUBLIC PREMISE: hU: it has the rounds of
the library's own block IM.k1Reads (Johnson/IMR/K1Seat.lean; typed there at Unit), carried to Cl by
Block.retype, and where it says yes that block says the same yes (Block.UnderR, step_under:
Johnson/Desc/Sound/SeatGuardChain.lean). WHY: the true chain's entry at a reads' place is not that
block: it is that block, retyped, under the seat's wrappers: k01_flat_reads
(Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR (Johnson/IMR/SeatForm.lean): by these two hU is
meant to be paid there; NO FILE PAYS IT YET. Of the member the proof spends its rounds and its
decision's yes alone.

Limits. Those of TieRowsFirstS.lean, but for what has fallen. SIXTEEN PUBLIC PREMISES. THE TIE OF
THE SCRIPT TO THE LOT's TEXTS (the records' fields msgs, pads) IS A PREMISE, at two members. ONE
SEGMENT OF TWENTY-FIVE. A law under "Stepped": it holds of nothing at a book that does not cover the
reads' part's count. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieRowsFirstS
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanShare
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatPlan
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsPlan

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

/-- **All that the two laws ask of a run at the first segment, under the thread's own binders.**
From the pair and the member's step. b₀: the opening's member; b₁: the reads'; n: the reads'
message; A: its address; g: the segment's group; hp₀: its plan. WHERE covOf REFUSES THE INSTANCE's
REQUEST, "(covOf ...).toOption.getD default" IS Lean's DEFAULT COVER, IN SILENCE: public data: it is
the term at which the lot's own data ask the values (u3ValsOf, Johnson/HonestTrace/U3Rows.lean).
FirstRowsS WITH A LETTER Sz₀ FOR Sz.ref, LESS THE TRACE T AND THE CLAUSE ON IT. A definition: a
premise's form. -/
def FirstPlanS (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b₀ b₁ : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (Sz₀ : Sz) (Z : Pub) (G : Ground)
    (gp : _root_.Desc.Plain.GPar) (n g : ℕ) (hp₀ : HPlan2) (A : MsgAddr) : Prop :=
  ∀ blk, L.bs[b₁]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b₁ k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl : HTailF2, s'.tl? = some tl →
    Book.BookFits s'.book ∧
    (∀ (z : ℕ) (T' : OnBytes.Tree), s'.book.trees[z]? = some T' → T'.number = z) ∧
    ∃ p : K9.Part, K9.segAt? s' = some p ∧ p.d.st.codes = (K1.firstPar G.first gp).codes ∧
    (∀ ν, ν < tl.NM → ∃ (n₀ o : ℕ) (x : _) (c₁ : ℕ × String) (a₁ : ReqArray),
      n₀ < (K1.firstPar G.first gp).sent.size ∧
      (L.N.group 0).contains (seatAtMember L.bs b₀ (K1.firstPar G.first gp) n₀) = true ∧
      p.d.st.oracles[o]? = some x ∧ x.shape = shapeAt (K1.firstPar G.first gp) n₀ ∧
      p.d.book.place[o]? = some (seatAtMember L.bs b₀ (K1.firstPar G.first gp) n₀) ∧
      Sound.seatBy Sound.noFirst p.d.book o =
        some (seatAtMember L.bs b₀ (K1.firstPar G.first gp) n₀) ∧
      p.L.arrayOf[tl.gtTree.getD ν 0]? = some c₁ ∧
      reqArray p.L.check.rows.layout c₁.1 c₁.2 = some a₁ ∧
      p.L.check.frame.whereIs c₁.1 a₁.message = some o ∧
      laidMatrixOk a₁ (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true ∧
      firstSeat G.first.shape 0 ⟨firstAddr, n₀⟩ = some (0, a₁.message) ∧
      msgFits G.first.codes G.first.shape G.first.layout 0 a₁.message = true ∧
      a₁ ∈ (G.first.layout.link.getD 0 []).filter (fun y => y.message == a₁.message) ∧
      labelNo a₁.name = some ν ∧
      (cellsVals Sz₀).size 0 a₁.name = some (Sz₀.packedShape 0 ν) ∧
      (Sz₀.packedShape 0 ν).1 ≤ a₁.sizeI ∧ (Sz₀.packedShape 0 ν).2 ≤ a₁.sizeC) ∧
    ∃ (c₀ : ℕ × String) (a : ReqArray) (nm : String) (M : Params.ReqMessage) (SV : SegVals)
      (vec : Cells → ℕ → OnBytes.E),
      p.L.arrayOf[u3Of tl]? = some c₀ ∧
      reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a ∧
      p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n) ∧
      laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
        (p.d.st.placeBits (s.st.oracles.size + n) .main) = true ∧
      arrayOf G.first.layout 0 nm = some a ∧
      Meaning.messageAt G.first.shape 0 a.message = some M ∧ M.shape.answers ≠ 0 ∧
      pairOf (u3Seats Z G) A = some (0, a.message) ∧ a.name = "U3" ∧ 0 < a.sizeI ∧
      hp₀.nU.getD 2 0 ≤ a.sizeC ∧
      valsAt Z G ((covOf Z G (wit μ.st.input).x).toOption.getD default) 0 = .ok SV ∧
      SV.vec (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok vec ∧
      ∀ (sps : List Spot) (pl : HPlan2) (k4 k3 : Spot × ℕ)
        (x : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (funs : Array HFun),
        spotsOf Z.cuts = some sps → G.W.G[g]? = some pl →
        placeIn Z sps 0 .K4 = .ok k4 → placeIn Z sps 0 .K3 = .ok k3 →
        layTables (OnBytes.Desc.First.K4.Honest.matsOf
            { P := G.W.layers, hp := pl, g := g, link := 0, piece := k4.1.place.piece,
              r0 := k4.2, seg := 0 }) (tableAsks G.W.layers.y G.W.layers.rd g) 0 = some x →
        funsOf G.W.layers.y
          (ptsOf
            { P := G.W.layers, hp := pl, g := g, link := 0, piece := k4.1.place.piece,
              r0 := k4.2, seg := 0 }
            { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
              look := k4LookOf G.W.layers.y.fo k3.2 }
            (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))).fo
          (namedPts
            { P := G.W.layers, hp := pl, g := g, link := 0, piece := k4.1.place.piece,
              r0 := k4.2, seg := 0 }
            (ptsOf
              { P := G.W.layers, hp := pl, g := g, link := 0, piece := k4.1.place.piece,
                r0 := k4.2, seg := 0 }
              { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
                look := k4LookOf G.W.layers.y.fo k3.2 }
              (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A))))
          x.2.1 = some funs →
        tl.funs = funs

variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b₀ b₁ : Nat}
  {blk₀ blk₁ : Block S Cl} {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ own₁ : X}
  {sort₀ sort₁ : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

/-- **TiePlanS at the first segment.** The data stand at nothing
seen; that the part's data at what it had seen are the same: heardOnly, not spent here. -/
theorem tiePlanS_first {Sz₀ : Sz} {Z : Pub} {G : Ground} {gp : _root_.Desc.Plain.GPar}
    {first₀ l piece first₁ pr : ℕ} {Y : OnBytes.Model.Stages.LinkH} {reads : Option (List ℕ)}
    {hp₀ : HPlan2}
    (R₀ : K1Seated L b₀ blk₀ wit
      (placeJob (K1.firstPar G.first gp) first₀ (firstFold G.first) (lotData Sz₀ Z G)) own₀
      sort₀ arr seats₀ ms rad)
    (R : K1Seated L b₁ blk₁ wit
      (laterJobAt G.first gp l piece 1 first₁ (lotData Sz₀ Z G)) own₁ sort₁ arr seats₀ ms rad)
    (hU : blk₁.UnderR ((IM.k1Reads Z G 0 Y pr reads).retype : Block S Cl))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (hb : b₀ ≤ b₁)
    (n : ℕ)
    (hn : n < (K1.parLater G.first gp l piece 1).sent.size)
    (hown : (L.N.group 0).contains
      (seatAtMember L.bs b₁ (K1.parLater G.first gp l piece 1) n) = true)
    (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece 1).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t) → momentIs t 1 = true)
    (hap : apartOk Z G = true) {st : OnBytes.HonestTrace.Seat} (hs : st ∈ u3Seats Z G)
    (hsa : st.addr = ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (hsg : 0 < G.first.shape.link.length)
    (h3 : ((shapeAt (K1.parLater G.first gp l piece 1) n).mainDeg == 3) = true)
    (hY : G.built[0]? = some Y) (hk : Y.kind = 0) (hG : G.W.G[Y.g]? = some hp₀)
    (H : FirstPlanS L Said b₀ b₁ wit Sz₀ Z G gp n Y.g hp₀ st.addr) :
    TiePlanS L Said G.first.codes arr ms Sz₀ wit (matsOwn G.W 0) b₁ 0 (hp₀.nU.getD 2 0) := by
  intro blk' hb' k s μ E ds y cols s' hA hd hS tl htl ds' A hAe
  obtain rfl : blk₁ = blk' := Option.some.inj (R.member.symm.trans hb')
  obtain ⟨hFits, hNum, p, hp, hcodes, hMat, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM,
    hansM, hPair, hname, hI, hC, hv, hvec, hfuns⟩ :=
    H _ hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨_, _, hmats, _, _, _, _⟩ := layers_record (quiet_layers_of_kind G 0 Y hY hk hG) hU hS htl
  obtain ⟨c, -, -, -, hc, -, -, -, -, hin, hheard⟩ := step_at_block R Said hA hd hS
  subst hAe
  refine ⟨fun ν hν cc hcc i' hi' => ?_, ?_⟩
  · obtain ⟨n₀, o, x, c₁, a₁, hn₀, hown₀, hx, hxs, hpl, hseat, hc₁, ha₁, ho₁, hok₁, t1, hfit, hin₁,
      hmu, hz, hI₁, hC₁⟩ := hMat ν hν
    exact tie_mat_firstP R₀ Said hb hA (ds ++ ds') s' (L.pubOf μ.st.input.x) 0 n₀ hn₀ hown₀ p hp o
      hcodes x hx hxs hpl hseat tl ν c₁ hc₁ a₁ ha₁ ho₁ hok₁ hlen t1 hfit hin₁ hmu hz hI₁ hC₁
      cc hcc i' hi'
  · have key := tie_reads_layersP R Said hA hd hS hFits hNum c hc n hn ds' 0 hown p hp tl c₀ hc₀ a
      ha ho hok hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec h3 hY hk
      hI hG hC hmats hfuns (L.pubOf μ.st.input.x)
    rw [hin, hheard, List.append_assoc] at key
    exact key

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.FirstPlanS
#print axioms ProofFile.Honest.K1.tiePlanS_first
