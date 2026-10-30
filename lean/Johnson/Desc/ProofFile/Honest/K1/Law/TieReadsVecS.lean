-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsVecS.lean: THE SECOND
FAMILY OF TiePlanS, TieReadsS (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanSplit.lean), AT ANY
SEGMENT, OF WHATEVER SORT, UNDER THE KIND's RECORD AT THAT SEGMENT's READS ALONE. One definition of
a premise's form, three statements and their proofs.

  VecPlanS             ReadsPlanS (TieReadsAtS.lean) WITH A LETTER nR FOR THE PLAN's NUMBER OF
                       READS AND ITS LAST CLAUSE SWAPPED FOR: the maker's vector has nR entries,
                       and at every reader of cells its entry j, for j below nR, is readAt at the
                       state's own sizes and tables, at the cells read through matsOwn G.W sg.
                       MADE BY PROGRAM OFF THAT DEFINITION's TEXT. Public in every clause. It
                       reads no sort of segment
  tieReadsS_vec        TieReadsS L Said G.first.codes arr ms wit (matsOwn G.W sg) b₁ sg nR, from:
                       the record R at the reads' member · eleven public premises · VecPlanS
  vecPlanS_of_layers   ReadsPlanS gives VecPlanS at a layers' segment (under hb, hU, hY, hk, hG)
  vecPlanS_of_head     HeadPlanS gives it at the output head's (under hb, hU, hY, hk)

WHY. The pointwise law tie_reads_vecB (TieReadsVecBound.lean; tie_reads_vecP, TieReadsPlan.lean,
with its premise asked below nR alone) reads no sort of segment. So the second family can be had at
all 25 segments under one public form; what differs from sort to sort is WHO PAYS ITS LAST CLAUSE.
At layers and the head: the two laws here, from the elder forms. AT AN ATTENTION's SEGMENT: NOBODY
YET: it wants what the filler's maker returns there (attVals, Johnson/HonestTrace/U3Rows.lean), that
attention's own reading of an entry is readAt, that the state's tables are the maker's, and that the
state's sizes are the plan's.

Limits. THE TIE OF THE SCRIPT TO OUR LOT's TEXTS (the record's fields msgs, pads) IS A PREMISE.
VecPlanS has no member and no negative test; IT MAY HOLD EMPTILY: where the pair ThrS holds of
nothing at b₁, where the member accepts no step, or where the state behind has no record of the
smallness test, it asks nothing. Its last clause is a sentence on the run: it ties what the maker
makes of what was heard to the state's own tables. A law under "Stepped": it holds of nothing at a
book that does not cover the reads' part's count. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsAtS
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsHeadAtS
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsVecBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2 HFun)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.HonestTrace (seatsOf seatAt pairOf parOfMats)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats placeIn)
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}

/-- **All that the law on the vector of reads asks of a run AT ANY SEGMENT sg, OF WHATEVER SORT,
under the thread's own binders.** ReadsPlanS (TieReadsAtS.lean) WITH A LETTER nR FOR THE PLAN's
NUMBER OF READS AND ITS LAST CLAUSE SWAPPED: for "the state's tables are those that K4's makers
give off what was heard": "the maker's vector has nR entries, and at every reader of cells its
entry j, FOR j BELOW nR, is the reading readAt at the state's own sizes and tables" (the bound: the
form asks what is spent). No
witness; no coin is read; of the input: the instance, in one clause; of the run: what was heard, in
one clause (through vec it bears on the last). WHERE covOf REFUSES THE INSTANCE's REQUEST, "(covOf
...).toOption.getD default" IS Lean's DEFAULT COVER, IN SILENCE: public data. IT MAY HOLD EMPTILY.
A definition: a premise's form. NO MEMBER, NO NEGATIVE TEST. -/
def VecPlanS (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) (b₁ : ℕ)
    (wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst) (Z : Pub) (G : Ground) (n sg nR : ℕ)
    (A : MsgAddr) : Prop :=
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
      nR ≤ a.sizeC ∧
      valsAt Z G ((covOf Z G (wit μ.st.input).x).toOption.getD default) sg = .ok SV ∧
      SV.vec (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) A)) = .ok vec ∧
      SV.n = nR ∧
      ∀ (C : Cells) (j : ℕ), j < nR → vec C j =
        First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf C (matsOwn G.W sg)) j

variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b₁ : Nat}
  {blk₁ : Block S Cl} {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₁ : X}
  {sort₁ : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **THE SECOND FAMILY AT ANY SEGMENT sg**: under the kind's record
at the segment's reads, ONE member of the kind K1. It reads no sort of segment. l (the sending's
link, in R's job) AND sg (the segment) ARE TWO LETTERS: a caller lays l := sg. -/
theorem tieReadsS_vec {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
    {gp : _root_.Desc.Plain.GPar} {l piece first₁ sg nR : ℕ}
    (R : K1Seated L b₁ blk₁ wit
      (laterJobAt G.first gp l piece 1 first₁ (lotData Sz₀ Z G)) own₁ sort₁ arr seats₀ ms rad)
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
    (H : VecPlanS L Said b₁ wit Z G n sg nR st.addr) :
    TieReadsS L Said G.first.codes arr ms wit (matsOwn G.W sg) b₁ sg nR := by
  intro blk' hb' k s μ E ds y cols s' hA hd hS tl htl ds' A hAe
  obtain rfl : blk₁ = blk' := Option.some.inj (R.member.symm.trans hb')
  obtain ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hnR, hvecEq⟩ := H _ hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨c, -, -, -, hc, -, -, -, -, hin, hheard⟩ := step_at_block R Said hA hd hS
  subst hAe
  have key := tie_reads_vecB R Said hA hd hS hFits hNum c hc n hn ds' sg hown p hp tl c₀ hc₀ a
    ha ho hok hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec h3 hI nR hnR hC
    hvecEq (L.pubOf μ.st.input.x)
  rw [hin, hheard, List.append_assoc] at key
  exact key

/-- **ReadsPlanS gives it at a layers' segment**, where the member lies under the library's reads'
block: "tl has the plan's matrices" comes off the member's own accept. -/
theorem vecPlanS_of_layers {Z : Pub} {G : Ground} {pr sg n : ℕ}
    {Y : OnBytes.Model.Stages.LinkH} {reads : Option (List ℕ)} {hp₀ : HPlan2} {A : MsgAddr}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop}
    (hb : L.bs[b₁]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G sg Y pr reads).retype : Block S Cl))
    (hY : G.built[sg]? = some Y) (hk : Y.kind = 0) (hG : G.W.G[Y.g]? = some hp₀)
    (H : ReadsPlanS L Said b₁ wit Z G n sg Y.g hp₀ A) :
    VecPlanS L Said b₁ wit Z G n sg (hp₀.nU.getD 2 0) A := by
  intro blk' hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain rfl : blk₁ = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hfuns⟩ := H _ hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨_, _, hmats, _, _, _, _⟩ :=
    layers_record (quiet_layers_of_kind G sg Y hY hk hG) hU hS htl
  obtain ⟨sps, hsp, hH⟩ := valsAt_layers Z G _ hv hY hk
  obtain ⟨pl, k4, k3, x, funs, hpl, hk4, hk3, hx, hn', hf, hvecEq⟩ :=
    layers_vec Z G sps sg Y.g hH hvec
  obtain rfl : hp₀ = pl := Option.some.inj (hG.symm.trans hpl)
  refine ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hn', fun C j _ => ?_⟩
  rw [hvecEq, hmats, hfuns sps _ k4 k3 x funs hsp hpl hk4 hk3 hx hf]

/-- **HeadPlanS gives it at the output head's segment**, likewise. -/
theorem vecPlanS_of_head {Z : Pub} {G : Ground} {pr n : ℕ}
    {Y : OnBytes.Model.Stages.LinkH} {reads : Option (List ℕ)} {A : MsgAddr}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop}
    (hb : L.bs[b₁]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G 24 Y pr reads).retype : Block S Cl))
    (hY : G.built[24]? = some Y) (hk : Y.kind = 2)
    (H : HeadPlanS L Said b₁ wit Z G n 24 A) :
    VecPlanS L Said b₁ wit Z G n 24 (G.W.H.nU.getD 2 0) A := by
  intro blk' hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain rfl : blk₁ = blk' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨hFits, hNum, p, c₀, a, nm, M, SV, vec, hp, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hfuns⟩ := H _ hb' k s μ E ds y cols s' hA hd hS tl htl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmats, _, _⟩ :=
    head_record (K1.quiet_of_kind G 24 Y hY hk) hU hS htl
  obtain ⟨sps, hsp, hH⟩ := valsAt_head Z G _ hv hY hk
  obtain ⟨hn', k6, k3, x, t, hk6, hk3, hx, ht, hvecEq⟩ := head_vec Z G _ sps 24 hH hvec
  refine ⟨hFits, hNum, p, hp, c₀, a, nm, M, SV, vec, hc₀, ha, ho, hok, ha', hM, hansM, hPair,
    hname, hI, hC, hv, hvec, hn', fun C j _ => ?_⟩
  rw [hvecEq, hfuns sps k6 k3 x t hsp hk6 hk3 hx ht]
  exact congrArg (fun m => First.K8.Honest.readAt (parOfMats m) t.funs.toList
    (cellsAtOf C (matsOwn G.W 24)) j) hmats.symm

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.VecPlanS
#print axioms ProofFile.Honest.K1.tieReadsS_vec
#print axioms ProofFile.Honest.K1.vecPlanS_of_layers
#print axioms ProofFile.Honest.K1.vecPlanS_of_head
