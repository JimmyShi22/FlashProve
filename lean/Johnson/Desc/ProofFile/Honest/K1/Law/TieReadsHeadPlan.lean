-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHeadPlan.lean: THE
SECOND EQUATION OF TiePlanS (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) AT THE THREAD's
OWN WITNESS's TABLE, AT ONE RUN, AT THE OUTPUT HEAD: THE VECTOR OF READS AT THE STATE's OWN TABLES,
AT THE BALANCED INTEGERS OF THE READER's OWN CELLS, READ THROUGH THE FILLER's OWN LIST matsOwn G.W
sg. One statement and its proof. No definition. The sister of tie_reads_layersP (TieReadsPlan.lean).

  tie_reads_headP   tie_reads_head (Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHead.lean) LESS
                    FIVE BINDERS (sg < 25 · hMarks · hParts · the trace T₀ · hcells); its end stands
                    at cellsAtOf (wit m.st.input).R.cells (matsOwn G.W sg)

MADE BY PROGRAM OFF THAT FILE's TEXT: the binders struck, the end's last term swapped, the proof's
last rewritings (hcells; planOwners_of_marks) struck; nothing else. That file keeps its own.

Limits. Those of TieReadsHead.lean, but for what has fallen. A law under "Stepped": it holds of
nothing at a book that does not cover the part's count. hmats (tl has the plan's matrices) and hfuns
(the state's tables are the filler's) are premises. Nothing on soundness, on completeness or on any
other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsHead
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (Reading HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt cellsAt_name)
open OnBytes.HonestTrace (seatsOf seatAt pairOf parOfMats)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats placeIn)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K5 (laidBack_covers)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}
variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **The vector of reads in the thread's own witness's table, at
the output head, at one run, at the balanced integers of the reader's own cells.** -/
theorem tie_reads_headP {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
    {gp : _root_.Desc.Plain.GPar} {l piece first : ℕ}
    (R : K1Seated L b blk wit (laterJobAt G.first gp l piece 1 first (lotData Sz₀ Z G)) own₀ sort
      arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr') X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr') X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (c : Cs (dueR (K1.parLater G.first gp l piece 1) (rideOf none)))
    (hc : lentCut k 0 ⟨(K1.parLater G.first gp l piece 1).place, 0⟩
      (dueR (K1.parLater G.first gp l piece 1) (rideOf none)) = some c)
    (n : ℕ) (hn : n < (K1.parLater G.first gp l piece 1).sent.size) (ds' : List Fmt.Drawn)
    (mm : ℕ)
    (hown : (L.N.group mm).contains
      (seatAtMember L.bs b (K1.parLater G.first gp l piece 1) n) = true)
    (p : K9.Part) (hp : K9.segAt? s' = some p) (tl : HTailF2) (c₀ : ℕ × String)
    (hc₀ : p.L.arrayOf[u3Of tl]? = some c₀) (a : ReqArray)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n))
    (hok : laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
      (p.d.st.placeBits (s.st.oracles.size + n) .main) = true)
    (hlen : G.first.codes.lengthsOk = true)
    (hne : (⟨(K1.parLater G.first gp l piece 1).place, 0⟩ : Addr) ≠ firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t ∨ seatAt (seatsOf Z G "U3") ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ =
        some t) → momentIs t 1 = true)
    (hap : apartOk Z G = true) {st : OnBytes.HonestTrace.Seat} (hs : st ∈ u3Seats Z G)
    (hsa : st.addr = ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true) {sg : ℕ} {nm : String}
    (ha' : arrayOf G.first.layout sg nm = some a) {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape sg a.message = some M) (hansM : M.shape.answers ≠ 0)
    (hPair : pairOf (u3Seats Z G) st.addr = some (sg, a.message)) (hname : a.name = "U3")
    (hsg : sg < G.first.shape.link.length) {SV : SegVals}
    (hv : valsAt Z G ((covOf Z G (wit m.st.input).x).toOption.getD default) sg = .ok SV)
    {vec : Cells → ℕ → OnBytes.E}
    (hvec : SV.vec (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) st.addr)) = .ok vec)
    (h3 : ((shapeAt (K1.parLater G.first gp l piece 1) n).mainDeg == 3) = true)
    {Y : OnBytes.Model.Stages.LinkH} (hY : G.built[sg]? = some Y) (hk : Y.kind = 2)
    (hI : 0 < a.sizeI) (hC : G.W.H.nU.getD 2 0 ≤ a.sizeC) (hmats : tl.mats = G.W.H.tl.mats)
    (hfuns : ∀ (sps : List Spot) (k6 k3 : Spot × ℕ) (x : OnBytes.Model.Head.Heard)
      (t : OnBytes.Model.Head.Tables), spotsOf Z.cuts = some sps →
      placeIn Z sps sg .K6 = .ok k6 → placeIn Z sps sg .K3 = .ok k3 →
      headHeardWholeAt (headParAt G) (Kinds.Head.requestOf Z.s₀) 0
        (k4LookOf G.W.HLy.fs k3.2
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) st.addr))) k6.2
        (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) st.addr)) = .ok x →
      ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
        ((covOf Z G (wit m.st.input).x).toOption.getD default) x = .ok t → tl.funs = t.funs)
    (z : P) :
    ∀ j < G.W.H.nU.getD 2 0,
      cellsAt (K1.parLater G.first gp l piece 1).codes arr ms L.N mm (z, s')
          (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) (u3Of tl) 0 j =
        Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf (wit m.st.input).R.cells (matsOwn G.W sg)) j) := by
  intro j hj
  obtain ⟨sps, hsp, hH⟩ := valsAt_head Z G _ hv hY hk
  obtain ⟨hn', k6, k3, x, t, hk6, hk3, hx, ht, hvecEq⟩ := head_vec Z G _ sps sg hH hvec
  obtain ⟨rp, hrp, -⟩ := laidBack_covers ok ha' hI (Nat.lt_of_lt_of_le hj hC)
  rw [cellsAt_name _ arr ms L.N mm z s' _ p hp (u3Of tl) c₀ hc₀ 0 j]
  refine (cell_is_u3 R Said hA hd hS hFits hNum c hc n hn ds' (L.N.group mm) hown p hp c₀ a 0 j rp
    ha ho hok hrp hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec Nat.one_pos
    (by rw [hn']; exact hj) h3).trans ?_
  rw [hvecEq, hmats, hfuns sps k6 k3 x t hsp hk6 hk3 hx ht]


end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tie_reads_headP
