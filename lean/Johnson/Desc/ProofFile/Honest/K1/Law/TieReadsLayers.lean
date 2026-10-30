-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsLayers.lean: THE SECOND
EQUATION OF TieRowsAt (Johnson/Desc/ProofFile/Honest/K1/Law/TieRowsCore.lean) AT THE THREAD's OWN
WITNESS, BEHIND THE READS' STEP, AT ONE RUN: FIRST AT ANY SEGMENT, FROM WHAT THE SEGMENT's VECTOR
IS; THEN AT A SEGMENT OF A GROUP OF LAYERS, UNDER NAMED PREMISES. Two statements and their proofs.
No definition.

  tie_reads_vec      AT ANY SEGMENT: where the maker's vector is readAt at the state's own record tl
                     (its sizes, its tables) and the cells read through matsOwn (hvecEq), and has nR
                     entries: for every j below nR the table of cells cellsAt of the thread's own
                     witness holds, in row 0 of the array of reads, entry j of readAt at tl and at
                     the cells cellsC G.W T₀ read through matsOf G.W sg
  tie_reads_layers   at a segment of the layers' sort: hvecEq is paid by valsAt_layers and
                     layers_vec (Johnson/Desc/ProofFile/Honest/K1/Law/U3ValLayers.lean) under hmats
                     and hfuns

tie_reads_vec IS tie_reads_head's JOIN (Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHead.lean)
WITHOUT THE HEAD's OWN TWO CALLS: that file keeps its own proof: it is not turned for this; at its
next touch it may call this one.

THE THREE PREMISES THAT CARRY THE WEIGHT AT LAYERS, MET BY NOBODY:
  hcells   the thread's reader of the input answers the trace's cells
  hmats    the state's record has the plan's list of matrices
  hfuns    THE STATE's TABLES ARE THE FILLER's: whatever funsOf returns at the points that the
           filler makes of what was heard in front of the sending is the state's record's list of
           tables

Limits. A law under "Stepped": it has the cut from the frame, and holds of nothing at a book that
does not cover the part's count. ONE RUN: not TieRowsS' form. THE FIRST EQUATION OF TieRowsAt IS NOT
HERE. No letters are given at which the premises hold together. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsU3
import Johnson.Desc.ProofFile.Honest.K1.Law.U3ValLayers
import Johnson.Desc.ProofFile.Honest.K1.Law.TieRowsCore
import Johnson.HonestTrace.PlanLabelsOfMarks
import Johnson.Desc.Sound.CellsAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (Reading HTailF2 HFun)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt cellsAt_name)
open OnBytes.HonestTrace (Tr seatsOf seatAt pairOf parOfMats cellsC matsOf PlanMarks PartsFit
  planOwners_of_marks)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats placeIn)
open OnBytes.Model.Layer (HPlan2 TableAsk TableAt layTables tableAsks funsOf)
open OnBytes.Desc.First.K4.Honest (ptsOf namedPts)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K5 (laidBack_covers)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}
variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **The vector of reads in the thread's own witness's table, at
any segment, from what the segment's vector is.** -/
theorem tie_reads_vec {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
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
    (hsg25 : sg < 25) (hMarks : PlanMarks G.W) (hParts : PartsFit G.W) (hI : 0 < a.sizeI) (nR : ℕ)
    (hnR : SV.n = nR) (hC : nR ≤ a.sizeC) (T₀ : Tr)
    (hcells : (wit m.st.input).R.cells = cellsC G.W T₀)
    (hvecEq : ∀ (C : Cells) (j : ℕ), vec C j =
      First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
        (cellsAtOf C (matsOwn G.W sg)) j)
    (z : P) :
    ∀ j < nR,
      cellsAt (K1.parLater G.first gp l piece 1).codes arr ms L.N mm (z, s')
          (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) (u3Of tl) 0 j =
        Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf (cellsC G.W T₀) (matsOf G.W sg)) j) := by
  intro j hj
  obtain ⟨rp, hrp, -⟩ := laidBack_covers ok ha' hI (Nat.lt_of_lt_of_le hj hC)
  rw [cellsAt_name _ arr ms L.N mm z s' _ p hp (u3Of tl) c₀ hc₀ 0 j]
  refine (cell_is_u3 R Said hA hd hS hFits hNum c hc n hn ds' (L.N.group mm) hown p hp c₀ a 0 j rp
    ha ho hok hrp hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec Nat.one_pos
    (by rw [hnR]; exact hj) h3).trans ?_
  rw [hvecEq, hcells, planOwners_of_marks hMarks hParts sg hsg25]

/-- **The same at a segment of a group of layers.** -/
theorem tie_reads_layers {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
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
    {Y : OnBytes.Model.Stages.LinkH} (hY : G.built[sg]? = some Y) (hk : Y.kind = 0)
    (hsg25 : sg < 25) (hMarks : PlanMarks G.W) (hParts : PartsFit G.W) (hI : 0 < a.sizeI)
    {hp₀ : HPlan2} (hG : G.W.G[Y.g]? = some hp₀) (hC : hp₀.nU.getD 2 0 ≤ a.sizeC) (T₀ : Tr)
    (hcells : (wit m.st.input).R.cells = cellsC G.W T₀) (hmats : tl.mats = hp₀.tl.mats)
    (hfuns : ∀ (sps : List Spot) (pl : HPlan2) (k4 k3 : Spot × ℕ)
      (x : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (funs : Array HFun),
      spotsOf Z.cuts = some sps → G.W.G[Y.g]? = some pl →
      placeIn Z sps sg .K4 = .ok k4 → placeIn Z sps sg .K3 = .ok k3 →
      layTables (OnBytes.Desc.First.K4.Honest.matsOf
          { P := G.W.layers, hp := pl, g := Y.g, link := sg, piece := k4.1.place.piece,
            r0 := k4.2, seg := sg }) (tableAsks G.W.layers.y G.W.layers.rd Y.g) 0 = some x →
      funsOf G.W.layers.y
        (ptsOf
          { P := G.W.layers, hp := pl, g := Y.g, link := sg, piece := k4.1.place.piece,
            r0 := k4.2, seg := sg }
          { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
            look := k4LookOf G.W.layers.y.fo k3.2 }
          (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) st.addr))).fo
        (namedPts
          { P := G.W.layers, hp := pl, g := Y.g, link := sg, piece := k4.1.place.piece,
            r0 := k4.2, seg := sg }
          (ptsOf
            { P := G.W.layers, hp := pl, g := Y.g, link := sg, piece := k4.1.place.piece,
              r0 := k4.2, seg := sg }
            { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[],
              look := k4LookOf G.W.layers.y.fo k3.2 }
            (m.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Z G) st.addr))))
        x.2.1 = some funs →
      tl.funs = funs)
    (z : P) :
    ∀ j < hp₀.nU.getD 2 0,
      cellsAt (K1.parLater G.first gp l piece 1).codes arr ms L.N mm (z, s')
          (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) (u3Of tl) 0 j =
        Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf (cellsC G.W T₀) (matsOf G.W sg)) j) := by
  obtain ⟨sps, hsp, hH⟩ := valsAt_layers Z G _ hv hY hk
  obtain ⟨pl, k4, k3, x, funs, hpl, hk4, hk3, hx, hn', hf, hvecEq⟩ :=
    layers_vec Z G sps sg Y.g hH hvec
  obtain rfl : hp₀ = pl := Option.some.inj (hG.symm.trans hpl)
  refine tie_reads_vec R Said hA hd hS hFits hNum c hc n hn ds' mm hown p hp tl c₀ hc₀ a ha ho hok
    hlen hne hmom hap hs hsa ok ha' hM hansM hPair hname hsg hv hvec h3 hsg25 hMarks hParts hI _
    hn' hC T₀ hcells ?_ z
  intro C j
  rw [hvecEq, hmats, hfuns sps _ k4 k3 x funs hsp hpl hk4 hk3 hx hf]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tie_reads_vec
#print axioms ProofFile.Honest.K1.tie_reads_layers
