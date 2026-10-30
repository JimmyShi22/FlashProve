-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/CellIsU3.lean: THE SHARED
"SENDING" (the kind K1) AT A SEGMENT's READS, AT THE LOT's OWN JOB AND DATA: BEHIND THE MEMBER's
STEP, A CELL THAT THE LIBRARY's ONE ACCESSOR READS OFF THE THREAD's OWN WITNESS AT THE ARRAY "U3" IS
THE ENTRY OF THE VECTOR THAT THE SEGMENT's MAKER RETURNS AT THE READER's CELLS. One statement and
its proof. No definition.

  cell_is_u3   under the kind's record K1Seated at the job laterJobAt ... 1 ... (lotData S Z G), the
               pair, the draws' fit and the member's step, at every continuation of the challenges:
               (dataQ own p (seatTab ...)).cell at the element (i, cc) of "U3" =
               Reading.gl.val (vec R.cells cc)

THE JOIN, SIX CALLS: u3_size_at and u3_val_at (K1/Law/U3ValHead.lean) · lot_val_reads
(K1/Law/LotAtReads.lean) · at_lays (K1/AgreeTools.lean) · later_lays_room (K1/LaterOffPad.lean): SO
THE FOUR PREMISES ON THE ROW AND PLACE OF cell_is_val (the row and the place lie in the sender's
shape; the message has a sample; off the pad) ARE PAID HERE, off "the data answers there" ·
cell_is_val (K1/Law/CellIsVal.lean). All paths under Johnson/Desc/ProofFile/Honest/.

WHAT IS LEFT AS PREMISES. On the state behind (public): as in cell_behind: hp, ha, ho, hok, hown,
hFits, hNum. On public data: hlen, hne, hmom (later_lays_room's) · hap, hs, hsa (the seat of "U3" at
the job's message n) · ok, ha', hM, hansM, hA, hname (the layout's array "U3", its message, the
seat's pair) · hsg, hv (the segment's maker accepts) · h3 (the message's main rows stand over the
extension field). On the challenges heard: hvec (the maker's vec accepts them). On the layout: hrp.
On the element: hi, hcc.

Limits. A law under "Stepped": it has the cut from the frame, and holds of nothing at a book that
does not cover the part's count. No letters are given at which the premises hold together. What vec
is: at the head: head_vec (K1/Law/U3ValHead.lean); not joined here. ha (the state's layout) and ha'
(the ground's layout) name one array a under two layouts: nothing here says that these are one
layout. sg (the seat's segment) and l (the job's link) are two letters: nothing here ties them.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.CellIsVal
import Johnson.Desc.ProofFile.Honest.K1.Law.LotAtReads
import Johnson.Desc.ProofFile.Honest.K1.Law.U3ValHead
import Johnson.Desc.ProofFile.Honest.K1.LaterOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem dataQ seatTab)
open OnBytes.HonestTrace (seatsOf seatAt pairOf)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats u3ValsOf)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr X P Cells' Tok : Type}
variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr X P Cells' Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **Behind the reads' step a cell of the thread's own witness at
"U3" is the entry of the vector that the segment's maker returns.** -/
theorem cell_is_u3 {Sz₀ : OnBytes.HonestTrace.Sz} {Z : Pub} {G : Ground}
    {gp : _root_.Desc.Plain.GPar} {l piece first : ℕ}
    (R : K1Seated L b blk wit (laterJobAt G.first gp l piece 1 first (lotData Sz₀ Z G)) own₀ sort
      arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {k : Coins Bk} {s s' : S}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hA : ThrS L.thread Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hS : L.thread.Stepped blk k s m E ds y cols s') (hFits : Book.BookFits s'.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z)
    (c : Cs (dueR (K1.parLater G.first gp l piece 1) (rideOf none)))
    (hc : lentCut k 0 ⟨(K1.parLater G.first gp l piece 1).place, 0⟩
      (dueR (K1.parLater G.first gp l piece 1) (rideOf none)) = some c)
    (n : ℕ) (hn : n < (K1.parLater G.first gp l piece 1).sent.size) (ds' : List Fmt.Drawn)
    (own : List (ℕ × ℕ))
    (hown : own.contains (seatAtMember L.bs b (K1.parLater G.first gp l piece 1) n) = true)
    (p : K9.Part) (hp : K9.segAt? s' = some p) (c₀ : ℕ × String) (a : ReqArray) (i cc : ℕ)
    (rp : ℕ × ℕ) (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some (s.st.oracles.size + n))
    (hok : laidMatrixOk a (p.d.st.rowBits (s.st.oracles.size + n) .main)
      (p.d.st.placeBits (s.st.oracles.size + n) .main) = true)
    (hrp : laidAt a i cc = some rp) (hlen : G.first.codes.lengthsOk = true)
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
    (hi : i < 1)
    (hcc : cc < SV.n) (h3 : ((shapeAt (K1.parLater G.first gp l piece 1) n).mainDeg == 3) = true) :
    (dataQ own p (seatTab (K1.parLater G.first gp l piece 1).codes arr ms
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).cell c₀.1 c₀.2 i cc =
      Reading.gl.val (vec (wit m.st.input).R.cells cc) := by
  have hz : (u3ValsOf Z G (wit m.st.input).x).size sg a.name = some (1, SV.n) := by
    rw [hname]
    exact u3_size_at Z G _ hsg hv
  have hval := lot_val_reads Sz₀ Z G (wit m.st.input).x hap hs ok ha' hrp hM hansM hPair hz hi hcc
    (wit m.st.input).R m.st.heard
  have hval' : (lotData Sz₀ Z G (wit m.st.input).x).at_ (wit m.st.input).R m.st.heard
      ⟨⟨(K1.parLater G.first gp l piece 1).place, 0⟩, n⟩ rp.1 rp.2 =
      some (.inr (Reading.gl.val (vec (wit m.st.input).R.cells cc))) := by
    rw [← hsa, hval]
    exact congrArg some (u3_val_at Z G _ hsg hv hvec _ _ _ _)
  obtain ⟨hr, hj, hpad, hans⟩ := later_lays_room Sz₀ Z G _ gp l piece 1 n hlen hne hmom
    (at_lays _ _ _ _ _ _ _ hval')
  refine (cell_is_val R Said hA hd hS hFits hNum c hc n hn ds' own hown p hp c₀ a i cc rp ha ho
    hok hrp hr hj hans hpad hval').trans ?_
  show dataE ((shapeAt (K1.parLater G.first gp l piece 1) n).mainDeg == 3) _ = _
  rw [h3]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.cell_is_u3
