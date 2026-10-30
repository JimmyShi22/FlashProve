-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieMatFirst.lean: THE FIRST
EQUATION OF TieRowsAt (Johnson/Desc/ProofFile/Honest/K1/Law/TieRowsCore.lean) AT THE THREAD's OWN
WITNESS, AT THE FIRST SEGMENT, AT ONE OF ITS MATRICES, AT ANY BORDER NOT IN FRONT OF THE OPENING's:
UNDER NAMED PREMISES. One statement and its proof. No definition.

  tie_mat_first   under the kind's record K1Seated at the opening's member b₀ and the lot's own job
                  and data there; the pair at a border b₁ with b₀ ≤ b₁; any continuation e of the
                  challenges; a state with an open part p at which the five facts on message o hold:
                  for every (i', c) inside the packed shape of matrix ν of segment 0 the table of
                  cells cellsAt of the thread's own witness holds, in the matrix's array, the packed
                  cells of cellOf G.W T₀

THE JOIN, NINE CALLS: once_and_back_msg (Law/LaidOnce.lean: the layout's rule answers inside the
array's size) · first_val (K1/Law/FirstIsPacked.lean) · data_first (K1/LotData.lean) · at_lays
(K1/AgreeTools.lean) · first_lays_room (K1/FirstOffPad.lean): SO THE FOUR PREMISES ON THE ROW AND
PLACE OF cell_later ARE PAID HERE · K1Seated.cut (K1/SeatedLaw.lean): THE CUT, OFF THE RECORD's
FIELD hasCoins, BY NAME · roundsTo_mono (Thread/ScriptFit.lean) · cellsAt_name
(Johnson/Desc/Sound/CellsAtName.lean) · cell_later (K1/Law/CellLater.lean). Paths under
Johnson/Desc/ProofFile/Honest/ where no folder is named.

WHAT IS LEFT AS PREMISES. THE ONE THAT CARRIES THE WEIGHT, MET BY NOBODY: hcells: the thread's
reader of the input answers the trace's cells. On the state (public): hp, hc₀, ha, ho, hok, hown and
the five facts hcodes, hx, hxs, hpl, hseat. On public data: hlen · t1, hfit, ha' (the opening's seat
names the array's message; it fits; the array lies in it) · hmu (the array's name reads as ν) · hz,
hI, hC (the values' size is the packed shape; the layout's array is as large). THE FILLING's SIZES
ARE Sz.ref: written into the job.

Limits. NO CHALLENGE AND NO TABLE IS NAMED: the first equation has no like of "the state's tables
are the filler's". ONE MATRIX, ONE RUN: not TieRowsS' form. THE FIRST SEGMENT ALONE: at the other 24
the arrays stand in another kind's sending. The data stand at nothing seen (cell_later's Limits). No
letters are given at which the premises hold together. Nothing on soundness, on completeness or on
any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.CellLater
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstIsPacked
import Johnson.Desc.ProofFile.Honest.K1.Law.TieRowsCore
import Johnson.Desc.ProofFile.Honest.K1.FirstOffPad
import Johnson.Desc.ProofFile.Honest.Law.LaidOnce
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit
import Johnson.Desc.Sound.CellsAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt cellsAt_name)
open OnBytes.HonestTrace (Tr Sz cellsC cellOf packedCells)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}
variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b₀ : Nat}
  {blk₀ : Block S Cl} {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **The packed cells of one matrix of the first segment in the
thread's own witness's table, at any border not in front of the opening's.** The data stand at
nothing seen; that the part's data at what it had seen are the same: heardOnly, not spent here. -/
theorem tie_mat_first {Z : Pub} {G : Ground} {gp : _root_.Desc.Plain.GPar} {first : ℕ}
    (R₀ : K1Seated L b₀ blk₀ wit
      (placeJob (K1.firstPar G.first gp) first (firstFold G.first) (lotData Sz.ref Z G)) own₀ sort
      arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr') X → Prop) {b₁ : ℕ} (hb : b₀ ≤ b₁)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc ProofFile.Inst Tr') X} {E : Env}
    (hA : ThrS L.thread Said b₁ k s m E) (e : List Fmt.Drawn) (s' : S) (z : P) (mm : ℕ) (n : ℕ)
    (hn : n < (K1.firstPar G.first gp).sent.size)
    (hown : (L.N.group mm).contains (seatAtMember L.bs b₀ (K1.firstPar G.first gp) n) = true)
    (p : K9.Part) (hp : K9.segAt? s' = some p) (o : ℕ)
    (hcodes : p.d.st.codes = (K1.firstPar G.first gp).codes) (x : _)
    (hx : p.d.st.oracles[o]? = some x) (hxs : x.shape = shapeAt (K1.firstPar G.first gp) n)
    (hpl : p.d.book.place[o]? = some (seatAtMember L.bs b₀ (K1.firstPar G.first gp) n))
    (hseat : Sound.seatBy Sound.noFirst p.d.book o =
      some (seatAtMember L.bs b₀ (K1.firstPar G.first gp) n))
    (tl : HTailF2) (ν : ℕ) (c₀ : ℕ × String)
    (hc₀ : p.L.arrayOf[tl.gtTree.getD ν 0]? = some c₀) (a : ReqArray)
    (ha : reqArray p.L.check.rows.layout c₀.1 c₀.2 = some a)
    (ho : p.L.check.frame.whereIs c₀.1 a.message = some o)
    (hok : laidMatrixOk a (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true)
    (hlen : G.first.codes.lengthsOk = true)
    (t1 : firstSeat G.first.shape 0 ⟨firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha' : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message)
    (hmu : labelNo a.name = some ν)
    (hz : (cellsVals Sz.ref).size 0 a.name = some (Sz.ref.packedShape 0 ν))
    (hI : (Sz.ref.packedShape 0 ν).1 ≤ a.sizeI) (hC : (Sz.ref.packedShape 0 ν).2 ≤ a.sizeC)
    (T₀ : Tr) (hcells : (wit m.st.input).R.cells = cellsC G.W T₀) :
    ∀ c, c < (Sz.ref.packedShape 0 ν).2 → ∀ i', i' < (Sz.ref.packedShape 0 ν).1 →
      cellsAt (K1.firstPar G.first gp).codes arr ms L.N mm (z, s')
          (L.Q.wit k m.st.input (m.st.heard ++ e)) (tl.gtTree.getD ν 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf G.W T₀) 0 ν i' c) := by
  intro c hc i' hi'
  obtain ⟨r, j, hrp, -⟩ := once_and_back_msg hfit ha' (Nat.lt_of_lt_of_le hi' hI)
    (Nat.lt_of_lt_of_le hc hC)
  have hval := first_val Sz.ref Z G (wit m.st.input).x (wit m.st.input).R
    ((m.st.heard ++ e).take (L.thread.front + roundsTo L.bs b₀)) t1 hfit ha' hrp hmu hz ⟨hi', hc⟩
  have hlays : (firstFill Sz.ref G.first).lays ⟨firstAddr, n⟩ r j = true := by
    have q := hval
    rw [data_first] at q
    exact at_lays _ _ _ _ _ _ _ q
  obtain ⟨hr, hj, hpad, hans⟩ := first_lays_room Sz.ref G.first gp hlen n r j hlays
  obtain ⟨cut, hcut⟩ := R₀.cut k
  have hlenH : m.st.heard.length = L.thread.front + roundsTo L.bs b₁ := by
    have q := drawsFit_length _ _ hA.1.2.1
    rw [q, List.length_append]
    rfl
  have hN : L.thread.front + roundsTo L.bs b₀ ≤ (m.st.heard ++ e).length := by
    have q := roundsTo_mono L.bs b₀ b₁ hb
    rw [List.length_append, hlenH]
    omega
  rw [cellsAt_name _ arr ms L.N mm z s' _ p hp (tl.gtTree.getD ν 0) c₀ hc₀ i' c]
  refine (cell_later R₀ k cut hcut m.st.input hA.1.2.2.2.2.2.2 (m.st.heard ++ e) hN n hn
    (L.N.group mm) hown p o hcodes x hx hxs hpl hseat c₀ a i' c (r, j) ha ho hok hrp hr hj hans
    hpad hval).trans ?_
  show algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (wit m.st.input).R.cells.cell 0 ν i' c) = _
  rw [hcells]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tie_mat_first
