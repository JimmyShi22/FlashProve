-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieMatPlan.lean: THE FIRST
EQUATION OF TiePlanS (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) AT THE THREAD's OWN
WITNESS's TABLE, AT THE FIRST SEGMENT, AT ONE MATRIX: THE PACKED CELLS, AT ANY SIZES Sz₀, OF THE
READER's OWN CELLS. One statement and its proof. No definition.

  tie_mat_firstP   tie_mat_first (Johnson/Desc/ProofFile/Honest/K1/Law/TieMatFirst.lean) WITH A
                   LETTER Sz₀ FOR Sz.ref (in the opening's job too), LESS TWO BINDERS (the trace T₀
                   · hcells); its end stands at packedCells Sz₀ (wit m.st.input).R.cells.cell 0 ν

MADE BY PROGRAM OFF THAT FILE's TEXT: the letter for the constant, the two binders struck, the end's
last term swapped, the proof's last rewriting (hcells) struck; nothing else. That file keeps its
own.

Limits. Those of TieMatFirst.lean, but for what has fallen. The data stand at nothing seen. Nothing
on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt cellsAt_name)
open OnBytes.HonestTrace (Sz packedCells)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}
variable {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b₀ : Nat}
  {blk₀ : Block S Cl} {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- **The packed cells of one matrix of the first segment in the
thread's own witness's table, at any border not in front of the opening's: AT ANY SIZES, AT THE
READER's OWN CELLS.** The data stand at
nothing seen; that the part's data at what it had seen are the same: heardOnly, not spent here. -/
theorem tie_mat_firstP {Sz₀ : Sz} {Z : Pub} {G : Ground} {gp : _root_.Desc.Plain.GPar} {first : ℕ}
    (R₀ : K1Seated L b₀ blk₀ wit
      (placeJob (K1.firstPar G.first gp) first (firstFold G.first) (lotData Sz₀ Z G)) own₀ sort
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
    (hz : (cellsVals Sz₀).size 0 a.name = some (Sz₀.packedShape 0 ν))
    (hI : (Sz₀.packedShape 0 ν).1 ≤ a.sizeI) (hC : (Sz₀.packedShape 0 ν).2 ≤ a.sizeC) :
    ∀ c, c < (Sz₀.packedShape 0 ν).2 → ∀ i', i' < (Sz₀.packedShape 0 ν).1 →
      cellsAt (K1.firstPar G.first gp).codes arr ms L.N mm (z, s')
          (L.Q.wit k m.st.input (m.st.heard ++ e)) (tl.gtTree.getD ν 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E
          (packedCells Sz₀ (wit m.st.input).R.cells.cell 0 ν i' c) := by
  intro c hc i' hi'
  obtain ⟨r, j, hrp, -⟩ := once_and_back_msg hfit ha' (Nat.lt_of_lt_of_le hi' hI)
    (Nat.lt_of_lt_of_le hc hC)
  have hval := first_val Sz₀ Z G (wit m.st.input).x (wit m.st.input).R
    ((m.st.heard ++ e).take (L.thread.front + roundsTo L.bs b₀)) t1 hfit ha' hrp hmu hz ⟨hi', hc⟩
  have hlays : (firstFill Sz₀ G.first).lays ⟨firstAddr, n⟩ r j = true := by
    have q := hval
    rw [data_first] at q
    exact at_lays _ _ _ _ _ _ _ q
  obtain ⟨hr, hj, hpad, hans⟩ := first_lays_room Sz₀ G.first gp hlen n r j hlays
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
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tie_mat_firstP
