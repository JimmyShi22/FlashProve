-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SymOfStand.lean: the honest side of the smallness test (K8): THE
PREMISE hsym OF `tie_at_head` (Johnson/Desc/ProofFile/Honest/K8/TieAtHead.lean), TO ITS VERY TEXT,
AT EVERY ONE OF THE 25 SEGMENTS AND AT EVERY SCRIPT, EXCHANGED FOR "THE STAND FORM" hst AND THREE
PREMISES BESIDE IT. One theorem; no definition.

hsym is exchanged, not paid. hst, hOwn and hR name the hidden input and are proved nowhere here: in
front of a sentence on hiding none of them stands as a bare premise. Behind a yes at which the
second stop is silent. hst is an equation on the Script.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).

  **`hsym_of_stand`**
The premises. hst, ON THE SCRIPT AND THE HIDDEN INPUT: AT THE STAND in front of the draw, at every
continuation of the challenges: inside the packed shape of each matrix of the state's record the
library's table `cellsAt` of the thread's witness holds, in the matrix's symbol array, the packed
cells of the job's reader of the input: the form in which `tie_mat_first`
(Johnson/Desc/ProofFile/Honest/K1/Law/TieMatFirst.lean) ends at segment 0. hShape
speaks of the record that the verifier's state holds wherever the thread stands at the draw's
number; neither the input nor the Script is read in it; it is a sentence over all such states, and
no evaluation of written data: the sizes S₀ give the segment's matrices that record's rows and
columns (`ShapesFit`, Johnson/HonestTrace/PackedJoins.lean). hOwn, on the hidden
input: a borrowed matrix's cells are its owner's (`OwnersAgree`,
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanWide.lean). hR, on two readers of the
hidden input. The head, the opening, the built segment, hOk and `K8Seated` stay too.
How. The draw's yes turns no cell of the table `cellsAhead` (`cellsAhead_putTl`) and two fields of
the record that none of these reads. At a symbol array `cellsAhead` is `cellsAt` (`cellsAhead_sent`,
with `msgNow_of_named` at `early_sym`); the premises on the state as in TieAtHead.lean. From packed
cells to the library's packing: `readsPacked_of_cells_wide` and `packedBy_iff`
(Johnson/HonestTrace/PackedTie.lean).
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches.
Limits. An implication. No letters are given at which the premises hold together. Counted nowhere.
It stands over files of two other houses that are on no row. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TieAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanWide
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz packedCells ShapesFit PackedBy packedBy_iff)
open OnBytes.Tie.Pv.Tail.Port (early_sym)
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT cellsAt)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (cellsAhead cellsAhead_putTl cellsAhead_sent msgNow_of_named
  putTl_tl)
open VerifiableInference.Desc.First.K8.Ready (cond_of_front planFitsAllB)
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K1 (OwnersAgree readsPacked_of_cells_wide)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script thrS_rchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The premise hsym of `tie_at_head`, exchanged, not paid**: for hst (on the Script and the
hidden input: the stand form), hOwn and hR (on the hidden input), each proved nowhere here, and
hShape (a sentence over the states at which the thread stands); the head, the opening, the built
segment, hOk and `K8Seated` stay too. Behind a yes at which the second stop is silent.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem hsym_of_stand {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {blk : Block S ProofFile.Cl} {cells : Tr → Cells}
    {mats : List (Nat × String × Nat)}
    (hK : K8Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells (ProofFile.k8Par Zp Bs.G₀ Xl l, mats))
    (S₀ : Sz) (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst)
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace)
    (hShape : ∀ k s m E tl,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      s.tl? = some tl → ShapesFit tl S₀ l)
    (hOwn : ∀ v, v = w ∧ Vd v → OwnersAgree S₀ (cells v.trace) mats l)
    (hst : ∀ k s m E e (z : ProofFile.InstPub) tl,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      s.tl? = some tl →
      ∀ ν, ν < tl.NM → ∀ c, c < (S₀.packedShape l ν).2 → ∀ i', i' < (S₀.packedShape l ν).1 →
        cellsAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s)
            ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
              (m.st.heard ++ e)) (tl.gtTree.getD ν 0) i' c =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells S₀ (wit m.st.input).R.cells.cell l ν i' c)) :
    ∀ k s m E ds y cols s' tl' e (z : ProofFile.InstPub),
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' →
      ∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
              ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
                (m.st.heard ++ e)) (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m =>
              cellsAtOf (cells m.st.input.trace) mats μ i c) i' : ℤ) : Cb.Gl.E) := by
  intro k s m E ds y cols s' tl' e z hA hd hS hF ht
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have hr0 := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ()
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hK.here).1) ⟨hA.1, hOk _ _ _ hA.2⟩
  have hV : m.st.input = w ∧ Vd m.st.input := hA.1.2.2.2.2.2.2
  -- the state in front of the draw
  obtain ⟨tlN, Lk, htN, hLk, hN⟩ := P1K8S.namedB_of_reach h.scope h.reads O₁ h.laid.planOk
    (P5J.namesDoorB_at_head h) hx e3 ((m.st.input.x.pub, s), ()) hr0
  obtain ⟨Fk, hFk⟩ := Q38.fork_of_link s Lk hLk
  obtain ⟨-, -, -, -, s₀, cols₀, hbeg, -, hfold⟩ := hA.1.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hfold
  have hW : planFitsAllB Bs.G₀.W = true := by
    rw [O₁.W]
    exact h.k8_planFits
  obtain ⟨tlF, htF, -, -, hgt, -⟩ := cond_of_front
    (P1K8S.front_at_place h.scope h.reads O₁ (P1K8S.planFitsAll_of_test hW) hx _ _ _ _ hfold)
  obtain rfl : tlN = tlF := Option.some.inj (htN.symm.trans htF)
  -- behind the draw's yes
  obtain ⟨tl, cf, first, h1, -, -, -, -, es⟩ := keeps_of_stepped hK hS
  obtain rfl : tlN = tl := Option.some.inj (htN.symm.trans h1)
  have et : tl' = { tlN with cfF := cf, cfFirst := first } := by
    rw [es, putTl_tl s tlN _ htN] at ht
    exact (Option.some.inj ht).symm
  have eA : (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s') : WtF → ℕ → ℕ → ℕ → Cb.Gl.E) =
      cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (m.st.input.x.pub, s) := by
    funext W
    rw [es, cellsAhead_putTl h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l z s tlN _ htN W]
    rfl
  subst et
  have hP : PackedBy { tlN with cfF := cf, cfFirst := first }
      (cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ e)))
      (cellsAtOf (cells m.st.input.trace) mats) :=
    (packedBy_iff _ _ _).2 (readsPacked_of_cells_wide
      (show ShapesFit { tlN with cfF := cf, cfFirst := first } S₀ l from
        hShape k s m E tlN hA htN)
      (cells m.st.input.trace) mats (hOwn _ hV) _ fun ν hν c hc i' hi' => by
        obtain ⟨o, ho⟩ := msgNow_of_named hN
          (early_sym (tl := tlN) (Nat.lt_of_lt_of_le hν hgt) i' c)
        rw [eA]
        show cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (m.st.input.x.pub, s) _
          (tlN.gtTree.getD ν 0) i' c = _
        rw [cellsAhead_sent h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l m.st.input.x.pub s _ hLk hFk htN ho i' c,
          hst k s m E e m.st.input.x.pub tlN hA htN ν hν c hc i' hi', hR _ hV])
  exact hP

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.hsym_of_stand
