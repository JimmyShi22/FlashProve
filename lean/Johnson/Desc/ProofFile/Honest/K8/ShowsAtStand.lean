-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ShowsAtStand.lean: the honest side of the smallness test (K8): AT
THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, AT EVERY SCRIPT AND EACH OF THE 25 SEGMENTS: (1) AT
THE THREAD's STAND IN FRONT OF THE DRAW THE LIBRARY's SENTENCE ON THE LAYOUT `ShowsAt`
(Johnson/P1K8R/SmallJoin.lean) HOLDS AT EVERY WITNESS; (2) SO "THE STAND FORM" hst, THE PREMISE OF
`hsym_of_stand` (Johnson/Desc/ProofFile/Honest/K8/SymOfStand.lean), TO ITS VERY TEXT, IS EXCHANGED
FOR "THE READS' FORM" hrd, IN WHOSE EQUATION NO STATE OF THE VERIFIER STANDS. Two theorems; no
definition.

hst is exchanged, not paid. hrd names the Script's witness and the hidden input and is proved
nowhere here: in front of a sentence on hiding it does not stand as a bare premise. An equation on
the Script. NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).

  `shows_at_stand` from the pair at the draw's number: the state is reached (`thrS_rchAt`), has not
                    failed (the thread's form) and passes the table's test on the book (the last
                    test of the thread's public form): so `shows_at_reach`
                    (Johnson/Desc/K8/Honest/ShowsAtReach.lean) speaks. On the verifier's state and
                    public data alone; the witness is a letter
  **`hst_of_reads`** hrd: at the pair, at every continuation e of the challenges, for each matrix μ
                    of the plan's record of segment l, each row r of its symbol array and each of
                    its columns c: the entry that `readAt` (Johnson/Desc/Sound/ReadAt.lean) reads
                    off the thread's witness, in the message of the plan's number, at the row and
                    place of the plan's seat (`seatC`), is the packed cell of the job's reader of
                    the input
The premises that stay beside hrd: the head, the ground, the built segment, l below 25, hOk, hb (the
draw's number is no greater than the chain's length) and hShape (`ShapesFit` of the record in each
state at which the thread stands: a sentence over states, and no evaluation of written data).
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath.
Tactics that search: `omega` on one line, on l.
Limits. Implications. No letters are given at which the premises hold together. Counted nowhere. The
full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.ShowsAtReach
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.HonestTrace.PackedJoins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz packedCells ShapesFit)
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT cellsAt readAt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (drawAt)
open VerifiableInference.Desc.First.K8.Honest (shows_at_reach)
open P1K8T (ShowsAt seatC)
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

/-- **The library's sentence on the layout at the thread's stand in front of a draw.** On the
verifier's state and public data alone; the witness is a letter. -/
theorem shows_at_stand {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hb : 14 * l + (if l = 24 then 5 else 4) + 2 ≤ cF.blocksInOrder.length) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) k s m E) (z : ProofFile.InstPub) (W : WtF) :
    ShowsAt Zp cF Z.lay l (z, s) W := by
  have hr0 := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w () hb
    ⟨hA.1, hOk _ _ _ hA.2⟩
  have hu : s.failed = none := Option.isNone_iff_eq_none.1 hA.1.2.2.1.1
  have hB : VerifiableInference.Desc.First.bookAt (P5J.At.N Zp cF)
      P5J.At.ps[14 * l + (if l = 24 then 5 else 4) + 2]? s = true := by
    rcases hA.1.2.2.1.2.2 with h' | h'
    · exact absurd hu h'
    · exact (Bool.and_eq_true_iff.1 h'.1).2
  rw [← P1K8T.drawAt_place] at hr0 hB
  have hS := shows_at_reach h hG (by omega : l ≤ 24) e3 m.st.input.x.pub s hr0 hu hB W
  exact hS

/-- **The stand form hst of `hsym_of_stand`, exchanged, not paid**: for hrd (on the Script's witness
and the hidden input: the reads' form), proved nowhere here, and hShape (a sentence over the states
at which the thread stands). No state of the verifier stands in hrd's equation.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem hst_of_reads {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hb : 14 * l + (if l = 24 then 5 else 4) + 2 ≤ cF.blocksInOrder.length)
    (S₀ : Sz) (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst)
    (hShape : ∀ k s m E tl,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      s.tl? = some tl → ShapesFit tl S₀ l)
    (hrd : ∀ k s m E e,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      ∀ (μ : Fin (Meaning.sizesOf (P5J.At.X Zp) l).NM) (r c : ℕ),
        r < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) l).m μ) →
        c < (Meaning.sizesOf (P5J.At.X Zp) l).k μ →
        readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
            ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
              (m.st.heard ++ e))
            (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells S₀ (wit m.st.input).R.cells.cell l μ r c)) :
    ∀ k s m E e (z : ProofFile.InstPub) tl,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      s.tl? = some tl →
      ∀ ν, ν < tl.NM → ∀ c, c < (S₀.packedShape l ν).2 → ∀ i', i' < (S₀.packedShape l ν).1 →
        cellsAt h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s)
            ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
              (m.st.heard ++ e)) (tl.gtTree.getD ν 0) i' c =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells S₀ (wit m.st.input).R.cells.cell l ν i' c) := by
  intro k s m E e z tl hA ht ν hν c hc i' hi'
  obtain ⟨eN, eM, hC⟩ := shows_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl hG e3 hb
    hA z ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
      (m.st.heard ++ e)) tl ht
  have eS := hShape k s m E tl hA ht ν hν
  have hν' : ν < (Meaning.sizesOf (P5J.At.X Zp) l).NM := by
    show ν < (Meaning.tlAt (P5J.At.X Zp) l).NM
    rw [← eN]
    exact hν
  have hi2 : i' < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) l).m ν) := by
    show i' < Alg.symRows (((Meaning.tlAt (P5J.At.X Zp) l).mats.getD ν {}).m)
    rw [← eM]
    have e1 : (S₀.packedShape l ν).1 = Alg.symRows (S₀.shapeNo l ν).1 := rfl
    rw [e1, eS] at hi'
    exact hi'
  have hc2 : c < (Meaning.sizesOf (P5J.At.X Zp) l).k ν := by
    show c < ((Meaning.tlAt (P5J.At.X Zp) l).mats.getD ν {}).k
    rw [← eM]
    have e2 : (S₀.packedShape l ν).2 = (S₀.shapeNo l ν).2 := rfl
    rw [e2, eS] at hc
    exact hc
  exact (hC ⟨ν, hν'⟩ i' c hi2 hc2).symm.trans (hrd k s m E e hA ⟨ν, hν'⟩ i' c hi2 hc2)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.shows_at_stand
#print axioms ProofFile.Honest.K8.hst_of_reads
