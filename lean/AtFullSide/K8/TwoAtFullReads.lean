-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TwoAtFullReads.lean: the honest side of the smallness test (K8): THE RECORD `K8TwoAt`
(Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) AT THE HEAD's LETTERS AND THE JOINED SCRIPT
OF ALL THREE SENDERS, AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS: `twoAt_full` (AtFullSide/K8/TwoAtFull.lean)
WITH hopen LAID IN AND hsym EXCHANGED FOR "THE READS' FORM" hrd, IN WHOSE EQUATION NO STATE OF THE
VERIFIER STANDS. One theorem; no definition.

`K8TwoAt` is exchanged here, not paid: for hrd (on the Script's witness and the hidden input), hOwn,
hsmall and hR (on the hidden input), each proved nowhere; for hShape (a sentence over the states at
which the thread stands; neither input nor Script is read in it); for hA (`onlineProverFromPublicFiles` returns) and hJ
(the proximity test's job has six stages); for `K8Seated`, hOk, the opening and the built segment.
Behind a yes at which the second stop is silent. Equations on the Script.
NOT IN FRONT OF A LAW OVER COINS. At the digits' message's first sending alone. hrd, hOwn, hsmall
and hR are premises on the hidden input: in front of a sentence on hiding none of them stands as a
bare premise: there it is had from Vd, by name, or the sentence says that its range is cut by a
condition on the trace.

  **`twoAt_full_reads`**   hopen := `head_tie_open`
                  (Johnson/Desc/ProofFile/Honest/K1/Law/TieOpenAtDraw.lean, of other authors), with
                  the draw's number turned by `drawAt_place` (Johnson/P1K8R/FillAt.lean) · hsym :=
                  `hsym_of_stand` (Johnson/Desc/ProofFile/Honest/K8/SymOfStand.lean) at hst :=
                  `hst_of_reads` (Johnson/Desc/ProofFile/Honest/K8/ShowsAtStand.lean) · hb: from the
                  field here of `K8Seated`
The sizes S₀ are the lot's own (`K1.lotData S₀`).
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. The Limits of TwoAtFull.lean, SymOfStand.lean and ShowsAtStand.lean are its
own too. No letters are given at which the premises hold together. Counted nowhere. The full size
alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.TwoAtFull
import Johnson.Desc.ProofFile.Honest.K8.SymOfStand
import Johnson.Desc.ProofFile.Honest.K8.ShowsAtStand
import Johnson.Desc.ProofFile.Honest.K1.Law.TieOpenAtDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (packedCells ShapesFit)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open ProofFile.Honest.FirstThread (TreeLot Others joinQ JoinFit lettersHead WtF coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P1K8T (seatC)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The record `K8TwoAt` at the joined Script of all three senders, at the book that `onlineProverFromPublicFiles`
returns: exchanged, not paid**: for hrd, hOwn, hsmall and hR, each proved nowhere, hShape, hA, hJ,
`K8Seated`, hOk, the opening and the built segment. Behind a yes at which the second stop is silent.
At the digits' message's first sending alone. Equations on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem twoAt_full_reads {Xf Xa X₂ : Type} {P : OnlineProverParts W₀ Rc Tr Xf Xa} {A : OnlineProverWithDescription W₀ Rc Tr Xf Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Said : ℕ → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (S₀ : OnBytes.HonestTrace.Sz)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) (blk : Block S ProofFile.Cl) (cells : Tr → Cells)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (Dk : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6) (own₂ : X₂)
    (n₀ : Nat) (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : O = (K2.switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ Dk readers rest).add
      (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (hK : K8Seated (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l))
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace)
    (hShape : ∀ k s m E tl,
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      s.tl? = some tl → ShapesFit tl S₀ l)
    (hOwn : ∀ v, v = w ∧ Vd v → K1.OwnersAgree S₀ (cells v.trace) (K3.matsOwn Bs.G₀.W l) l)
    (hrd : ∀ k s m E e,
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      ∀ (μ : Fin (Meaning.sizesOf (P5J.At.X Zp) l).NM) (r c : ℕ),
        r < Alg.symRows ((Meaning.sizesOf (P5J.At.X Zp) l).m μ) →
        c < (Meaning.sizesOf (P5J.At.X Zp) l).k μ →
        readAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
            ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
              (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                         wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit
              k m.st.input (m.st.heard ++ e))
            (seatC Zp l μ r c).1 false (seatC Zp l μ r c).2.1 (seatC Zp l μ r c).2.2 =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells S₀ (wit m.st.input).R.cells.cell l μ r c))
    (hsmall : ∀ v, v = w ∧ Vd v → ∀ μ i c,
      |cellsAtOf (cells v.trace) (K3.matsOwn Bs.G₀.W l) μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) :
    K8TwoAt (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) := by
  have hb : 14 * l + (if l = 24 then 5 else 4) + 2 ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hK.here).1
  have hopen := K1.head_tie_open h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
    (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
               wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w hl
  rw [P1K8T.drawAt_place] at hopen
  exact twoAt_full h H test carryX item n₁ n₂ b₀ Vd Rd Kp w hA hOk O₁ no S₀ Dd blk cells cellsQ
    tokQ wit own₀ Dk readers rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ O hO hl e3 hK hR hopen
    (hsym_of_stand h H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl O₁ e3 hK S₀ wit hR hShape hOwn
      (hst_of_reads h H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl O₁.blank e3 hb S₀ wit hShape
        hrd))
    hsmall

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.twoAt_full_reads
