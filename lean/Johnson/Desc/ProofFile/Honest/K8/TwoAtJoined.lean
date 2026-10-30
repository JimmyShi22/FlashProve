-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/TwoAtJoined.lean: the honest side of the smallness test (K8): THE
RECORD `K8TwoAt` (Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) AT THE HEAD's LETTERS AND
THE JOINED SCRIPT, BUILT OF `tie_at_head` (Johnson/Desc/ProofFile/Honest/K8/TieAtHead.lean) AND
`zz_at_join_public` (Johnson/Desc/ProofFile/Honest/K8/ZzPublicAtHead.lean): so that Lean, and not
the eye, holds that the two ends are the record's two fields at one list of matrices. One theorem;
no definition.

`K8TwoAt` is exchanged here, not paid: for hsym (on the Script and the hidden input: the symbols'
clause), hsmall and hR (on the hidden input), each proved nowhere; for hopen (public), shown by
nobody yet; for F and hc on the joined lists and the book; for `K8Seated`, hOk, the opening and the
built segment. Behind a yes at which the second stop is silent. Equations on the Script.
NOT IN FRONT OF A LAW OVER COINS. At the digits' message's first sending alone.
Whoever quotes it at a book names hasCoins at that book beside it: hc is asked here. hsym and hsmall
are premises ON THE HIDDEN INPUT: in front of a sentence on hiding neither stands as a bare premise:
there it is had from Vd, by name, or the sentence says that its range is cut by a condition on the
trace. The like holds of hR.

  **`twoAt_at_join`**
The record's list of matrices is `K3.matsOwn Bs.G₀.W l`; `K8Seated` is asked at that list.
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. No letters are given at which the premises hold together. Counted nowhere.
The Limits of TieAtHead.lean and ZzPublicAtHead.lean are its own too. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TieAtHead
import Johnson.Desc.ProofFile.Honest.K8.ZzPublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open ProofFile.Honest.FirstThread (Others joinQ JoinFit lettersHead WtF coinsB byNo)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The record `K8TwoAt` at the head's letters and the joined Script, exchanged, not paid**: for
hsym, hsmall and hR, each proved nowhere, hopen, F, hc, `K8Seated`, hOk, the opening and the built
segment. Behind a yes at which the second stop is silent. At the digits' message's first sending
alone. Equations on the Script. NOT IN FRONT OF A LAW OVER COINS. Whoever quotes it
at a book names hasCoins at that book beside it. -/
theorem twoAt_at_join {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (S₀ : OnBytes.HonestTrace.Sz)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) (blk : Block S ProofFile.Cl) (cells : Tr → Cells)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr)) {seats : List (ℕ × ℕ)}
    (F : JoinFit cF.blocksInOrder 0 h.𝔇.arr seats wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) O)
    (hc : coinsB Bk (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
               wJobs (X := X) no Dd Zp Bs.G₀)) = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (hK : K8Seated (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l))
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace)
    (hopen : Item.tie l ∈ (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened
      (14 * l + (if l = 24 then 5 else 4) + 2))
    (hsym : ∀ k s m E ds y cols s' tl' e (z : ProofFile.InstPub),
      ThrS (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + (if l = 24 then 5 else 4) + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.Stepped blk k s m E ds y cols s' →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form
        (14 * l + (if l = 24 then 5 else 4) + 2 + 1) k s' y.2 →
      s'.tl? = some tl' →
      ∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l (z, s')
              ((lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
                (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                           wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
                w).thread.wit k m.st.input (m.st.heard ++ e)) (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m =>
              cellsAtOf (cells m.st.input.trace) (K3.matsOwn Bs.G₀.W l) μ i c) i' : ℤ) :
                Cb.Gl.E))
    (hsmall : ∀ v, v = w ∧ Vd v → ∀ μ i c,
      |cellsAtOf (cells v.trace) (K3.matsOwn Bs.G₀.W l) μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) :
    K8TwoAt (lettersHead h H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) :=
  { tie := tie_at_head h H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk hl O₁ e3 hK hopen hsym hsmall
    zz := zz_at_join_public h H test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk O₁ no S₀ Dd blk cells
      cellsQ tokQ wit own₀ O F hc hl e3 hK hR }

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.twoAt_at_join
