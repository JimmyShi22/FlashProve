-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TwoAtFull.lean: the honest side of the smallness test (K8): THE RECORD `K8TwoAt`
(Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) AT THE HEAD's LETTERS AND THE JOINED SCRIPT
OF ALL THREE SENDERS OF THE FIRST CHAIN, AT THE BOOK THAT `onlineProverFromPublicFiles` RETURNS: `twoAt_at_join`
(Johnson/Desc/ProofFile/Honest/K8/TwoAtJoined.lean) WITH ITS TWO PREMISES ON THE JOINED LISTS AND
THE BOOK, F AND hc, LAID IN BY `joinFit_full` (AtFullSide/K2/JoinFitFull.lean). One theorem; no
definition.

`K8TwoAt` is exchanged here, not paid: for hsym (on the Script and the hidden input: the symbols'
clause), hsmall and hR (on the hidden input), each proved nowhere; for hopen (public: met in
AtFullSide/K8/TwoAtFullReads.lean by a law of other authors); for hA (`onlineProverFromPublicFiles` returns) and hJ (the
proximity test's job has six stages); for `K8Seated`, hOk, the opening and the built segment. Behind
a yes at which the second stop is silent. Equations on the Script. NOT IN FRONT OF A LAW OVER COINS.
At the digits' message's first sending alone. hsym and hsmall are premises ON THE
HIDDEN INPUT: in front of a sentence on hiding neither stands as a bare premise: there it is had
from Vd, by name, or the sentence says that its range is cut by a condition on the trace. The like
holds of hR.

  **`twoAt_full`**   the others' record O is the sum of the code switch's share and the proximity
                  test's (hO); F := `joinFit_full` at front 0 and the lot's own data; hc: from F's
                  field coins, job by job
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. THE LIMITS OF JoinFitFull.lean ARE ITS OWN: "fit" is a sentence on numbers,
seats, places and counts and on lots that agree: that a lot's text answers is not in it; of the book
it asks the shared sending's counts alone; the tree 77, the member 354 and hJ are fixed by hand or
assumed. That the head, the opening and hA can be met together is not said. The Limits of
TwoAtJoined.lean are its own too. Counted nowhere. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TwoAtJoined
import AtFullSide.K2.JoinFitFull

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
open ProofFile.Honest.FirstThread (TreeLot Others joinQ JoinFit lettersHead WtF coinsB byNo)
open ProofFile.Honest.K2.Law (joinFit_full)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
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
returns: exchanged, not paid**: for hsym, hsmall and hR, each proved nowhere, hopen, hA, hJ,
`K8Seated`, hOk, the opening and the built segment. Behind a yes at which the second stop is silent.
At the digits' message's first sending alone. Equations on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem twoAt_full {Xf Xa X₂ : Type} {P : OnlineProverParts W₀ Rc Tr Xf Xa} {A : OnlineProverWithDescription W₀ Rc Tr Xf Xa}
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
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) := by
  subst hO
  have F := joinFit_full (X := X) h O₁ hA no (K1.lotData S₀) Dd 0 wit own₀ Dk readers rest ch Jt hJ
    own₂ n₀ ok codes sh sh₁ rest₂
  exact twoAt_at_join h H test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk O₁ no S₀ Dd blk cells cellsQ
    tokQ wit own₀ _ F (List.all_eq_true.2 fun y hy => decide_eq_true (F.coins y hy)) hl e3 hK hR
    hopen hsym hsmall

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.twoAt_full
