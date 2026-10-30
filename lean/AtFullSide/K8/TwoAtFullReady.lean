-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TwoAtFullReady.lean: the honest side of the smallness test (K8): THE RECORD `K8TwoAt`
(Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) AT EACH OF THE 25 SEGMENTS, AS
`twoAt_full_owners` (AtFullSide/K8/TwoAtFullOwners.lean) HAS IT, AT A FILLING AT WHICH
`ReadyLaws` HOLDS: THREE OF ITS PREMISES ON THE HIDDEN INPUT, hOwn, hsmall AND hBor, ARE HAD FROM Vd, WHICH
IS `ReadyInput`: BY NAME. One theorem; no definition.

`K8TwoAt` is exchanged here, not paid. ON THE HIDDEN INPUT ONE PREMISE STAYS BESIDE Vd: hR (at a
valid input the reader of the letter wit yields the input's trace as its cells), proved nowhere: in
front of a sentence on hiding it does not stand as a bare premise. `ReadyInput` ITSELF IS A
CONDITION ON THE HIDDEN INPUT (the instance passes `okStart`; the index is in range; the trace is
the prover's own at the index and the instance): IT CUTS THE RANGE OF INPUTS, AND NO INPUT IS SHOWN
HERE TO MEET IT: where none does, the record holds for nothing. The others that stay: hA (`onlineProverFromPublicFiles`
returns), hT (`ReadyLaws`: its holder is the trace's), hV, hJ, `K8Seated`, hOk, the opening, the built
segment, and from segment 1 on hD (the light test at the reads' filling says yes at each instance
that passes `okStart`), proved by nobody. Behind a yes at which the second stop is silent. Equations
on the Script. NOT IN FRONT OF A LAW OVER COINS. At the messages' first sending
alone.

  **`twoAt_full_ready`**   at Tr := `Cells`, cells := `id`. From Vd at v:
                  the named premise `ReadyLaws` (AtFullSide/K8/LawsAtIndex.lean):
                  the input's trace is the reader of cells at the model's own trace, with
                  `MeetsAll`, `BorrowedSame`, `NamesFit`, `PartsFit`, `PlanMarks`;
                  the opening's fields pub and W: the maker's public part is the head's;
                  `planOwners_of_marks` (Johnson/HonestTrace/PlanLabelsOfMarks.lean, of other
                  authors). Then hOwn := `own_of_trace`, hsmall := `small_of_trace`
                  (Johnson/Desc/ProofFile/Honest/K8/InputAtTrace.lean), hBor := `bor_of_trace`
                  (Johnson/Desc/ProofFile/Honest/K8/BorrowedAtTrace.lean) behind hR
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. The Limits of the files that it calls are its own too. Through
ReadyAtFullIn.lean it stands over files under Johnson/Goal/ (HonestTrace/ServesAtOfGoal.lean,
HonestTrace/PlanMarksInScope.lean, and what these two import there): it names none of the library's
goals and calls none. NOT SAID: that an honest prover's Script is the joined one; that the thread
ever reaches one of the draws' numbers; that any instance passes `okStart`; that `onlineProverFromPublicFiles` returns.
No letters are given at which the premises hold together. Counted nowhere. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.TwoAtFullOwners
import Johnson.Desc.ProofFile.Honest.K8.InputAtTrace
import Johnson.Desc.ProofFile.Honest.K8.BorrowedAtTrace
import AtFullSide.K8.LawsAtIndex
import Johnson.HonestTrace.PlanLabelsOfMarks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz packedCells cellsC theTrace MeetsAll BorrowedSame NamesFit PartsFit
  planOwners_of_marks)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open ProofFile.Honest.FirstThread (TreeLot Others joinQ lettersHead WtF byNo)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Rc X₀ X : Type}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Cells)

/-- **The record `K8TwoAt` at each of the 25 segments, at a filling whose trace is `fullIn`'s:
exchanged, not paid**: hOwn, hsmall and hBor are had from Vd, which is `ReadyInput`, by name; on the
hidden input hR stays beside Vd, proved nowhere; hD from segment 1 on, proved by nobody; hA, hT, hV,
hJ, `K8Seated`, hOk, the opening and the built segment. `ReadyInput` cuts the range of inputs, and
no input is shown here to meet it. Behind a yes at which the second stop is silent. At the messages'
first sending alone. Equations on the Script. NOT IN FRONT OF A LAW OVER COINS. -/
theorem twoAt_full_ready {X₂ : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hT : ReadyLaws (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A)
    (hV : Vd = ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
    {Said : ℕ → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Cells) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) (blk : Block S ProofFile.Cl)
    (cellsQ : Local W₀ Rc ProofFile.Inst Cells → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Cells → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Cells)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Cells) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂)
    (n₀ : Nat) (ok : Local W₀ Rc ProofFile.Inst Cells → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Cells))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Cells))
    (hO : O = (K2.switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R) rest).add
      (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (hK : K8Seated (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk id
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l))
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = v.trace)
    (hD : 1 ≤ l → ∀ ξ, (P5J.F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
      K2.Law.ReadsLight Zp Bs.G₀ ξ) :
    K8TwoAt (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk id
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) := by
  have hpub : A.Z = Zp ∧ Bs.G₀.W = Zp.p.X :=
    ⟨Except.ok.inj ((ProofFile.Honest.atPure_ok hA).1.symm.trans O₁.pub), O₁.W⟩
  have key : ∀ v, v = w ∧ Vd v → ∃ (i : Cm.Idx) (ξ : Instance ppref) (T : OnBytes.HonestTrace.Tr),
      v.trace = cellsC Bs.G₀.W T ∧ MeetsAll Bs.G₀.W i ξ T ∧ BorrowedSame Bs.G₀.W T ∧
        NamesFit Bs.G₀.W T ∧ PartsFit Bs.G₀.W ∧ K3.PlanOwners Bs.G₀.W := by
    intro v hv
    have hv' : ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H v := by
      rw [← hV]
      exact hv.2
    obtain ⟨i, ξ, -, -, hc, M, B, N, Pf, Mk⟩ := hT v hv'
    have eX : A.Z.p.X = Bs.G₀.W := by rw [hpub.1, hpub.2]
    rw [eX] at hc M B N Pf Mk
    exact ⟨i, ξ, theTrace Bs.G₀.W i ξ, hc, M, B, N, Pf, planOwners_of_marks Mk Pf⟩
  refine twoAt_full_owners h test carryX item n₁ n₂ b₀ Vd Rd Kp w hA hV hOk O₁ no Dd blk id cellsQ
    tokQ wit own₀ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ O hO hl e3 hK hR ?_ hD ?_ ?_
  · intro v hv
    obtain ⟨i, ξ, T, hc, -, B, -, Pf, Ow⟩ := key v hv
    show K1.OwnersAgree Sz.ref v.trace (K3.matsOwn Bs.G₀.W l) l
    rw [hc]
    exact own_of_trace Ow Pf B hl
  · intro _ v hv μ hμ ρ c
    obtain ⟨i, ξ, T, hc, -, B, -, Pf, -⟩ := key v hv
    rw [hR v hv, hc]
    exact bor_of_trace Pf B hl hμ ρ c
  · intro v hv μ i c
    obtain ⟨j, ξ, T, hc, M, -, N, -, Ow⟩ := key v hv
    show |cellsAtOf v.trace (K3.matsOwn Bs.G₀.W l) μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)
    rw [hc]
    exact small_of_trace Ow N M hl μ i c

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.twoAt_full_ready
