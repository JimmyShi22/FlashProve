-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/TwoAtFullOwners.lean: the honest side of the smallness test (K8): THE RECORD `K8TwoAt`
(Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) AT EACH OF THE 25 SEGMENTS, AT THE PROVER AND
THE BOOK THAT `onlineProverFromPublicFiles` RETURNS AND THE JOINED SCRIPT OF ALL THREE SENDERS AT THE SIZES `Sz.ref`:
`twoAt_full_reads` (AtFullSide/K8/TwoAtFullReads.lean) WITH hShape MET AND "THE READS' FORM" hrd
LAID IN: AT SEGMENT 0 WITHOUT ANY PREMISE ON THE HIDDEN INPUT; AT SEGMENTS 1 TO 24 FOR hBor AND hD.
One theorem; no definition.

`K8TwoAt` is exchanged here, not paid: for hR, hOwn, hsmall and, from segment 1 on, hBor (on the
hidden input), each proved nowhere; for hD (from segment 1 on: the light test at the reads' filling
says yes at each instance that passes `okStart`), proved by nobody; for hA (`onlineProverFromPublicFiles` returns), hV
(the valid inputs are `ReadyInput`'s) and hJ (the proximity test's job has six stages); for
`K8Seated`, hOk, the opening and the built segment. Behind a yes at which the second stop is silent.
Equations on the Script. NOT IN FRONT OF A LAW OVER COINS. At the messages' first
sending alone. hR, hOwn, hsmall and hBor are premises on the hidden input: in front of a sentence on
hiding none of them stands as a bare premise: there it is had from Vd, by name, or the sentence says
that its range is cut by a condition on the trace.

  **`twoAt_full_owners`**   hShape := `shapes_at_stand` · hrd at l = 0 := `hrd_first` (both
                  Johnson/Desc/ProofFile/Honest/K8/ReadsAtFirst.lean) · hrd at 1 ≤ l :=
                  `reads_at_links` (AtFullSide/K8/ReadsAtLinks.lean) at hK1 :=
                  `owner_first_at_stand` (ReadsAtFirst.lean), hin := `shareIn_add_left`
                  (Johnson/Desc/ProofFile/Honest/K2/JoinShare.lean, of other authors) · F :=
                  `joinFit_full` (AtFullSide/K2/JoinFitFull.lean), hcoins from its field coins
The code switch's share stands at the data `withSwitchData Sz.ref (K1.lotData Sz.ref)` and at the
readers of the letter wit.
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. The Limits of the files that it calls are its own too, those of
JoinFitFull.lean among them ("fit" asks of the book the shared sending's counts alone). NOT SAID:
that an honest prover's Script is the joined one; that the letter wit reads the trace of the model;
that the thread stands at any of the draws' numbers. No letters are given at which the premises hold
together. Counted nowhere. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.TwoAtFullReads
import AtFullSide.K8.ReadsAtLinks
import Johnson.Desc.ProofFile.Honest.K8.ReadsAtFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz packedCells)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open ProofFile.Honest.FirstThread (TreeLot Others joinQ JoinFit lettersHead WtF coinsB byNo)
open ProofFile.Honest.K2.Law (joinFit_full shareIn_add_left)
open OnBytes.SendSim.Seat (wJobs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5J (AtMgA CellsM TS)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Rc Tr X₀ X : Type}
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The record `K8TwoAt` at each of the 25 segments, at the prover and the book that `onlineProverFromPublicFiles`
returns: exchanged, not paid**: for hR, hOwn, hsmall and, from segment 1 on, hBor and hD, each
proved nowhere; for hA, hV, hJ, `K8Seated`, hOk, the opening and the built segment. Behind a yes at
which the second stop is silent. At the messages' first sending alone. Equations on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem twoAt_full_owners {X₂ : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hV : Vd = ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
    {Said : ℕ → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) (blk : Block S ProofFile.Cl) (cells : Tr → Cells)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : X)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂)
    (n₀ : Nat) (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (O : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : O = (K2.switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀
        (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R) rest).add
      (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (hK : K8Seated (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l))
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = cells v.trace)
    (hOwn : ∀ v, v = w ∧ Vd v → K1.OwnersAgree Sz.ref (cells v.trace) (K3.matsOwn Bs.G₀.W l) l)
    (hD : 1 ≤ l → ∀ ξ, (P5J.F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
      K2.Law.ReadsLight Zp Bs.G₀ ξ)
    (hBor : 1 ≤ l → ∀ v, v = w ∧ Vd v → ∀ μ, μ < K8Q35.nmW l → ∀ r c,
      packedCells Sz.ref (wit v).R.cells.cell (Meaning.ownerK (K8Q35.labW l μ))
          (Meaning.ownerA (K8Q35.labW l μ)) r c =
        packedCells Sz.ref (wit v).R.cells.cell l μ r c)
    (hsmall : ∀ v, v = w ∧ Vd v → ∀ μ i c,
      |cellsAtOf (cells v.trace) (K3.matsOwn Bs.G₀.W l) μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) :
    K8TwoAt (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) blk cells
      (ProofFile.k8Par Zp Bs.G₀ Xl l, K3.matsOwn Bs.G₀.W l)
      (fun a => cellsAhead h.𝔇.cs h.𝔇.arr h.𝔇.ms h.𝔇.N l a) := by
  have hb : 14 * l + (if l = 24 then 5 else 4) + 2 ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hK.here).1
  have F := joinFit_full (X := X) h O₁ hA no (K1.lotData Sz.ref) Dd 0 wit own₀
    (K2.withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R) rest ch Jt hJ own₂
    n₀ ok codes sh sh₁ rest₂
  rw [← hO] at F
  have hcoins := List.all_eq_true.2 fun y hy => decide_eq_true (F.coins y hy)
  refine twoAt_full_reads h A.H test carryX item n₁ n₂ b₀ Vd Rd Kp w hA hOk O₁ no Sz.ref Dd blk
    cells cellsQ tokQ wit own₀ _ _ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ O hO hl e3 hK hR
    (shapes_at_stand h A.H test carryX item n₁ n₂ b₀ Vd Rd Kp w _ hOk hl O₁.blank e3 hb) hOwn ?_
    hsmall
  by_cases h0 : l = 0
  · subst h0
    exact hrd_first h A.H test carryX item n₁ n₂ b₀ Vd Rd Kp w O₁ no Dd cellsQ tokQ wit own₀ O F
      hcoins
  · have h1 : 1 ≤ l := Nat.pos_of_ne_zero h0
    exact AtFullSide.K8.reads_at_links h hA 0 _ cellsQ tokQ wit own₀ _ O rest F
      (by rw [hO]; exact shareIn_add_left _ _) _ rfl test carryX item n₁ n₂ b₀ Vd hV Rd Kp w
      O₁.made (hD h1) h1 hl
      (owner_first_at_stand h A.H test carryX item n₁ n₂ b₀ Vd Rd Kp w O₁ no Dd cellsQ tokQ wit
        own₀ O F hcoins l)
      (hBor h1)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.twoAt_full_owners
