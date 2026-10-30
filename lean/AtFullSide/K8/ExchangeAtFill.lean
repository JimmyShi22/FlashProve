-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/ExchangeAtFill.lean: the honest side of the smallness test (K8): ProofFile's hXk AT THE KIND
K8 (`k8_exchange_by_kind`, Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) AT THE PROVER AND
THE BOOK THAT `onlineProverFromPublicFiles` RETURNS, AT THE JOINED SCRIPT OF ALL THREE SENDERS, AT A FILLING AT WHICH
`ReadyLaws` HOLDS AND WHOSE LOTS HOLD THE KIND's ONE LOT: `K8Seated` AND `K8TwoAt` AT ALL 25 ARE LAID
IN. One theorem; no definition.

It is exchanged here, not paid. ON THE HIDDEN INPUT: Vd IS `ReadyInput`, WHICH CUTS THE RANGE OF
INPUTS, AND NO INPUT IS SHOWN HERE TO MEET IT; hR, proved nowhere. ON THE THREAD: hB (`BehindS` at
each of the 25 numbers). ON WHAT IS SAID: hOk. PUBLIC OR ON THE MAKER: the head h, hA, hT, hV, hJ,
hO (the share's sum), the opening, hex and ho (the filling's lots hold the kind's one lot at `cells
:= id`, `mats := K3.matsOwn`, and no other half of the kind), hD. Behind a yes at which the second
stop is silent. Equations on the Script. NOT IN FRONT OF A LAW OVER COINS. At the
messages' first sending alone.

  **`k8_exchange_at_fill`**   hSeat of `k8_exchange_by_kind`: at each l < 25: `k8Seated_at_fill`
                  (Johnson/Desc/ProofFile/Honest/K8/SeatedAtFill.lean) at `hlen_matsOwn`
                  (Johnson/Desc/ProofFile/Honest/K8/PlaysAtOwnMats.lean) and `twoAt_full_ready`
                  (AtFullSide/K8/TwoAtFullReady.lean) at the same member; G := Bs.G₀ by the opening
One option is raised (maxHeartbeats) and one instance is taken away, as in the files beneath. No
tactic that searches. The sign 𝔇 is the name of a field of
the library's head, as the library writes it.
Limits. An implication. The Limits of the files that it calls are its own too. NOT SAID: that an
honest prover's Script is the joined one; that the thread ever reaches one of the draws' numbers;
that any instance passes `okStart`; that `onlineProverFromPublicFiles` returns; that hex and ho hold at any filling. No
letters are given at which the premises hold together. Counted nowhere. The full size alone.
Nothing is claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.TwoAtFullReady
import Johnson.Desc.ProofFile.Honest.K8.SeatedAtFill
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtOwnMats

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc.First (S)
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

/-- **hXk at the kind K8, at the maker's prover and book: exchanged, not paid**: for hR (proved
nowhere), hB, hD, hex, ho, hA, hT, hV, hJ, hO, hOk, the head and the opening. `ReadyInput` cuts the
range of inputs, and no input is shown here to meet it. Behind a yes at which the second stop is
silent. At the messages' first sending alone. Equations on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k8_exchange_at_fill {X₂ : Type} {P : OnlineProverParts W₀ Rc Cells X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (hT : ReadyLaws (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A)
    (hV : Vd = ReadyInput (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.H)
    {Said : ℕ → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Cells) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {Bs : ProofFile.PureBase}
    {base₀ : List (Block S ProofFile.Cl)}
    (O₁ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
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
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G =
      (smallLot id fun _ G _ l => K3.matsOwn G.W l).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K8) ∨
      M.halves A.Z A.G = (smallLot id fun _ G _ l => K3.matsOwn G.W l).halves A.Z A.G)
    (hR : ∀ v, v = w ∧ Vd v → (wit v).R.cells = v.trace)
    (hD : ∀ ξ, (P5J.F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true →
      K2.Law.ReadsLight Zp Bs.G₀ ξ)
    (hB : ∀ l, l < 25 → BehindS (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2)) :
    ∀ b (p : Place), P5J.At.ps[b]? = some p → p.kind = KindName.K8 →
      ∀ j : VerifiableInference.Desc.First.Item,
      j ∈ ((lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.row b).owes →
      (j ∈ (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ .constr m q) →
      ExchangeAtS (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said b j := by
  refine k8_exchange_by_kind h A.H _ test carryX item n₁ n₂ b₀ Vd Rd Kp w hOk O₁.blank id ?_ hB
  intro l hl
  obtain ⟨G₀, Xl, blk, hG, hX, hS⟩ :=
    k8Seated_at_fill id (fun _ G _ l => K3.matsOwn G.W l) h hA hex ho (hlen_matsOwn h hA)
      (joinQ cF.blocksInOrder 0 cellsQ tokQ h.𝔇.arr wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                   wJobs (X := X) no Dd Zp Bs.G₀)) O) test carryX item n₁ n₂ b₀ Vd Rd Kp w hl
  obtain rfl : G₀ = Bs.G₀ := Option.some.inj (hG.symm.trans O₁.blank)
  exact ⟨Xl, blk, K3.matsOwn Bs.G₀.W l, hX, hS,
    twoAt_full_ready h test carryX item n₁ n₂ b₀ Vd Rd Kp w hA hT hV hOk O₁ no Dd blk cellsQ tokQ
      wit own₀ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ O hO hl hX hS hR (fun _ => hD)⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8_exchange_at_fill
