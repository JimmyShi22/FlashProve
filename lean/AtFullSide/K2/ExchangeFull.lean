-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/ExchangeFull.lean: the kind "the code switch" (K2): THE KIND's WHOLE DEBT UNDER "THE
EXCHANGE", BY KIND, AT THE LETTERS OF THE HOUSE's LAST ASSEMBLIES: the joined Script `joinQ`, the
book `A.B` and the prover `A.H` that `onlineProverFromPublicFiles` returns, the switches' filling at `Sz.ref`. A JOIN:
calls alone. A closed fact by Lean's kernel; statements with their proofs.

WHICH SLOT IT IS FOR. Its end is `k2_exchange_of_values`'s (Honest/K2/Law/MadeValuesLeft.lean): the
hypothesis hXk of the frame's gather `owesS_framesK` at the kind K2, at these letters, at a Said
that gives `SaidOk`.

  `placesKindW`, `placesKindW_can_fail`   BY LEAN's KERNEL: each written switch's place has the
                    kind K2; a control
  `k2_left_full`    the record `SwitchLeftL` at one written switch: its four first fields laid in by
                    calls
  `k2_exchange_full`   THE TOP

LAID IN, BY CALLS: the field half: `switch_half_fill` (Honest/K2/Law/HalfAtArms.lean) · publicAt:
`publicOk_of_reads` (Honest/K2/Law/PublicOkOfReads.lean) · msgs: `msgs_at_lot_data`
(MsgsAtLotData.lean of this folder, of other authors) · pads: `pads_at_join`
(Honest/K2/Law/TieAtJoin.lean, of other authors) · the list's fit: `joinFit_full`
(JoinFitFull.lean) · the book: `pure_book_written` (LendAtPure.lean, of other authors) · the
exchange: `k2_exchange_of_asks` (Honest/K2/Law/ValuesOfLock.lean).

WHAT IS LEFT, BY THE THEOREM's OWN BINDERS. hOk, hst, y₀: the thread's letter and the prover's
stored words · hex, ho: where the filling's lots stand · hR4: `ReadsLight` at each valid input's
instance (another house's law, `readsLight_of_att`, has it from the input's test and attention's
maker's return: not called here) · hD1: how far the filling's data have heard · hI: the sender's
reader hands the input's own instance · hJ: the proximity test's job has six stages · hO: which
share the others' list is · left: `ValuesAsks` (Honest/K2/Law/ValuesOfLock.lean) at each written
switch: that the input is typed; `LockAsks`; `SymbolsAre`.

Limits. AN IMPLICATION: EVERY BINDER NAMED ABOVE IS A PREMISE, SHOWN OF NO PROVER. h, O AND hA ARE
PREMISES TOO: the library's head, the opening, and that `onlineProverFromPublicFiles` returns at the filling P: at the
earlier hash, at the full size. `left` binds a run's coins and speaks of entries that hold them. CLOSED FACTS BY LEAN's KERNEL,
REPLAYED BY NO INDEPENDENT CHECKER. One run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ValuesOfLock
import Johnson.Desc.ProofFile.Honest.K2.Law.HalfAtArms
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicOkOfReads
import Johnson.Desc.ProofFile.Honest.K2.Law.TieAtJoin
import AtFullSide.K2.JoinFitFull
import AtFullSide.K2.MsgsAtLotData
import AtFullSide.K2.LendAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block KindName Strs)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT allOf EAll)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open OnBytes.Maker (WholeD)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem placesKindW : (placesW.all fun p => p.place.kind == KindName.K2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control. -/
theorem placesKindW_can_fail : (placesW.all fun p => p.place.kind == KindName.K1) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X Y X₂ : Type} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- h, O, hA, hp AND EVERY BINDER NAMED IN THE HEAD ARE PREMISES; the rest are letters. **The record
at one written switch, its first four fields laid in.** -/
theorem k2_left_full (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp
               Bs.G₀)
      (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData
      Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R)).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
        (fun v => (wit v).R)).halves A.Z A.G)
    (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ReadsLight Zp Bs.G₀ v.x)
    (hD1 : ∀ p₀ ∈ switchPlaces Zp Bs.G₀, ∀ p ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link →
      ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ∀ s m a, s < p₀.link → p.addrs s m = some a →
        (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ v.x).heardAt a ≤ 0 + roundsTo cF.blocksInOrder
          (switchNo p₀))
    (hI : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → (wit v).x = v.x)
    {p : SwitchPlace} (hp : p ∈ placesW)
    (left : ValuesAsks (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p) :
    SwitchLeftL (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hk : p.place.kind = KindName.K2 := beq_iff_eq.1 (List.all_eq_true.1 placesKindW p hp)
  have F := joinFit_full h O hA no (K1.lotData Sz.ref) Dd 0 wit own₀ (withSwitchData Sz.ref
    (K1.lotData Sz.ref) Zp Bs.G₀)
    (fun v => (wit v).R) rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂
  rw [← hO] at F
  have hin : ShareIn (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData
             Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) rest) Oth := by
    rw [hO]
    exact shareIn_add_left _ _
  have hB := pure_book_written h hA
  exact ⟨switch_half_fill O hA _ _ hex ho hpS hk,
    fun v hv => publicOk_of_reads h O (hR4 v hv) p hpS,
    msgs_at_lot_data h O hB Sz.ref no Dd F hin cellsQ tokQ _
      (fun p hp v hv => publicOk_of_reads h O (hR4 v hv) p hp) hD1 hI (fun _ _ => rfl) p hpS,
    pads_at_join h O hpS F hin cellsQ tokQ _, left⟩

/-- h, O, hA AND EVERY BINDER NAMED IN THE HEAD ARE PREMISES; the rest are letters. **K2's WHOLE
DEBT UNDER "THE EXCHANGE", BY KIND, AT THE LETTERS OF THE HOUSE's LAST ASSEMBLIES.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_full (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp
               Bs.G₀)
      (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.stored v i x = some u →
      ∀ a ∈ u, a < fieldPrimeWord)
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData
      Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R)).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
        (fun v => (wit v).R)).halves A.Z A.G)
    (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ReadsLight Zp Bs.G₀ v.x)
    (hD1 : ∀ p₀ ∈ switchPlaces Zp Bs.G₀, ∀ p ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link →
      ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ∀ s m a, s < p₀.link → p.addrs s m = some a →
        (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ v.x).heardAt a ≤ 0 + roundsTo cF.blocksInOrder
          (switchNo p₀))
    (hI : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → (wit v).x = v.x)
    (left : ∀ p ∈ placesW, ValuesAsks (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr
               Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p) :
    ∀ b p₀, P5J.At.ps[b]? = some p₀ → p₀.kind = KindName.K2 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ
        tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.opened b →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠
          VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread Said b j :=
  k2_exchange_of_asks h A.H _ test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst y₀ fun p hp =>
    k2_left_full h O hA no Dd cellsQ tokQ wit own₀ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ Oth
      hO
      test item n₁ n₂ b₀ Vd Rd Kp w hex ho hR4 hD1 hI hp (left p hp)

end AtFullSide.K2

#print axioms AtFullSide.K2.placesKindW
#print axioms AtFullSide.K2.placesKindW_can_fail
#print axioms AtFullSide.K2.k2_left_full
#print axioms AtFullSide.K2.k2_exchange_full
