-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/PlaysAtWider.lean: THE SMALLNESS TEST: THE DEBT "IT PLAYS"
(`PlaysS`, Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) AT ALL 25 OF THE KIND's DRAWS, AT THE
PROVER THAT THE MAKER `onlineProverFromPublicFiles` BUILDS AT THE FILLING `widerFillAt`
(Johnson/Desc/ProofFile/Honest/AtPureWiderAt.lean): UNDER THE LIBRARY's HEAD, FROM "THE MAKER
RETURNS" ALONE. Four theorems; no definition; none of the library's goals.

  `k8_pair_mem`   the kind's lot, with its kind, is the last of the filling's ten pairs
  `hex_wider`   the filling's list of lots has a member with the halves of
                   `smallLot id (fun _ G _ l => K3.matsOwn G.W l)`: it is the last of the ten
  `ho_wider`    every lot of that list has halves at places of other kinds than K8 alone, or these
                   halves
  **`playsS_at_wider`**   under the library's head (h : `P5J.AtMgA`): the maker returns A at the
                   head's own three files, at widerFillAt I o S O · l < 25 ⊢ PlaysS ‹the thread at
                   H := A.H› Said (14 * l + (if l = 24 then 5 else 4) + 2)
HOW. A JOIN OF OTHER AUTHORS' LEMMAS WITH THIS KIND's: `widerKinds` (every half of each of the ten
lots stands at a place of the lot's kind: no premise), `WiderKinds.all`, `widerFillAt_lots`,
`widerPairs_nodup` (Johnson/Desc/ProofFile/Honest/Thread/FirstFillAll.lean, FirstFill.lean) ·
`playsS_at_ownMats` (Johnson/Desc/ProofFile/Honest/K8/PlaysAtOwnMats.lean). KIN, NOT CALLED:
`k8_half_wider` (Johnson/Desc/ProofFile/Honest/Thread/FirstFillK8.lean) has the half at the draw's
place at this filling outright.
ONE LINE TAKES AN INSTANCE AWAY (attribute [-instance] Inst.Model.Scl.ref), as the files beneath do.
NO TACTIC THAT SEARCHES.
Limits. THAT `onlineProverFromPublicFiles` RETURNS IS A PREMISE, proved here of no files. I, o, S, O and the thread's
letters are free. Nothing on whether a list's entry names the right cells. THE FULL SIZE ALONE.
Which of the files that this head names are rows of the library is for the library's own list to
say: it is not said here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.PlaysAtOwnMats
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place Claim Block KindName)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.FirstFill

variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  (Zq : Pub) (G : Ground)

/-- The kind's pair is the last of the ten. -/
theorem k8_pair_mem :
    ((smallLot id fun _ G _ l => K3.matsOwn G.W l, KindName.K8) :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName) ∈
      widerPairs I o Sz O := by
  unfold widerPairs
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
    (.head _)))))))))

/-- **The filling holds the kind's lot.** -/
theorem hex_wider : ∃ M ∈ (widerFillAt I o Sz O).lots, M.halves Zq G =
    (smallLot id fun _ G _ l => K3.matsOwn G.W l).halves Zq G := by
  refine ⟨smallLot id fun _ G _ l => K3.matsOwn G.W l, ?_, rfl⟩
  rw [widerFillAt_lots]
  exact List.mem_map.2 ⟨_, k8_pair_mem I o Sz O, rfl⟩

/-- **Every other lot's halves stand at places of other kinds.** -/
theorem ho_wider : ∀ M ∈ (widerFillAt I o Sz O).lots,
    (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K8) ∨
      M.halves Zq G = (smallLot id fun _ G _ l => K3.matsOwn G.W l).halves Zq G := by
  intro M hM
  rw [widerFillAt_lots] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  by_cases e : r.2 = KindName.K8
  · right
    have er := List.inj_on_of_nodup_map (widerPairs_nodup (I := I) (o := o) (S := Sz) (O := O)) hr
      (k8_pair_mem I o Sz O) e
    rw [er]
  · left
    intro x hx h8
    exact e (((widerKinds I o Sz O Zq G).all r hr x hx).symm.trans h8)

variable {I o Sz O}
  {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o Sz O) = .ok A) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
include hA

/-- **IT PLAYS AT ALL 25 DRAWS, AT THE FILLING, FROM "THE MAKER RETURNS" ALONE.** -/
theorem playsS_at_wider
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {l : ℕ}
    (hl : l < 25) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) :=
  playsS_at_ownMats h hA id (hex_wider I o Sz O A.Z A.G) (ho_wider I o Sz O A.Z A.G) Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w Said hl

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8_pair_mem
#print axioms ProofFile.Honest.K8.hex_wider
#print axioms ProofFile.Honest.K8.ho_wider
#print axioms ProofFile.Honest.K8.playsS_at_wider
