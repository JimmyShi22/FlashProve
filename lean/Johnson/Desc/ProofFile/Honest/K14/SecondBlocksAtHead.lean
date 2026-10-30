-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondBlocksAtHead.lean: kind K14: "K14, second part" (the place
⟨3, none, 0, .K14⟩): second_door_saidS (Honest/K14/OmegaAtHead.lean) WITHOUT ITS PREMISE ON THE
WEIGHTS, AND WITH THREE TESTS IN THE PLACE OF FIVE, UNDER hR (Honest/K14/SecondBlocks.lean). One
statement with its proof: a call. No definition.

  second_door_three_saidS   under the library's head, from ThrS at the shared chain's last border,
                  at every Said: secondDoor from secondRest3, sW and hR

What stays a premise: the head; ThrS at the shared chain's last border at s₂; the start's return at
that same s₂; hR, on the first chain's last state s₁, which is a variable; sW; the three tests of
secondRest3.

What is not claimed. That one of these premises holds at any run, or that they can hold together.
That the sub-protocol accepts. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaAtHead
import Johnson.Desc.ProofFile.Honest.K14.SecondBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linLayW E stretchBlocks)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Common W₀ Rc OnBytes.TableKey → MeaningS St P₁ Wt)
  (shape : Nat → St → Bool) (nothingLeft : St → Bool) (order : St → Prop)
  (wit : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    Place × Table)
  (fixed : Fmt.TreeSource → Nat) (n₁ n₂ : Nat) (Vd : Common W₀ Rc OnBytes.TableKey → Prop)
  (Rd : Nat → Common W₀ Rc OnBytes.TableKey → St → Prop) (Kp : Place → St → St → Prop)
  (w : Common W₀ Rc OnBytes.TableKey)

/-- **Under the library's head, from ThrS at the shared chain's last border, at every Said:
secondDoor from secondRest3, sW and hR.** -/
theorem second_door_three_saidS {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins Bk} {s₂ : St} {m : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E' : Env}
    (hA : ThrS (SharedThread.lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed
      n₁ n₂ Vd Rd Kp w).thread Said (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k s₂ m E')
    (x : ProofFile.InstPub) (s₁ : P5J.TS) (s : S₃)
    (hs : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₃ x s₁ s₂ = .ok s)
    (hR : ∀ row ∈ s₁.rows, ∀ v ∈ row.g,
      ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (a : E),
        firstRow + values.size ≤ (ToldDesc.p14At Zp).S.matrixRows ∧
          ∃ t ∈ stretchBlocks (ToldDesc.p14At Zp).S.kRow firstRow values fuel start,
            v = t.scale a)
    (sW : PadsBehind s.st s.loc.w (linLayW s.st.codes (ToldDesc.p14At Zp).S)
      (2 ^ (ToldDesc.p14At Zp).S.kCol))
    (h3 : ok (secondRest3 (ToldDesc.p14At Zp) s) = true) :
    ok (secondDoor (ToldDesc.p14At Zp) s) = true :=
  have hB := blocks_at_border Zp Np cF x s₁ s₂ s hs hR
  second_door_saidS Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w h Said
    hA x s₁ s hs (fun b hb => weightsFit_blocks _ _ (hB b hb)) sW (rest5_of_three _ s hB h3)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.second_door_three_saidS
