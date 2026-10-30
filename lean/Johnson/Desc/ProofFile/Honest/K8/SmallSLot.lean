-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/SmallSLot.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE
KIND's ROWS AS A LOT OF ROWS WITH SIMULATORS (`SLot`, `Unlettered`:
Johnson/Desc/ProofFile/Honest/Thread/Rows.lean); THE ONE EQUATION TO THE KIND's LOT OF HALVES
(`smallLot`, Honest/K8/Part.lean); AND `Good` AT A ROW's OWN SIDE, IN THE FORM IN WHICH THE FRAME's
`hand_of_house` TAKES IT. Definitions and lemmas on the frame's own definitions; none of the
library's goals.

  `smallBare cells P`   ONE ROW WITHOUT LETTERS: the kind's place · the half's one part with its
                   simulator (`smallRow`, Honest/K8/Side.lean) · On := True · bud := True
  `smallSLot cells mats`   THE LOT: a row at each segment, at the numbers at which the lot makes its
                   block
  `smallBare_half`   a row's half is the kind's half
  **`smallSLot_toHLot`**   THE ONE EQUATION: (smallSLot cells mats).toHLot = smallLot cells mats
  **`small_hand`**   `Good` at the row's own side: from Side.seated bs r.place r.row fs = some σ, at
                   whatever falls, at the letters A' := B' := False, at the row's own On and bud: by
                   `small_good` (Honest/K8/QuietForm.lean), under its five public premises
Limits. On := True and bud := True: so `Good.exact` is owed, and shown, at every stand. The five
premises (the seat's test · the block's one round, without an item but roots · no oracle message ·
the book lends nothing of the part's coins) are shown at no description here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.QuietForm
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.First.K8 (Par)

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- **One row without letters.** -/
def smallBare (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) :
    Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb :=
  ⟨smallPlace P.1, smallRow cells P, fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- **The lot of rows.** -/
def smallSLot (cells : Tr → Cells)
    (mats : Pub → Ground → OnBytes.Model.Stages.LinkH → Nat → List (Nat × String × Nat)) :
    SLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb :=
  { name := "the smallness test"
    rows := fun Z G =>
      G.built.toList.zipIdx.map fun y => smallBare cells (k8Par Z G y.1 y.2, mats Z G y.1 y.2) }

/-- A row's half is the kind's half. -/
theorem smallBare_half (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) :
    (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).half =
      smallHalf cells P := rfl

/-- **The one equation.** -/
theorem smallSLot_toHLot (cells : Tr → Cells)
    (mats : Pub → Ground → OnBytes.Model.Stages.LinkH → Nat → List (Nat × String × Nat)) :
    (smallSLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells mats).toHLot =
      smallLot cells mats := by
  unfold SLot.toHLot smallSLot smallLot
  simp only [List.map_map]
  rfl

/-- **`Good` at the row's own side.** -/
theorem small_hand (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (bs : List (Block S Cl)) (cells : Tr → Cells)
    (P : Par × List (Nat × String × Nat)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (d₀ : Fmt.DeclaredRound)
    (hσ : Side.seated bs
      (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).place
      (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).row fs = some σ)
    (hf : smallFits P = true) (hr : σ.block.rounds = [d₀])
    (hi : d₀.items.filter (· != .root) = []) (ho : σ.block.oracles = [[]])
    (hb : ∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = []) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).On
      (smallBare (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells P).bud :=
  small_good W₀ Rc Xi Tr X Pb S Cl bs cells P fs σ pre φ Bk ord chain firstTree d₀ hσ hf hr hi ho hb

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.smallBare_half
#print axioms ProofFile.Honest.K8.smallSLot_toHLot
#print axioms ProofFile.Honest.K8.small_hand
