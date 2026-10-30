-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/AtFlat.lean: THE SIX ROWS AT ANY FLAT LIST OF THE KIND's FORM: no head, no description named: at a list of the form `FlatOf`, where the
library's maker makes the eight sub-protocols of a plan and the shapes pass `sendingsFit`, at a book that passes the three tests: at each of the six rows a side and `Good`,
at A := False. So a chain of either file that has this form has K14's rows.

  `six_good_flat`  **the statement**
  `six_onFromS_flat`   `OnFromS` at the six rows, at any frame's sentence over such a list

Limits. The book's three tests and the plan's two are premises. At A := False `plays` and `acc` are met for nothing. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sim.Good
import Johnson.Desc.ProofFile.Honest.K14.OnRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (St P14 blocks)
open Desc.K14.Honest (FlatOf)
open ProofFile.Honest.Small (noneSpent)

variable {Cl X W₀ Rc Ky : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- **At every row of the six: a side off the list, and `Good` as one term, at A := False.** -/
theorem six_good_flat (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hfit : sendingsFit P = true)
    (d : Data) (hd : d.S = P.S) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (fs : List (Fall St)) (Bk : ProverCoinCounts) (ord : List Place) (hB : OwnClear Bk)
    (okU : (maskOwner ⟨P, 0⟩).ok Bk ord ⟨sendPlace 2, 0⟩ = true)
    (okO : (spOwner ⟨P, 0⟩).ok Bk ord ⟨sendPlace 5, 0⟩ = true)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Ky)
    (hr : r ∈ simRows d ⟨P, 0⟩ weights rand)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∃ σ, Side.seated xs r.place r.row fs = some σ ∧
      Good pre .shared σ Bk ord 1 0 (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On r.bud := by
  rcases List.mem_append.1 hr with h' | h'
  · obtain ⟨i, hi, hp⟩ := place_of_row _ weights r h'
    have hN : noneSpent Bk { place := r.place, part := 0 } = true := by
      rw [hp]
      obtain ⟨a, b, e, g⟩ := hB
      rcases hi with rfl | rfl | rfl | rfl
      · exact a
      · exact b
      · exact e
      · exact g
    obtain ⟨σ, hσ⟩ := seated_some F hb i hi r.row fs
    rw [← hp] at hσ
    exact ⟨σ, hσ, good_rows F hb d hd weights r h' fs σ hσ .shared Bk ord 1 0 pre hN⟩
  · have serve := rowsServe_of (X := X) (W₀ := W₀) (Rc := Rc) (Ky := Ky) xs P hfit
      (fun row fs => seated_declares F hb 0 row fs) weights rand fs Bk ord r h'
    cases hσ : Side.seated xs r.place r.row fs with
    | none =>
      exfalso
      unfold Side.seated at hσ
      obtain ⟨b, hbm, hp⟩ := List.any_eq_true.1 serve.1
      rw [Option.map_eq_none_iff, List.find?_eq_none] at hσ
      exact hσ b hbm hp
    | some σ =>
      obtain ⟨f1, f2, f3⟩ := serve.2 σ hσ
      exact ⟨σ, rfl, { fits := f1, plays := fun _ _ _ _ _ h => h.elim, acc := fun _ _ _ _ _ h => h.elim
                       exact := fun u hu ca m front ds asks o s _ dd b e t =>
                         f2 u hu ca m front ds asks o s dd b e t
                       fresh := f3 okU okO }⟩

/-- **At a frame's sentence whose list has the form `FlatOf`: `OnFromS` at each of the six rows.** -/
theorem six_onFromS_flat {Bk : ProverCoinCounts} (T₂ : Thread Bk St Cl Empty (Common W₀ Rc Ky) X Ky)
    (F : FlatOf T₂.bs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X → Prop) (d : Data)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Ky) (hr : r ∈ simRows d ⟨P, 0⟩ weights rand)
    (L : Lettered Bk St Cl Empty (Common W₀ Rc Ky) X Ky) (hplace : L.place = r.place)
    (hrow : L.row = r.row) (hOn : L.On = r.On) (b : Nat) (blk : Block St Cl)
    (hx : T₂.bs[b]? = some blk) (hp : blk.place = L.place) (len : Nat → Nat → Nat) :
    OnFromS T₂ S₂ L b len := by
  rcases List.mem_append.1 hr with g | g
  · have e : L.On = k14On := by
      refine hOn.trans ?_
      unfold ownRows at g
      rcases List.mem_append.1 g with g | g
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
        rcases g with rfl | rfl | rfl <;> rfl
      · split at g
        · obtain rfl := List.mem_singleton.1 g
          rfl
        · cases g
    intro σ _ u _ k m E ca front _ _ _
    rw [e]
    trivial
  · exact onFromS_of_onFrom T₂ S₂
      (onFrom_rows T₂ F hb weights rand r g L hplace hrow hOn b blk hx hp len)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.six_onFromS_flat
#print axioms ProofFile.Honest.K14.six_good_flat
