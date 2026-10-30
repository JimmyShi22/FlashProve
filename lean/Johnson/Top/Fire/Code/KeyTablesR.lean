-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyTablesR.lean, adapted by a program of this project that is not in this repository: at the full size: AT THE KEY FILE's OWN DESCRIPTION `Key.descriptionFromSource X N P`: THE KEY FILE's THREE TABLES OF PROMISES WITH THE GENERIC HISTORY WOVEN IN, NAMED ONCE: so that all files spell them one way.
Main names. `On₁'` | `On₂'` | `On₃'`: `Onⱼ' … k x := Onⱼ … k x ∧ Histⱼ (Key.descriptionFromSource X N P) D k x.1`: the table's promise at border k (`On₁` | `On₂` | `On₃`, Johnson/RunOne/KeyRowsAtFk.lean, TO THE BYTE) AND «this state was reached: from the chain's start its first k blocks have each said yes, at some rounds and columns, and have led here» (`Reached`, Reached.lean; `Histⱼ`, RowsWoven.lean). The claims `Cl₁` | `Cl₂` | `Cl₃` are the tables' own.
HOW A LAW IS TYPED OVER THEM. A field of `The35` (The35.lean) is `KeepsAt (Onⱼ' …) (Clⱼ …) ‹the maker's row› i`. A LAW THAT DOES NOT KNOW THE HISTORY is proved at `Onⱼ` and lifted by `KeepsAt.reached`. A LAW THAT SPENDS IT is proved as `Keeps (Onⱼ' … i) (Onⱼ … (i + 1)) …` and gets the history behind for nothing by `keeps_reached`. OF ONE STEP OF THE HISTORY come out (`Reached.last`): the block's decision went on, and the rounds fit the declared ones. THE BLOCKS ARE THE DESCRIPTION's AS A PIECE HOLDS THEM (`held b`): from `held b`'s decision to b's: `held_decide` (Johnson/Desc/Plain/PaidKeeps.lean); `(held b).rounds = b.rounds`: `rounds_held` here.
Limits. Definitions. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowsWoven
import Johnson.RunOne.KeyRowsAtFk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)

/-- A block as a piece holds it declares the block's own rounds. -/
theorem rounds_held {P S Cl : Type} (b : Block S Cl) : (held b : Block (P × S) Cl).rounds = b.rounds := rfl

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **The first chain's promise with its history.** -/
abbrev On₁' : ℕ → (Xi × FirstState) × (EAll D (allOf D)).Str → Prop := fun k x => On₁ X N P D B at_ R coll k x ∧ Hist₁ (Fk X N P) D k x.1
/-- **The shared chain's.** -/
abbrev On₂' : ℕ → ((Xi × FirstState) × St₂) × (EAll D (allOf D)).Str → Prop := fun k x => On₂ X N P D B at_ R enc rad coll off₂ k x ∧ Hist₂ (Fk X N P) D k x.1
/-- **The last chain's.** -/
abbrev On₃' : ℕ → ((Xi × FirstState × St₂) × St₃) × (EAll D (allOf D)).Str → Prop := fun k x => On₃ X N P D B at_ R coll off₂ off₃ k x ∧ Hist₃ (Fk X N P) D k x.1

end

end LPFD

#print axioms LPFD.rounds_held
#print axioms LPFD.On₁'
#print axioms LPFD.On₂'
#print axioms LPFD.On₃'
