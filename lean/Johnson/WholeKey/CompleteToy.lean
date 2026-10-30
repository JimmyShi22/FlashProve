-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/WholeKey/CompleteToy.lean: THE FIVE PREMISES OF complete_argW
(Johnson/WholeKey/Complete.lean) CAN BE MET TOGETHER, AT AN INTERFACE WHERE THE NUMBER HAS A TOOTH:
the small interface whose keys hold an OOD sample, of Johnson/TypedOracleCompiler/Joined/ToyArmsExt.lean (LRX, WRX,
SRX; digests of one bit), as in Johnson/Prover/All/ToyAll.lean, at a written honest side with TWO
copies; the theorem is called: the scheme with the whole key has completeness error at most 1/2
there.

Main names (namespace OnBytes.WholeKey.ToyW).
  playsX, sideX   the strategies with their tests for a stop; THE HONEST SIDE: two copies.
  accAtW, accLaws, sideFit, stopsIn   the premises (LawFit, WiresFit: ToyAll's).
  toy_complete   complete_argW, CALLED.

Limits. A TOY's. ONE TOOTH: the collision seeds at the first table (1/2); no round has a test, the
caps are idle, the three sets of verifier messages are empty. THE TESTS FOR A STOP NEVER RETURN
TRUE: StopsIn is met emptily: a stop that fires is tried nowhere. The public starts of salts and the
word behind a slot's string are empty; the window of a run's leaf salts is 7 rounds, 2 trees, 4
leaves, with one written bit beyond it; a table's salts are cut at its tree's two leaves. Each
enumeration lists one value, so the two copies are equal and the mean over the committer's coins is
a mean over one value; the prover's place has two values. 1/2 is an upper bound: that the verifier
does reject somewhere is not shown. It says nothing of any intended file. Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Complete
import Johnson.Prover.All.ToyAll

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey.ToyW
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open TypedOracleCompiler.Joined TypedOracleCompiler.Joined.Toy
open OnBytes.Prover OnBytes.Prover.ToyAll
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Prover.ToyFileRun (σ₀)
open scoped ENNReal

/-- The three strategies of ToyAll, each with one coin; no test for a stop ever returns true. -/
def playsX : Plays LRX Unit Unit Unit where
  T := fun _ _ _ _ => σ₀
  Lk := fun _ _ _ _ => σL
  B := fun _ _ _ _ _ _ => σ₀
  stopT := fun _ _ _ _ => false
  stopL := fun _ _ _ _ => false
  stopB := fun _ _ _ _ _ _ => false

/-- **The honest side**: two copies; each enumeration lists one value. -/
def sideX : HonestSide 1 LRX BdX G.ann aLX where
  KT := Unit
  KL := Unit
  KB := Unit
  st := playsX
  b₀ := .inr (.inr false)
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 0
  nm := fun j => j
  M := 1
  RV := Unit
  rvT := fun _ => ()
  rvL := fun _ => ()
  rvB := fun _ => ()
  startT := fun _ _ _ _ => []
  startL := fun _ _ _ _ => []
  startB := fun _ _ _ _ => []
  pvT := fun _ => ()
  pvL := fun _ => ()
  pvB := fun _ => ()
  rtail := fun _ => []
  nR := 7
  nK := 2
  nJ := 4
  fill := [true]
  ri := ⟨0, fun _ => ()⟩
  sl := ⟨0, fun _ j => [j % 2 == 0]⟩
  kT := ⟨0, fun _ => ()⟩
  kL := ⟨0, fun _ => ()⟩
  kB := ⟨0, fun _ => ()⟩
  coT := ⟨0, fun _ => co0⟩
  coL := ⟨0, fun _ => co0⟩
  coB := ⟨0, fun _ => co1⟩

/-- The accept laws at every sample, at every index i and the instance (i, true). -/
theorem accAtW (i : Bool) (d : Draw 1 LRX BdX G.ann aLX (Unit × Unit × Unit)) :
    AccAt WRX SRX playsX.joint i () (i, true) d BsX where
  T := fun e₁ h1 τ _ hp _ => by
    have hc : e₁ 0 0 = false := by simpa [BsX, coll0] using h1
    show (gT (e₁, i) (fun _ => i) && str₁ τ _ && str₁ τ _) = true
    rw [str_true τ hp]
    simp [gT, hc]
  Lk := fun e₁ e₂ h1 _ τ _ hp _ => by
    have hc : e₁ 0 0 = false := by simpa [BsX, coll0] using h1
    have hs : τ.1.1 = (fun _ => true, false) := hp.1
    show (decide (linkLgX ((e₁, i), (e₂, i)) (fun _ => i, fun _ => i)) && τ.1.1.1 _) = true
    rw [hs]
    have hl : linkLgX ((e₁, i), (e₂, i)) (fun _ => i, fun _ => i) := by
      by_cases h2 : coll0 e₂
      · exact Or.inr (Or.inl h2)
      · have h2' : e₂ 0 0 = false := by simpa [coll0] using h2
        refine Or.inr (Or.inr ?_)
        simp [decX, gT, hc, h2']
    simp [hl]
  B := fun e₂ _ τ _ hp _ => by
    show (gB ((i, true), (e₂, i)) (fun _ => i) && str₁ τ _ && str₁ τ _) = true
    rw [str_true τ hp]
    simp [gB]
  num := fun _ _ _ => rfl

/-- the true instances -/
def YesX (i : Bool) (x : Bool × Bool) : Prop := x = (i, true)

theorem accLaws : AccLaws WRX SRX sideX.st.joint YesX (fun _ _ _ _ => BsX) (1 / 2) 0 0 0 0 where
  acc := fun i _ _ d hY => by
    obtain rfl := hY
    exact accAtW i d
  small := fun _ _ _ _ _ => small

theorem sideFit : SideFit WRX pX sideX where
  sl := fun _ j hj => by
    show (if j < 2 ^ WRX.depth then [j % 2 == 0] else []).length = 1
    rw [if_pos (show j < 2 ^ WRX.depth from hj)]
    rfl
  coT := fun _ _ => ⟨drawFit.T.salt, fun i b k j => by
    show ([] ++ if i < 7 ∧ k < 2 ∧ j < 4 then co0.leaf i b k j else [true]).length = 1
    split <;> rfl, drawFit.T.slot, drawFit.T.path⟩
  coL := fun _ _ => ⟨drawFit.Lk.salt, fun i b k j => by
    show ([] ++ if i < 7 ∧ k < 2 ∧ j < 4 then co0.leaf i b k j else [true]).length = 1
    split <;> rfl, drawFit.Lk.slot, drawFit.Lk.path⟩
  coB := fun _ _ => ⟨drawFit.B.salt, fun i b k j => by
    show ([] ++ if i < 7 ∧ k < 2 ∧ j < 4 then co1.leaf i b k j else [true]).length = 1
    split <;> rfl, drawFit.B.slot, drawFit.B.path⟩

theorem stopsIn : StopsIn (lam := 1) (Bd := BdX) (aT := G.ann) (aL := aLX) sideX.st
    (fun _ _ _ _ => BsX) where
  T := fun _ _ _ _ _ _ hs => by cases hs
  Lk := fun _ _ _ _ _ _ _ hs => by cases hs
  B := fun _ _ _ _ _ _ hs => by cases hs

/-- **complete_argW, called**: at two copies: the verifier rejects with probability at most 1/2. -/
theorem toy_complete (r₀ : LRX.Rec) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation YesX))
      (argW WRX SRX cAX r₀ pX sideX) 1 (1 / 2) := by
  have e := alpha_eq sideX.capT sideX.capL sideX.capB
  rw [← e]
  exact complete_argW WRX SRX cAX r₀ pX sideX YesX (fun _ _ _ _ => BsX)
    (lawFit _ _ _) wiresFit sideFit accLaws stopsIn

end OnBytes.WholeKey.ToyW
