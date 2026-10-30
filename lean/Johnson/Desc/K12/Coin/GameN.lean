-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameN.lean: **THE GAME OF THE PROXIMITY TEST WITH NOTHING PROMISED OF THE
BATCHED ROWS**, over the block's parts with guard (c). Statements and proofs: each is two calls.

  `stepComb`: `StepComb π` (GameYes.lean) holds: it is `comb_of_step`
    (Johnson/Desc/K12/Law/Step8.lean, the kind's own law's side).
  `K12GameY`, `k12_gameY`; `K12GameYO`, `k12_gameYO`: Game.lean's two statements with `GameAtY` |
    `GameAtYO` concluded: the promise is the record's count of roots and `FirstOpens` |
    `FirstOpensOwn` alone.
  `K12GameF2Y`, `k12_gameF2Y`: the first arm at the first chain's finish of a description, at the
    seat on the chain's own state: Game.lean's `K12GameF2` with that smaller promise.
Limits: those of Game.lean, but for `PayRec`. NO SOUNDNESS IS CLAIMED. It stands only where the
block's parts ask guard (c).

-/
import Johnson.Desc.K12.Coin.GameYes
import Johnson.Desc.K12.Law.Step8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK (recAt)
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk PayPub johOk batV0)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)

theorem stepComb (π : P12) : StepComb π := H2K.JointK.comb_of_step π

/-- **THE GAME, FIRST ARM, NOTHING PROMISED OF THE BATCHED ROWS.** -/
def K12GameY : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : T12 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (n : ℕ) (r : Fmt.M1.Stage → ℕ),
    π.early = true → (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true →
    (π.nums.free = n → AtPlace F π num L mC mS mW rad base dB dt εt) →
    (∀ s, rad s = r s.st) → johOk π r = true → batOneOk π = true →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    GameAtY F π num no rad rd base n
      (pieceOf (proximityTestKind guardedProximityTestParts π) base (dB :: dt) [] ⟨ext, (e, εt)⟩)

theorem k12_gameY : K12GameY := by
  intro F W π num no L mC mS mW rad rd base dB dt ext e εt n r he hp hA hr hj hb1 hle
  exact gameY_of_game F π num no rad rd base n _ (stepComb π) rfl rfl
    (k12_game F W π num no L mC mS mW rad rd base dB dt ext e εt n r he hp hA hr hj hb1 hle)

/-- **THE SECOND ARM.** -/
def K12GameYO : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : T12 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (n : ℕ),
    π.early = true → (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true →
    (π.nums.free = n → AtPlaceOwn F π num L mC mS mW rad base dB dt εt) →
    PayPub π rad dB.entry.rows v₀ → Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] →
    dB.entry.logN ≤ 64 → v₀ * (bsRound .two dB.entry dB.kind).w ≤ e →
    GameAtYO F π num no rad rd base n
      (pieceOf (proximityTestKind guardedProximityTestParts π) base (dB :: dt) [] ⟨ext, (e, εt)⟩)

theorem k12_gameYO : K12GameYO := by
  intro F W π num no L mC mS mW rad rd base dB dt ext e v₀ εt n he hp hA hP h1 hlog hle
  exact gameYO_of_game F π num no rad rd base n _ (stepComb π) rfl rfl
    (k12_gameO F W π num no L mC mS mW rad rd base dB dt ext e v₀ εt n he hp hA hP h1 hlog hle)

/-- **THE GAME AT A DESCRIPTION, NOTHING PROMISED OF THE BATCHED ROWS.** -/
def K12GameF2Y : Prop :=
  ∀ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    ∀ (key : ℕ → ℕ) (ft : ℕ) (W : Type) (π : P12) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (pre post : List Fmt.DeclaredRound)
    (r₀ : Fmt.DeclaredRound),
    F.roundsDeclaredByBlocks.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])) →
    ∀ (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt)),
    dB :: dt = (D.ds₁.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length →
    π.early = true → π.answers = 1 → (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true →
    spendOk π = true → CodesAt L mC mS mW rad π.nums.stages → π.nums.ownMask = false →
    ∀ (w0 : WR) (l : List WR), writtenOf π.nums = some (w0 :: l) →
    (∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) →
    ∀ (r : Fmt.M1.Stage → ℕ), (∀ s, rad s = r s.st) → johOk π r = true → batOneOk π = true →
    ∀ (ext : First.S × (frameAt D (allOf D) key ft).E.Str →
        Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ),
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := frameAt D (allOf D) key ft) (atFinish π)
        (0 + nTrees (D.ds₁.take pre.length)) (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun x => ∀ fo, x.1.here = .fin fo → (recAt x.1 fo).roots = rootsOf pre ∧
        FirstOpens π (numAt F.t₁ F.t₂ 0) no (0 + nTrees (D.ds₁.take pre.length)) (recAt x.1 fo))
      (fun x y => ∃ fo, x.1.here = .fin fo ∧ x.1.noneWaits = true ∧ x.1.failed.isNone = true ∧
        QN π (NTuple (frameAt D (allOf D) key ft) π no rad rd) (recAt x.1 fo, x.2) ∧
        ∃ st book roots, y.1 = { x.1 with st := st, book := book, roots := roots })
      (e, εt)

theorem k12_gameF2Y : K12GameF2Y := by
  intro Xi F file D h key ft W π no L mC mS mW rad rd pre post r₀ e' dB dt εt hcons early answers
    planOk spend codes ho w0 l hw bears r hr hj hb1 ext e hle a ha
  exact leads_atFinish (frameAt D (allOf D) key ft) W π (0 + nTrees (D.ds₁.take pre.length)) dB dt
    e εt
    (fun x => x.1.roots = rootsOf pre ∧
      FirstOpens π (numAt F.t₁ F.t₂ 0) no (0 + nTrees (D.ds₁.take pre.length)) x.1)
    (fun x => QN π (NTuple (frameAt D (allOf D) key ft) π no rad rd) x)
    (k12_gameY _ W π _ no L mC mS mW rad rd _ dB dt (fun _ _ w => w) e εt (rootsOf pre) r early
      planOk
      (fun hfree => atPlace_first F file D h key ft π L mC mS mW rad pre post r₀ e' dB dt εt hcons
        hfree early answers planOk spend codes ho w0 l hw bears) hr hj hb1 hle) a ha

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.stepComb
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameY
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameYO
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameF2Y
