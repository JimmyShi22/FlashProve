-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Typed against the files of Johnson/Desc/K12/Coin/.
/-
Johnson/Desc/K12/Coin/PaidByPlan.lean: WHAT THE BLOCK's OWN TEST ON THE PLAN PAYS OF THE LAW IN THE COIN's PUBLIC PREMISES. One-line proofs over the lemmas of Johnson/Desc/K12/Law/DealMade.lean, MasksFixed.lean, MasksPlan.lean. NO SOUNDNESS IS CLAIMED.
  atPlace_of_plan: AtPlace WITHOUT its fields deal, own0, trees: in their stead π.nums.ownMask = false.
  atPlaceOwn_of_plan: AtPlaceOwn WITHOUT deal, own1, trees: in their stead π.nums.ownMask = true.
  firstOpens_of_first: FirstOpens from its first clause alone, under two pins on num (n2, n3).
  n2_numAt: at numAt the pin n2 is the one equation of numOwn_numAt (Bools.lean).
  firstOpensOwn_third: the third clause of FirstOpensOwn from its first, under numOwn and «the last of D.ts is D.fresh.t».
-/
import Johnson.Desc.K12.Coin.Bools
import Johnson.Desc.K12.Coin.BoolsOwn
import Johnson.Desc.K12.Law.MasksPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk)
open H2K.First (Plain)

theorem treesOwn_iff {s : Sg} (c : OnBytes.Slice.Chain s) : TreesOwn c ↔ H2K.Made.TreesOwnP c := by
  cases c <;> exact Iff.rfl

theorem n2_numAt (t₁ t₂ chain free base : ℕ) (h : numAt t₁ t₂ chain (.own free) = base) :
    ∀ n, n < free → numAt t₁ t₂ chain (.own n) < base := by
  intro n hn
  rw [← h]
  show _ + n < _ + free
  omega

theorem atPlace_of_plan (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages)
    (like : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l))
    (batNone : dB.trees = []) (ho : π.nums.ownMask = false)
    (wants : ∀ Rs,
      wantsOf F.a (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth (dB :: dt) Rs =
        wantsDecl num (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds Rs)
    (numOwn : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlace F π num L mC mS mW rad base dB dt εt :=
  have M := H2K.Made.masksFixed_of_planOk π planOk
  ⟨early, answers, planOk, spend, H2K.Made.dealOk_of_planOk guardedProximityTestParts π planOk, codes, like, batNone,
    M.own0 ho, wants, numOwn, fun a rest w0 l c hs hw hc => M.trees ho _ a rest w0 l c hs hw hc,
    bears⟩

theorem atPlaceOwn_of_plan (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages)
    (like : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l))
    (batNone : dB.trees = []) (ho : π.nums.ownMask = true)
    (wants : ∀ Rs,
      wantsOf F.a (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth (dB :: dt) Rs =
        wantsDecl num (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds Rs)
    (numOwn : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlaceOwn F π num L mC mS mW rad base dB dt εt :=
  have M := H2K.Made.masksFixed_of_planOk π planOk
  ⟨early, answers, planOk, spend, H2K.Made.dealOk_of_planOk guardedProximityTestParts π planOk, codes, like, batNone,
    M.own1 ho, wants, numOwn,
    fun a rest w0 l c hs hw hc => (treesOwn_iff c).2 (M.treesOwn ho _ a rest w0 l c hs hw hc), bears⟩

theorem firstOpens_of_first (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = false)
    (n2 : ∀ n, n < π.nums.free → num (.own n) < base)
    (n3 : ∀ c n, (c + 1, n) ∈ π.before → num (.taken c n) < base)
    (h1 : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D →
      D.opens.map (fun o => num o.2) = D.ts.map no) : FirstOpens π num no base t :=
  fun a rest G0 Ly D hf => ⟨h1 a rest G0 Ly D hf,
    (H2K.Made.masksFixed_of_planOk π planOk).firstOpens2 ho a rest hf.1 num base n2 n3 D no
      (H2K.First.made_of π _ a Ly D (hf.2.2.2 default)).opens (h1 a rest G0 Ly D hf)⟩

theorem firstOpensOwn_third (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = true)
    (numOwn : ∀ n, num (.own (π.nums.free + n)) = base + n) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) (h1 : D.opens.map (fun o => num o.2) = D.ts.map no)
    (hlast : D.ts.getLast? = some D.fresh.t) : no D.fresh.t = base :=
  (H2K.Made.masksFixed_of_planOk π planOk).freshBase ho a rest hf.1 num base numOwn D no
    (H2K.First.made_of π _ a Ly D (hf.2.2.2 default)).opens h1 hlast

end VerifiableInference.Desc.K12.Coin
