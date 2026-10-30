-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/AtDescOwn.lean: THE PUBLIC PREMISES OF THE PROXIMITY TEST's LAW's SECOND ARM
(`AtPlaceOwn`, OwnArm.lean: the first fold sends its own mask) AT A DESCRIPTION's OWN DATA.
Statements and proofs.

AtDesc.lean's four theorems again, at `AtPlaceOwn`, ownMask = true and `atPlaceOwn_of_plan`
(PaidByPlan.lean): `atPlaceOwn_of_cut`; `atPlaceOwn_first`, `atPlaceOwn_shared`, `atPlaceOwn_last`.
The texts were made of AtDesc.lean's own by a program that turns these names and that one value.
What is left as a premise, and the limits: AtDesc.lean's, at ownMask = true. NO SOUNDNESS IS
CLAIMED.
-/
import Johnson.Desc.K12.Coin.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk)
open Johnson.G.OfPlan (rootsOf)

/-- **The step on lists, general in the chain.** -/
theorem atPlaceOwn_of_cut (Fr : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (ds : List RDT) (pre mid post : List Fmt.DeclaredRound) (base₀ : ℕ)
    (allTs : List Fmt.Shape) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hcons : dB :: dt = (ds.drop pre.length).take mid.length)
    (hAs : List.Forall₂ RoundAsG ds (pre ++ (mid ++ post)))
    (hmid : mid = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (hwants : ∀ Rs, wantsOf Fr.a (stg Fr (base₀ + nTrees (ds.take pre.length))
        ((ds.drop pre.length).take mid.length)).depth ((ds.drop pre.length).take mid.length) Rs =
      wantsDecl num mid Rs)
    (hchain : ∀ n x, (ds.flatMap (·.trees))[n]? = some x → allTs[base₀ + n]? = some x)
    (hopen : ∀ r ∈ mid, ∀ o ∈ r.opens, allTs[num o.2]? = some o.1)
    (hnum0 : ∀ m, num (.own m) = base₀ + m) (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages) (ho : π.nums.ownMask = true) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlaceOwn Fr π num L mC mS mW rad (base₀ + nTrees (ds.take pre.length)) dB dt εt := by
  have hrs : H2U.roundsOfNums π.nums = some mid := by
    rw [hmid]
    exact VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π planOk
  have hpre : nTrees (ds.take pre.length) = rootsOf pre := by
    have h1 := List.forall₂_take pre.length hAs
    rw [List.take_left] at h1
    exact nTrees_roots h1
  have hnumOwn : ∀ n, num (.own (π.nums.free + n)) = base₀ + nTrees (ds.take pre.length) + n := by
    intro n
    rw [hnum0, hfree, hpre, Nat.add_assoc]
  have hst := H2K.Sw.roundsOfNums_stored π.nums mid hrs
  have hE : List.Forall₂ RoundAs (dB :: dt) mid := by
    rw [hcons]
    exact forall₂_imp_mem (forall₂_cut pre mid post hAs) fun d r hr h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.trans (hst r hr)⟩
  have hcut : ∀ n x, ((dB :: dt).flatMap (·.trees))[n]? = some x →
      allTs[base₀ + nTrees (ds.take pre.length) + n]? = some x := by
    intro n x h
    rw [hcons] at h
    rw [Nat.add_assoc]
    exact hchain _ x (cutTrees ds pre.length mid.length n x h)
  have hopen' : ∀ o ∈ mid.flatMap (·.opens), allTs[num o.2]? = some o.1 := by
    intro o ho'
    obtain ⟨r, hr, hor⟩ := List.mem_flatMap.1 ho'
    exact hopen r hr o hor
  have hlike := like_of_data π mid hrs w0 l hw (dB :: dt) hE num _ allTs hcut hopen' hnumOwn
  have hbat : dB.trees = [] := by
    obtain ⟨_, _, _, R, _, _, hR⟩ := H2K.Made.rounds_top π.nums mid hrs
    rw [hR] at hE
    cases hE with
    | cons h _ => exact List.eq_nil_of_length_eq_zero h.2.2.2.1
  exact atPlaceOwn_of_plan Fr π num L mC mS mW rad _ dB dt εt early answers planOk spend codes hlike
    hbat ho (by rw [← hmid]; exact wants_form Fr num mid _ _ hwants _ dB dt rfl hcons) hnumOwn bears

/-- **At the first chain: the stretch ends in front of the sealing round.** -/
theorem atPlaceOwn_first {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (pre post : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])))
    (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hcons : dB :: dt =
      (D.ds₁.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages) (ho : π.nums.ownMask = true) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlaceOwn (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 0) L mC mS mW rad
      (0 + nTrees (D.ds₁.take pre.length)) dB dt εt := by
  obtain ⟨hS, k₁, k₂⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  refine atPlaceOwn_of_cut _ π _ L mC mS mW rad D.ds₁ pre _ post (0) (allT D) dB dt εt
    hcons ?_ rfl (wants_first h pre _ post r₀ e key ft)
    (fun n x hx => (by rw [Nat.zero_add]; exact ((chainTrees D n x).1 hx))) ?_ ?_ hfree early
    answers planOk spend codes ho w0 l hw bears
  · have ed : F.roundsDeclaredByBlocks.1.dropLast = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post) := by
      rw [e]
      simp only [← List.append_assoc, List.dropLast_concat]
    rw [← ed]
    exact hA.1
  · intro r hr o ho'
    exact hS.1 r (by rw [e]; simp [hr]) o ho'
  · intro m
    simp [numAt]

/-- **At the shared chain.** -/
theorem atPlaceOwn_shared {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (pre post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.1 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post))
    (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hcons : dB :: dt =
      (D.ds₂.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages) (ho : π.nums.ownMask = true) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlaceOwn (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 1) L mC mS mW rad
      (D.t₁ + nTrees (D.ds₂.take pre.length)) dB dt εt := by
  obtain ⟨hS, k₁, k₂⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  refine atPlaceOwn_of_cut _ π _ L mC mS mW rad D.ds₂ pre _ post (D.t₁) (allT D) dB dt εt
    hcons ?_ rfl (wants_shared h pre _ post e key ft)
    (fun n x hx => (chainTrees D n x).2.1 hx) ?_ ?_ hfree early
    answers planOk spend codes ho w0 l hw bears
  · rw [← e]
    exact hA.2.1
  · intro r hr o ho'
    exact hS.2.1 r (by rw [e]; simp [hr]) o ho'
  · intro m
    simp [numAt, k₁]

/-- **At the last chain.** -/
theorem atPlaceOwn_last {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (key : ℕ → ℕ) (ft : ℕ) (π : P12) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (pre post : List Fmt.DeclaredRound)
    (e : F.roundsDeclaredByBlocks.2.2 = pre ++ ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ post))
    (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt))
    (hcons : dB :: dt =
      (D.ds₃.drop pre.length).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length)
    (hfree : π.nums.free = rootsOf pre)
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages) (ho : π.nums.ownMask = true) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlaceOwn (frameAt D (allOf D) key ft) π (numAt F.t₁ F.t₂ 2) L mC mS mW rad
      (D.t₁ + D.t₂ + nTrees (D.ds₃.take pre.length)) dB dt εt := by
  obtain ⟨hS, k₁, k₂⟩ := opensShaped F file D h
  have hA := roundsOfData F file D h
  refine atPlaceOwn_of_cut _ π _ L mC mS mW rad D.ds₃ pre _ post (D.t₁ + D.t₂) (allT D) dB dt εt
    hcons ?_ rfl (wants_last h pre _ post e key ft)
    (fun n x hx => (chainTrees D n x).2.2 hx) ?_ ?_ hfree early
    answers planOk spend codes ho w0 l hw bears
  · rw [← e]
    exact hA.2.2
  · intro r hr o ho'
    exact hS.2.2 r (by rw [e]; simp [hr]) o ho'
  · intro m
    simp [numAt, k₁, k₂]

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_of_cut
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_first
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_shared
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_last
