-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12AtPlaceRow.lean: THE PUBLIC PREMISES OF THE PROXIMITY TEST's LAW (`AtPlace`) AT THE MAKER's OWN PIECE OF A DESCRIPTION's FIRST CHAIN: the joining of the closed forms of Johnson/Top/Fire/Code/RowCut.lean and Johnson/Desc/K12/Coin/AtDesc.lean. Statements with proofs.
OBJECT. The base `cutBase 0 D.ds₁ …` and the stretch `cutDs D.ds₁ …` that the maker's n-th piece of the first chain has (Johnson/Top/Fire/Code/RowCut.lean: rowAt₁), against the base `0 + nTrees (D.ds₁.take pre.length)` and the stretch `(D.ds₁.drop pre.length).take …` at which `AtPlace` is shown at a description's own data (Johnson/Desc/K12/Coin/AtDesc.lean: atPlace_first).
USER. Whoever pays a field of the key file's tables at the first chain's proximity test.
LETTERS. The description F, its data D, the chain's blocks c₁ :: k₁, the number n, the place π: all free. Premises: F.data file = .ok D · the flat list is c₁ :: k₁ · the n-th block is b, it is not the last, and it declares the kind's block's rounds at π · what the blocks behind it declare ends in a round (post ++ [r₀]: the sealing round) · the maker's stretch is written dB :: dt · AND ALL THAT atPlace_first LEAVES AS PREMISES: early · answers · planOk · spendOk · ownMask = false · the written rounds exist · CodesAt · bears · free: π.nums.free = the roots that the first n blocks declare.

  before_inFront: `before b l n` (RowCut.lean) is `inFront (b :: l) n` (RoundsInFront.lean).
  inFront_map: it reads of a block its number of rounds alone.
  before_held: so at the blocks as the pieces hold them it is the length of the first n blocks' declared rounds in a row.
  atPlace_row₁: the statement.
Limits. IT MOVES PREMISES; IT PAYS NONE: "free" above all is shown of no test. The first arm and the first chain alone. Nothing on soundness, nothing on hiding.

-/
import Johnson.Top.Fire.Code.RowCut
import Johnson.Desc.K12.Coin.AtDesc
import Johnson.RunOne.Law.RoundsInFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12AtPlaceRow
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt spendOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Law.RoundsInFront
open LPFD (before cutBase cutDs cutDs_inner cutBase_eq)

section
variable {S Cl : Type}

theorem before_inFront : ∀ (l : List (Block S Cl)) (b : Block S Cl) (n : ℕ),
    before b l n = inFront (b :: l) n
  | _, _, 0 => by simp [before, inFront]
  | [], b, n + 1 => by simp [before, inFront]
  | b' :: l, b, n + 1 => by
    have ih := before_inFront l b' n
    simp only [before, ih, inFront, List.take_succ_cons, List.map_cons, List.sum_cons]

theorem inFront_map {T : Type} (f : Block S Cl → Block T Cl) (hf : ∀ b, (f b).rounds = b.rounds)
    (bs : List (Block S Cl)) (n : ℕ) : inFront (bs.map f) n = inFront bs n := by
  unfold inFront
  rw [← List.map_take, List.map_map]
  congr 1
  exact List.map_congr_left fun b _ => by simp [hf]

theorem before_held {P : Type} (c : Block S Cl) (k : List (Block S Cl)) (n : ℕ) :
    before (held c : Block (P × S) Cl) (k.map held) n =
      (((c :: k).take n).flatMap (·.rounds)).length := by
  rw [before_inFront, length_inFront]
  exact inFront_map (held (P := P)) (fun _ => rfl) (c :: k) n

end

/-- **`AtPlace` at the maker's n-th piece of the first chain.** -/
theorem atPlace_row₁ {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D) (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl))
    (hf : F.first.blocksInOrder = c₁ :: k₁) (n : ℕ) (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b)
    (hn : n < k₁.length) (π : P12) (hr : b.rounds = (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds)
    (post : List Fmt.DeclaredRound) (r₀ : Fmt.DeclaredRound)
    (hpost : ((c₁ :: k₁).drop (n + 1)).flatMap (·.rounds) = post ++ [r₀])
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (dB : RDT) (dt : List RDT)
    (εt : Err (uLT (ckP .two) dt))
    (hcons : cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n = dB :: dt)
    (hfree : π.nums.free = rootsOf (((c₁ :: k₁).take n).flatMap (·.rounds)))
    (early : π.early = true) (answers : π.answers = 1)
    (planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (spend : spendOk π = true)
    (codes : CodesAt L mC mS mW rad π.nums.stages) (ho : π.nums.ownMask = false) (w0 : WR)
    (l : List WR) (hw : writtenOf π.nums = some (w0 :: l))
    (bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
      writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
      Bears c.errL εt) :
    AtPlace (frameAt D (allOf D) D.key₁ 0) π (numAt F.t₁ F.t₂ 0) L mC mS mW rad
      (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) dB dt εt := by
  have e : F.roundsDeclaredByBlocks.1 = ((c₁ :: k₁).take n).flatMap (·.rounds) ++
      ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ++ (post ++ [r₀])) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [hf, rounds_part (c₁ :: k₁) n b hb, hr, hpost]
  have hb' : ((held c₁ : Block (F.XiPub × F.S₁) F.Cl) :: k₁.map held)[n]? = some (held b) := by
    have : ((c₁ :: k₁).map (held (P := F.XiPub)))[n]? = some (held b) := by
      rw [List.getElem?_map, hb]; rfl
    exact this
  have hn' : n < (k₁.map (held (P := F.XiPub))).length := by rw [List.length_map]; exact hn
  have ed := cutDs_inner (k₁.map (held (P := F.XiPub))) n D.ds₁ (held c₁) (held b) hn' hb'
  have eb := cutBase_eq (k₁.map (held (P := F.XiPub))) n 0 D.ds₁ (held c₁) (Nat.le_of_lt hn')
  rw [before_held] at ed eb
  rw [eb]
  refine atPlace_first F file D h D.key₁ 0 π L mC mS mW rad _ post r₀ e dB dt εt ?_ hfree early
    answers planOk spend codes ho w0 l hw bears
  rw [← hcons, ed]
  show _ = (D.ds₁.drop _).take (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length
  rw [← hr]
  rfl

end Johnson.RunOne.Law.K12AtPlaceRow

#print axioms Johnson.RunOne.Law.K12AtPlaceRow.before_inFront
#print axioms Johnson.RunOne.Law.K12AtPlaceRow.before_held
#print axioms Johnson.RunOne.Law.K12AtPlaceRow.atPlace_row₁
