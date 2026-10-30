-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/HgAtPure.lean: CONDITIONAL.

What is here. WHAT K4's OWN LOT HOLDS AT THE PUBLIC PART AND THE GROUND OF THE HONEST PROVER THAT
THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS (Honest/AtPure.lean) AT THE PUBLIC FILES OF h : AtMgA: statements
on the lot's own list alone, with no hypothesis on the filling's other lots. (1) the maker's public
part is h's, and its ground is `ProofFile.blankBy ProofFile.pureRoad.links Zp`: by the frame's `atPure_ok`
(Honest/AtPureLaw.lean). (2) hg: the first half of `k4HLot` at the member's place, AT A.Z AND A.G,
is `k4Half` at the public data `k4PubAt`: the premise "what my own list holds at the place" of the
frame's laws on which half is found at a place (`firstOf_find`, `atPure_first_find`,
Honest/FirstFind.lean, and their forms by kinds and by pairs), in their own letters. (3) ho, the
premise on the filling's other lots of `atPure_first_find_kind` (Honest/FirstFindKind.lean) and of
the statements of this folder at the maker's prover, FROM ONE KIND A LOT: where each lot of a list
either has the halves of a given lot or has all its halves at places of one kind other than K4.
General in the lists. Statements and proofs: calls.

Not shown here. THAT `onlineProverFromPublicFiles` RETURNS AT ANY FILLING (hA): a hypothesis. K4's share of the maker's
test `strays` is `k4HLot_noStray` (Law/LotNoStray.lean), which asks no hA. THAT ANY OTHER LOT HAS
ITS HALVES AT ONE KIND: the premise of (3). THAT PREMISE IS STRONGER THAN ho:
(3) turns a form and pays nothing; one call of it, at two lots, is `ho_k4_reply`
(Law/DescAtPure.lean). That K4's lot stands in the filling's list; which half the WHOLE list holds
at the place: the frame's laws', from (2). That the maker's own description is the library's term
over cF: `atPure_desc` (Law/DescAtPure.lean). THAT h CAN HOLD: the side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). OF h TOGETHER WITH hA
NO EXAMPLE IS KNOWN TO US (`LaidK4` asks nothing beyond h: `laid_head`, Law/SeatedHead.lean, at the
library's `atK4_full`). THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone. Beneath (2) stand
comparisons by Lean's own kernel: `k4PubOf` returns through `k4Pub_head` (Law/FrontCount.lean),
which rests on one closed fact by `decide +kernel` (`k4_front_closed`, Law/FrontClosed.lean) and
holds over the entry tests' second issue alone; the test `k4TableFits` is accepted through
`tableFits_member` (Law/FitsMember.lean), whose head counts its uses of `kernel_rfl`. No independent
checker has replayed them. Nothing on what a half plays. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one: as Law/DearTop.lean says of itself.
Transitive imports: those of Law/HalfHead.lean and Honest/AtPureLaw.lean: not counted.
No property is claimed.

  `atPure_pub`, `atPure_ground`   the maker's public part; its ground.
  `hg_atPure`   **hg at A.Z and A.G.**
  `ho_of_kinds`   **ho, from one kind a lot.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfHead
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Block)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X' : Type}

/-- CONDITIONAL: on h and hA. The maker's public part is h's. -/
theorem atPure_pub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    A.Z = Zp :=
  Except.ok.inj ((atPure_ok hA).1.symm.trans h.laid.pub)

/-- CONDITIONAL: on h and hA. The maker's ground is the one that is made of h's public part. -/
theorem atPure_ground (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G :=
  atPure_pub h hA ▸ (atPure_ok hA).2.1

/-- CONDITIONAL: on h, `LaidK4` and hA. **hg AT THE MAKER's PUBLIC PART AND GROUND.** -/
theorem hg_atPure (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard) :
    ((k4HLot (Rc := Rc) (X := X') cells weights look).halves A.Z A.G).find?
      (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens (look Zp A.G) (k4PubAt cF k x)) := by
  obtain ⟨G₀, hG₀, hx⟩ := Lh.lot
  have eG : G₀ = A.G := Option.some.inj (hG₀.symm.trans (atPure_ground h hA))
  subst eG
  rw [atPure_pub h hA]
  exact lot_half_head h Lh cells weights look hx

/-- CONDITIONAL: on hk. **ho FROM ONE KIND A LOT**: each lot of the list has the halves of L, or has
all its halves at places of one kind that is not K4. -/
theorem ho_of_kinds {V W X : Type} {Zq : ProofFile.Pub} {G : ProofFile.Ground} {ls : List (HLot V W X)}
    {L : HLot V W X}
    (hk : ∀ M ∈ ls, M.halves Zq G = L.halves Zq G ∨
      ∃ κ : VerifiableInference.Desc.KindName, κ ≠ .K4 ∧ ∀ y ∈ M.halves Zq G, y.place.kind = κ) :
    ∀ M ∈ ls, (∀ y ∈ M.halves Zq G, y.place.kind ≠ .K4) ∨ M.halves Zq G = L.halves Zq G := by
  intro M hM
  rcases hk M hM with e | ⟨κ, hκ, hy⟩
  · exact Or.inr e
  · exact Or.inl fun y h' => by
      rw [hy y h']
      exact hκ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.atPure_pub
#print axioms ProofFile.Honest.K4.atPure_ground
#print axioms ProofFile.Honest.K4.hg_atPure
#print axioms ProofFile.Honest.K4.ho_of_kinds
