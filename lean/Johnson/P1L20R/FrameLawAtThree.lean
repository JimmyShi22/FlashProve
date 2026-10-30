-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameLawAtThree.lean: THE SHARE OF THE KIND "frame" ON THE FIRST CHAIN, IN THE FORM
IN WHICH IT IS COUNTED: at the three rows of pieces as one named term (threeCap,
Johnson/Goal/Skeleton/TheThree.lean), at the composed meaning mgAll Dm mgBase, at the table's own
extractor, with a condition Rch beside the promise.

  FD                the description as the maker returns it in scope
  extAt9            the table's own extractor at Dm's letters
  flat_plan         the flat list's tests on the plan from the description's one test
  frame_law_atThreeT   in scope, at an opening of the maker, with the description's data and its
                    test on the plan: FrameParams9 at that term, "Dm.N's numbers of trees and
                    messages do not move across the 51", "Kn k holds of every reached statement that
                    bears no mark", and the two shares of other files (the seal; the 25 behind the
                    batching) give: at every place of the kind "frame": TiedAtR

What it does not take: OfDesc (threeCap_ofDesc), "the extractor lays nothing at the 51
numbers" (ext_lays_nothing), the promise's half of GivesIn.

Limits. FrameRows9.lean's and FrameSitsR.lean's: no premise is shown at a filling. No soundness
statement.

-/
import Johnson.P1L20R.FrameKindR
import Johnson.Goal.Skeleton.TheThree
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)

/-- The description as the maker returns it in scope. -/
abbrev FD (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) :
    FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- The flat list's tests on the plan, from the description's one test. -/
theorem flat_plan {Z : ProofFile.Pub} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {c : Chain S Cl}
    (hp : (FD Z A B c).planOk = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true :=
  fun b hb => (((FileDescription.planOk_ok _).1 hp).blocks₁ b hb).1

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Xi Tok : Type} {rows cols nR : ℕ}
  {X : OnBytes.Model.Verify.Public}

/-- The table's own extractor at Dm's letters. -/
noncomputable abbrev extAt9 {Fr : Frame} (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X)
    (c₀ : CellsQ rows cols) (tokOf : ProofFile.InstPub × S → Tok) (k : ℕ) :
    (ProofFile.InstPub × S) × Fr.E.Str → (ProofFile.InstPub × S) × Fr.E.Str →
      Wit (CellsQ rows cols) Tok MsgT → Wit (CellsQ rows cols) Tok MsgT :=
  extQAt Dm.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N linksFull
    (flatPlacesOf linksFull true) (fun a => a) k

/-- **THE LAW OF THE KIND "frame", AS IT IS COUNTED.** -/
theorem frame_law_atThreeT (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {D : WholeD} {file : String} (hD : (FD Z A B c).data file = .ok D)
    (hp : (FD Z A B c).planOk = true)
    {b₁ : Block (FD Z A B c).S₁ (FD Z A B c).Cl} {l₁ : List (Block (FD Z A B c).S₁ (FD Z A B c).Cl)}
    {b₂ : Block (FD Z A B c).S₂ (FD Z A B c).Cl} {l₂ : List (Block (FD Z A B c).S₂ (FD Z A B c).Cl)}
    {b₃ : Block (FD Z A B c).S₃ (FD Z A B c).Cl} {l₃ : List (Block (FD Z A B c).S₃ (FD Z A B c).Cl)}
    (q₁ : (FD Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Z A B c).second.blocksInOrder = b₃ :: l₃)
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (e₁) (e₂) (e₃)
    (dW wEnd : Wit (CellsQ rows cols) Tok MsgT) (c₀ : CellsQ rows cols)
    (tokOf : ProofFile.InstPub × S → Tok) (Kn : ℕ → ProofFile.InstPub × S → Strs → Prop)
    (H : FrameParams9 Dm Z (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd) Kn)
    (hN : NoneBetween Dm.N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween Dm.N (flatPlacesOf linksFull true) (clearIx l))
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (hKn : ∀ k a, Rch k a → a.1.2.failed = none →
      Kn k (a.1.1, a.1.2) (strsOf (frameAt D (allOf D) D.key₁ 0) a.2))
    (hSeal : ∀ q, ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[357]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch 357
        (q.withMap (extAt9 Dm c₀ tokOf 357)))
    (hBehind : ∀ l, l < 25 → ∀ q,
      ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[behindIx l]? = some q →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch
        (behindIx l) (q.withMap (extAt9 Dm c₀ tokOf (behindIx l)))) :
    ∀ i q p, ((threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[i]? = some q →
      (flatPlacesOf linksFull true)[i]? = some p → p.kind = KindName.frame →
      TiedAtR Dm.N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) Rch i
        (q.withMap (extAt9 Dm c₀ tokOf i)) :=
  frame_kindTiedR9 hS hR O (threeCap_ofDesc e₁ e₂ e₃ dW wEnd hD hp q₁ q₂ q₃) (flat_plan hp) H
    (fun k => extAt9 Dm c₀ tokOf k)
    (ext_lays_nothing Dm.cs Dm.G Dm.arr Dm.smp Dm.ms Dm.decT c₀ tokOf Dm.N fun a => a) hN
    (givesIn_of_kn hKn) hSeal hBehind

end

end P1L20

#print axioms P1L20.flat_plan
#print axioms P1L20.frame_law_atThreeT
