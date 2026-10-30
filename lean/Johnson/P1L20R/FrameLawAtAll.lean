-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1L20R/FrameLawAtAll.lean: THE SHARE OF THE KIND "frame" ON THE FIRST CHAIN, AT THE
CLOSED CONSTANT, WITH EVERY HAND-IN THAT LIES SPENT: what is still in front of it, a binder a debt.

  frame_law_atAll   at Dm := dmOf h (FrameAtAll.lean), at the three rows of pieces threeCap
                    (Johnson/Goal/Skeleton/TheThree.lean), at the table's own extractor, with a
                    condition Rch beside the promise: at every place of the kind "frame": TiedAtR

In front of it, beside the head h, the scope, the opening of the maker, the description's data and
its test on the plan:
  low               the OOD-sampled oracle messages whose pin is open in front of each of the 51 sit
                    in trees below the piece's base
  hW, hBase, hSize  three facts on the files' data, the pieces' bases and the book's number of trees
                    (FrameKn.lean: fence9_of's binders; its fourth, on the code switch's first tree,
                    is paid: FtAtSwitch.lean)
  carryElseLaid, carryElseClear   the carried word's sentence where the next code switch does not
                    stand at a link
  hN                the constant's numbers of trees and messages do not move across the 51
  hKn               of every statement that is reached in front of one of the 51 numbers and bears
                    no mark: the tight list KnTight 0: the book is in order from tree 0 on, it fits,
                    the carried rows name messages that have a place
  hSeal, hBehind    the two shares that are other files' to show

Limits. None of these binders is shown here. A member of the head AtMgA is proved at storedPublicFiles and zGap
alone (at secondHashFunction; side library AtFullSide/Top/). The chain c
of the opening and the head's cF, the seats A and B and the head's, the second hash function o and
secondHashFunction are tied by nothing here. No soundness statement.

-/
import Johnson.P1L20R.FrameAtAll
import Johnson.P1L20R.FrameLawAtThree
import Johnson.P1L20R.FrameKn
import Johnson.P1L20R.FtAtSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K2Caller (rest)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA)

section
variable {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The witnesses' type at the constant. -/
abbrev WitAll : Type :=
  Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok MsgT

/-- **THE LAW OF THE KIND "frame" AT THE CONSTANT.** -/
theorem frame_law_atAll (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Z.pol lay Z.KL F Zp Bs base₀ c A B)
    {D : WholeD} {file : String} (hD : (FD Zp A B c).data file = .ok D)
    (hp : (FD Zp A B c).planOk = true)
    {b₁ : Block (FD Zp A B c).S₁ (FD Zp A B c).Cl}
    {l₁ : List (Block (FD Zp A B c).S₁ (FD Zp A B c).Cl)}
    {b₂ : Block (FD Zp A B c).S₂ (FD Zp A B c).Cl}
    {l₂ : List (Block (FD Zp A B c).S₂ (FD Zp A B c).Cl)}
    {b₃ : Block (FD Zp A B c).S₃ (FD Zp A B c).Cl}
    {l₃ : List (Block (FD Zp A B c).S₃ (FD Zp A B c).Cl)}
    (q₁ : (FD Zp A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Zp A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Zp A B c).second.blocksInOrder = b₃ :: l₃)
    (h : AtMgA o Z D₀ r Zp Np cF x) (e₁) (e₂) (e₃) (dW wEnd : WitAll)
    (c₀ : CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull))
    (tokOf : ProofFile.InstPub × S → P5J.At.Tok)
    (low : ∀ k, k ∈ our51 → ∀ q,
      ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[k]? = some q →
      LowAt (dmOf h).N (openL9 k) q.base)
    (Dw : WholeD) (hW : ProofFile.wholeAt Zp = some Dw)
    (hBase : ∀ k, k ∈ our51 → ∀ q,
      ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[k]? = some q →
      q.base ≤ Dw.t₁)
    (hSize : ∀ k, k ∈ our51 → ∀ q,
      ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[k]? = some q →
      ∀ p s y, InAt9 (dmOf h) (KnTight 0) k (p, s) y → s.book.trees.size ≤ q.base)
    (carryElseLaid : ∀ l, l < 25 → ∀ q,
      ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[14 * l + 1]? = some q →
      ∀ m, openP9 (14 * l + 1 + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
      GoesBack (StepRel (Yes (layFront l)) q.base (InAt9 (dmOf h) (KnTight 0) (14 * l + 1)))
        ((dmOf h).cr1 m))
    (carryElseClear : ∀ l, l < 25 → ∀ fs f,
      Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs →
      fs[l]? = some f → ∀ q,
      ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[clearIx l]? = some q →
      ∀ m, openP9 (clearIx l + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
      GoesBack (StepRel (Yes f.clear) q.base (InAt9 (dmOf h) (KnTight 0) (clearIx l)))
        ((dmOf h).cr1 m))
    (hN : NoneBetween (dmOf h).N (flatPlacesOf linksFull true) 0 ∧
      (∀ l, l < 25 → NoneBetween (dmOf h).N (flatPlacesOf linksFull true) (14 * l + 1)) ∧
      ∀ l, l < 25 → NoneBetween (dmOf h).N (flatPlacesOf linksFull true) (clearIx l))
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ 0).E.Str → Prop)
    (hKn : ∀ k a, Rch k a → a.1.2.failed = none →
      KnTight 0 k (a.1.1, a.1.2) (strsOf (frameAt D (allOf D) D.key₁ 0) a.2))
    (hSeal : ∀ q, ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[357]? = some q →
      TiedAtR (dmOf h).N (mgAll (dmOf h) mgBase) linksFull (flatPlacesOf linksFull true)
        (fun a => a) Rch 357 (q.withMap (extAt9 (dmOf h) c₀ tokOf 357)))
    (hBehind : ∀ l, l < 25 → ∀ q,
      ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[behindIx l]? = some q →
      TiedAtR (dmOf h).N (mgAll (dmOf h) mgBase) linksFull (flatPlacesOf linksFull true)
        (fun a => a) Rch (behindIx l) (q.withMap (extAt9 (dmOf h) c₀ tokOf (behindIx l)))) :
    ∀ i q p, ((threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).p₁ ::
        (threeCap (FD Zp A B c) D b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ dW wEnd).l₁)[i]? = some q →
      (flatPlacesOf linksFull true)[i]? = some p → p.kind = KindName.frame →
      TiedAtR (dmOf h).N (mgAll (dmOf h) mgBase) linksFull (flatPlacesOf linksFull true)
        (fun a => a) Rch i (q.withMap (extAt9 (dmOf h) c₀ tokOf i)) :=
  frame_law_atThreeT hS hR O hD hp q₁ q₂ q₃ (dmOf h) e₁ e₂ e₃ dW wEnd c₀ tokOf (KnTight 0)
    (frameParams9_of (frameOwed9_atAll h low
      (fence9_of Dw hW hBase hSize fun _ _ m _ _ => ft_at_switch O.pub m) carryElseLaid
      carryElseClear)) hN Rch hKn hSeal hBehind

end

end P1L20

#print axioms P1L20.frame_law_atAll
