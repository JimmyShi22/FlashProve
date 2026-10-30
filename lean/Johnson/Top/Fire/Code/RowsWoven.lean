-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/RowsWoven.lean: at the full size: ON THE PLAIN ROAD: THE GENERIC HISTORY (Reached.lean) WOVEN INTO THE KEY FILE's THREE TABLES AT THE FRAME: no table's binder turns. General in the description.
Main names.
  `st₁ F` | `st₂ F D` | `st₃ F D`: the three chains' starts, at the pieces' own states: what `RowsOwed`'s first boundary and its two seams lay, AND THAT WHAT IS HANDED WAS ITSELF REACHED BEHIND THE CHAIN BEFORE's LAST BLOCK.
  `reached_held_fst` · `hist₂_handed` | `hist₃_handed`: THE HISTORY CROSSES THE SEAMS: a step of a block as a piece holds it leaves what was handed alone (`held_decide`): so at every reached record of a later chain the handed part was reached.
  `Hist₁ F D k a` | `Hist₂` | `Hist₃`: `Reached` at the chain's frame's first tree, the description's own blocks as a piece holds them (`F.first.blocksInOrder.map held` …) and that start.
  `SeamsOwed`: `RowsOwed`'s five fields that are no law of a block (two seams · the end · the first boundary's two facts), to the letter.
  `rowsOwed_woven`: **`SeamsOwed` AT TABLES on | L, WITH ONE LAW A BLOCK AT THE WOVEN TABLES `fun k x => onⱼ k x ∧ Histⱼ F D k x.1`, GIVES `RowsOwed` AT THE WOVEN TABLES**: the seams and the first boundary hand each chain's start by their own make.
  `SeamsOwedH` · `rowsOwed_wovenH`: THE SEAMS AND THE END MAY SPEND THE HISTORY TOO: each is asked only at a record that was reached. `SeamsOwed.toH`: the first form gives it.
  `rowBlocksF₁` | `₂` | `₃`: under the heads, the n-th piece's block is the n-th of `F.….blocksInOrder.map held`: what `KeepsAt.reached` asks.
So a law may spend «this record was reached» in front, and a law that does not know it rides (Reached.lean).
Limits. BOOK-KEEPING: NOTHING IS PAID. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyOfRows
import Johnson.Top.Fire.Code.Reached
import Johnson.Desc.Plain.PaidKeeps

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

section
variable {P S Cl : Type}

/-- **A step of a block as a piece holds it leaves what was handed alone**: so whatever the start says of the handed part holds at every state that is reached. -/
theorem reached_held_fst (ft : ℕ) (l : List (Block S Cl)) (st₀ : P × S → Prop) (Q : P → Prop) (h0 : ∀ a, st₀ a → Q a.1) :
    ∀ (k : ℕ) (a : P × S), Reached ft (l.map held) st₀ k a → Q a.1
  | 0, a, h => h0 a h
  | k + 1, a, h => by
    obtain ⟨a', b, rs, cols, _, hr, hb, hs⟩ := h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, _, rfl⟩ := Option.map_eq_some_iff.1 hb
    rw [(held_decide b₀ a' _ _ a (step_decides hs)).1]
    exact reached_held_fst ft l st₀ Q h0 k a' hr

end

section
variable {XiK : Type} (F : FileDescription XiK) (D : WholeD)

/-- The first chain's start, at a piece's state. -/
def st₁ : F.XiPub × F.S₁ → Prop := fun a => a.2 = F.start₁ a.1
/-- **This state of the first chain was reached.** -/
abbrev Hist₁ : ℕ → F.XiPub × F.S₁ → Prop := Reached (frameAt D (allOf D) D.key₁ 0).ft (F.first.blocksInOrder.map held) (st₁ F)
/-- The shared chain's start: WHAT IS HANDED WAS REACHED BEHIND THE FIRST CHAIN's LAST BLOCK, and the state is the start at it. -/
def st₂ : (F.XiPub × F.S₁) × F.S₂ → Prop := fun a => Hist₁ F D F.first.blocksInOrder.length a.1 ∧ a.2 = F.start₂ a.1.1
abbrev Hist₂ : ℕ → (F.XiPub × F.S₁) × F.S₂ → Prop := Reached (frameAt D (allOf D) D.key₂ 0).ft (F.shared.blocksInOrder.map held) (st₂ F D)
/-- The last chain's start: likewise behind the shared chain's last block. -/
def st₃ : (F.XiPub × F.S₁ × F.S₂) × F.S₃ → Prop := fun a =>
  Hist₂ F D F.shared.blocksInOrder.length ((a.1.1, a.1.2.1), a.1.2.2) ∧ (F.start₃ a.1.1 a.1.2.1 a.1.2.2).toOption = some a.2
abbrev Hist₃ : ℕ → (F.XiPub × F.S₁ × F.S₂) × F.S₃ → Prop := Reached (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).ft (F.second.blocksInOrder.map held) (st₃ F D)

/-- **The history crosses the first seam**: at every state of the shared chain that is reached, what was handed was reached behind the first chain's last block. -/
theorem hist₂_handed (k : ℕ) (a : (F.XiPub × F.S₁) × F.S₂) (h : Hist₂ F D k a) : Hist₁ F D F.first.blocksInOrder.length a.1 :=
  reached_held_fst _ F.shared.blocksInOrder (st₂ F D) (Hist₁ F D F.first.blocksInOrder.length) (fun _ h => h.1) k a h

/-- **And the second.** -/
theorem hist₃_handed (k : ℕ) (a : (F.XiPub × F.S₁ × F.S₂) × F.S₃) (h : Hist₃ F D k a) :
    Hist₂ F D F.shared.blocksInOrder.length ((a.1.1, a.1.2.1), a.1.2.2) :=
  reached_held_fst _ F.second.blocksInOrder (st₃ F D) (fun x => Hist₂ F D F.shared.blocksInOrder.length ((x.1, x.2.1), x.2.2)) (fun _ h => h.1) k a h

end

section
variable {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD)
    {W : Type}
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)
    (on₁ L₁ : ℕ → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₂ L₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₃ L₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)

/-- **What is asked of the key file's rows beside the blocks' laws.** -/
structure SeamsOwed : Prop where
  seam₁ : ∀ b : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₁ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b →
    on₂ 0 ((b.1, F.start₂ b.1.1), b.2) ∧ (L₂ 0 ((b.1, F.start₂ b.1.1), b.2) → L₁ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b)
  seam₂ : ∀ b : ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₂ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b →
    (∀ s, (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s → on₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) ∧
      ((∃ s, (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s ∧ L₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) →
        L₂ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b)
  ends : ∀ b : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₃ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b → L₃ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b
  firstOn : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), F.okStart (instK rec) = true → ¬ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 → (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none →
    on₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => []))
  firstClaim : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), F.okStart (instK rec) = true → ¬ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 →
    L₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => [])) → (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none


/-- **The same, where the seams and the end MAY SPEND THE HISTORY**: each is asked only at a state that was reached. -/
structure SeamsOwedH : Prop where
  seam₁ : ∀ b : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₁ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b → Hist₁ F (DK.at frS.P.T.a) (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b.1 →
    on₂ 0 ((b.1, F.start₂ b.1.1), b.2) ∧ (L₂ 0 ((b.1, F.start₂ b.1.1), b.2) → L₁ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length) b)
  seam₂ : ∀ b : ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₂ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b → Hist₂ F (DK.at frS.P.T.a) (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b.1 →
    (∀ s, (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s → on₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) ∧
      ((∃ s, (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s ∧ L₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) →
        L₂ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length) b)
  ends : ∀ b : ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str, on₃ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b → Hist₃ F (DK.at frS.P.T.a) (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b.1 → L₃ (0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃.length) b
  firstOn : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), F.okStart (instK rec) = true → ¬ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 → (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec = none →
    on₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => []))
  firstClaim : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str), F.okStart (instK rec) = true → ¬ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 →
    L₁ 0 ((F.pub (instK rec), F.start₁ (F.pub (instK rec))), (y, fun _ => [])) → (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none


variable {F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃}

/-- The first form gives the second. -/
theorem SeamsOwed.toH (S : SeamsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃) : SeamsOwedH F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃ :=
  ⟨fun b h _ => S.seam₁ b h, fun b h _ => S.seam₂ b h, fun b h _ => S.ends b h, S.firstOn, S.firstClaim⟩

/-- **The history woven in.** -/
theorem rowsOwed_wovenH (S : SeamsOwedH F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂)
    (keeps₁ : Plain.EachKeeps (fun k x => on₁ k x ∧ Hist₁ F (DK.at frS.P.T.a) k x.1) L₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (keeps₂ : Plain.EachKeeps (fun k x => on₂ k x ∧ Hist₂ F (DK.at frS.P.T.a) k x.1) L₂ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (keeps₃ : Plain.EachKeeps (fun k x => on₃ k x ∧ Hist₃ F (DK.at frS.P.T.a) k x.1) L₃ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)) :
    RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (fun k x => on₁ k x ∧ Hist₁ F (DK.at frS.P.T.a) k x.1) L₁ (fun k x => on₂ k x ∧ Hist₂ F (DK.at frS.P.T.a) k x.1) L₂ (fun k x => on₃ k x ∧ Hist₃ F (DK.at frS.P.T.a) k x.1) L₃ where
  keeps₁ := keeps₁
  keeps₂ := keeps₂
  keeps₃ := keeps₃
  seam₁ := fun b h =>
    have e : 0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁.length = F.first.blocksInOrder.length := by
      rw [rowLen₁, q₁, List.length_cons]; omega
    ⟨⟨(S.seam₁ b h.1 h.2).1, (congrArg (fun n => Hist₁ F (DK.at frS.P.T.a) n b.1) e).mp h.2, rfl⟩, (S.seam₁ b h.1 h.2).2⟩
  seam₂ := fun b h =>
    have e : 0 + 1 + (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂.length = F.shared.blocksInOrder.length := by
      rw [rowLen₂, q₂, List.length_cons]; omega
    ⟨fun s hs => ⟨(S.seam₂ b h.1 h.2).1 s hs, (congrArg (fun n => Hist₂ F (DK.at frS.P.T.a) n b.1) e).mp h.2, hs⟩, (S.seam₂ b h.1 h.2).2⟩
  ends := fun b h => S.ends b h.1 h.2
  firstOn := fun rec y h₁ h₂ h₃ => ⟨S.firstOn rec y h₁ h₂ h₃, rfl⟩
  firstClaim := S.firstClaim

/-- The same from the first form. -/
theorem rowsOwed_woven (S : SeamsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃)
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂)
    (keeps₁ : Plain.EachKeeps (fun k x => on₁ k x ∧ Hist₁ F (DK.at frS.P.T.a) k x.1) L₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (keeps₂ : Plain.EachKeeps (fun k x => on₂ k x ∧ Hist₂ F (DK.at frS.P.T.a) k x.1) L₂ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (keeps₃ : Plain.EachKeeps (fun k x => on₃ k x ∧ Hist₃ F (DK.at frS.P.T.a) k x.1) L₃ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)) :
    RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (fun k x => on₁ k x ∧ Hist₁ F (DK.at frS.P.T.a) k x.1) L₁ (fun k x => on₂ k x ∧ Hist₂ F (DK.at frS.P.T.a) k x.1) L₂ (fun k x => on₃ k x ∧ Hist₃ F (DK.at frS.P.T.a) k x.1) L₃ :=
  rowsOwed_wovenH S.toH q₁ q₂ keeps₁ keeps₂ keeps₃

/-- `RowsOwed` holds them. -/
theorem RowsOwed.seams (H : RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃) : SeamsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃ :=
  ⟨H.seam₁, H.seam₂, H.ends, H.firstOn, H.firstClaim⟩

/-- Under the head, the n-th piece's block of chain 1 is the n-th of the description's own, held. -/
theorem rowBlocksF₁ (q : F.first.blocksInOrder = c₁ :: k₁) (n : ℕ) (p) (h : ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p) : (F.first.blocksInOrder.map held)[n]? = some p.b := by
  rw [q]
  exact rowBlocks₁ (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h

/-- Under the head, the n-th piece's block of chain 2 is the n-th of the description's own, held. -/
theorem rowBlocksF₂ (q : F.shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (p) (h : ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) : (F.shared.blocksInOrder.map held)[n]? = some p.b := by
  rw [q]
  exact rowBlocks₂ (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h

/-- Under the head, the n-th piece's block of chain 3 is the n-th of the description's own, held. -/
theorem rowBlocksF₃ (q : F.second.blocksInOrder = c₃ :: k₃) (n : ℕ) (p) (h : ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? = some p) : (F.second.blocksInOrder.map held)[n]? = some p.b := by
  rw [q]
  exact rowBlocks₃ (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd n p h

end

end LPFD

#print axioms LPFD.reached_held_fst
#print axioms LPFD.hist₂_handed
#print axioms LPFD.hist₃_handed
#print axioms LPFD.SeamsOwed
#print axioms LPFD.SeamsOwedH
#print axioms LPFD.rowsOwed_wovenH
#print axioms LPFD.rowsOwed_woven
#print axioms LPFD.RowsOwed.seams
#print axioms LPFD.rowBlocksF₁
#print axioms LPFD.rowBlocksF₂
#print axioms LPFD.rowBlocksF₃
