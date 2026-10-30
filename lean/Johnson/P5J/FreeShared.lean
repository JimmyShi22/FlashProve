-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FreeShared.lean: THE TOWER'S FREE LETTERS (structure `Free`, TowerFree.lean) LAID AT
CONSTANTS, FIRST HALF: the letters that the shared table's constant, the three flat lists and the
top fix. Definitions, and equations by rfl. Under the one head `AtMg`.
  `AtMg.shPlan`   the shared table's plan at the seat: `Sh.planAt` at F0T.
  `AtMg.shFirst`  the first table's five letters that the shared table's constant reads.
  `AtMg.shOpen`   the shared table's open letters at the seat: `Sh.openAt` itself.
  `AtMg.c₁ … k₃`  the heads and tails of the three flat lists, at proofs that none is empty
                  (`flatSome` at the laid data): no default value.
  `idlePlaces`    a value for Q₀. Of Q₀ the tower reads nothing: `placesM` lays its own on₁ and R₁
                  over it and no other field is read (`placesM_on₁_any`, `placesM_R₁_any`).
  `AtMg.freeOf`   **the value**, general in the seven letters of the last table's and the pieces'
                  side (ML PLm e₁ e₂ e₃ dW wEnd): FreeAt.lean lays these.
  `freeOf_*`      what each letter is at the value, in the form in which a field's
                  lemma ends: each by rfl.
Limits. A VALUE AND EQUATIONS: no law, no field of h.Five or h.Kind is paid here. smp₁ is the first
table's reader of samples AT THE SHARED CHAIN's CODES (the two tables' files reach the codes by two
paths of the public part; that the paths agree under the head is owed: hcs).
(Where this and lean/THEOREM.md differ, the page holds.)
Whether AtMg can be met at
the release's own files is not shown here. The full size alone. No soundness follows. Nothing on
hiding. It holds no coding theory.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.RowsAtMg
import Johnson.Goal.Skeleton.ProofAtName
import Johnson.Desc.K14.Law.SharedConstHeldAt
import Johnson.Desc.K14.Law.SharedConstStart
import Johnson.Desc.K14.Law.SharedConstZero

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open Johnson.Desc.First.Walk.Tied (EndAt₁)
open Desc.K14.Law.Fence (numbersSh)
open Desc.K14.Law (ShPlan ShOpen Sh.planAt Sh.openAt Sh.Open₁ Sh.nums Sh.mg Sh.pm Sh.own Sh.ex)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- A list that is not empty is its head on its tail. -/
theorem cons_of_ne.{u} {α : Type u} : ∀ (l : List α) (h : l ≠ []), l = l.head h :: l.tail
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

/-- **The shared table's plan at the seat.** -/
def AtMg.shPlan (_ : AtMg o Z D r Zp Np cF) : ShPlan ProofFile.Inst :=
  Sh.planAt Zp Np (F0T o Zp Np cF)

/-- **The first table's five letters, as the shared table's constant reads them.** The reader of
    samples is the first table's own text (`smpNamed` at the plan's seats), at the shared chain's
    codes. -/
def AtMg.shFirst (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)) :
    Sh.Open₁ (CellsM numsFull) At.Tok h.shPlan.Q where
  N₁ := At.N Zp cF
  links := fullLinks
  Mg₁ := h.mq 𝔇₀
  smp₁ := smpNamed h.shPlan.Q.codes (At.seats Zp)
  ms₁ := At.ms Zp Z.lay

/-- **The shared table's open letters at the seat**: `Sh.openAt`. -/
def AtMg.shOpen (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp)) :
    ShOpen ProofFile.InstPub (ProofFile.InstPub × TS) (CellsM numsFull) At.Tok h.shPlan.Q :=
  Sh.openAt o Zp Np (Desc.K14.Law.secondAt Zp Np) cF h.plan.shape (ppAtFiles Z.pol Z.KL) (At.EAt Z)
    (h.shFirst 𝔇₀)

/-- None of the three flat lists is empty. -/
theorem AtMg.flats (h : AtMg o Z D r Zp Np cF) :
    (F0T o Zp Np cF).first.blocksInOrder ≠ [] ∧ (F0T o Zp Np cF).shared.blocksInOrder ≠ [] ∧
      (F0T o Zp Np cF).second.blocksInOrder ≠ [] :=
  flatSome _ (F0T o Zp Np cF) "proof file" _ h.laid.data

def AtMg.c₁ (h : AtMg o Z D r Zp Np cF) := (F0T o Zp Np cF).first.blocksInOrder.head h.flats.1
def AtMg.k₁ (_ : AtMg o Z D r Zp Np cF) := (F0T o Zp Np cF).first.blocksInOrder.tail
def AtMg.c₂ (h : AtMg o Z D r Zp Np cF) := (F0T o Zp Np cF).shared.blocksInOrder.head h.flats.2.1
def AtMg.k₂ (_ : AtMg o Z D r Zp Np cF) := (F0T o Zp Np cF).shared.blocksInOrder.tail
def AtMg.c₃ (h : AtMg o Z D r Zp Np cF) := (F0T o Zp Np cF).second.blocksInOrder.head h.flats.2.2
def AtMg.k₃ (_ : AtMg o Z D r Zp Np cF) := (F0T o Zp Np cF).second.blocksInOrder.tail

/-- A value for a letter of which nothing is read. -/
def idlePlaces (D' : WholeD) (all : List LeftT) (S₁ S₂ S₃ W : Type) : Places D' all S₁ S₂ S₃ W where
  on₁ := fun _ _ => True
  R₁ := fun _ _ _ => True
  on₂ := fun _ _ => True
  R₂ := fun _ _ _ => True
  on₃ := fun _ _ => True
  R₃ := fun _ _ _ => True

section Letters

variable (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
  (ML : MeaningL (F0T o Zp Np cF).S₃ (Wit (CellsM numsFull) At.Tok MsgT))
  (PLm : PromMeaningL (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).S₃
    ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁))
  (e₁ : (i : ℕ) → (ds : List RDT) → ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM numsFull) At.Tok MsgT →
      Wit (CellsM numsFull) At.Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) →
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM numsFull) At.Tok MsgT →
      Wit (CellsM numsFull) At.Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) →
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) ×
        (F0T o Zp Np cF).S₃) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
        (F0T o Zp Np cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM numsFull) At.Tok MsgT →
      Wit (CellsM numsFull) At.Tok MsgT)
  (dW wEnd : Wit (CellsM numsFull) At.Tok MsgT)

/-- **The three rows of pieces at the value.** -/
def AtMg.threeOf :=
  piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) h.c₁ h.k₁ h.c₂ h.k₂ h.c₃ h.k₃
    (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd

/-- **The relation at which the shared chain's row is counted**: the shared table's constant's own
    step. -/
def AtMg.q₂Of :=
  stepAt (Sh.nums h.shPlan (h.shOpen 𝔇₀)) (Sh.mg h.shPlan (h.shOpen 𝔇₀))
    (Sh.pm h.shPlan (h.shOpen 𝔇₀)) (Sh.own h.shPlan (h.shOpen 𝔇₀)) true
    (h.threeOf e₁ e₂ e₃ dW wEnd).p₂ (h.threeOf e₁ e₂ e₃ dW wEnd).l₂
    (extOf (Sh.nums h.shPlan (h.shOpen 𝔇₀)) (h.threeOf e₁ e₂ e₃ dW wEnd).p₂
      (h.threeOf e₁ e₂ e₃ dW wEnd).l₂ (Sh.ex h.shPlan (h.shOpen 𝔇₀) _))

/-- **THE VALUE, general in the last table's and the pieces' seven letters.** -/
def AtMg.freeOf : Free numsFull D (F0T o Zp Np cF) At.Tok where
  Q₀ := idlePlaces _ _ _ _ _ _
  c₀ := At.c₀
  Ns := numbersSh (Desc.K14.Law.Sh.t₁ h.shPlan) (Desc.K14.Law.Sh.layU h.shPlan)
    (Desc.K14.Law.Sh.layO h.shPlan) (0, 0) (0, 0)
  MgS := Sh.mg h.shPlan (h.shOpen 𝔇₀)
  ML := ML
  Pm := Sh.pm h.shPlan (h.shOpen 𝔇₀)
  PLm := PLm
  split := true
  Q₂ := h.q₂Of 𝔇₀ e₁ e₂ e₃ dW wEnd
  rP := VerifierAndGoals.AtTheName.recZ Z
  c₁ := h.c₁
  k₁ := h.k₁
  c₂ := h.c₂
  k₂ := h.k₂
  c₃ := h.c₃
  k₃ := h.k₃
  e₁ := e₁
  e₂ := e₂
  e₃ := e₃
  dW := dW
  wEnd := wEnd

local notation "𝔏₀" => AtMg.freeOf h 𝔇₀ ML PLm e₁ e₂ e₃ dW wEnd

/-! ## What each letter is at the value -/

theorem freeOf_q₁ : (F0T o Zp Np cF).first.blocksInOrder = (𝔏₀).c₁ :: (𝔏₀).k₁ := cons_of_ne _ h.flats.1
theorem freeOf_q₂ : (F0T o Zp Np cF).shared.blocksInOrder = (𝔏₀).c₂ :: (𝔏₀).k₂ := cons_of_ne _ h.flats.2.1
theorem freeOf_q₃ : (F0T o Zp Np cF).second.blocksInOrder = (𝔏₀).c₃ :: (𝔏₀).k₃ := cons_of_ne _ h.flats.2.2

/-- The numbers that the tower reads are the constant's. -/
theorem freeOf_nums : tiedNumbers (At.N Zp cF) (𝔏₀).Ns = Sh.nums h.shPlan (h.shOpen 𝔇₀) := rfl

/-- The meaning that the tower reads is the constant's. -/
theorem freeOf_mg : tiedMeaning (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
      ((a.1, a.2) : (F0T o Zp Np cF).XiPub × TS)) (h.mq 𝔇₀) (𝔏₀).MgS =
    Sh.mg h.shPlan (h.shOpen 𝔇₀) := rfl

theorem freeOf_pm : (𝔏₀).Pm = Sh.pm h.shPlan (h.shOpen 𝔇₀) := rfl

theorem freeOf_split : (𝔏₀).split = true := rfl

/-- The constant's R, at the tower's own name of the IOP as written in Lean: reached at the first
    chain's end, at a typed instance's public part. -/
theorem shOpen_R : (h.shOpen 𝔇₀).R = fun p => EndAt₁ (F0T o Zp Np cF) p ∧
    ∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub := rfl

/-- The two later tables' own condition, as the tower spells it, is the constant's. -/
theorem freeOf_own : ocR (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
      ((a.1, a.2) : (F0T o Zp Np cF).XiPub × TS)) (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps
      (h.shOpen 𝔇₀).R =
    Sh.own h.shPlan (h.shOpen 𝔇₀) := rfl

/-- Of Q₀ nothing is read: the first chain's two fields are the table's, whatever Q₀ is. -/
theorem placesM_any {D' : WholeD} {all : List LeftT} {P S₁ S₂ S₃ W : Type} (ft : ℕ) (N : Numbers)
    (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
    (get : S₁ → P × VerifiableInference.Desc.First.S) (R₀ : S₁ × (EAll D' all).Str → W → Prop)
    (Q Q' : Places D' all S₁ S₂ S₃ W) :
    (placesM ft N Mg links ps get R₀ Q).on₁ = (placesM ft N Mg links ps get R₀ Q').on₁ ∧
      (placesM ft N Mg links ps get R₀ Q).R₁ = (placesM ft N Mg links ps get R₀ Q').R₁ :=
  ⟨rfl, rfl⟩

/-- The reader of samples is one text at equal codes. -/
theorem smpNamed_heq {P : Type} {c c' : OnBytes.Codes} (e : c = c') (seats : List (ℕ × ℕ)) :
    HEq (smpNamed (P := P) c seats) (smpNamed (P := P) c' seats) := by
  subst e
  rfl

/-- **Where the two paths to the codes agree, the constant's reader of the first chain's samples is
    the first table's own.** hcs: `Sh.hcs_in_scope`, under its premises. -/
theorem shOpen_smp (hcs : At.cs Zp = h.shPlan.Q.codes) :
    HEq (At.smp Zp) (h.shOpen 𝔇₀).smp₁ :=
  smpNamed_heq hcs (At.seats Zp)

/-- **"The key fits" at every typed instance, at the value**: the premise of the tower's payer of
    tables_fit's field SH, from the shared table's files' theorem, under its test on the sizes. -/
theorem freeOf_hk (hA : H2K.Sizes.AtFull Zp.p.chains.made) (z : LPFD.Full.XF × RecFull) :
    (𝔏₀).Pm.shape 0 (Desc.K14.first (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes
      (LPFD.Full.instanceAsPlainRecord z).pub.key) = true :=
  Desc.K14.Law.Sh.shape_start_at Zp Np (F0T o Zp Np cF) (h.shOpen 𝔇₀) z hA

end Letters

end P5J

#print axioms P5J.AtMg.flats
#print axioms P5J.freeOf_q₁
#print axioms P5J.freeOf_q₂
#print axioms P5J.freeOf_q₃
#print axioms P5J.freeOf_nums
#print axioms P5J.freeOf_mg
#print axioms P5J.freeOf_pm
#print axioms P5J.freeOf_split
#print axioms P5J.shOpen_R
#print axioms P5J.freeOf_own
#print axioms P5J.placesM_any
#print axioms P5J.shOpen_smp
#print axioms P5J.freeOf_hk
