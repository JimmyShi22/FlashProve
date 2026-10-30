-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainFilled.lean: first_chain_at_first_L WITH THE FIELDS FILLED AS THE HOUSES'
THEOREMS LAND: the theorem's premise list is the list of what is still owed.

Filled here: reply (338: reply_values), switchHead (339: switchHead_at_head) and lookHead (345: valuesJ_345).

  FilledRest            the eight fields left
  first_chain_filled    **yes₁ ∧ carry₁**

Limits. An implication: hyes, hL and the eight fields are premises. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainAtFirstL
import Johnson.AtFull.Shape.HeadValsReach
import Johnson.AtFull.Shape.Scope.SwitchHeadValues
import Johnson.Desc.ProofFile.Honest.K7.AtValues
import Johnson.Desc.ProofFile.Honest.K7.AtFill
import Johnson.Desc.ProofFile.Honest.Thread.AskedIsToken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (Shape Thread ProverCoinCounts Coins Mid Prover Local SaidOk ValuesJ NextJ AcceptedJ shapeJ
  halved OnlineProverWithDescription onlineProverFromPublicFiles onlineProverPartsInUse WiderIn OnlineProverArguments IndexCommitterCoins Cells SaidWalk Fall fallsBy replyHalf
  replyLot K7Stands reply_values)
open ProofFile.Honest.FirstThread

/-- **THE EIGHT FIELDS LEFT.** A premise's form. -/
structure FilledRest {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  layers : ∀ l, l < 24 → l % 2 = 0 → PaidJ T Said J Zs fall (14 * l + 3 + 1)
  batch : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 8 + 1)
  behind : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 9 + 1)
  equation : ∀ l, l < 24 → PaidJ T Said J Zs fall (14 * l + 10 + 1)
  head : PaidJ T Said J Zs fall (337 + 4)
  batchHead : PaidJ T Said J Zs fall (337 + 10)
  behindHead : PaidJ T Said J Zs fall (337 + 11)
  equationHead : PaidJ T Said J Zs fall (337 + 12)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

/-- A side of the kind K7 in the base prover's first chain is the lot's. -/
theorem k7_side_only (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind = .K7 →
      g = replyHalf (A.G.built.size - 1) 1 A.G.W.hS.V := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := ProofFile.Honest.atPure_ok hA
  intro g hg hk
  rw [eH] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1
    (hg : g ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O).lots.flatMap fun L => L.halves A.Z A.G)
  rw [ProofFile.Honest.widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h1 | rfl) | rfl) | rfl
  · obtain rfl := ProofFile.Honest.k7_only I OnBytes.secondHashFunction Sz O A.Z A.G M h1 g hgM hk
    exact List.mem_singleton.1 hgM
  · have hk' := ProofFile.Honest.closeLotAt_kinds I Sz A.Z A.G g hgM
    rw [hk] at hk'
    cases hk'
  · have hk' := ProofFile.Honest.proxLotAt_kinds I Sz A.Z A.G g hgM
    rw [hk] at hk'
    cases hk'
  · rw [ProofFile.Honest.wLotAt_halves] at hgM
    cases hm : OnBytes.linMessageW A.Z.first.lin with
    | none =>
      rw [hm] at hgM
      cases hgM
    | some msg =>
      rw [hm] at hgM
      have e := List.mem_singleton.1 hgM
      rw [e] at hk
      cases hk

/-- **The search at the place of K7 finds the lot's half.** -/
theorem k7_find (h : HeadAtReturn files A)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) :
    A.H.first.find? (fun g => g.place == IM.k7Place) = some (replyHalf 24 1 Bs.G₀.W.hS.V) := by
  obtain ⟨Bs', base, O'⟩ := h.head.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O'.made)
  obtain ⟨-, eG, -⟩ := ProofFile.Honest.atPure_at_laid_ground h.head.laid O'.blank hA
  have hs : A.G.built.size = 25 := by
    rw [eG]
    exact ProofFile.Honest.FirstFill.built_25 h.head O'.blank
  have hm0 := ProofFile.Honest.K1.Pay.side_in_first I Sz O hA (M := replyLot)
    (g := replyHalf (A.G.built.size - 1) 1 A.G.W.hS.V)
    (by
      show replyLot ∈ [_, _, _, _, _, _, _, _, _, _]
      exact .tail _ (.tail _ (.head _)))
    (List.Mem.head _)
  have hm : replyHalf (W₀ := W₀) (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) 24 1 A.G.W.hS.V ∈ A.H.first := by
    rw [hs] at hm0
    exact hm0
  have hsome : (A.H.first.find? fun g => g.place == IM.k7Place).isSome = true :=
    List.find?_isSome.2 ⟨_, hm, beq_self_eq_true _⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have pb := List.find?_some hy
  have hp : y.place = IM.k7Place := beq_iff_eq.1 pb
  have e := k7_side_only I Sz O hA y (List.mem_of_find?_eq_some hy) (by rw [hp])
  rw [hy, e, hs, eG]

/-- The token is a token, at the thread's inputs. -/
theorem asked_at (h : HeadAtReturn files A) (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) :
    ∀ v, (firstThread h parts w).valid v → OnBytes.Desc.Reply.isToken Bs.G₀.W.hS.V v.x.asked = true := by
  intro v hv
  obtain ⟨Bs', base, O'⟩ := h.head.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O'.made)
  have ho : ProofFile.okBy _ _ A.Z v.x = true := (Bool.and_eq_true_iff.1 hv.2.1).1
  have eV : A.Z.p.X.hS.V = A.Z.p.X.P.h.V := by
    have e : Bs.G₀.W.hS.V = Bs.G₀.W.P.h.V :=
      congrArg (·.V) (Meaning.HeadS.headShape_of_public O'.public)
    rw [O'.W] at e
    exact e
  rw [O'.W]
  exact asked_is_token ho eV (IM.vocab_small h.head.scope h.head.reads O')

set_option maxRecDepth 100000 in
/-- **yes₁ AND carry₁ WITH reply, switchHead AND lookHead PAID.** -/
theorem first_chain_filled (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (f₁ : List (Fall TS))
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes startShA 358 = true)
    (hL : AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (fallsBy f₁ h.description.first.blocksInOrder) (353 + 1))
    (Rest : FilledRest (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀))
      (fallsBy f₁ h.description.first.blocksInOrder)) :
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy f₁ h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy f₁ h.description.first.blocksInOrder) b) := by
  obtain ⟨Bs', base, O'⟩ := h.head.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O'.made)
  obtain ⟨blk, -, -, -, K, -⟩ := ProofFile.Honest.k7_stands_of_open h.head.scope h.head.reads O'
    (firstThread h parts w) rfl (k7_find I Sz O h hA hB)
  have rp := reply_values A.Z Bs.G₀ K (asked_at h hB parts w)
    (SaidWalk (firstThread h parts w) B m₀)
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
    (Tab.g A.Z Bs.G₀) (fallsBy f₁ h.description.first.blocksInOrder)
  have lk := valuesJ_345 h.head Bs.G₀ A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ProofFile.Honest.ReadyInput h.description A.H)
    (ProofFile.Honest.ridersOf (ProofFile.Honest.csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (ProofFile.Honest.kpBy (firstClauses h)) w
    (SaidWalk (firstThread h parts w) B m₀)
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
    (fallsBy f₁ h.description.first.blocksInOrder)
  have sw := Scope.switchHead_at_head h.head hB A.H parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
    (ProofFile.Honest.ReadyInput h.description A.H)
    (ProofFile.Honest.ridersOf (ProofFile.Honest.csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (ProofFile.Honest.kpBy (firstClauses h)) w
    (SaidWalk (firstThread h parts w) B m₀) (fun _ _ _ a => a.1.1)
    (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
    (fallsBy f₁ h.description.first.blocksInOrder)
  exact first_chain_at_first_L I Sz O hK hA h parts w hB B m₀ f₁ hyes hL
    { layers := Rest.layers, batch := Rest.batch, behind := Rest.behind, equation := Rest.equation,
      reply := .inl rp, switchHead := .inl sw, head := Rest.head, lookHead := .inl lk,
      batchHead := Rest.batchHead, behindHead := Rest.behindHead,
      equationHead := Rest.equationHead }

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_filled
