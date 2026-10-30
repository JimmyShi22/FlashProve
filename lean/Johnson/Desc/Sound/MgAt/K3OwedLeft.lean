-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3OwedLeft.lean: the kind "lookup" (K3): THE LEDGER `K3OwedR`
(Johnson/Desc/Sound/MgAt/K3Owed.lean) CUT IN TWO: its five sentences on 𝔇 and Mg alone (hM, es, hD,
hd, hIn), which are shown at the closed constant (Johnson/P5J/K03Terms.lean), and the five fields
that are left: `K3LeftR`: fold (the facts along the fold) and the four families dig, att, lay, head.

Main names: `K3LeftR` · `k3Owed_of_left` · `k3Owed_iff_left`.

THE FIELDS' TEXTS ARE `K3OwedR`'s OWN, LAID HERE BY A PROGRAM; Lean holds each against its original.

Limits: a definition and two re-packings. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.Sound.MgAt.K3Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  {Fr : Frame} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (codes : Codes) (shape : Params.ReqShape)
  (pieces : List (Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl
    (Desc.Wit (CellsQ rows cols) Tok MsgT)))
  (seats : List (ℕ × ℕ)) (s₀ : Desc.First.S)
  (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
  (tok : Desc.Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V)
  (told : List (List Desc.Oracle)) (arrs : Array (Nat × String))

/-- **What is left of the ledger beside its sentences on 𝔇 and Mg.** -/
structure K3LeftR : Prop where
  /-- what the kind's paid fields spend of the facts along the fold -/
  fold : K3Fold Rch 𝔇.sent
  dig : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → ∀ x tl, digAt X l = some (x, tl) →
    ∀ q, pieces[k3K l true]? = some q → ∀ b', k3Const X codes shape l true = some b' →
      DigOwedR 𝔇.G X 𝔇.sent 𝔇.l3 𝔇.N (mgAll 𝔇 Mg) Rch K3Lot.ofForm 𝔇.ms (IM.k3Place l true)
        (MgAt.nextOf l true) (k3K l true) l sub x tl
        (smpDigits seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  att : ∀ l < 25, ∀ x A tl, attAt X l = some (x, A, tl) →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      lookAt X l false = some x ∧
      AttOwedR 𝔇 Mg Rch K3Lot.ofForm num (idx l) tls tok (IM.k3Place l false)
        (MgAt.nextOf l false)
        (k3K l false) l x A tl (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  lay : ∀ l < 25, ∀ x tl, layAt X l = some x → tlAt X l = some tl →
    ∀ q, pieces[k3K l false]? = some q → ∀ b', k3Const X codes shape l false = some b' →
      lookAt X l false = some x ∧
      LayOwedR 𝔇 Mg Rch K3Lot.ofForm num (idx l) tls tok (IM.k3Place l false)
        (MgAt.nextOf l false)
        (k3K l false) l x tl (smpCalls seats 𝔇.sent 𝔇.l3.rad 𝔇.l3.seat x) q b' told
  head : ∀ x, Desc.Kinds.Head.Law.headAt X = some x →
    ∀ q, pieces[k3K 24 false]? = some q → ∀ b', k3Const X codes shape 24 false = some b' →
      HeadRestR 𝔇 Mg Rch K3Lot.ofForm seats s₀ x q b' arrs (IM.k3Place 24 false)
        (MgAt.nextOf 24 false) told

variable {𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs}

/-- **The five sentences and what is left give the ledger.** -/
theorem k3Owed_of_left (hM : Mg.more = {}) (es : 𝔇.smp = smpNamed 𝔇.cs seats)
    (hD : 𝔇.digitsPart = digitsPartK3 X 𝔇.sent 𝔇.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → 𝔇.decT c y' = 𝔇.decT c y)
    (hIn : InOrderReads Mg)
    (V : K3LeftR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs) :
    K3OwedR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs :=
  ⟨hM, es, hD, hd, hIn, V.fold, V.dig, V.att, V.lay, V.head⟩

/-- And the ledger gives them. -/
theorem k3Owed_iff_left :
    K3OwedR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs ↔
      (Mg.more = {} ∧ 𝔇.smp = smpNamed 𝔇.cs seats ∧
        𝔇.digitsPart = digitsPartK3 X 𝔇.sent 𝔇.l3 ∧
        (∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → 𝔇.decT c y' = 𝔇.decT c y) ∧
        InOrderReads Mg) ∧
      K3LeftR 𝔇 Mg Rch codes shape pieces seats s₀ num idx tls tok told arrs :=
  ⟨fun W => ⟨⟨W.hM, W.es, W.hD, W.hd, W.hIn⟩, ⟨W.fold, W.dig, W.att, W.lay, W.head⟩⟩,
    fun h => k3Owed_of_left h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 h.2⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3Owed_of_left
#print axioms VerifiableInference.OnPublicFiles.k3Owed_iff_left
