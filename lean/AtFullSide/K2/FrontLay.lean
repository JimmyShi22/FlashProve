-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FrontLay.lean: what is public of the layout that a code switch's front carries, against
the members of the closed group, at each of the 25 fronts. One structure, three theorems, proved.
Over the first text: two imports without which it did not type (Johnson.P5J.MgAtAll,
Johnson.P5J.FourAtMg) and the two files of helpers (AtFullSide/K2/FrontLayA.lean, at letters;
AtFullSide/K2/FrontLayB.lean, at a reached state); the structure and the three statements stand to
the letter. Limits: that a reached state with a front exists under the head is not shown here.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.K2.Honest.Returns.FrontTiesReached
import Johnson.Desc.K2.Honest.Carry.OfRows
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import AtFullSide.K2.FrontLayA
import AtFullSide.K2.FrontLayB

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (GE readE readL)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Sizes GroupMember sizesAt membersTrue keptOf shapeOf zeroG)
open VerifiableInference.Desc.Sound (allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- **What is public of a front's layout against the group's members.** old: the carried rows. ms:
the members. Z: the sizes. γ: the fold's challenges. -/
structure FrontLay (Z : Sizes) (ms : List GroupMember) (γ : List GE) (old : SingleRows) : Prop where
  masks : old.masks = 2
  keptRows : old.keptRows =
    ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b)).length
  gamma : ∀ t, t < old.layout.k → γ.getD t zeroG = readL old.gamma t
  keptShapes : Z.kept = (VerifiableInference.Desc.Own.keptNos old.layout).map (shapeOf ms)
  keptNos : ((List.range ms.length).filter fun w => keptOf ms w) =
    VerifiableInference.Desc.Own.keptNos old.layout
  keptFirst : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = true →
    old.layout.mainFirst.getD w none = none
  apartMain : ∀ w w', w < old.layout.members.size → w' < old.layout.members.size →
    w ≠ w' → ∀ f f', old.layout.mainFirst.getD w none = some f →
    old.layout.mainFirst.getD w' none = some f' →
    f + (shapeOf ms w).mainRows ≤ f' ∨ f' + (shapeOf ms w').mainRows ≤ f
  apartMask : ∀ w w', w < old.layout.members.size → w' < old.layout.members.size →
    w ≠ w' → ∀ f f', old.layout.maskFirst.getD w none = some f →
    old.layout.maskFirst.getD w' none = some f' →
    f + (shapeOf ms w).maskRows ≤ f' ∨ f' + (shapeOf ms w').maskRows ≤ f
  length : ms.length = old.layout.members.size

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a segment's first place** (14 (m + 1) + 2, m < 23). -/
theorem link_frontLay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx) (T : SwitchTarget) :
    FrontLay (sizesAt fx.st fx.f.rows T) (membersTrue fx.st fx.f.rows)
      (fx.f.rows.gamma.map readE) fx.f.rows := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G, hL⟩ :=
    (VerifiableInference.Desc.K2.Honest.Returns.link_frontTies h.scope h.reads O h23 hr.1 hq
      hfx).lay
  obtain ⟨hm, hk⟩ := link_frontRows h.scope h.reads O h23 hr.1 hq hfx
  have hsz : fx.f.rows.layout.kept.size = fx.f.rows.layout.members.size := by
    rw [hL.kept, hL.members]
    exact hL.sizes
  exact ⟨hm, keptRows_true T hk, fun t _ => gammaRead _ t, keptShapes_true hsz T, keptNos_true hsz,
    keptFirst_true hL, apart_true hL .main _ hL.mainFirst, apart_true hL .mask _ hL.maskFirst,
    members_length hsz⟩

/-- **At the output head's front** (339). -/
theorem head_frontLay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {p : VerifiableInference.Desc.First.K2.P2}
    (hq : p.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt p a.1.2 = some fx) (T : SwitchTarget) :
    FrontLay (sizesAt fx.st fx.f.rows T) (membersTrue fx.st fx.f.rows)
      (fx.f.rows.gamma.map readE) fx.f.rows := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G, hL⟩ :=
    (VerifiableInference.Desc.K2.Honest.Returns.head_frontTies h.scope h.reads O hr.1 hq hfx).lay
  obtain ⟨hm, hk⟩ := head_frontRows h.scope h.reads O hr.1 hq hfx
  have hsz : fx.f.rows.layout.kept.size = fx.f.rows.layout.members.size := by
    rw [hL.kept, hL.members]
    exact hL.sizes
  exact ⟨hm, keptRows_true T hk, fun t _ => gammaRead _ t, keptShapes_true hsz T, keptNos_true hsz,
    keptFirst_true hL, apart_true hL .main _ hL.mainFirst, apart_true hL .mask _ hL.maskFirst,
    members_length hsz⟩

/-- **At the front behind the last segment** (353). -/
theorem fin_frontLay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t)
    {p : VerifiableInference.Desc.First.K2.P2} (hq : p.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : VerifiableInference.Desc.First.K2.frontAt p t = some fx)
    (T : SwitchTarget) :
    FrontLay (sizesAt fx.st fx.f.rows T) (membersTrue fx.st fx.f.rows)
      (fx.f.rows.gamma.map readE) fx.f.rows := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G, hL⟩ :=
    (VerifiableInference.Desc.K2.Honest.Returns.fin_frontTies h.scope h.reads O hr.1 he hq hfx).lay
  obtain ⟨hm, hk⟩ := fin_frontRows h.scope h.reads O hr.1 he hq hfx
  have hsz : fx.f.rows.layout.kept.size = fx.f.rows.layout.members.size := by
    rw [hL.kept, hL.members]
    exact hL.sizes
  exact ⟨hm, keptRows_true T hk, fun t _ => gammaRead _ t, keptShapes_true hsz T, keptNos_true hsz,
    keptFirst_true hL, apart_true hL .main _ hL.mainFirst, apart_true hL .mask _ hL.maskFirst,
    members_length hsz⟩

end AtFullSide.K2

#print axioms AtFullSide.K2.link_frontLay
#print axioms AtFullSide.K2.head_frontLay
#print axioms AtFullSide.K2.fin_frontLay
