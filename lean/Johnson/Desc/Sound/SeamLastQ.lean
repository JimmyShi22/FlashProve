-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamLastQ.lean: **tupleNine_members | tupleTen_members (SeamLast.lean) WITH A WEAKER PREMISE: MemberFacts MAY SPEND THE GAME's OWN CONCLUSION NTuple AT THE SAME FIXINGS.** Two statements; the proofs are SeamLast.lean's over tupleNine_ofQ | tupleTen_ofQ and fixes_unique (SeamFactsQ.lean).
  **tupleNine_membersQ | tupleTen_membersQ**   hM : … → Fixes π t a₀ rest G0 Ly D → NTuple Fr π (noAt t₁ t₂ c) (fun s => r s.st) rdN (t, a.2) a₀ rest G0 Ly D → ∀ j, ….
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamLast
import Johnson.Desc.Sound.SeamFactsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain)
open H2K.Pub (sgOf johOk)

variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (π : P12) (t₁ t₂ c : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (hj : johOk π r = true) (he : π.early = true)
  (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hsU : sentU.size = 2)
  (hsO : (withOmega P.S).size = 2)
  (hrd : ∀ z m part i, rd z m part i = tabP cs (z.1.l.get z.2).1 m part i)
include hj he hp hsU hsO hrd

/-- **THE CORE AT THE TEST ON G_u, FROM MemberFacts, WHICH MAY SPEND NTuple.** -/
theorem tupleNine_membersQ
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (hcod : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      a.1.2.st.codes = cs)
    (hI : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      InOrder a.1.2.st)
    (x₀ x₁ : Mem) (e₀ e₁ : ℕ) (hne : x₀ ≠ x₁)
    (huniq : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 ∨
      SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2 → z = x₀ ∨ z = x₁)
    (hM : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → inGu a.1.2 = .ok t →
      ∀ (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
        Fixes π t a₀ rest G0 Ly D →
        NTuple Fr π (noAt t₁ t₂ c) (fun s => r s.st) rdN (t, a.2) a₀ rest G0 Ly D →
        ∀ j : Fin D.mems.length,
        (j.val = 0 → MemberFacts cs G Fr (noAt t₁ t₂ c) (fun s => r s.st) (smpSt cs oNo stSh) mem a.2
          ((actQ N f l 9).2 a).1 (strsOfAct Fr ((actQ N f l 9).2 a)) a₀ D j x₀ e₀) ∧
        (j.val = 1 → MemberFacts cs G Fr (noAt t₁ t₂ c) (fun s => r s.st) (smpSt cs oNo stSh) mem a.2
          ((actQ N f l 9).2 a).1 (strsOfAct Fr ((actQ N f l 9).2 a)) a₀ D j x₁ e₁)) :
    TupleNine cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c (fun s => r s.st) rdN x := by
  refine tupleNine_ofQ cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c _ rdN x hrd
    (fun a τ b t ha hout ht hq => ?_) hI
  obtain ⟨a₁, rest₁, G1, Ly₁, D₁, hf₁, hN₁⟩ := hq
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
  refine coreFacts_two cs G Fr π _ _ _ mem a.2 _ _ _ t x₀ x₁ e₀ e₁ hne
    (fun z hz => huniq z hz.1 hz.2) fun a₀ rest G0 Ly D hf => ?_
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_unique hf₁ hf
  obtain ⟨hg, h2⟩ := group_nine cs P sentU layU layO π r hj he hp (by omega) (by omega) _ _ rs gs hd
    hX (hcod a ha) t ht _ _ _ _ _ hf
  refine ⟨hg, h2, fun j => ?_⟩
  have hjl := j.isLt
  by_cases e : j.val = 0
  · exact .inl ⟨e, (hM a τ b t ha hout ht _ _ _ _ _ hf hN₁ j).1 e⟩
  · exact .inr ⟨by omega, (hM a τ b t ha hout ht _ _ _ _ _ hf hN₁ j).2 (by omega)⟩

/-- **THE CORE AT THE TEST ON G_omega, FROM MemberFacts, WHICH MAY SPEND NTuple.** The data's first member is o_omega, its second o_sp. -/
theorem tupleTen_membersQ
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (hcod : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      a.1.2.st.codes = cs)
    (hI : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      InOrder a.1.2.st)
    (x₀ x₁ : Mem) (e₀ e₁ : ℕ) (hne : x₀ ≠ x₁)
    (huniq : ∀ z ∈ ms, SitsAt z (N.tenant .oSp).1 (N.tenant .oSp).2 ∨
      SitsAt z (N.tenant .oOmega).1 (N.tenant .oOmega).2 → z = x₀ ∨ z = x₁)
    (hM : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t →
      ∀ (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
        Fixes π t a₀ rest G0 Ly D →
        NTuple Fr π (noAt t₁ t₂ c) (fun s => r s.st) rdN (t, a.2) a₀ rest G0 Ly D →
        ∀ j : Fin D.mems.length,
        (j.val = 0 → MemberFacts cs G Fr (noAt t₁ t₂ c) (fun s => r s.st) (smpSt cs oNo stSh) mem a.2
          ((actQ N f l 10).2 a).1 (strsOfAct Fr ((actQ N f l 10).2 a)) a₀ D j x₀ e₀) ∧
        (j.val = 1 → MemberFacts cs G Fr (noAt t₁ t₂ c) (fun s => r s.st) (smpSt cs oNo stSh) mem a.2
          ((actQ N f l 10).2 a).1 (strsOfAct Fr ((actQ N f l 10).2 a)) a₀ D j x₁ e₁)) :
    TupleTen cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c (fun s => r s.st) rdN x := by
  refine tupleTen_ofQ cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c _ rdN x hrd
    (fun a τ b t ha hout ht hq => ?_) hI
  obtain ⟨a₁, rest₁, G1, Ly₁, D₁, hf₁, hN₁⟩ := hq
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 10 a ha
  refine coreFacts_two cs G Fr π _ _ _ mem a.2 _ _ _ t x₀ x₁ e₀ e₁ hne
    (fun z hz => huniq z hz.1 hz.2) fun a₀ rest G0 Ly D hf => ?_
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := fixes_unique hf₁ hf
  obtain ⟨hg, h2⟩ := group_ten cs P sentU layU layO π r hj he hp (by omega) _ _ rs gs hd
    hX (hcod a ha) t ht _ _ _ _ _ hf
  refine ⟨hg, h2, fun j => ?_⟩
  have hjl := j.isLt
  by_cases e : j.val = 0
  · exact .inl ⟨e, (hM a τ b t ha hout ht _ _ _ _ _ hf hN₁ j).1 e⟩
  · exact .inr ⟨by omega, (hM a τ b t ha hout ht _ _ _ _ _ hf hN₁ j).2 (by omega)⟩

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.tupleNine_membersQ
#print axioms Desc.K14.Law.Fence.tupleTen_membersQ
