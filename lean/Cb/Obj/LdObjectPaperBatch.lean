-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPaperBatch.lean: the test for linear constraints at N instances with the closing of
this protocol's technical report (lean/CREDITS.md; one splitting, by the shared part), at the
standard senders: both items of the object's list for a batch, with no hypothesis on a fresh mask.
(not all hypotheses are named
here: see `Spec.ldOnP_object`, `Spec.ldOnP_far`)

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation. In a session it runs on a batch of at most N instances that share the encoded
index. This file puts other files' theorems together for one choice of the test's last part, the
closing, and of its senders.

Statements (Cb.Spec.ldOnP_*) and proofs (an assembly). Generic: any configuration, any plan
`p : LdLinPp O.toC` with its tests.

Main names:
  `Spec.ldOnP_same`: the closing on which the batch is built is the one of which the one-instance
    theorems speak (Cb/Ld/LdLinCloseDemandPA.lean: `ldLinPpT_tailA`, `ldLinPpT_topA`).
  `Spec.ldOnP_le`: the positions for one instance are at most those for N ≥ 1 instances.
  `Spec.ldOnP_object`: under what "Limits" lists as asked, the value `O.termT`
    (Cb/Obj/LdObjectOnBTerm.lean) with the closing `T.cZV` (Cb/Ld/LdLinClosePlanPV.lean), for any
    condition on0 on the index that fits the list's item and any bound εf on the fold's bad points:
    `Hiop.LinBListR` ∧ `Hiop.LinBKnowR`.
  `Spec.ldOnP_far`: the same in the second regime: the index decodes with its record; e' + eM below
    the distance; εf = 0. (The technical report also asks the index's radius below half the
    distance there; not asked here: wider.)

It puts together: the core for a batch (Cb/Ld/LdLinB*.lean, Cb/Obj/LdObjectOnBTerm*.lean); one
instance's chain behind the core (Cb/Ld/LdLinCloseDemandPA.lean: `T.QF`); sound for a batch
(Cb/Ld/LdLinClosePlanPB.lean); honest for a batch (Cb/Ld/LdLinClosePlanPV.lean); under the
hypotheses below,
the mask κ is fresh, for one instance and for sets of slots, by the sender's law
(Cb/Ld/LdSendStdOwnCut.lean: `stdL_ownOne`; Cb/Ld/LdLinStdSpV.lean: `ldSpV_fresh`).

Limits: what is asked:
  of the index: its code has a position (`Nonempty (Fin O.Cf.C₀.n)`), distance, radii, `FoldErr`,
    `Function.Injective O.py`, `O.Fits on0`;
  of the senders: `(Ts.snd LW LU LO tW tU tO).OK`, places, the layouts' conditions;
  κ a free entry of a member of Ω's family (`p.k₀`, `Ts.YO.entF n₀`); `p.Rs₀` holds no pad entry of
    Ω's family (`Ts.YO.NoPad`);
  of the plan: `Shared`, `Plain`, `Kept`, "restG is rest", `SaysA`;
  the three tests' `D.OK`;
  of what closes the rest: its own conditions for one instance (`Q'.OK`, its demand), sound (`KB`)
    and honest (`QV'.OK`, its tie is carried); the links of cA' are those of `T.Q'.c` (same');
  the four inequalities on positions for N instances, 1 ≤ N;
  of qa: it is kept by subsets, and holds wherever `O.toC.Sa.qFam q₀ ba` does;
  a value of each of `O.toC.E₀.Str`, `O.toC.Sh6`, `O.toC.P.X4`, `O.toC.P.E4.Str`, `O.toC.P.Ea.Str`.
What closes the rest (`T.Q'`, cA', QV', tie') is a parameter with its own conditions.
That these conditions can be met together is not said here. No theorem of this library states that
the hypotheses of `ldOnP_object` can be met together. This file says nothing on the errors as a
list, but that `Spec.ldOnP_object` and `Spec.ldOnP_far` conclude `LinBKnowR` at the `P.err` of the
value `O.termT`; it does not write the errors out. Nothing under the object is moved by this file.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanPVProofs
import Cb.Ld.LdLinClosePlanPBProofs
import Cb.Ld.LdLinCloseDemandPAProofs
import Cb.Ld.LdLinCloseDemandLe
import Cb.Obj.LdObjectOnBTermProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec

/-- States: the closing on which the batch is built is the one-instance test's. -/
def ldOnP_same : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype κ] [Fintype J] [Fintype Y]
      (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c),
    (T.QA cA' same').Q = T.QF

def ldOnP_le : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype κ] [Fintype J] [Fintype Y]
      (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (N : ℕ) (b' : p.S₃.O → ℕ) (o : C.S.O),
    1 ≤ N → T.D₁.need (T.D₂.need (T.D₃.need b')) o ≤
      T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => C.isSh a.1.1) b')) o

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

/-- Both items of the object's list. -/
def ldOnP_object : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPp O.toC) (T : LdLinPpT p) (N : ℕ)
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (εf : ℕ)
      (q₀ : Finset O.toC.E₀.Pos → Prop) (b' : p.S₃.O → ℕ) (ba : O.toC.Sa.O → ℕ)
      (tie' : O.toC.P.Sh6 → T.Q'.St × p.S₃.Smp → (O.toC.E₀.prod p.S₃.ext).Str →
        p.S₃.Wit × O.toC.Wpa → Prop)
      (x₀ : O.toC.S.Smp) (y₀ : O.toC.S.ext.Str) (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (xB : T.StB) (xC : T.StC) (_ : O.toC.E₀.Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ O.toC.E₀ O.toC.Wpa)
        ⟨O.toC.P.Sh6, tie', T.qB₃ N q₀ b'⟩)
      (Ts : O.toC.P.Std Fp) (LW : O.toC.P.NW.O → ℕ) (LU : O.toC.P.NU.O → ℕ) (LO : O.toC.P.NO.O → ℕ)
      (tW : O.toC.P.NW.O → ℕ) (tU : O.toC.P.NU.O → ℕ) (tO : O.toC.P.NO.O → ℕ) (n₀ : Σ a, Ts.YO.Fr a)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (_ : O.toC.Sh6) (_ : O.toC.P.X4) (_ : O.toC.P.E4.Str)
      (d : O.toC.P.W0) (d₀ : O.P.W0) (_ : O.toC.P.Ea.Str) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.Fits on0 → O.toC.P.FoldErr on0 εf →
    Function.Injective O.py → (Ts.snd LW LU LO tW tU tO).OK → (∀ U V, V ⊆ U → qa U → qa V) →
    p.Shared → p.Plain → p.Kept →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = O.toC.rest sa (O.toC.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK →
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → cA'.KB N (ldKeyU _) ldKeyT → QV'.OK →
    (∀ x y w, (O.toC.P.V6 (Ts.snd LW LU LO tW tU tO) qa N).rel x y w →
      tie' w.1 (T.fa (O.toC.toSt x).1.1.1.1,
          p.S₂.res (T := OMsg.Smp) p.kp₃
            (p.S₁.res (T := OMsg.Smp) p.kp₂ (O.toC.S.res (T := OMsg.Smp) p.kp₁ (O.toC.toSmp x))))
        (T.D₃.outY (T.D₂.outY (T.D₁.outY (O.toC.toE.map y))))
        (T.D₃.outW (T.D₂.outW (T.D₁.outW (O.toC.toW w.2))))) →
    (∀ W, O.toC.Sa.qFam q₀ ba W → qa W) → 1 ≤ N →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b'))
        (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b'))
        (.inl (.inl (.inr a))) ≤ tW a) →
    (∀ a,
      T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b')) (.inl (.inr a)) ≤ tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b')) (.inr a) ≤ tO a) →
    Ts.Places → Ts.YW.OK tW → Ts.YU.OK tU → Ts.YO.OK tO →
    (⟨p.k₀.o, p.k₀.j⟩ : O.toC.S.Ent) = O.toC.eO (Ts.YO.entF n₀) →
    (∀ n, p.Rs₀ (O.toC.eO n) → Ts.YO.NoPad n) →
    LinBListR O.left
      (O.termT on0 (Ts.snd LW LU LO tW tU tO) qa εf N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).Q
      (O.termT on0 (Ts.snd LW LU LO tW tU tO) qa εf N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).hQ
      N (O.termT on0 (Ts.snd LW LU LO tW tU tO) qa εf N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).P ∧
    LinBKnowR O.left
      (O.termT on0 (Ts.snd LW LU LO tW tU tO) qa εf N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).Q
      N d0 (O.termT on0 (Ts.snd LW LU LO tW tU tO) qa εf N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).P.err

/-- The second regime: the index decodes with its record; no point is bad for the fold.
(not all hypotheses are named here: see the statement below) -/
def ldOnP_far : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPp O.toC) (T : LdLinPpT p) (N : ℕ)
      (q₀ : Finset O.toC.E₀.Pos → Prop) (b' : p.S₃.O → ℕ) (ba : O.toC.Sa.O → ℕ)
      (tie' : O.toC.P.Sh6 → T.Q'.St × p.S₃.Smp → (O.toC.E₀.prod p.S₃.ext).Str →
        p.S₃.Wit × O.toC.Wpa → Prop)
      (x₀ : O.toC.S.Smp) (y₀ : O.toC.S.ext.Str) (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (xB : T.StB) (xC : T.StC) (_ : O.toC.E₀.Str)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ O.toC.E₀ O.toC.Wpa)
        ⟨O.toC.P.Sh6, tie', T.qB₃ N q₀ b'⟩)
      (Ts : O.toC.P.Std Fp) (LW : O.toC.P.NW.O → ℕ) (LU : O.toC.P.NU.O → ℕ) (LO : O.toC.P.NO.O → ℕ)
      (tW : O.toC.P.NW.O → ℕ) (tU : O.toC.P.NU.O → ℕ) (tO : O.toC.P.NO.O → ℕ) (n₀ : Σ a, Ts.YO.Fr a)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (_ : O.toC.Sh6) (_ : O.toC.P.X4) (_ : O.toC.P.E4.Str)
      (d : O.toC.P.W0) (d₀ : O.P.W0) (_ : O.toC.P.Ea.Str) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.e' + O.Cf.eM < O.Cf.C₀.d → Function.Injective O.py →
    (Ts.snd LW LU LO tW tU tO).OK → (∀ U V, V ⊆ U → qa U → qa V) → p.Shared → p.Plain → p.Kept →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = O.toC.rest sa (O.toC.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK →
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → cA'.KB N (ldKeyU _) ldKeyT → QV'.OK →
    (∀ x y w, (O.toC.P.V6 (Ts.snd LW LU LO tW tU tO) qa N).rel x y w →
      tie' w.1 (T.fa (O.toC.toSt x).1.1.1.1,
          p.S₂.res (T := OMsg.Smp) p.kp₃
            (p.S₁.res (T := OMsg.Smp) p.kp₂ (O.toC.S.res (T := OMsg.Smp) p.kp₁ (O.toC.toSmp x))))
        (T.D₃.outY (T.D₂.outY (T.D₁.outY (O.toC.toE.map y))))
        (T.D₃.outW (T.D₂.outW (T.D₁.outW (O.toC.toW w.2))))) →
    (∀ W, O.toC.Sa.qFam q₀ ba W → qa W) → 1 ≤ N →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b'))
        (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b'))
        (.inl (.inl (.inr a))) ≤ tW a) →
    (∀ a,
      T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b')) (.inl (.inr a)) ≤ tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.needV N (fun a => O.toC.isSh a.1.1) b')) (.inr a) ≤ tO a) →
    Ts.Places → Ts.YW.OK tW → Ts.YU.OK tU → Ts.YO.OK tO →
    (⟨p.k₀.o, p.k₀.j⟩ : O.toC.S.Ent) = O.toC.eO (Ts.YO.entF n₀) →
    (∀ n, p.Rs₀ (O.toC.eO n) → Ts.YO.NoPad n) →
    LinBListR O.left
      (O.termT O.onDec (Ts.snd LW LU LO tW tU tO) qa 0 N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).Q
      (O.termT O.onDec (Ts.snd LW LU LO tW tU tO) qa 0 N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).hQ
      N (O.termT O.onDec (Ts.snd LW LU LO tW tU tO) qa 0 N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).P ∧
    LinBKnowR O.left
      (O.termT O.onDec (Ts.snd LW LU LO tW tU tO) qa 0 N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).Q
      N d0 (O.termT O.onDec (Ts.snd LW LU LO tW tU tO) qa 0 N
        (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') d d₀).P.err

end
end Spec

theorem ldOnP_same : Spec.ldOnP_same := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldOnP_le : Spec.ldOnP_le := fun E _ _ _ _ _ _ _ _ _ C p T N b' o hN =>
  ldDemandLe_mono E C.S T.D₁ _ _
    (fun a =>
      ldDemandLe_mono E p.S₁ T.D₂ _ _
        (fun c => ldDemandLe_need E p.S₂ T.D₃ N (fun a => C.isSh a.1.1) b' c hN) a) o

section
variable (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E]

theorem ldOnP_object : Spec.ldOnP_object F E Fp := by
  classical
  intro O _ p T N on0 εf q₀ b' ba tie' x₀ y₀ cA' same' xB xC yE QV' Ts LW LU LO tW tU tO n₀ qa sh₀
    x₄ y₄ d d₀ ya d0 hd hM hFit hF hpy hS hmono hSh hP hK hr hA h₁ h₂ h₃ hQ' hq' hKB' hV hcar hqa hN
    nA nW nU nO hPl oW oU oO hk hR
  have hSays : O.toC.Says (p.x₁ T.Q'.base).A (O.toC.fqP T.fa) :=
    ldLinPp_says E _ _ _ _ O.toC p _ T.Q'.base T.fa hr hA
  have h0 : p.Rs₀ (O.toC.eO (Ts.YO.entF n₀)) := hk ▸ hP.rs₀K
  -- one instance: the mask is fresh by the sender's law
  have l0 := stdL_ownOne Fp E O.toC.P.NO Ts.YO tO O.toC.P.W4 O.toC.P.W3 Ts.datO (fun w => w.2)
    (fun _ => 0, Ts.w3) n₀ O.toC.P.SdO (fun n => p.Rs₀ (O.toC.eO n)) oO hR h0
  have f0 := ldLinSp_entO E _ _ _ _ O.toC on0 εf (Ts.snd LW LU LO tW tU tO) (p.x₁ T.Q'.base)
    (O.toC.fqP T.fa) (Ts.YO.ownOne Ts.datO (fun w => w.2) (fun _ => 0, Ts.w3) n₀) p.Rs₀
    (fun _ => False) (Ts.YO.entF n₀) l0 hS.hidO (fun _ h => h) h0
  rw [← hk] at f0
  have hbeh := ldLinPpT_behindA E _ _ _ _ O.toC p T on0 εf (Ts.snd LW LU LO tW tU tO) p.Rs₀
    (fun _ => False) hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' (fun _ h => h) f0
  have hdem := ldLinPpT_demand E _ _ _ _ O.toC p T (Ts.snd LW LU LO tW tU tO) qa q₀ ba b' hq' hqa
    (fun a => (ldOnP_le E _ _ _ _ O.toC p T N b' _ hN).trans (nA a))
    (fun a => (ldOnP_le E _ _ _ _ O.toC p T N b' _ hN).trans (nW a))
    (fun a => (ldOnP_le E _ _ _ _ O.toC p T N b' _ hN).trans (nU a))
    (fun a => (ldOnP_le E _ _ _ _ O.toC p T N b' _ hN).trans (nO a))
  obtain ⟨hC1, hC2⟩ := ldLinAlt_chain E _ _ _ _ O.toC on0 εf (Ts.snd LW LU LO tW tU tO) qa T.QF
    (O.toC.fqP T.fa) hF hpy hS hSays hbeh hdem
  have hKB := ldLinPpB_kb E _ _ _ _ O.toC p T cA' same' N hSh hr hA hP hK h₁ h₂ h₃ hKB'
  obtain ⟨v1, v2, v3, v4, v5⟩ :=
    ldLinPV_std Fp E _ _ _ _ O.toC p T N q₀ b' tie' x₀ y₀ cA' same' xB xC yE QV' Ts LW
      LU LO tW tU tO n₀ qa ba on0 εf sh₀ x₄ y₄ hSh hP hK hr hA h₁ h₂ h₃ hV hcar hqa nA
      nW nU nO hPl oW oU oO hk hR
  have v5' : (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC
        (Ts.snd LW LU LO tW tU tO) qa QV').forget.forget =
      O.toC.cZ T.QF (O.toC.fqP T.fa) := v5
  rw [← v5'] at hC1 hC2
  rw [← v4] at hKB
  exact ldOnT_object F E O on0 (Ts.snd LW LU LO tW tU tO) qa εf N _
    (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC (Ts.snd LW LU LO tW tU tO) qa QV') ldKeyT d d₀ ya d0
    hd hM hFit hF hpy hS (ldLinStd_apart O.toC.P Ts LW LU LO tW tU tO) hmono hC1 hC2 hKB v1 v2 v3

theorem ldOnP_far : Spec.ldOnP_far F E Fp := by
  intro O _ p T N q₀ b' ba tie' x₀ y₀ cA' same' xB xC yE QV' Ts LW LU LO tW tU tO n₀ qa sh₀ x₄
    y₄ d d₀ ya d0 hd he hpy hS hmono hSh hP hK hr hA h₁ h₂ h₃ hQ' hq' hKB' hV hcar hqa hN nA nW
    nU nO hPl oW oU oO hk hR
  exact ldOnP_object F E Fp O p T N O.onDec 0 q₀ b' ba tie' x₀ y₀ cA' same' xB xC yE QV' Ts LW LU LO
    tW tU tO n₀ qa sh₀ x₄ y₄ d d₀ ya d0 hd (lt_of_le_of_lt (Nat.le_add_left _ _) he)
    (ldOB_fits F E O).1 (ldOB_foldErr F E O hd he) hpy hS hmono hSh hP hK hr hA h₁ h₂ h₃ hQ' hq'
    hKB' hV hcar hqa hN nA nW nU nO hPl oW oU oO hk hR

end
end Cb
