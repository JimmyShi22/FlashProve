-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TieLight.lean: the code switch: TWO PREMISES OF THE TIE's LAST FORM
(TiePaid.lean's afterAtYes_paid) FALL: «logN ≤ 32», and the clause «Slots» inside FrontAt.sample.

TiePaid.lean brings the tie's one premise AfterAtYes to three records, logN ≤ 32 and LdLocD.Lin.
Two of the things asked there follow from what stands beside them.
  FrontAtL     FrontAt without «Slots» in its clause sample: what is asked of the statement in front
  FrontAt.light   FrontAt gives FrontAtL: so whoever has the elder record has this one
  frontAt_of_light   AT A YES (Whole.lean's AtYes; RowsAt.lean's Laid): FrontAtL, CallerAt and
               logN ≤ 32 give FrontAt: «Slots» is Paid.lean's paid_slots at the record AtSwitch,
               which AtYes.lean's atSwitch_of makes there WITHOUT the clause sample. It leans on the
               target's test's yes, which the text asks itself: so it is had at a yes for nothing,
               while in front it would want that test as a clause more
  FrontOnL, handsAtYes_light, afterAtYes_light   the two end theorems of TiePaid.lean from FrontOnL,
               and from «the kind's test on the plan says yes» in the place of logN ≤ 32
               (AtYes.lean's plan_32)
LIMITS. CallerAt (5), FrontAtL (16 clauses, one lighter) and YesAt (3) are premises: every clause;
so is LdLocD.Lin. «on» is a letter. No member is named here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.TiePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **What is asked of the statement in front, lighter**: FrontAt without «Slots» in sample. -/
structure FrontAtL (W₀ : OnBytes.SwitchFrame) (p : K2.P2) (mem row : R.Kp → ℕ)
    (pl : R.Kp → OnBytes.KeptPlace) (aOf : (LocK).hd.K → ℕ)
    (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (s : Rec) (orc : ℕ → ℕ → List UInt64)
    (xc : (LocK).Xc × (LocK).hd.Smp) (str : (LocK).C.ext.Str) (fx : _root_.Tw.K2.Front) :
    Prop where
  frameIs : K2.frameAt fx = some W₀
  z32 : W₀.zk.logN ≤ 32
  twoOld : ∀ (a a' : ℕ) (k k' : OnBytes.KeptPlace), W₀.kept[a]? = some k → W₀.kept[a']? = some k' →
    k.old = k'.old → a = a'
  codes : fx.st.codes = cs
  keptPos : K2.KeptPos fx.T
  keptRows : fx.f.rows.keptRows = (W₀.kept.map (·.rows)).sum
  ell : ∀ (a : ℕ) (k : OnBytes.KeptPlace), W₀.kept[a]? = some k →
    (fx.st.codes.base.getD (fx.st.oracles.getD k.old default).shape.code default).ell = W₀.code.ell
  first : ∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = fx.T.shape
  next : ∀ i (hi : i < fx.T.kept.size), ∃ h : 1 + i < l.length,
    (l.get ⟨1 + i, h⟩).1 = fx.T.kept[i].shape
  mainVars : ∀ v ∈ fx.f.rows.c.tensors, v.vars = W₀.code.logEll
  d0 : (fx.f.rows.d.getD 0 #[]).size ≤ W₀.zk.ell
  d1 : (fx.f.rows.d.getD 1 #[]).size ≤ W₀.zk.ell
  strIs : StrIs R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s fx orc
    (coordOf R.s R.Kp W₀ fx.f.rows mem row) str
  target : xc.1.1 = readE fx.f.rows.target
  vector : xc.1.2 = vecOf R.s R.Kp fx.f.rows row pl
  sample : ∀ ks : Σ k, ((LocK).hd.o k).Z.S, ∃ (k : OnBytes.KeptPlace) (smp : OnBytes.Row),
    W₀.kept[aOf ks.1]? = some k ∧ (samplesOf fx.st k)[iOf ks.1 ks.2]? = some smp ∧
      (xc.2 ks.1).2 ks.2 = readE smp.target ∧
      pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat (xc.2 ks.1).1 ks.2) =
        slotVec R.s R.Kp mem row (aOf ks.1) k.rowBits (formOn smp)

variable {R Hd Sb sl Z A₀ cs l iJ iQ t w₀} in
/-- The elder record gives the lighter one. -/
theorem FrontAt.light {W₀ : OnBytes.SwitchFrame} {p : K2.P2} {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} {s : Rec} {orc : ℕ → ℕ → List UInt64}
    {xc : (LocK).Xc × (LocK).hd.Smp} {str : (LocK).C.ext.Str} {fx : _root_.Tw.K2.Front}
    (P : FrontAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc xc str fx) :
    FrontAtL R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc xc str fx :=
  ⟨P.frameIs, P.z32, P.twoOld, P.codes, P.keptPos, P.keptRows, P.ell, P.first, P.next, P.mainVars,
    P.d0, P.d1, P.strIs, P.target, P.vector, fun ks => by
      obtain ⟨k, smp, h1, h2, -, h4, h5⟩ := P.sample ks
      exact ⟨k, smp, h1, h2, h4, h5⟩⟩

/-- **At a yes the lighter record gives the elder one.** -/
theorem frontAt_of_light {W₀ : OnBytes.SwitchFrame} {p : K2.P2} (h32 : p.logN ≤ 32)
    {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {xc : (LocK).Xc × (LocK).hd.Smp} {str : (LocK).C.ext.Str}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : OnBytes.Statement}
    {Y : Array OnBytes.E} {rows : List OnBytes.Row} {G : OnBytes.Group} {c : OnBytes.Code}
    {W : OnBytes.SwitchFrame} {carried : OnBytes.Row} {orc : ℕ → ℕ → List UInt64}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    (L : Laid S3 fx.f.rows fx.T (y.ids.getD 0 OnBytes.noId) (y.ids.extract 1 (1 + fx.T.kept.size))
      (OnBytes.Positions.ofDraws p.logN r₂.drawn.poss) Y rows W carried)
    (C : CallerAt R cs l iJ iQ mem row pl W₀)
    (P : FrontAtL R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc xc str fx) :
    FrontAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc xc str fx := by
  have eW : W₀ = W := by
    have h1 := L.frame
    rw [K2.frame_of_front Y1, P.frameIs] at h1
    exact Option.some.inj h1
  subst eW
  have hKO := K2.keptOld_of Y1.check P.keptPos
  have hold : ∀ (a : ℕ) (k : OnBytes.KeptPlace), W₀.kept[a]? = some k →
      k.old < fx.st.oracles.size := fun a k hk => by
    obtain ⟨hi, e, -⟩ := kept_rec S3 fx.f.rows fx.T _ _ W₀ L.frame a k hk
    rw [e]
    exact hKO _ (Array.getElem_mem_toList hi)
  have hc3 : S3.codes = fx.st.codes := Y1.same.codes.trans Y1.sent.codes
  have A : AtSwitch S3 fx.f.rows fx.T (y.ids.getD 0 OnBytes.noId)
      (y.ids.extract 1 (1 + fx.T.kept.size)) W₀ l R.s R.Kp mem row pl
      (fun i => fx.st.oracles.size + i) :=
    K2.atSwitch_of Y1.sent Y1.same P.keptPos Y1.check L l R.s R.Kp mem row pl Y1.code
      (by rw [Y1.logN]; exact h32) P.z32 P.keptRows
      (fun a k hk => by
        rw [hc3, (old_at_yes Y1 k.old (hold a k hk)).1]
        exact P.ell a k hk)
      P.first P.next C.codeC C.codeZ C.slots
  have hc : S3.codes = cs := hc3.trans P.codes
  have hS : ∀ (a : ℕ) (k : OnBytes.KeptPlace), W₀.kept[a]? = some k →
      Slots R.s R.Kp cs l W₀ (fun i => fx.st.oracles.size + i) mem row a k := fun a k hk => by
    rw [← hc]
    exact paid_slots A a k hk
  exact ⟨P.frameIs, P.z32, P.twoOld, P.codes, P.keptPos, P.keptRows, P.ell, P.first, P.next,
    P.mainVars, P.d0, P.d1, P.strIs, P.target, P.vector, fun ks => by
      obtain ⟨k, smp, h1, h2, h4, h5⟩ := P.sample ks
      exact ⟨k, smp, h1, h2, hS _ k h1, h4, h5⟩⟩

variable {Pw : Type} (Cw : LdCode GE Pw) {r₁ r₂ : Round}
  (ρ : Rd (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw) r₁ r₂) (p : K2.P2)
  (v₁ : r₁.Msg → r₁.Chal → Fmt.RoundView) (v₂ : r₂.Msg → r₂.Chal → Fmt.RoundView)
  {Yt : Type} (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀
      Cw).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).X)
  (shown : Rec × Yt → Tr [r₁, r₂] → Gs) (orcs : Rec × Yt → ℕ → ℕ → List UInt64)

/-- FrontAtL at the front that the text makes of a statement's record. -/
def FrontOnL (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ) (pl : R.Kp → OnBytes.KeptPlace)
    (aOf : (LocK).hd.K → ℕ) (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (a : Rec × Yt) : Prop :=
  ∀ fx, K2.frontAt p a.1 = some fx →
    FrontAtL R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf a.1 (orcs a) (inX a.1).1.1
      (strs a).1.1 fx

/-- **HandsAtYes from the lighter record and the plan's test.** -/
theorem handsAtYes_light {Cl : Type} (hp : (K2.codeSwitchKind (Cl := Cl) p).planOk = true)
    (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ)
    (pl : R.Kp → OnBytes.KeptPlace) (aOf : (LocK).hd.K → ℕ)
    (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (on : Rec × Yt → Prop)
    (C : CallerAt R cs l iJ iQ mem row pl W₀)
    (F : ∀ a, on a →
      FrontOnL R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p strs inX orcs W₀ mem row pl aOf iOf a)
    (P : YesAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ shown orcs on) :
    HandsAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on := by
  intro a τ s' Qs fx y S3 Y rows G c W carried ha ht hQ Y1 L
  have h32 := K2.plan_32 hp
  obtain ⟨F1, D, DK, hm, hr, h2, Q, X⟩ :=
      hands_of_plan R Hd Sb sl Z A₀ cs l iJ iQ t w₀ h32 ht Y1 L C
    (frontAt_of_light R Hd Sb sl Z A₀ cs l iJ iQ t w₀ h32 Y1 L C (F a ha fx Y1.front))
    (P a τ s' Qs ha ht hQ)
  exact ⟨_, _, _, _, _, mem, row, pl, _, aOf, iOf, F1, D, DK, hm, hr, h2, rfl, rfl, Q, X⟩

/-- **AfterAtYes from the lighter record, the plan's test and the library's Lin.** -/
theorem afterAtYes_light {Cl : Type} (hp : (K2.codeSwitchKind (Cl := Cl) p).planOk = true)
    (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ)
    (pl : R.Kp → OnBytes.KeptPlace) (aOf : (LocK).hd.K → ℕ)
    (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (on : Rec × Yt → Prop)
    (C : CallerAt R cs l iJ iQ mem row pl W₀)
    (hL : (LocK).Lin
      (fun j : R.Sh.Cf.J => (⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (LocK).S.Ent))
      (fun q : R.Sh.Cf.Q => (⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (LocK).S.Ent)) Slf.idf id)
    (F : ∀ a, on a →
      FrontOnL R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p strs inX orcs W₀ mem row pl aOf iOf a)
    (P : YesAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ shown orcs on) :
    AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on :=
  afterAtYes_of R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on hL
    (handsAtYes_light R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown orcs hp W₀ mem
      row pl aOf iOf on C F P)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.frontAt_of_light
#print axioms VerifiableInference.Desc.First.K2Hands.afterAtYes_light
