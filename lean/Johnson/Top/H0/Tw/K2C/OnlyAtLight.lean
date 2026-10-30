-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/OnlyAtLight.lean: THE LIGHT ROAD: code switching
(the kind K2): EVERY ROW THAT THE SWITCH LAYS HAS, INSIDE THE TABLES, NO COEFFICIENT BUT AT A TYPED
ENTRY OF THE NEW SENDING: WITH NO TYPED STATEMENT AMONG THE PREMISES.

Why. `only_at_rows` (K2C/OnlyAtRows.lean) asks `TieN` at a typed statement x; at an accept
`hands_of_plan` (K2Hands/TiePaid.lean) makes it out of `FrontAt`, `YesAt` and "the decision
accepts". But of `TieN` the clause `OnlyAt` of `hands_on_rows` (K2Hands/HandsOn.lean) spends "draw"
and the first three conjuncts of "sample" alone; and these are had for less: the first two of
"sample" from `Held.member`, the third from `paid_slots` (K2Hands/Paid.lean), "draw" from the list
of draws itself.

  only_at_rows_light   `only_at_rows`' premises without x and `TieN`; with `Slots` at every kept
                       member and "every draw is below 2 ^ (the code's logN)"
  FrontLight           twelve of `FrontAt`'s sixteen fields: those that name no typed statement, no
                       string and no oracle
  FrontAt.toFrontLight `FrontAt` gives it
  only_at_yes_light    at what an accept gives (`K2.AtYes`): from `CallerAt`, `FrontLight`, `Held`,
                       the count of the drawn positions and their range; at the public frame W₀;
                       no `Laid` is asked (`laid_of` makes it); no `YesAt`; no "the decision
                       accepts"
  only_at_yes_of_yes   the range from "the decision accepts" (`K2.inRangeOfYes`)





Limits. `CallerAt`, `FrontLight`, `Held`, the count and the range stay premises. Shown at no real
state. No soundness statement.

-/
import Johnson.Top.H0.K2Hands.TiePaid
import Johnson.Top.H0.Tw.K2C.OnlyAtRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

/-- **Twelve of `FrontAt`'s fields**: of the front fx that the text makes of the state, and of a
public frame W₀. No typed statement, no string and no oracle occurs. -/
structure FrontLight (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (W₀ : OnBytes.SwitchFrame) (fx : _root_.Tw.K2.Front) : Prop where
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

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- `FrontAt` gives `FrontLight`. -/
theorem FrontAt.toFrontLight {W₀ : OnBytes.SwitchFrame} {p : K2.P2} {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} {s : Rec} {orc : ℕ → ℕ → List UInt64}
    {xc : (LocK).Xc × (LocK).hd.Smp} {str : (LocK).C.ext.Str} {fx : _root_.Tw.K2.Front}
    (P : FrontAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc xc str fx) :
    FrontLight cs l W₀ fx :=
  ⟨P.frameIs, P.z32, P.twoOld, P.codes, P.keptPos, P.keptRows, P.ell, P.first, P.next, P.mainVars,
    P.d0, P.d1⟩

/-- **Every laid row, with no typed statement among the premises.** -/
theorem only_at_rows_light {St : OnBytes.Statement} {old : OnBytes.SingleRows}
    {T : OnBytes.SwitchTarget} {g : ℕ} {anew : Array ℕ} {pos : OnBytes.Positions}
    {y : Array OnBytes.E} {rows : List OnBytes.Row} {W : OnBytes.SwitchFrame}
    {carried : OnBytes.Row} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aKept : R.Kp → ℕ} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} (L : Laid St old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1)
    (D : Names R.s R.Kp cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK R.s R.Kp cs l iJ iQ W ids mem row pl aKept)
    (hm : old.masks = 2) (h0 : aM0 = W.parts.maskAt.getD 0 0) (h1 : aM1 = W.parts.maskAt.getD 1 0)
    (Q : ∀ ks, old.kept.toList.mapM (placeOf W) = some ks →
      ClaimOK R.s R.Kp cs l W ids mem row pl old ks)
    (A : SlotsAll R.Kp W mem row pl) (H : Held St W aOf iOf)
    (Sl : ∀ a k, W.kept[a]? = some k → Slots R.s R.Kp cs l W ids mem row a k)
    (hd : pos.draws.toList.length = (LocK).t)
    (hin : ∀ v ∈ pos.draws.toList, v < 2 ^ W.code.logN) :
    ∀ r ∈ rows, OnlyAt cs l ids (Inside R.s W pl) r := by
  intro r hr
  obtain ⟨m, hm', hrm⟩ := List.getElem_of_mem hr
  rw [hands_on_count L hm hd] at hm'
  obtain ⟨b, hb⟩ := rowNo_onto (s := R.s) A H m hm'
  have key : ∃ r' : OnBytes.Row, rows[rowNo R.s R.Kp St W mem row aOf iOf b]? = some r' ∧
      OnlyAt cs l ids (Inside R.s W pl) r' := by
    rcases b with ⟨⟩ | ks | ⟨i, α⟩
    · obtain ⟨ks, hks, rfl⟩ := (switchCarried_iff W old carried).1 L.claim
      exact ⟨_, rows_claim L, fun o part J hi =>
        claim_only F D DK A.member old ks hm h0 h1 (Q ks hks) o part J hi.2⟩
    · obtain ⟨k, hk, hi⟩ := H.member ks.1
      exact ⟨_, rows_sample L (aOf ks.1) (iOf ks.1 ks.2) k _ hk
        (List.getElem?_eq_getElem (hi ks.2)), fun o part J hj =>
        sample_only D DK A.member (aOf ks.1) k hk (Sl _ k hk) _ o part J
          (hj.2.2 k (List.mem_of_getElem? hk))⟩
    · have hi : i.val < pos.draws.toList.length := by
        rw [hd]
        exact i.isLt
      obtain ⟨r', hr', -, -, ho⟩ := gen_join2 L F D DK A.member A.rowIn hm i.val _
        (List.getElem?_eq_getElem hi) (hin _ (List.getElem_mem hi)) α
      exact ⟨r', hr', fun o part J hj => ho o part J hj.1⟩
  obtain ⟨r', hr', ho⟩ := key
  have e : r' = r := by
    have h2 : rows[m]? = some r' := (congrArg (fun i => rows[i]?) hb).symm.trans hr'
    rw [List.getElem?_eq_getElem (by rw [hands_on_count L hm hd]; exact hm'), hrm] at h2
    exact (Option.some.inj h2).symm
  subst e
  exact ho

/-- **At what an accept gives.** -/
theorem only_at_yes_light {W₀ : OnBytes.SwitchFrame} {p : K2.P2} (h32 : p.logN ≤ 32)
    {mem row : R.Kp → ℕ} {pl : R.Kp → OnBytes.KeptPlace} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : OnBytes.Statement}
    {Y : Array OnBytes.E} {rows : List OnBytes.Row} {G : OnBytes.Group} {c : OnBytes.Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    (C : CallerAt R cs l iJ iQ mem row pl W₀) (P : FrontLight cs l W₀ fx)
    (H : Held S3 W₀ aOf iOf) (hlen : r₂.drawn.poss.length = (LocK).t)
    (hin : ∀ v ∈ r₂.drawn.poss, v < 2 ^ p.logN) :
    ∀ ρ ∈ rows, OnlyAt cs l (fun i => fx.st.oracles.size + i) (Inside R.s W₀ pl) ρ := by
  obtain ⟨W, carried, L⟩ := laid_of Y1.made
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
  have hN : W₀.code.logN = p.logN := by
    rw [K2.frame_code Y1.same L.frame Y1.code]
    exact Y1.logN
  have hm := (check_facts A.check).1
  have eJ := C.mapJ
  have eQ := C.mapQ
  have hQ := fun ks hks => paid_claim A P.mainVars P.d0 P.d1 P.twoOld ks hks
  have hD := paid_names A
  have hDK := paid_namesK A
  have hSl := paid_slots A
  have hA := A.fit
  have hF := paid_frame A
  have hsl := C.slots
  clear P C
  subst hc
  rw [eJ hA, eQ hA] at *
  exact only_at_rows_light R Hd Sb sl Z A₀ S3.codes l _ _ t w₀ L hF hD hDK hm rfl rfl hQ hsl H hSl
    hlen (fun v hv => by rw [hN]; exact hin v hv)

/-- The range from "the decision accepts". -/
theorem only_at_yes_of_yes {W₀ : OnBytes.SwitchFrame} {p : K2.P2} (h32 : p.logN ≤ 32)
    {mem row : R.Kp → ℕ} {pl : R.Kp → OnBytes.KeptPlace} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : OnBytes.Statement}
    {Y : Array OnBytes.E} {rows : List OnBytes.Row} {G : OnBytes.Group} {c : OnBytes.Code}
    (ht : K2.decideWith _root_.Tw.K2.sendByL8 p s [r₁, r₂] gs = .ok s')
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    (C : CallerAt R cs l iJ iQ mem row pl W₀) (P : FrontLight cs l W₀ fx)
    (H : Held S3 W₀ aOf iOf) (hlen : r₂.drawn.poss.length = (LocK).t) :
    ∀ ρ ∈ rows, OnlyAt cs l (fun i => fx.st.oracles.size + i) (Inside R.s W₀ pl) ρ :=
  only_at_yes_light R Hd Sb sl Z A₀ cs l iJ iQ t w₀ h32 Y1 C P H hlen
    (K2.inRangeOfYes _ p s r₁ r₂ gs s' ht)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.FrontAt.toFrontLight
#print axioms VerifiableInference.Desc.First.K2Hands.only_at_rows_light
#print axioms VerifiableInference.Desc.First.K2Hands.only_at_yes_light
#print axioms VerifiableInference.Desc.First.K2Hands.only_at_yes_of_yes
