-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TiePaid.lean: the code switch: WHAT IS LEFT OF THE TIE's PREMISE
HandsAtYes (TieT.lean), ONCE ALL THAT THE LAST JOIN HAS SHOWN IS LAID IN.

HandsAtYes asks hands_on_rows' premises at every yes of the kind's decision. Most of them are shown
elsewhere from the yes itself: AtYes.lean's atSwitch_of (eight of AtSwitch's sixteen clauses; the
other eight it hands through from its own premises, which are clauses of CallerAt and FrontAt here),
Paid.lean's paid_frame | names | namesK | claim, TieSym.lean's tieN_of. Here they are called in a
row.
  CallerAt   ASKED ONCE, of the typed caller's letters and a PUBLIC frame W₀ (a letter), 5: codeC ·
             codeZ · slots · mapJ · mapQ (the caller's two maps of names are W₀'s own)
  FrontAt    ASKED OF THE STATEMENT IN FRONT, 16: of the front fx that the text makes of the record:
             frameIs (the frame at the front, FrameOfFront.lean's frameAt, is W₀) · z32 (the MASK
             code's logN is at most 32) · twoOld (two kept places have two old numbers; these two
             stand beside frameIs, so that a law on switchFrame's value can pay them) · codes ·
             keptPos · keptRows · ell · first · next · mainVars · d0 · d1; of the typed open word's
             string: strIs (ShowsCols.lean's StrIs: it is what the front reads off the oracles,
             position by position); of the typed claim and held samples: target · vector · sample.
             NOTHING OF THE TWO ROUNDS OCCURS IN IT: so it can stand in «on»
  YesAt      ASKED AT A YES, 3: len · reads (the reading of the positions) · cols (every column that
             the decision is shown is the oracles': K2Hears/LongCols.lean's ColsOf). That the
             columns shown are the typed string's symbols (TieSym.lean's ShowsAt) is no premise:
             ShowsCols.lean's shows_of_cols has it from strIs and cols
  old_at_yes  an old message has, in the statement that the rows' maker reads, the shape and the
             sample rows that it had in front
  hands_of_plan  at one yes: hands_on_rows' premises out of the three records, logN ≤ 32 (a premise,
             h32) and two records that are premises HERE and that a yes gives: AtYes
             (K2Hears/Whole.lean's yes_whole) and Laid (RowsAt.lean's laid_of)
  FrontOn, YesAtYes  FrontAt at the front that the text makes of a statement's record; YesAt at
             every yes of the text over the two written rounds: the forms in which the two end
             theorems take them
  handsAtYes_paid  HandsAtYes from CallerAt, FrontAt at every statement with «on», YesAt at every
             yes, and logN ≤ 32
  afterAtYes_paid  AfterAtYes, the one premise of tie_hT and sel_law_at (TieT.lean), from these and
             LdLocD.Lin
That the frame which the rows' maker uses at a yes is the front's is shown: FrameOfFront.lean's
frame_of_front.
LIMITS. CallerAt, FrontAt and YesAt are premises: every clause of the three; so is logN ≤ 32
(AtYes.lean's plan_32 has it from the kind's test on the plan; no theorem here calls it). «on» is a
letter: at on := never all this is true and says nothing; no member is named. No soundness is
claimed.
-/
import Johnson.Top.H0.K2Hands.TieT
import Johnson.Top.H0.K2Hands.TieSym
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H0.K2Hands.HandsOnPaid
import Johnson.Top.H0.K2Hands.FrameOfFront
import Johnson.Top.H0.K2Hands.ShowsCols

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

/-- **What is asked once, of the typed caller's letters and of a public frame W₀.** -/
structure CallerAt (mem row : R.Kp → ℕ) (pl : R.Kp → OnBytes.KeptPlace)
    (W₀ : OnBytes.SwitchFrame) : Prop where
  codeC : R.s.C = codeOf W₀.code
  codeZ : R.s.Z = codeOf W₀.zk
  slots : SlotsAll R.Kp W₀ mem row pl
  mapJ : ∀ F : Fit cs l R.s W₀ mem row pl, iJ = Johnson.Top.H.iJ R.s W₀ mem row pl cs l F.nameJ
  mapQ : ∀ F : Fit cs l R.s W₀ mem row pl, iQ = Johnson.Top.H.iQ R.s W₀ mem row cs l F.nameQ

/-- **What is asked of the statement in front**: of the front fx that the text makes of the record,
and of
the typed statement's claim and held samples xc. Nothing of the two rounds occurs. -/
structure FrontAt (W₀ : OnBytes.SwitchFrame) (p : K2.P2) (mem row : R.Kp → ℕ)
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
      Slots R.s R.Kp cs l W₀ (fun i => fx.st.oracles.size + i) mem row (aOf ks.1) k ∧
      (xc.2 ks.1).2 ks.2 = readE smp.target ∧
      pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat (xc.2 ks.1).1 ks.2) =
        slotVec R.s R.Kp mem row (aOf ks.1) k.rowBits (formOn smp)

/-- **What stays asked at a yes.** -/
structure YesAt (p : K2.P2) (r₂ : Fmt.RoundView) (gs : Gs) (orc : ℕ → ℕ → List UInt64)
    (Qs : Fin (LocK).t → (LocK).P) : Prop where
  len : r₂.drawn.poss.length = (LocK).t
  reads : ∀ i, (Qs i).val = r₂.drawn.poss.getD i.val 0 % 2 ^ p.logN
  cols : K2.ColsOf orc (K2.flat p gs)

/-- An old message, behind the sending and the joins, as the rows' maker reads it. -/
theorem old_at_yes {p : K2.P2} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs} {fx : _root_.Tw.K2.Front}
    {y : _root_.Tw.K2.Sent} {S3 : OnBytes.Statement} {Y : Array OnBytes.E}
    {rows : List OnBytes.Row} {G : OnBytes.Group} {c : OnBytes.Code}
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c) (o : ℕ) (ho : o < fx.st.oracles.size) :
    (S3.oracles.getD o default).shape = (fx.st.oracles.getD o default).shape ∧
      (S3.oracles.getD o default).sampleRows = (fx.st.oracles.getD o default).sampleRows := by
  have a := (Y1.same.shape o).trans (congrArg (Option.map (·.shape)) (Y1.sent.old o ho))
  have b := (Y1.same.samples o).trans (congrArg (Option.map (·.sampleRows)) (Y1.sent.old o ho))
  have h3 : o < S3.oracles.size := by
    rw [Y1.same.size, Y1.sent.size]
    omega
  constructor
  · simpa [Array.getD, ho, h3] using a
  · simpa [Array.getD, ho, h3] using b

/-- At one yes: hands_on_rows' premises, out of the three records and what the yes gives. -/
theorem hands_of_plan {W₀ : OnBytes.SwitchFrame} {p : K2.P2} (h32 : p.logN ≤ 32)
    {mem row : R.Kp → ℕ}
    {pl : R.Kp → OnBytes.KeptPlace} {aOf : (LocK).hd.K → ℕ}
    {iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ} {s s' : Rec} {r₁ r₂ : Fmt.RoundView} {gs : Gs}
    {xc : (LocK).Xc × (LocK).hd.Smp} {str : (LocK).C.ext.Str} {Qs : Fin (LocK).t → (LocK).P}
    {fx : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : OnBytes.Statement}
    {Y : Array OnBytes.E} {rows : List OnBytes.Row} {G : OnBytes.Group} {c : OnBytes.Code}
    {W : OnBytes.SwitchFrame} {carried : OnBytes.Row} {orc : ℕ → ℕ → List UInt64}
    (ht : K2.decideWith _root_.Tw.K2.sendByL8 p s [r₁, r₂] gs = .ok s')
    (Y1 : K2.AtYes p s s' r₁ r₂ gs fx y S3 Y rows G c)
    (L : Laid S3 fx.f.rows fx.T (y.ids.getD 0 OnBytes.noId) (y.ids.extract 1 (1 + fx.T.kept.size))
      (OnBytes.Positions.ofDraws p.logN r₂.drawn.poss) Y rows W carried)
    (C : CallerAt R cs l iJ iQ mem row pl W₀)
    (P : FrontAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc xc str fx)
    (Q : YesAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p r₂ gs orc Qs) :
    FrameOK W W.parts.mainTailAt (W.parts.maskAt.getD 0 0) (W.parts.maskTailAt.getD 0 0)
        (W.parts.maskAt.getD 1 0) (W.parts.maskTailAt.getD 1 0) ∧
      Names R.s R.Kp cs l iJ iQ W (fun i => fx.st.oracles.size + i) W.parts.mainTailAt
        (W.parts.maskAt.getD 0 0) (W.parts.maskTailAt.getD 0 0) (W.parts.maskAt.getD 1 0)
        (W.parts.maskTailAt.getD 1 0) ∧
      NamesK R.s R.Kp cs l iJ iQ W (fun i => fx.st.oracles.size + i) mem row pl
        (fun κ => W.parts.keptTailAt.getD (keptNo W (mem κ) (row κ)) 0) ∧
      (∀ κ, W.kept[mem κ]? = some (pl κ)) ∧ (∀ κ, row κ < (pl κ).rows) ∧ fx.f.rows.masks = 2 ∧
      (∀ ks, fx.f.rows.kept.toList.mapM (placeOf W) = some ks →
        ClaimOK R.s R.Kp cs l W (fun i => fx.st.oracles.size + i) mem row pl fx.f.rows ks) ∧
      TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ (xc, (Qs, fun i => (LocK).C.T str (Qs i))) S3 W
        (fun i => fx.st.oracles.size + i) fx.f.rows
        (OnBytes.Positions.ofDraws p.logN r₂.drawn.poss) Y mem row pl aOf iOf := by
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
  have hV := shows_of_cols R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Y1 Q.cols
    (coordOf_lt C.slots P.keptRows (check_facts Y1.check).1) P.strIs
  have X := tieN_of R Hd Sb sl Z A₀ cs l iJ iQ t w₀ ht xc Qs str Y1.heard Q.len Q.reads hV
    P.target P.vector (St := S3) (fun ks => by
      obtain ⟨k, smp, h1, h2, h3⟩ := P.sample ks
      refine ⟨k, smp, h1, ?_, h3⟩
      unfold samplesOf at h2 ⊢
      rw [(old_at_yes Y1 k.old (hold _ k h1)).2]
      exact h2)
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
  refine ⟨paid_frame A, ?_, ?_, A.slots.member, A.slots.rowIn, (check_facts A.check).1, ?_, X⟩
  · have e := paid_names A
    have eJ := C.mapJ
    have eQ := C.mapQ
    clear X P C Q hV
    subst hc
    rw [eJ A.fit, eQ A.fit]
    exact e
  · have e := paid_namesK A
    have eJ := C.mapJ
    have eQ := C.mapQ
    clear X P C Q hV
    subst hc
    rw [eJ A.fit, eQ A.fit]
    exact e
  · intro ks hks
    have e := paid_claim A P.mainVars P.d0 P.d1 P.twoOld ks hks
    clear X P C Q hV
    subst hc
    exact e

variable {Pw : Type} (Cw : LdCode GE Pw) {r₁ r₂ : Round}
  (ρ : Rd (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw) r₁ r₂) (p : K2.P2)
  (v₁ : r₁.Msg → r₁.Chal → Fmt.RoundView) (v₂ : r₂.Msg → r₂.Chal → Fmt.RoundView)
  {Yt : Type} (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀
      Cw).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).X)
  (shown : Rec × Yt → Tr [r₁, r₂] → Gs) (orcs : Rec × Yt → ℕ → ℕ → List UInt64)

set_option quotPrecheck false in
local notation "zS" => switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw

/-- What is asked of a statement in front: FrontAt at the front that the text makes of its record.
-/
def FrontOn (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ) (pl : R.Kp → OnBytes.KeptPlace)
    (aOf : (LocK).hd.K → ℕ) (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (a : Rec × Yt) : Prop :=
  ∀ fx, K2.frontAt p a.1 = some fx →
    FrontAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf a.1 (orcs a) (inX a.1).1.1
      (strs a).1.1 fx

/-- YesAt at every yes of the text over the two written rounds. -/
def YesAtYes (on : Rec × Yt → Prop) : Prop :=
  ∀ (a : Rec × Yt) (τ : Tr [r₁, r₂]) (s' : Rec) (Qs : Fin (zS).sw.t → (zS).sw.P), on a →
    textT p v₁ v₂ shown a τ = .ok s' →
    ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs →
    YesAt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p (v₂ τ.2.2.1 τ.2.2.2.1) (shown a τ) (orcs a) Qs

/-- **HandsAtYes from the three records.** -/
theorem handsAtYes_paid (h32 : p.logN ≤ 32) (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ)
    (pl : R.Kp → OnBytes.KeptPlace) (aOf : (LocK).hd.K → ℕ)
    (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (on : Rec × Yt → Prop)
    (C : CallerAt R cs l iJ iQ mem row pl W₀)
    (F : ∀ a, on a →
      FrontOn R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p strs inX orcs W₀ mem row pl aOf iOf a)
    (P : YesAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ shown orcs on) :
    HandsAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on := by
  intro a τ s' Qs fx y S3 Y rows G c W carried ha ht hQ Y1 L
  obtain ⟨F1, D, DK, hm, hr, h2, Q, X⟩ :=
      hands_of_plan R Hd Sb sl Z A₀ cs l iJ iQ t w₀ h32 ht Y1 L C
    (F a ha fx Y1.front) (P a τ s' Qs ha ht hQ)
  exact ⟨_, _, _, _, _, mem, row, pl, _, aOf, iOf, F1, D, DK, hm, hr, h2, rfl, rfl, Q, X⟩

/-- **AfterAtYes, the tie's one premise, from the three records and the library's Lin.** -/
theorem afterAtYes_paid (h32 : p.logN ≤ 32) (W₀ : OnBytes.SwitchFrame) (mem row : R.Kp → ℕ)
    (pl : R.Kp → OnBytes.KeptPlace) (aOf : (LocK).hd.K → ℕ)
    (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ) (on : Rec × Yt → Prop)
    (C : CallerAt R cs l iJ iQ mem row pl W₀)
    (hL : (LocK).Lin
      (fun j : R.Sh.Cf.J => (⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (LocK).S.Ent))
      (fun q : R.Sh.Cf.Q => (⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (LocK).S.Ent)) Slf.idf id)
    (F : ∀ a, on a →
      FrontOn R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p strs inX orcs W₀ mem row pl aOf iOf a)
    (P : YesAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ shown orcs on) :
    AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on :=
  afterAtYes_of R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on hL
    (handsAtYes_paid R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown orcs h32 W₀ mem
      row pl aOf iOf on C F P)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.afterAtYes_paid
#print axioms VerifiableInference.Desc.First.K2Hands.hands_of_plan
