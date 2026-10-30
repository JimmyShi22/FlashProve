-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TieT.lean: the code switch: THE TIE hT OF THE SWITCH's LAW OVER TWO
WRITTEN ROUNDS (sel_law, Johnson/Top/H/SwitchLeads.lean), AT THE KIND's OWN TEXT.

sel_law takes a text out, a reading fa, a condition on, a relation Rb behind and seven readings ρ as
letters, and one premise with content, hT: where the text says yes, the seed and the positions have
readings, and what stands behind gives the typed joint behind. Here out, fa and Rb are DEFINED, at
the decision of the kind K2 (decideWith sendByL8 p), and hT is shown FROM ONE PREMISE, AfterAtYes
(below).
  relR_of    the typed end: the joint behind holds of w if every message's word decodes with its
             sample to w's message, the claim After holds of w's messages, and the carried joint A₁
             holds. By unfolding.
  faT        a statement in front is a carried record with oracles of any type Yt (a letter: the
             file's own, or the typed strings themselves); strs reads the strings of the open word
             and the open messages off THE RECORD AND THE ORACLES (the open word is the fold of the
             committed words by elements that earlier rounds drew, and these stand in the record:
             StrMade.lean); the typed reading is (inX of the record, strs of both); inX and strs are
             letters
  textT      the kind's decision at the two real views of a written transcript and at the groups of
             columns shown
  outT       THE TEXT OVER THE TWO WRITTEN ROUNDS: nothing where a round's test of work fails; else
             the kind's decision at the two real views (v₁, v₂) and at the groups of columns shown
             (a letter: a function of the statement and the whole written transcript); what it puts
             out is the record behind TOGETHER WITH the typed statement behind at the readings
             (ρ.after …)
  outT_inv   what a yes of outT is made of: both tests of work pass, textT says yes with the record
             behind, and the seed and the positions have readings
  outT_yes   under "the readings are defined where the tests of work pass": outT says yes JUST WHERE
             both tests pass and the kind's decision says yes: so nothing is hidden in the readings
  ReadOK     WHAT IS OWED BY WHOEVER LAYS ρ, v₁, v₂, pass₁, pass₂ IN: outT_yes' two premises; that
             where the tests pass the typed side's views show the text's elements, positions and
             items; Rd.ViewOK. NO THEOREM HERE TAKES IT BUT outT_yes (its first two): without it the
             law is of a text that may refuse more than the kind does, and the typed seed need not
             be the seed that the text's sending read
  RowsHoldT  every row that the switch's group has in the record behind BEYOND those that it had in
             front holds of w's new messages (AfterText.lean's TextHolds), the messages' numbers
             being (the number of messages in front of the sending) + i. (Not every row of the
             group: an earlier row that names no new entry would read «0 = its target», and the law
             would be idle there.)
  RbT        what stands behind: the decodings; RowsHoldT; the carried joint A₁
  AfterAtYes  THE ONE PREMISE WITH CONTENT THAT IS LEFT: at a yes, with ALL that the yes gives at
             one set of witnesses (K2Hears/Whole.lean's record AtYes): if all rows that the maker
             made hold, After holds at the typed statement behind. It is after_of_text's conclusion
             (AfterText.lean)
  tie_hT     hT, to the letter of sel_law
  HandsAtYes, afterAtYes_of  AfterAtYes follows from hands_on_rows' premises at every yes
             (HandsOn.lean) and the library's LdLocD.Lin, by after_of_text
  sel_law_at  sel_law called at these values
WHAT IS STILL A LETTER OR A PREMISE: the place's numbers p and the error ε'; the typed caller's
letters R, Hd, Sb, sl, Z, A₀, cs, l, iJ, iQ, t, w₀, Cw (the file's «variable» lines); ρ, v₁, v₂,
pass₁, pass₂, Yt, strs, inX, shown, on; AfterAtYes; sel_law's own hz, hon, hpr, hFit. At on := never
it is still true and says nothing. That the columns shown are the strings' (the hearing law's
ShowsR) enters through AfterAtYes (TieN's clause «symbol»). The decodings in RbT are said of the
typed statement that outT carries beside the record, not yet of the record's own pins. TextHolds is
a sum over the new sending's entries: that it is «the program's row holds», as a sum over all that a
world of tables names, is TextSum.lean's textHolds_iff, under hands_on_rows' fifth conjunct
(OnlyAt), tables that are 0 outside their ranges and a one-to-one numbering of the messages.
Kin: sel_behind_of (Johnson/Top/H/SwitchBehind.lean [not in this library]) has relR_of's conclusion
from «all typed rows
hold» in After's place, under hC : Sh.Cf.Laws. No soundness is claimed.
-/
import Johnson.Top.H.SwitchLeads
import Johnson.Top.H0.K2Hands.AfterText
import Johnson.Top.H0.K2Hears.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

/-- The carried record. -/
abbrev Rec : Type := VerifiableInference.Desc.First.S
/-- The groups of columns that a step is shown. -/
abbrev Gs : Type := List (List (ℕ × List UInt64))

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "zS" => switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw
set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **The typed end.** -/
theorem relR_of
    (a : (Cb.Pv.SendLoc.loc (zS).sw).tgt.X × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str)
    (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W)
    (hd : ∀ i, (LocK).S.decs a.1.2 a.2.1.2 i = some (w.1 i).1)
    (hA : (LocK).After a.1.1.1 ((LocK).S.msgs w.1))
    (h1 : (LocK).A₁.relR (a.1.1.2, a.2.1.1) ((LocK).S.msgs w.1, w.2)) :
    (Cb.Pv.SendLocRide.outJ (zS)).relR a w := Or.inl ⟨hd, hA, h1⟩

variable {r₁ r₂ : Round} (ρ : Rd (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw) r₁ r₂) (p : K2.P2)
  (v₁ : r₁.Msg → r₁.Chal → Fmt.RoundView) (v₂ : r₂.Msg → r₂.Chal → Fmt.RoundView)
  (pass₁ : r₁.Chal → Bool) (pass₂ : r₂.Chal → Bool)
  {Yt : Type} (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀
      Cw).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).X)
  (shown : Rec × Yt → Tr [r₁, r₂] → Gs)

/-- The typed reading of a statement in front. -/
def faT (a : Rec × Yt) :
    (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str := (inX a.1, strs a)

/-- The kind's decision at the real views of a written transcript. -/
def textT (a : Rec × Yt) (τ : Tr [r₁, r₂]) :
    Except String Rec :=
  K2.decideWith _root_.Tw.K2.sendByL8 p a.1 [v₁ τ.1 τ.2.1, v₂ τ.2.2.1 τ.2.2.2.1]
    (shown a τ)

/-- **The text over the two written rounds.** -/
noncomputable def outT (a : Rec × Yt) (τ : Tr [r₁, r₂]) :
    Option (Rec × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str)) :=
  if (pass₁ τ.2.1 && pass₂ τ.2.2.2.1) = true then
    (textT p v₁ v₂ shown a τ).toOption.bind fun s' =>
      (ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn).bind fun sd =>
        (ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn).map fun Qs =>
          (s',
              ρ.after (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a) sd Qs (ρ.answ τ.2.2.1)
                  τ.1)
  else none

/-- What a yes of outT is made of. -/
theorem outT_inv {a : Rec × Yt} {τ : Tr [r₁, r₂]}
    {b : Rec × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str)}
    (h : outT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown a τ = some b)
        :
    pass₁ τ.2.1 = true ∧ pass₂ τ.2.2.2.1 = true ∧
      textT p v₁ v₂ shown a τ = .ok b.1 ∧
      ∃ sd Qs, ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd ∧
        ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
        b.2 = ρ.after (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a) sd Qs (ρ.answ τ.2.2.1)
            τ.1 := by
  unfold outT at h
  split at h
  · rename_i hp
    rw [Bool.and_eq_true] at hp
    obtain ⟨s', hs, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨sd, hsd, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨Qs, hQ, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨hp.1, hp.2, ?_, sd, Qs, hsd, hQ, rfl⟩
    cases ht : textT p v₁ v₂ shown a τ with
    | error e => rw [ht] at hs; cases hs
    | ok s'' => rw [ht] at hs; cases hs; rfl
  · cases h

/-- **outT says yes just where both tests of work pass and the kind's decision says yes**, if the
readings are defined where the tests pass. -/
theorem outT_yes
    (hS : ∀ m c, pass₁ c = true → (ρ.rdSeed (ρ.view₁ m c).drawn).isSome = true)
    (hP : ∀ m c, pass₂ c = true → (ρ.rdPos (ρ.view₂ m c).drawn).isSome = true)
    (a : Rec × Yt) (τ : Tr [r₁, r₂]) :
    (outT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown a τ).isSome = true
        ↔
      pass₁ τ.2.1 = true ∧ pass₂ τ.2.2.2.1 = true ∧
        ∃ s', textT p v₁ v₂ shown a τ = .ok s' := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨h1, h2, h3, -⟩ := outT_inv R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs
      inX shown hb
    exact ⟨h1, h2, _, h3⟩
  · rintro ⟨h1, h2, s', h3⟩
    obtain ⟨sd, hsd⟩ := Option.isSome_iff_exists.1 (hS τ.1 τ.2.1 h1)
    obtain ⟨Qs, hQ⟩ := Option.isSome_iff_exists.1 (hP τ.2.2.1 τ.2.2.2.1 h2)
    unfold outT
    rw [if_pos (by rw [h1, h2]; rfl), h3, hsd, hQ]
    rfl

/-- **What is owed by whoever lays ρ, v₁, v₂, pass₁, pass₂ in**: the readings are defined where the
tests of
work pass; there the views that the typed side reads show the elements, the positions and the items
that the
text's views show; the second view's items do not hang on the verifier's message. -/
structure ReadOK : Prop where
  seed : ∀ m c, pass₁ c = true → (ρ.rdSeed (ρ.view₁ m c).drawn).isSome = true
  pos : ∀ m c, pass₂ c = true → (ρ.rdPos (ρ.view₂ m c).drawn).isSome = true
  elems : ∀ m c, pass₁ c = true → (ρ.view₁ m c).drawn.elems = (v₁ m c).drawn.elems
  poss : ∀ m c, pass₂ c = true → (ρ.view₂ m c).drawn.poss = (v₂ m c).drawn.poss
  vals : ∀ m c, pass₂ c = true → (ρ.view₂ m c).vals = (v₂ m c).vals
  viewOK : ρ.ViewOK

/-- Every row that the switch's group has in the record behind BEYOND those that it had in front
holds of
w's new messages. -/
def RowsHoldT (s s' : Rec) (u : (LocK).S.Msg) : Prop :=
  ∀ fx, K2.frontAt p s = some fx → ∀ G0 G', fx.st.groups[fx.f.group]? = some G0 →
    s'.st.groups[fx.f.group]? = some G' →
    ∀ r ∈ G'.rows.toList.drop G0.rows.size, TextHolds cs l (fun i => fx.st.oracles.size + i) r
      (fun n => (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n))

/-- **What stands behind.** -/
def RbT (a : Rec × Yt)
    (b : Rec × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str))
    (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W) : Prop :=
  (∀ i, (LocK).S.decs b.2.1.2 b.2.2.1.2 i = some (w.1 i).1) ∧
    RowsHoldT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p a.1 b.1 ((LocK).S.msgs w.1) ∧
    (LocK).A₁.relR (b.2.1.1.2, b.2.2.1.1) ((LocK).S.msgs w.1, w.2)

/-- **The premise that is left**: after_of_text's conclusion at every yes. -/
def AfterAtYes (on : Rec × Yt → Prop) : Prop :=
  ∀ (a : Rec × Yt) (τ : Tr [r₁, r₂]) (s' : Rec)
    (Qs : Fin (zS).sw.t → (zS).sw.P) (fx : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent)
    (S3 : OnBytes.Statement) (Y : Array OnBytes.E) (rows : List OnBytes.Row) (G : OnBytes.Group)
    (c : OnBytes.Code), on a →
    textT p v₁ v₂ shown a τ = .ok s' →
    ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs →
    K2.AtYes p a.1 s' (v₁ τ.1 τ.2.1) (v₂ τ.2.2.1 τ.2.2.2.1)
      (shown a τ) fx y S3 Y rows G c →
    ∀ u : (LocK).S.Msg,
      (∀ r ∈ rows, TextHolds cs l (fun i => fx.st.oracles.size + i) r
        (fun n => (LocK).S.ents u (newEnt R Hd Sb sl Z A₀ cs l iJ iQ t w₀ n))) →
      (LocK).After ((inX a.1).1.1, (Qs, fun i => (zS).sw.C.T (strs a).1.1 (Qs i))) u

/-- **hT, to the letter of sel_law.** -/
theorem tie_hT (on : Rec × Yt → Prop)
    (hA : AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on) :
    ∀ a τ b, on a →
      outT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown a τ = some b →
      ∃ sd Qs, ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd ∧
        ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
        ∀ w, RbT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p a b w →
          (Cb.Pv.SendLocRide.outJ (zS)).relR
            (ρ.after (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a) sd Qs (ρ.answ τ.2.2.1) τ.1)
            w := by
  intro a τ b ha hb
  obtain ⟨-, -, ht, sd, Qs, hsd, hQ, hb2⟩ :=
    outT_inv R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown hb
  refine ⟨sd, Qs, hsd, hQ, fun w hw => ?_⟩
  obtain ⟨hdec, hrows, h1⟩ := hw
  rw [hb2] at hdec h1
  obtain ⟨fx, y, S3, Y, rows, G, c, Y1⟩ := K2.yes_whole p a.1 _ _ _ b.1 ht
  obtain ⟨G', hG', hr⟩ := Option.map_eq_some_iff.1 Y1.kept
  obtain ⟨G0, hG0, h0⟩ := Option.map_eq_some_iff.1 Y1.before
  refine relR_of R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw _ w hdec ?_ h1
  refine hA a τ b.1 Qs fx y S3 Y rows G c ha ht hQ Y1 _ fun r hr' => ?_
  refine hrows fx Y1.front G0 G' hG0 hG' r ?_
  have e : (G.rows ++ rows.toArray).toList.drop G.rows.size = rows := by simp
  rw [hr, h0, e]
  exact hr'

set_option quotPrecheck false in
local notation "pJK" => fun j : R.Sh.Cf.J =>
  ((⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))
set_option quotPrecheck false in
local notation "pQK" => fun q : R.Sh.Cf.Q =>
  ((⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.S.Ent))

/-- What hands_on_rows asks, at every yes: of the frame that the maker made there, of the names, of
the old
claim, and of the typed statement behind. -/
def HandsAtYes (on : Rec × Yt → Prop) : Prop :=
  ∀ (a : Rec × Yt) (τ : Tr [r₁, r₂]) (s' : Rec)
    (Qs : Fin (zS).sw.t → (zS).sw.P) (fx : _root_.Tw.K2.Front) (y : _root_.Tw.K2.Sent)
    (S3 : OnBytes.Statement) (Y : Array OnBytes.E) (rows : List OnBytes.Row) (G : OnBytes.Group)
    (c : OnBytes.Code) (W : OnBytes.SwitchFrame) (carried : OnBytes.Row), on a →
    textT p v₁ v₂ shown a τ = .ok s' →
    ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs →
    K2.AtYes p a.1 s' (v₁ τ.1 τ.2.1) (v₂ τ.2.2.1 τ.2.2.2.1)
      (shown a τ) fx y S3 Y rows G c →
    Laid S3 fx.f.rows fx.T (y.ids.getD 0 OnBytes.noId) (y.ids.extract 1 (1 + fx.T.kept.size))
      (OnBytes.Positions.ofDraws p.logN (v₂ τ.2.2.1 τ.2.2.2.1).drawn.poss) Y rows W carried →
    ∃ (aMain aM0 aT0 aM1 aT1 : ℕ) (mem row : R.Kp → ℕ) (pl : R.Kp → OnBytes.KeptPlace)
      (aKept : R.Kp → ℕ) (aOf : (LocK).hd.K → ℕ) (iOf : ∀ k, ((LocK).hd.o k).Z.S → ℕ),
      FrameOK W aMain aM0 aT0 aM1 aT1 ∧
      Names R.s R.Kp cs l iJ iQ W (fun i => fx.st.oracles.size + i) aMain aM0 aT0 aM1 aT1 ∧
      NamesK R.s R.Kp cs l iJ iQ W (fun i => fx.st.oracles.size + i) mem row pl aKept ∧
      (∀ κ, W.kept[mem κ]? = some (pl κ)) ∧ (∀ κ, row κ < (pl κ).rows) ∧ fx.f.rows.masks = 2 ∧
      aM0 = W.parts.maskAt.getD 0 0 ∧ aM1 = W.parts.maskAt.getD 1 0 ∧
      (∀ ks, fx.f.rows.kept.toList.mapM (placeOf W) = some ks →
        ClaimOK R.s R.Kp cs l W (fun i => fx.st.oracles.size + i) mem row pl fx.f.rows ks) ∧
      TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀
        ((inX a.1).1.1, (Qs, fun i => (zS).sw.C.T (strs a).1.1 (Qs i))) S3 W
        (fun i => fx.st.oracles.size + i) fx.f.rows
        (OnBytes.Positions.ofDraws p.logN (v₂ τ.2.2.1 τ.2.2.2.1).drawn.poss) Y mem row pl aOf iOf

/-- **AfterAtYes from hands_on_rows' premises at every yes**, by after_of_text. -/
theorem afterAtYes_of (on : Rec × Yt → Prop)
    (hL : (LocK).Lin pJK pQK Slf.idf id)
    (H : HandsAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on) :
    AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on := by
  intro a τ s' Qs fx y S3 Y rows G c ha ht hQ Y1 u hu
  obtain ⟨W, carried, L⟩ := laid_of Y1.made
  obtain ⟨aMain, aM0, aT0, aM1, aT1, mem, row, pl, aKept, aOf, iOf, F, D, DK, hmem, hrow, h2, h0,
      h1,
    Q, X⟩ := H a τ s' Qs fx y S3 Y rows G c W carried ha ht hQ Y1 L
  exact after_of_text R Hd Sb sl Z A₀ cs l iJ iQ t w₀ L F D DK hmem hrow h2 h0 h1 Q _ X hL u hu

set_option quotPrecheck false in
local notation "hdS" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd

/-- **sel_law, called at the kind's own text.** -/
theorem sel_law_at (hz : Cb.Pv.SendLocRide.OK (zS))
    (on : Rec × Yt → Prop)
    (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (zS)).on
      (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a))
    (hpr : ∀ a, on a →
      ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).on
        (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a))
    (ε' : Err [r₁, r₂]) (hFit : ρ.carS.Fits (Cb.Pv.SendLocRide.eps (zS)) ε')
    (hA : AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on) :
    (⟨[r₁, r₂], outT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown⟩ :
        Reduction _ _).Leads on
      (fun a b => ∀ w, RbT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p a b w →
        ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).relR
            (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a)
            (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) ∧
          ∀ k : (hdS).K, ((hdS).o k).decW
              ((hdS).sW k (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a).2.1.1)
              ((faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a).1.1.1.2 k) =
            some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k))
      ε' :=
  sel_law Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ hz _ _ on hon hpr ε' hFit _
    (tie_hT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown on hA)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.afterAtYes_of
#print axioms VerifiableInference.Desc.First.K2Hands.sel_law_at
#print axioms VerifiableInference.Desc.First.K2Hands.relR_of
#print axioms VerifiableInference.Desc.First.K2Hands.outT_yes
#print axioms VerifiableInference.Desc.First.K2Hands.tie_hT
