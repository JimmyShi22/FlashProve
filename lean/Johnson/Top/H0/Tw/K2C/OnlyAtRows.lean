-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/OnlyAtRows.lean: code switching (the kind K2): EVERY ROW THAT THE SWITCH
LAYS HAS, INSIDE THE TABLES, NO COEFFICIENT BUT AT A TYPED ENTRY OF THE NEW SENDING. NO BLOCK
IMPORTS THIS FILE. Why. «What a row says of words» (a sum over both tables of all messages) is
carried to «what it says of the new sending's typed entries» under OnlyAt (says_iff_textHolds,
Johnson/Top/H0/K2Caller/SaysText.lean). hands_on_rows (K2Hands/HandsOn.lean) has OnlyAt at the row
of each TYPED number; the numbering is onto (rowNo_onto, K2Hands/Numbering.lean): so it holds of
every row of the list.
  only_at_rows   under text_of_after's premises, but for its last three: ∀ r ∈ rows, OnlyAt cs l
                 ids (Inside R.s W pl) r
By the way of text_of_after (K2Hands/AfterText.lean), whose lines it follows. All premises of
hands_on_rows stay premises, with SlotsAll, Held and «as many draws as typed positions». No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.AfterText

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

theorem only_at_rows {St : OnBytes.Statement} {old : OnBytes.SingleRows}
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
    (x : ((LocK).Xc × (LocK).hd.Smp) × (LocK).Lc)
    (X : TieN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ x St W ids old pos y mem row pl aOf iOf)
    (A : SlotsAll R.Kp W mem row pl) (H : Held St W aOf iOf)
    (hd : pos.draws.toList.length = (LocK).t) :
    ∀ r ∈ rows, OnlyAt cs l ids (Inside R.s W pl) r := by
  intro r hr
  obtain ⟨m, hm', hrm⟩ := List.getElem_of_mem hr
  rw [hands_on_count L hm hd] at hm'
  obtain ⟨b, hb⟩ := rowNo_onto (s := R.s) A H m hm'
  obtain ⟨r', hr', -, -, -, ho⟩ :=
    hands_on_rows R Hd Sb sl Z A₀ cs l iJ iQ t w₀ L F D DK A.member A.rowIn hm h0 h1 Q x X b
  have e : r' = r := by
    have h2 : rows[m]? = some r' := (congrArg (fun i => rows[i]?) hb).symm.trans hr'
    rw [List.getElem?_eq_getElem (by rw [hands_on_count L hm hd]; exact hm'), hrm] at h2
    exact (Option.some.inj h2).symm
  subst e
  exact ho

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.only_at_rows
