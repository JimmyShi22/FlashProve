-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/TieKeeps.lean: the code switch: THE TIE OF THE LAW THAT KEEPS THE
PROMISE BEHIND (sel_keeps_law, Johnson/Top/H/SwitchKeeps.lean), AT THE KIND's OWN TEXT.

sel_keeps_law differs from sel_law (SwitchLeads.lean) in its tie: the typed promise behind gives Pb;
and what stands behind gives the typed relation behind ITSELF (outJP), not «the relation, or the
promise fails» (outJ). TieT.lean's road gives just that: relR_of's proof was the left arm.
  relRP_of      the typed relation behind from the decodings, After and the carried joint
  PbT           the promise behind, said of the typed statement that outT carries beside the record
  tie_hT_keeps  sel_keeps_law's tie, to its letter, at outT | faT | RbT | PbT, under AfterAtYes
  sel_keeps_at  sel_keeps_law called there; beside AfterAtYes it takes sel_keeps_law's own premises:
                allMeet cs l = true · Hd.Laws · R.G.Fits · hpr (where «on» holds, the typed promise
                in front holds) · hFit (the error fits)
LIMITS. Those of TieT.lean: AfterAtYes is a premise (TiePaid.lean brings it to three records); the
five premises named at sel_keeps_at; «on» is a letter; no member. PbT speaks of the typed statement
beside the record, not of the record's own pins. No soundness is claimed.
-/
import Johnson.Top.H.SwitchKeeps
import Johnson.Top.H0.K2Hands.TieT

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
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "zS" => switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw
set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

/-- **The typed relation behind.** -/
theorem relRP_of
    (a : (Cb.Pv.SendLoc.loc (zS).sw).tgt.X × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str)
    (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W)
    (hd : ∀ i, (LocK).S.decs a.1.2 a.2.1.2 i = some (w.1 i).1)
    (hA : (LocK).After a.1.1.1 ((LocK).S.msgs w.1))
    (h1 : (LocK).A₁.relR (a.1.1.2, a.2.1.1) ((LocK).S.msgs w.1, w.2)) :
    (Cb.Pv.SendLocRide.outJP (zS)).relR a w := ⟨hd, hA, h1⟩

variable {r₁ r₂ : Round} (ρ : Rd (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw) r₁ r₂) (p : K2.P2)
  (v₁ : r₁.Msg → r₁.Chal → Fmt.RoundView) (v₂ : r₂.Msg → r₂.Chal → Fmt.RoundView)
  (pass₁ : r₁.Chal → Bool) (pass₂ : r₂.Chal → Bool)
  {Yt : Type} (strs : Rec × Yt → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀
      Cw).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).X)
  (shown : Rec × Yt → Tr [r₁, r₂] → Gs)

/-- The promise behind, of the typed statement that outT carries. -/
def PbT (_ : Rec × Yt)
    (b : Rec × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str)) : Prop :=
  (Cb.Pv.SendLocRide.outJP (zS)).on b.2

/-- **sel_keeps_law's tie, to its letter.** -/
theorem tie_hT_keeps (on : Rec × Yt → Prop)
    (hA : AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on) :
    ∀ a τ b, on a →
      outT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown a τ = some b →
      ∃ sd Qs, ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd ∧
        ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
        ((Cb.Pv.SendLocRide.outJP (zS)).on
            (ρ.after (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a) sd Qs (ρ.answ τ.2.2.1)
              τ.1) →
          PbT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw a b) ∧
        ∀ w, RbT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p a b w →
          (Cb.Pv.SendLocRide.outJP (zS)).relR
            (ρ.after (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a) sd Qs (ρ.answ τ.2.2.1)
              τ.1) w := by
  intro a τ b ha hb
  obtain ⟨-, -, ht, sd, Qs, hsd, hQ, hb2⟩ :=
    outT_inv R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown hb
  refine ⟨sd, Qs, hsd, hQ, fun h => ?_, fun w hw => ?_⟩
  · unfold PbT
    rw [hb2]
    exact h
  obtain ⟨hdec, hrows, h1⟩ := hw
  rw [hb2] at hdec h1
  obtain ⟨fx, y, S3, Y, rows, G, c, Y1⟩ := K2.yes_whole p a.1 _ _ _ b.1 ht
  obtain ⟨G', hG', hr⟩ := Option.map_eq_some_iff.1 Y1.kept
  obtain ⟨G0, hG0, h0⟩ := Option.map_eq_some_iff.1 Y1.before
  refine relRP_of R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw _ w hdec ?_ h1
  refine hA a τ b.1 Qs fx y S3 Y rows G c ha ht hQ Y1 _ fun r hr' => ?_
  refine hrows fx Y1.front G0 G' hG0 hG' r ?_
  have e : (G.rows ++ rows.toArray).toList.drop G.rows.size = rows := by simp
  rw [hr, h0, e]
  exact hr'

/-- **sel_keeps_law, called at the kind's own text.** -/
theorem sel_keeps_at (h : allMeet cs l = true) (hL : Hd.Laws) (hF : R.G.Fits)
    (on : Rec × Yt → Prop)
    (hpr : ∀ a, on a → (Cb.Pv.SendLocRide.inJP (zS)).on
      (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a))
    (ε' : Err [r₁, r₂]) (hFit : ρ.carS.Fits (Cb.Pv.SendLocRide.eps (zS)) ε')
    (hA : AfterAtYes R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ strs inX shown on) :
    (⟨[r₁, r₂], outT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown⟩ :
        Reduction _ _).Leads on
      (fun a b => KeepsQ Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw
        (PbT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw a) (RbT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw p a)
        (faT R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw strs inX a) b) ε' :=
  sel_keeps_law Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ h hL hF _ _ on hpr ε' hFit _ _
    (tie_hT_keeps R Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw ρ p v₁ v₂ pass₁ pass₂ strs inX shown on hA)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.tie_hT_keeps
#print axioms VerifiableInference.Desc.First.K2Hands.sel_keeps_at
