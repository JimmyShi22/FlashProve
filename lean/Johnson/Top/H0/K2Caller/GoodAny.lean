-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/GoodAny.lean: THE LAW OF THE CODE SWITCH AT A SEATED BLOCK, IN
`Piece.GoodIn`'s FORM, AT ANY EXTRACTOR. In GoodAt.lean the relation in front is said at the chain's
witness, read by a letter inW, and a premise hExt ties the piece's extractor to the block's. Here
the relation in front is said under a "there is": R a _ := for every state t that the way in lets
in: there is a typed witness u with the relation in front at (t, a.2) and u. It reads nothing of the
chain's witness: so the law holds at every extractor, the table of joints' own among them, and
neither inW nor hExt is asked.

Main names:
  `k2_goodIn_any`: at all letters.
  `k2_good_plain_any`: at the plain letters and the made words (as `k2_good_plain`, PlainGood.lean).
Limits. WHETHER THIS R IS ENOUGH FOR THE TABLE's TIE IN FRONT IS NOT SHOWN: that tie must get what
the switch's row closes, at the extractor's value, from «there is u» and what the row opens behind:
the carried claim's sentence has a "there is" of its own; for the kept members' pins it leans on how
the table's extractor lays what decodes in front, which is not held at
its text. Else those of GoodAt.lean and PlainGood.lean. No member. It is no soundness of the
protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PlainGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

variable {F : Frame} {W : Type}

set_option maxHeartbeats 2000000 in
/-- **THE LAW AT A SEATED BLOCK, IN THE FORM THAT THE RULE OF COMPOSITION ASKS, AT ANY EXTRACTOR**:
    the
relation in front is said under a "there is": it reads nothing of the chain's witness. -/
theorem k2_goodIn_any {W' Cl Cl₀ : Type} {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true) (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X) (on : Rec × F.E.Str → Prop)
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on)
    (n0 : ℕ) (b₀ : TB X iJ iQ) (oldB : Rec × F.E.Str → (selZ X iJ iQ).sw.S₀.Smp)
    (strB : Rec × F.E.Str → (selLoc X iJ iQ).S.ext.Str)
    (carB : Rec × F.E.Str → X.St₀ × X.E₀.Str)
    (hR : Rides (W := W) X iJ iQ d₁ d₂ ρ p base ext strs inX on oldB strB carB)
    (hN : FrontNums (F := F) (r := r) p n0 on)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (hD : DoorKeeps (F := F) X iJ iQ p leave (fbOf X iJ iQ n0 b₀ oldB strB carB))
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.W) :
    (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').GoodIn
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun b => lawPb X iJ iQ (fbOf X iJ iQ n0 b₀ oldB strB carB b))
      (fun a _ => ∀ t, enter a.1 = .ok t → ∃ u, ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
        (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX (t, a.2)) u)
      (fun b w => ∀ a, on a →
        lawRb X iJ iQ p F.E.Str a (b.1, fbOf X iJ iQ n0 b₀ oldB strB carB b) (wtOf b w)) := by
  have hs' : SeatStep B (K2.codeSwitchKind (Cl := Claim) p) enter leave := hs
  refine seated_goodIn (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) (K2.codeSwitchKind p) rfl rfl B enter leave
    hr hs' ext' on _ (k2_keeps_read h hW X iJ iQ d₁ d₂ ρ w p base ext strs inX on hpr hA n0 b₀ oldB
      strB carB hR hN) _ _ _ _ (fun _ ha => ha) ?_
  intro a b t t' τ ha _ e1 e2 hq
  obtain ⟨q1, q2⟩ := hq
  obtain ⟨d1, d2⟩ := hD a.1 t' b.1 b.2 e2
  obtain ⟨t₀, e0, hon⟩ := ha
  obtain rfl : t₀ = t := Except.ok.inj (e0.symm.trans e1)
  refine ⟨pb_alike X iJ iQ d1.symm q1, fun w hw t₂ e3 => ?_⟩
  obtain rfl : t₀ = t₂ := Except.ok.inj (e1.symm.trans e3)
  exact ⟨_, (q2 _ (rb_alike X iJ iQ p F.E.Str (t₀, a.2) t' d1 _
    (d2 (t₀, a.2) _ _ (hw (t₀, a.2) hon)))).1⟩

set_option maxHeartbeats 2000000 in
/-- **The same at the plain letters and the made words.** -/
theorem k2_good_plain_any {W' Cl Cl₀ Xi : Type} {r : SwRow} (h : r.ok = true)
    (hW : r.writtenOK = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM
      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM
      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)
    (w : K2Wr r d₁ d₂) (p : K2.P2)
    (hseat : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X)
    (on : Rec × F.E.Str → Prop)
    (hfree : ∀ a, on a → KeptFree iJ iQ strs inX a)
    (hA : LawAfter (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p
        strs inX
      (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p base
          idExt) on)
    (n0 : ℕ) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (hN : FrontNums (F := F) (r := r) p n0
        on)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (hD : DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ p leave
      (fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G
          seat)
        (fun _ => ((), ()))))
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W' → W')
    (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).tgt.W) :
    (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
        seat base d₁ F) p base
      idExt) B ext').GoodIn
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ (fbOf (Letters.plain r (r.ok_says h)) iJ
          iQ n0 b₀ (fun _ i => isEmptyElim i)
        (strMadeB iJ iQ G seat) (fun _ => ((), ())) b))
      (fun a _ => ∀ t, enter a.1 = .ok t →
        ∃ u, ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR
            (lawFa (Letters.plain r (r.ok_says h)) iJ iQ strs inX (t, a.2)) u)
      (fun b w => ∀ a, on a → lawRb (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a
        (b.1, fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB
            iJ iQ G seat)
          (fun _ => ((), ())) b) (wtOf b w)) :=
  k2_goodIn_any h hW (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F)
      w p base idExt strs inX
    on (fun a ha => hpr_plain iJ iQ strs inX a (hfree a ha)) hA n0 b₀ _ _ _
    (rides_made iJ iQ G seat base d₁ d₂ p idExt strs inX on hseat) hN B enter leave hr hs hD ext'
    wtOf

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2_good_plain_any
#print axioms VerifiableInference.Desc.First.K2Caller.k2_goodIn_any
