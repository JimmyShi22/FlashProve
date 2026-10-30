-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/GoodAt.lean: THE LAW OF THE CODE SWITCH IN THE FORM THAT THE RULE OF
COMPOSITION ASKS (`Piece.GoodIn`, Johnson/Desc/Sound/GoodIn.lean): at the piece of the kind's block,
and at the piece of a block that sits on it behind a door.

`Piece.GoodIn p on on' R R'`: from every statement with on, at the piece's errors, the prover has
lost towards: where the piece says yes, the statement behind has on', and every witness of R' behind
gives, by the piece's extractor, a witness of R in front. HERE: on: a letter · on' b := `lawPb` at
the reading `fbOf` of b: NO COLLISION at the new samples' seeds · R a w := the relation in front at
the typed reading of a, at the witness w read by inW · R' b w := for every statement a with on: what
stands behind (`lawRb`) at the record of b, the reading `fbOf` of b and the witness w read by wtOf.

Main names:
  `Alike.symm`.
  `k2_keeps_read`: the piece's own reduction leads to the promise behind and `K2Q` (SeatedAt.lean),
    at `fbOf` (BehindPaid.lean).
  `k2_goodIn`: the form, at `k2Piece`. hExt: the piece's extractor is the block's, read through inW
    and wtOf.
  `seated_goodIn`: general in the two blocks, their records and their types of claims: from a
    `Leads` of the piece q to a `GoodIn` of the piece at a block that sits on q's, under two ties of
    the conditions and relations through the door.
  `DoorKeeps leave fb`: what is asked of the way out: the reading fb of the record that it hands on
    is alike to that of the record that it was handed, and what stands behind at the one holds at
    the other.
  `k2_goodIn_seated`: the form at a seated block: on: the way in lets in a record with on; R: at
    every record that the way in lets in.
Limits. R' ASKS `lawRb` AT EVERY STATEMENT WITH on, not only at the one that led to b: `lawRb` reads
of a statement in front the front's group, that group's number of rows and the number of messages:
so whoever pays R' wants an on that pins these three. hExt, `DoorKeeps`, hpr, `LawAfter`, `Rides`,
`FrontNums` are premises; inW, wtOf are letters. No member. It is no soundness of the protocol. On
hiding nothing.

-/
import Johnson.Top.H0.K2Caller.KeepsAt
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

theorem Alike.symm {r : SwRow} {H : r.OK} {X : Letters r H}
    {iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent}
    {iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent}
    {b b' : TB X iJ iQ} (h : Alike X iJ iQ b b') : Alike X iJ iQ b' b :=
  ⟨fun i => (h.mat i).symm, fun i => (h.ans i).symm, h.words.symm, h.carried.symm⟩

variable {F : Frame} {W : Type}

set_option maxHeartbeats 2000000 in
/-- **The law of the piece's own reduction, THE PROMISE BEHIND KEPT**, at the reading `fbOf`. -/
theorem k2_keeps_read {r : SwRow} (h : r.ok = true)
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
    (hN : FrontNums (F := F) (r := r) p n0 on) :
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.Leads on
      (fun a a' => lawPb X iJ iQ (fbOf X iJ iQ n0 b₀ oldB strB carB a') ∧
        K2Q X iJ iQ p strs inX (fbOf X iJ iQ n0 b₀ oldB strB carB) a a')
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err := by
  have L := keeps_at h hW X iJ iQ d₁ d₂ ρ w p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on hpr hA
  refine fun a ha => Doomed.mono _ _ ?_ (L a ha)
  intro τ hτ a' ha'
  obtain ⟨b₂, hb⟩ := piece_is_lawOut X iJ iQ d₁ d₂ ρ p base ext strs inX w a a' τ ha'
  have hAl := behindAlike_paid X iJ iQ d₁ d₂ ρ p base ext strs inX w n0 b₀ oldB strB carB on hR hN
    a a' τ b₂ ha ha' hb
  obtain ⟨q1, q2⟩ := hτ (a'.1, b₂) hb
  exact ⟨pb_alike X iJ iQ hAl.symm q1,
    fun wt hw => q2 wt (rb_alike X iJ iQ p F.E.Str a a'.1 hAl wt hw)⟩

set_option maxHeartbeats 2000000 in
/-- **THE LAW IN THE FORM THAT THE RULE OF COMPOSITION ASKS** (`Piece.GoodIn`): from every statement
with on, at the piece's errors, the prover has lost towards: where the piece says yes, the promise
behind holds, and every witness of what stands behind gives, by the piece's extractor, a witness of
the relation in front. inW, wtOf: how a witness of the chain's one type W is read as the typed
witness in front and behind; hExt: the piece's extractor is the block's, read so. -/
theorem k2_goodIn {r : SwRow} (h : r.ok = true)
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
    (inW : Rec × F.E.Str → W → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).W)
    (wtOf : Rec × F.E.Str → W → (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.W)
    (hExt : ∀ a τ b w, on a →
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some b →
      inW a (ext a τ w) = selBk X iJ iQ (wtOf b w)) :
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).GoodIn on
      (fun b => lawPb X iJ iQ (fbOf X iJ iQ n0 b₀ oldB strB carB b))
      (fun a w => ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
        (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a) (inW a w))
      (fun b w => ∀ a, on a →
        lawRb X iJ iQ p F.E.Str a (b.1, fbOf X iJ iQ n0 b₀ oldB strB carB b) (wtOf b w)) := by
  intro a ha
  refine Doomed.mono _ _ ?_ (k2_keeps_read h hW X iJ iQ d₁ d₂ ρ w p base ext strs inX on hpr hA n0
      b₀
    oldB strB carB hR hN a ha)
  intro τ hτ b hb
  obtain ⟨h1, h2⟩ := hτ b hb
  refine ⟨h1, fun w hw => ?_⟩
  show ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
    (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a) (inW a (ext a τ w))
  rw [hExt a τ b w ha hb]
  exact (h2 _ (hw a ha)).1

/-! ### At a seated block -/

/-- **A law of the piece q, in the form that the rule of composition asks, at the piece at a block
that sits on q's**: general in the two blocks, their records and their types of claims. -/
theorem seated_goodIn {S T Cl Cl' W₀ W' : Type} (q : Piece (ckP .two) F T Cl' W₀) (K : Block T Cl')
    (hq : q.b = below K) (hback : q.back = []) (B : Block S Cl) (enter : S → Except String T)
    (leave : S → T → Except String S) (hr : B.rounds = K.rounds) (hs : SeatStep B K enter leave)
    (ext' : S × F.E.Str → Tr (uLT (ckP .two) q.ds) → W' → W')
    (on : T × F.E.Str → Prop) (Q : T × F.E.Str → T × F.E.Str → Prop)
    (L : q.ior.red.Leads on Q q.err)
    (onB o'B : S × F.E.Str → Prop) (RB R'B : S × F.E.Str → W' → Prop)
    (h1 : ∀ a, onB a → ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
    (h2 : ∀ a b t t' τ, onB a → (seatedAt q B ext').ior.red.out a τ = some b →
      enter a.1 = .ok t → leave a.1 t' = .ok b.1 → Q (t, a.2) (t', b.2) →
      o'B b ∧ ∀ w, R'B b w → RB a (ext' a τ w)) :
    (seatedAt q B ext').GoodIn onB o'B RB R'B := by
  intro a ha
  refine Doomed.mono _ _ ?_ (seated_leads q K hq hback B enter leave hr hs ext' on Q L a (h1 a ha))
  intro τ hτ b hb
  obtain ⟨t, t', e1, e2, e3⟩ := hτ b hb
  exact h2 a b t t' τ ha hb e1 e2 e3

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) (p : K2.P2)

/-- **What is asked of the way out**: it keeps what the law reads of the record behind. -/
def DoorKeeps (leave : Rec → Rec → Except String Rec) (fb : Rec × F.E.Str → TB X iJ iQ) : Prop :=
  ∀ s t' s' y, leave s t' = .ok s' →
    Alike X iJ iQ (fb (s', y)) (fb (t', y)) ∧
      ∀ (a : Rec × F.E.Str) bb wt, lawRb X iJ iQ p F.E.Str a (s', bb) wt →
        lawRb X iJ iQ p F.E.Str a (t', bb) wt

end

set_option maxHeartbeats 2000000 in
/-- **THE LAW OF THE CODE SWITCH AT A SEATED BLOCK, IN THE FORM THAT THE RULE OF COMPOSITION ASKS.**
    -/
theorem k2_goodIn_seated {W' Cl Cl₀ : Type} {r : SwRow} (h : r.ok = true)
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
    (inW : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).W)
    (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.W)
    (hExt : ∀ a τ b w, (∃ t, enter a.1 = .ok t ∧ on (t, a.2)) →
      (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').ior.red.out a τ = some b →
      inW a (ext' a τ w) = selBk X iJ iQ (wtOf b w)) :
    (seatedAt (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) B ext').GoodIn
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun b => lawPb X iJ iQ (fbOf X iJ iQ n0 b₀ oldB strB carB b))
      (fun a w => ∀ t, enter a.1 = .ok t → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
        (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX (t, a.2)) (inW a w))
      (fun b w => ∀ a, on a →
        lawRb X iJ iQ p F.E.Str a (b.1, fbOf X iJ iQ n0 b₀ oldB strB carB b) (wtOf b w)) := by
  have hs' : SeatStep B (K2.codeSwitchKind (Cl := Claim) p) enter leave := hs
  refine seated_goodIn (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) (K2.codeSwitchKind p) rfl rfl B enter leave
    hr hs' ext' on _ (k2_keeps_read h hW X iJ iQ d₁ d₂ ρ w p base ext strs inX on hpr hA n0 b₀ oldB
      strB carB hR hN) _ _ _ _ (fun _ ha => ha) ?_
  intro a b t t' τ ha hb e1 e2 hq
  obtain ⟨q1, q2⟩ := hq
  obtain ⟨d1, d2⟩ := hD a.1 t' b.1 b.2 e2
  obtain ⟨t₀, e0, hon⟩ := ha
  obtain rfl : t₀ = t := Except.ok.inj (e0.symm.trans e1)
  refine ⟨pb_alike X iJ iQ d1.symm q1, fun w hw t₂ e3 => ?_⟩
  obtain rfl : t₀ = t₂ := Except.ok.inj (e1.symm.trans e3)
  rw [hExt a τ b w ⟨t₀, e1, hon⟩ hb]
  exact (q2 _ (rb_alike X iJ iQ p F.E.Str (t₀, a.2) t' d1 _ (d2 (t₀, a.2) _ _ (hw (t₀, a.2)
      hon)))).1

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seated_goodIn
#print axioms VerifiableInference.Desc.First.K2Caller.k2_goodIn_seated
#print axioms VerifiableInference.Desc.First.K2Caller.k2_keeps_read
#print axioms VerifiableInference.Desc.First.K2Caller.k2_goodIn
