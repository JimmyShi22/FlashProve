-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TopFam.lean: THE CODE SWITCH's LAW AT A PLACE, WITH THE PLACE's FRAME NOT
PINNED. The text's frame numbers the old messages by the statement's own numbers. The law is said
statement by statement; the typed reading in front takes the frame off the verifier's state itself;
neither the promise behind nor the relation in front names the frame; the relation behind asks what
stands behind at every statement with the condition, at whichever frame of the family. So the
condition in front may ask `OnTop` at SOME frame of a family.

Main names:
  `goodIn_family`: general: a law (`Piece.GoodIn`) at each condition of a family, with one promise
    behind and one relation in front, is a law at "one of them holds"; behind, the relation asks
    all.
  `k02_good_fam`: `k02_good_wit` (TopWit.lean) so: Wok: which frames; `CallerAt` is asked at every
    frame with Wok (the written frame renumbered in every way has it:
    Johnson/Top/H0/K2Hands/CallerRenumber.lean); hExt is asked at every yes.
Limits. Those of TopWit.lean. No member. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.ExtMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit)
open VerifiableInference.Desc.Sound (Frame Piece below MsgT msgsOf Sending Mem seatOf extAt)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open _root_.Run.PQ (CK)
open _root_.Tw.K2 (switchNotices)
open scoped ENNReal

variable {F : Frame}

/-- **A law at each condition of a family is a law at "one of them holds"**: the promise behind and
the relation in front are the same at all; behind, the relation asks all. -/
theorem goodIn_family {C : CK} {S Cl W ι : Type} (q : Piece C F S Cl W)
    (on : ι → S × F.E.Str → Prop) (on' : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop)
    (R' : ι → S × F.E.Str → W → Prop) (h : ∀ i, q.GoodIn (on i) on' R (R' i)) :
    q.GoodIn (fun a => ∃ i, on i a) on' R (fun b w => ∀ i, R' i b w) := by
  rintro a ⟨i, hi⟩
  refine Doomed.mono _ _ ?_ (h i a hi)
  intro τ hτ b hb
  exact ⟨(hτ b hb).1, fun w hw => (hτ b hb).2 w (hw i)⟩

set_option maxHeartbeats 4000000 in
/-- **THE CODE SWITCH's LAW AT A PLACE, WITH THE PLACE's FRAME NOT PINNED**: the condition in front
    asks
`OnTop` at SOME frame W₀ with Wok; `CallerAt` is asked at every such frame. So the numbers that a
frame gives the old messages need not be one closed value at a place. -/
theorem k02_good_fam {W' Cl Cl₀ Cl₁ Xi : Type} {r : SwRow} (h : r.ok = true) (hW : r.writtenOK =
    true) (hz : r.sizedB = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
    (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
    (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
    (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
    (sigOf r.cs r.l).Ent) (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)
    (p : K2.P2) (hp : P2At r p) (he : [d₁, d₂].map (·.entry) = (K2.rounds p).map (·.entry)) (hk : ∀
    d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind) (hpl : (K2.codeSwitchKind (Cl := Cl₁) p).planOk = true)
    (hseat : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length) (smp : _root_.Tw.K2.Front
    → SwitchFrame → (vecD (plainD r (r.ok_says h))).held.Smp) (d₀ : (Cb.Pv.SendLoc.stage (selZ
    (Letters.plain r (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
    (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str) (Wok : SwitchFrame → Prop) (n0 grp rows : ℕ)
    (aOf : (selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.K → ℕ) (iOf : ∀ k, ((selLoc
    (Letters.plain r (r.ok_says h)) iJ iQ).hd.o k).Z.S → ℕ) (C : ∀ W₀, Wok W₀ → CallerAt (selR
    (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK rowK (plK W₀) W₀) (hkeys : KeysFit (F := F)
    (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p
    base idExt) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (B : Block Rec Cl) (enter : Rec →
    Except String Rec) (leave : Rec → Rec → Except String Rec) (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀)
    p).rounds) (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave) (hD : DoorKeeps (F := F)
                (Letters.plain r (r.ok_says h)) iJ iQ p leave (fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀
                (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seat) (fun _ => ((), ())))) (ext' : Rec × F.E.Str →
                Tr (uLT (ckP .two) [d₁, d₂]) → W' → W') (inW : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.stage (selZ
                (Letters.plain r (r.ok_says h)) iJ iQ).sw).W) (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc
                (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).tgt.W) (hExt : ∀ a τ b w, (seatedAt (k2Piece (W
                := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p base
                idExt) B ext').ior.red.out a τ = some b → inW a (ext' a τ w) = selBk (Letters.plain r (r.ok_says
                h)) iJ iQ (wtOf b w)) : (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁
                d₂ (wordsMade iJ iQ G seat base d₁ F) p base idExt) B ext').GoodIn (fun a => ∃ W₀ : {W // Wok
                                                                                                      W}, ∃ t,
                enter a.1 = .ok t ∧ OnTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base
                [d₁, d₂]) y) smp d₀ y₀ W₀.1 n0 grp rows aOf iOf (t, a.2)) (fun b => lawPb (Letters.plain r
                (r.ok_says h)) iJ iQ (fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim
                i) (strMadeB iJ iQ G seat) (fun _ => ((), ())) b)) (fun a w => ∀ t, enter a.1 = .ok t →
                ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over
                (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR (lawFa
                (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ p (fun y => K2.orcS
                (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp d₀) (inXTop iJ iQ p (fun y =>
                K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp d₀ y₀) (t, a.2)) (inW a w))
    (fun b w => ∀ W₀ : {W // Wok W}, ∀ a, OnTop iJ iQ p (fun y => K2.orcS
    (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) smp d₀ y₀ W₀.1 n0 grp rows aOf iOf a →
    lawRb (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a (b.1, fbOf (Letters.plain r (r.ok_says
    h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seat) (fun _ => ((), ())) b) (wtOf
    b w)) :=
  goodIn_family _ _ _ _ _ fun W₀ =>
    k02_good_wit h hW hz iJ iQ G seat base d₁ d₂ p hp he hk hpl hseat smp d₀ y₀ W₀.1 n0 grp rows aOf
      iOf (C W₀.1 W₀.2) hkeys b₀ B enter leave hr hs hD ext' inW wtOf
      (fun a τ b w _ hb => hExt a τ b w hb)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.goodIn_family
#print axioms VerifiableInference.Desc.First.K2Caller.k02_good_fam
