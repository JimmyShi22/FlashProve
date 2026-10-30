-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PlaceLaw2.lean: THE CODE SWITCH's LAW AT A PLACE, WITH WHAT EVERY ACCEPTANCE
GIVES TAKEN OUT OF THE CONDITION IN FRONT: one theorem over `k02_place` (PlaceLaw.lean), in the same
form (`Piece.GoodIn` at the seated sub-protocol): THE FORM THAT THE FIRST TIE CAN PAY: under the
table of joints' promise there is no acceptance in hand, so that a front is there, that it reads the
old group's columns, and that the program's test on the public sizes accepts cannot be shown.

Main names:
  `k02_place2`: the condition in front speaks only of a front that the text makes of a state that
    the way in lets in; «no kept slot of the open word has a collision» (`KeptFree`) is asked only
    where that front's reading of the old group's columns is there and the program's test accepts.
    Promise behind and both relations: `k02_place`'s, to the letter. By `goodIn_of_yes`
    (GoodCases.lean), `seated_atYes` (SeatYes.lean), `there_of_atYes`, `listed_of_drawn`
    (Johnson/Top/H0/K2Hears/).
Limits. `k02_place`'s limits; one premise more: the typed structure counts at least one position. No
member. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.PlaceLaw
import Johnson.Top.H0.K2Caller.SeatYes
import Johnson.Top.H0.K2Hears.CheckSkel
import Johnson.Top.H0.K2Hears.OrcStrs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit)
open VerifiableInference.Desc.Sound (Frame Piece below MsgT msgsOf goodIn_weaken strsOf)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)
open scoped ENNReal

variable {F : Frame}

set_option maxHeartbeats 8000000 in
/-- **THE CODE SWITCH's LAW AT A PLACE, WITH WHAT EVERY ACCEPTANCE GIVES TAKEN OUT OF THE CONDITION
    IN
FRONT.** As `k02_place` (PlaceLaw.lean), but: the condition speaks only of a front that the text
makes; and «no kept slot of the open word has a collision» is asked only where the front's reading
of the old group's columns is there and the program's test on the public sizes accepts: both hold
at every acceptance (`seated_atYes`, `there_of_atYes`), so where one fails the piece never accepts
(`goodIn_of_yes`). -/
theorem k02_place2 {Cells Tok Cl Cl₀ Cl₁ Xi : Type} {r : SwRow} (h : r.ok = true) (hW : r.writtenOK
    = true) (hz : r.sizedB = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
    (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
    (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
    (Letters.plain r (r.ok_says h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
    (sigOf r.cs r.l).Ent) (G : FileDescription Xi) (seat : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)
    (p : K2.P2) (hp : P2At r p) (he : [d₁, d₂].map (·.entry) = (K2.rounds p).map (·.entry)) (hk : ∀
    d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind) (hpl : (K2.codeSwitchKind (Cl := Cl₁) p).planOk = true)
    (hseat : ∀ i, base ≤ (seat i).1 ∧ (seat i).1 - base < d₁.trees.length) (x₀ : (vecD (plainD r
    (r.ok_says h))).held.Smp) (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
    iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ :
    F.E.Str) (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (n0 grp rows : ℕ) (h0 : K2.frameAt f₀ =
    some W) (hcs : f₀.st.codes = r.cs) (hpub : frontPubB r.l.length f₀ = true) (hkA : r.keptAt W =
    true) (hbB : keptBitsB r W = true) (hsB : keptShapeB r = true) (C : ∀ W₀, Renumbered W W₀ →
    CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK rowK (plK W₀) W₀) (hkeys :
    KeysFit (F := F) (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat
    base d₁ F) p base idExt) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (B : Block Rec Cl)
    (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec) (hr : B.rounds =
    (K2.codeSwitchKind (Cl := Cl₀) p).rounds) (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave) (hD :
                            DoorKeeps (F := F) (Letters.plain r (r.ok_says h)) iJ iQ p leave (fbOf (Letters.plain r
                            (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seat) (fun _ => ((),
                            ())))) (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells Tok
                            MsgT) (arr : ℕ → ℕ → ℕ) (hE : ∀ a τ w, msgsOf r.cs r.l seat arr (ext' a τ w) = msgsOf r.cs r.l
                            seat arr w) (hposB : 0 < baseCount r.set .request r.g) : (seatedAt (k2Piece (W := Unit)
                            (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁ F) p base idExt) B
                            ext').GoodIn (fun a => ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx → (∃ olds : List
                            ℕ, olds.Nodup ∧ frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T
                            fx.others) ∧ K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true) ∧ ((K2.longFront
                            p t fx (K2.orcY F.all F.key (strsOf F a.2)) 0).isSome = true → switchTargetCheck fx.st fx.f.rows
                            fx.T = true → KeptFree iJ iQ (strsTop iJ iQ p (fun y => K2.orcS
                            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount
                            r.set .request r.g) x₀) d₀) (inXTop iJ iQ p (fun y => K2.orcS
                            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount
                            r.set .request r.g) x₀) d₀ y₀) (t, a.2))) (fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ
                            (fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G
                            seat) (fun _ => ((), ())) b)) (fun a w => ∀ t, enter a.1 = .ok t → ((Cb.Pv.SendLoc.stage (selZ
                            (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over (Cb.Pv.SendLoc.stage (selZ (Letters.plain r
                            (r.ok_says h)) iJ iQ).sw).A).relR (lawFa (Letters.plain r (r.ok_says h)) iJ iQ (strsTop iJ iQ p
                            (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says
                            h) iJ iQ (baseCount r.set .request r.g) x₀) d₀) (inXTop iJ iQ p (fun y => K2.orcS
                            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount
                            r.set .request r.g) x₀) d₀ y₀) (t, a.2)) (selBk (Letters.plain r (r.ok_says h)) iJ iQ (wtMade iJ
                            iQ seat arr w))) (fun b w => ∀ W₀ : {V // Renumbered W V}, ∀ a, OnTop iJ iQ p (fun y => K2.orcS
                            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount
                            r.set .request r.g) x₀) d₀ y₀ W₀.1 n0 grp rows (aOfK r (r.ok_says h)) (fun _ _ => 0) a → lawRb
                            (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a (b.1, fbOf (Letters.plain r (r.ok_says h)) iJ
                            iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB iJ iQ G seat) (fun _ => ((), ())) b) (wtMade iJ iQ
                            seat arr w)) := by
  refine goodIn_of_yes _ (fun a => ∀ t, enter a.1 = .ok t → ∃ fx, K2.frontAt p t = some fx ∧
    (K2.longFront p t fx (K2.orcY F.all F.key (strsOf F a.2)) 0).isSome = true ∧ switchTargetCheck
        fx.st fx.f.rows fx.T = true) _ _ _ _ ?_ ?_
  · intro a τ b _ hb t et
    obtain ⟨t₀, t', et₀, -, hlen, x, y', S3, Y, rws, Gg, c, A⟩ := seated_atYes (Letters.plain r
        (r.ok_says h)) iJ iQ d₁ d₂
      (wordsMade iJ iQ G seat base d₁ F) p base idExt (k2Wr_of hp he hk) B enter leave hr hs ext'
      (strsTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
          (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) x₀) d₀) (inXTop iJ iQ p (fun
          y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says
          h) iJ iQ (baseCount r.set .request r.g) x₀) d₀ y₀) a b τ hb
    obtain rfl : t = t₀ := Except.ok.inj (et.symm.trans et₀)
    have hne : (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss ≠ [] := by
      intro e
      rw [e] at hlen
      exact absurd hlen.symm (Nat.ne_of_gt hposB)
    exact ⟨x, A.front, K2.there_of_atYes A (K2.listed_of_drawn _ _ hne) _ 0, A.check⟩
  · refine goodIn_weaken _ _ _ _ _ _ _ _ _ ?_ (fun _ hb => hb) (fun _ _ hw => hw)
      (fun _ _ hw => hw) (k02_place h hW hz iJ iQ G seat base d₁ d₂ p hp he hk hpl hseat x₀ d₀ y₀ f₀
        W n0 grp rows h0 hcs hpub hkA hbB hsB C hkeys b₀ B enter leave hr hs hD ext' arr hE)
    rintro a ⟨ho, hy⟩ t et
    obtain ⟨fx, hf, hl, hc⟩ := hy t et
    exact ⟨fun fx' hf' => (ho t et fx' hf').1, (ho t et fx hf).2 hl hc⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_place2
