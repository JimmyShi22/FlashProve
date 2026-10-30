-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PlaceLaw.lean: THE CODE SWITCH's LAW AT A PLACE, WITH EVERY LETTER THAT CAN
BE MADE, MADE: one theorem, in the form that the rule of composition asks of a piece
(`Piece.GoodIn`), at the seated sub-protocol, over a witness of the table of joints. It joins
TopFam.lean (`k02_good_fam`), OnTopFacts.lean (`onTop_of_tests`), GoodCases.lean
(`seated_goodIn_imp`) and BehindSig.lean's `wtMade`.

Main names:
  `k02_place`. THE CONDITION IN FRONT, at every state t that the way in lets in: at the front that
    the text makes of t there are numbers of the kept old messages, none twice, at which the test
    `frontB2` accepts · the sending's notices are the typed list · the invariant on stored sample
    rows (`SampleGoodS`) · the test `storedB` · no kept slot of the open word has a collision at its
    held OOD sample's seed (`KeptFree`). THE PROMISE BEHIND: no new member has a collision at its
    OOD sample's seed. THE RELATION IN FRONT: the typed relation in front of the switch at the typed
    witness that the sub-protocol's extractor hands back at `wtMade` of the chain's witness. THE
    RELATION BEHIND: at every statement that meets `OnTop` at a frame of the family: the new
    members' words decode to the witness's messages, and each row that the switch's group has gained
    holds of them.
  WHAT IT STILL ASKS, each by name: three tests with code on the typed structure r · `P2At` · two
    written rounds with the declared entries and kinds · the kind's test on the list of rounds ·
    each new member's tree is one that the first written round sends · six closed facts at a written
    front and its frame · `CallerAt` at every frame of the family (`caller_fam` pays it at the maps
    of names made off the written frame) · `KeysFit` (`keysFit_in_scope`) · the seated sub-protocol
    declares the kind's rounds and sits on it behind a door · `DoorKeeps` · hE: the piece's
    extractor leaves the new members' messages (`msgsOf_ext`).
Limits. A SENTENCE WITH PREMISES. Who makes the condition in front true along the chain is not said;
`SampleGoodS` and `KeptFree` have no code. Letters that stay: iJ, iQ (paid at `iJW`, `iQW`) · which
tree and tenant holds a new member · base · the numbers n0, grp, rows · four defaults that are read
nowhere under the condition. No member. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.OnTopFacts
import Johnson.Top.H0.K2Caller.GoodCases
import Johnson.Top.H0.K2Caller.MadeOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit)
open VerifiableInference.Desc.Sound (Frame Piece below MsgT msgsOf goodIn_weaken)
open VerifiableInference.Desc.First.K2Hands
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)
open scoped ENNReal

variable {F : Frame}

set_option maxHeartbeats 8000000 in
/-- **THE CODE SWITCH's LAW AT A PLACE, WITH EVERY LETTER THAT CAN BE MADE, MADE.** At the seated
sub-protocol; over a witness of the table of joints. THE CONDITION IN FRONT, at every state t that
    the
way in lets in: at the front that the text makes of t there are numbers of the kept old messages,
none twice, at which the test `frontB2` accepts; the notices are the typed list; the invariant on
stored sample rows; the test `storedB`; and no kept slot of the open word has a collision. THE
RELATION IN FRONT: at the typed witness that the sub-protocol's extractor hands back at `wtMade` of
the chain's witness. hE: the piece's extractor leaves the new members' messages. -/
theorem k02_place {Cells Tok Cl Cl₀ Cl₁ Xi : Type} {r : SwRow} (h : r.ok = true) (hW : r.writtenOK =
    true) (hz : r.sizedB = true) (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀
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
                            seat arr w) : (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂
                            (wordsMade iJ iQ G seat base d₁ F) p base idExt) B ext').GoodIn (fun a => ∀ t, enter a.1 = .ok t
                            → (∀ fx, K2.frontAt p t = some fx → ∃ olds : List ℕ, olds.Nodup ∧ frontB2 f₀ W grp rows n0 olds
                            fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧ storedB r
                            (placeFrame W n0 olds) fx = true) ∧ KeptFree iJ iQ (strsTop iJ iQ p (fun y => K2.orcS
                            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount
                            r.set .request r.g) x₀) d₀) (inXTop iJ iQ p (fun y => K2.orcS
                            (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount
                            r.set .request r.g) x₀) d₀ y₀) (t, a.2)) (fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ
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
  have hs' : SeatStep B (K2.codeSwitchKind (Cl := Claim) p) enter leave := hs
  refine seated_goodIn_imp (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂
    (wordsMade iJ iQ G seat base d₁ F) p base idExt) (K2.codeSwitchKind (Cl := Claim) p) rfl rfl B enter leave
        hr
    hs' ext'
    (fun x => (∀ fx, K2.frontAt p x.1 = some fx → ∃ olds : List ℕ, olds.Nodup ∧
      frontB2 f₀ W grp rows n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others) ∧
      K2.SampleGoodS fx.st ∧ storedB r (placeFrame W n0 olds) fx = true) ∧
      KeptFree iJ iQ (strsTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base
          [d₁, d₂]) y) (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) x₀) d₀)
        (inXTop iJ iQ p (fun y => K2.orcS (VerifiableInference.Desc.Sound.stg F base [d₁, d₂]) y)
            (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) x₀) d₀ y₀) x) _ _ _ ?_
  refine goodIn_weaken _ _ _ _ _ _ _ _ _ ?_ (fun _ hb => hb) (fun _ _ hw => hw) (fun _ _ hw => hw)
    (k02_good_fam h hW hz iJ iQ G seat base d₁ d₂ p hp he hk hpl hseat
      (smpTop r (r.ok_says h) iJ iQ (baseCount r.set .request r.g) x₀) d₀ y₀ (Renumbered W) n0 grp
          rows
      (aOfK r (r.ok_says h)) (fun _ _ => 0) C hkeys b₀ B enter leave hr hs hD ext'
      (fun _ w => selBk (Letters.plain r (r.ok_says h)) iJ iQ (wtMade iJ iQ seat arr w))
      (fun _ w => wtMade iJ iQ seat arr w)
      (fun a τ b w _ => by
        show selBk (Letters.plain r (r.ok_says h)) iJ iQ (wtMade iJ iQ seat arr (ext' a τ w)) = _
        unfold wtMade
        rw [hE a τ w]))
  rintro a ⟨t, et, hf, hfree⟩
  obtain ⟨W₀, hW₀, hO⟩ := onTop_of_tests iJ iQ p _ x₀ d₀ y₀ f₀ W n0 grp rows h0 hcs hpub hkA hbB hsB
    (t, a.2) hf hfree
  exact ⟨⟨W₀, hW₀⟩, t, et, hO⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k02_place
