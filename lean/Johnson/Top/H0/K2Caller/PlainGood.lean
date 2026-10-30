-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PlainGood.lean: THE LAW OF THE CODE SWITCH AT A SEATED BLOCK, IN THE FORM
THAT THE RULE OF COMPOSITION ASKS, WITH THE LETTERS THAT CAN BE MADE, MADE: the plain letters
(Member.lean), the new words and all words behind by make (WordsMade.lean). `Rides` is paid; of hpr
one clause is left.

Main names:
  `KeptFree`: the promise in front at the plain letters: no kept slot of the open word has a
    collision at its stored sample's seed. `hpr_plain`: it is all that hpr asks there.
  `idExt`: the extractor of the piece beneath: it is read by nothing.
  `k2_good_plain`: `k2_goodIn_seated` (GoodAt.lean) there. WHAT IS LEFT, each by name: r.ok ·
    r.writtenOK · the two written rounds (`K2Wr`) · one fact on the plan: each new member's tree is
    one that the first written round sends · `KeptFree` where on holds · `LawAfter` at the piece's
    own shown columns (brought further: AfterMade.lean) · `FrontNums` · B declares the kind's rounds
    and sits on the kind's block behind the door · `DoorKeeps` · hExt.
Limits. Those of GoodAt.lean. strs, inX, on, inW, wtOf, which tree and tenant holds a member, G and
base are letters. No member. It is no soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WordsMade

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

variable {F : Frame}

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X)

/-- **The promise in front at the plain letters**: no kept slot of the open word has a collision at
its stored sample's seed. -/
def KeptFree (a : Rec × F.E.Str) : Prop :=
  ∀ k : (selHd (Letters.plain r H) iJ iQ).K,
    ¬ ((selHd (Letters.plain r H) iJ iQ).o k).ClashW
      ((selHd (Letters.plain r H) iJ iQ).sW k (lawFa (Letters.plain r H) iJ iQ strs inX a).2.1.1)
      ((lawFa (Letters.plain r H) iJ iQ strs inX a).1.1.1.2 k).1

/-- It is all that hpr asks there. -/
theorem hpr_plain (a : Rec × F.E.Str) (hk : KeptFree iJ iQ strs inX a) :
    ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).A).on
        (lawFa (Letters.plain r H) iJ iQ strs inX a) :=
  ⟨fun i => ((plain_empty iJ iQ).false i).elim, hk, trivial⟩

end

/-- The extractor of the piece beneath: the identity on Unit. It is read by nothing. -/
def idExt {d₁ d₂ : RDT} : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Unit → Unit :=
  fun _ _ w => w

set_option maxHeartbeats 2000000 in
/-- **THE LAW OF THE CODE SWITCH AT A SEATED BLOCK, IN THE FORM THAT THE RULE OF COMPOSITION ASKS,
    AT
THE PLAIN LETTERS AND THE MADE WORDS.** -/
theorem k2_good_plain {W' Cl Cl₀ Xi : Type} {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
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
    (inW : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).W)
    (wtOf : Rec × F.E.Str → W' → (Cb.Pv.SendLoc.loc (selZ (Letters.plain r (r.ok_says h)) iJ
        iQ).sw).tgt.W)
    (hExt : ∀ a τ b w, (∃ t, enter a.1 = .ok t ∧ on (t, a.2)) →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seat base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      inW a (ext' a τ w) = selBk (Letters.plain r (r.ok_says h)) iJ iQ (wtOf b w)) :
    (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
        seat base d₁ F) p base
      idExt) B ext').GoodIn
      (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2))
      (fun b => lawPb (Letters.plain r (r.ok_says h)) iJ iQ (fbOf (Letters.plain r (r.ok_says h)) iJ
          iQ n0 b₀ (fun _ i => isEmptyElim i)
        (strMadeB iJ iQ G seat) (fun _ => ((), ())) b))
      (fun a w => ∀ t, enter a.1 = .ok t →
        ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).A).relR
            (lawFa (Letters.plain r (r.ok_says h)) iJ iQ strs inX (t, a.2)) (inW a w))
      (fun b w => ∀ a, on a → lawRb (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a
        (b.1, fbOf (Letters.plain r (r.ok_says h)) iJ iQ n0 b₀ (fun _ i => isEmptyElim i) (strMadeB
            iJ iQ G seat)
          (fun _ => ((), ())) b) (wtOf b w)) :=
  k2_goodIn_seated h hW (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seat base d₁
      F) w p base idExt strs inX
    on (fun a ha => hpr_plain iJ iQ strs inX a (hfree a ha)) hA n0 b₀ _ _ _
    (rides_made iJ iQ G seat base d₁ d₂ p idExt strs inX on hseat) hN B enter leave hr hs hD ext'
        inW
    wtOf hExt

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.hpr_plain
#print axioms VerifiableInference.Desc.First.K2Caller.k2_good_plain
