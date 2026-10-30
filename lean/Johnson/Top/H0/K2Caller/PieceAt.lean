-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PieceAt.lean: the code switch as a PIECE of the first chain's description
(`Piece`, Johnson/Desc/Sound/ChainRule.lean): the kind's own block at its stretch of two written
rounds. The piece's yes is a yes of the text of LawAt.lean; so the law of LawAt.lean is a law of the
piece's own reduction, at written counts that are shares of at most 2⁻¹ ^ target, under one named
premise more.

LawAt.lean has the law for `lawOut`, a text over the two written rounds that puts out the record
behind TOGETHER WITH the typed statement behind. A piece's reduction is the chain's own fold at this
one block, behind the stage's tests; it puts out the record behind and the file's oracles behind.
Definitions, and theorems with their proofs.

Main names:
  `piece_yes_shown`: general in the block: what a yes of a piece's reduction holds, WITH THE COLUMNS
    NAMED: the stage's tests of work pass, and the block's decision says yes at the rounds without
    their digests and at `Block.shown` of what the stage's view opens. It sharpens `piece_yes`
    (Johnson/Top/H0/MergeLaw/AtPiece.lean), which has "there are columns".
  `k2Piece`: the block `K2.codeSwitchKind p`, with the test on words in front, at the stretch [d₁, d₂]; its
    errors: the written counts of Reading.lean.
  `shownP`: the columns that the piece's step shows, off a statement and a written transcript.
  `piece_is_lawOut`: **the piece's yes is `lawOut`'s yes**, with the same record behind.
  `BehindIs`: THE NAMED PREMISE: a reading fb of the piece's statements behind gives, at every yes,
    the typed statement behind that `lawOut` puts out.
  `k2_leads`: `Reduction.Leads` of the piece's reduction, towards `sel_law`'s conclusion for every
    witness of what stands behind at (the record behind, fb of the statement behind); and the
    piece's errors are shares of at most 2⁻¹ ^ target.

WHAT `BehindIs` ASKS. The typed statement behind (`Rd.after`, Johnson/Top/H/LocPlace.lean) holds:
the positions drawn, with the open word's long symbols at them; for each new member the sample made
of the joint seed, with its answer; the new members' words and the rider's word. So fb must read
these back: the seed's samples, the positions and the answers off the record behind or the oracles
behind, and the words off the file's oracles behind, as `WordsOf` reads them off the first written
message. That such an fb exists is not shown. BY READING, NOT SHOWN:
it is a matter of the fields pin, carry and row of the table of the first chain's joints, and the
like is wanted in front of the next switch.

What stays a premise beside it: `LawAfter`; `on` with its two consequences. What stays a letter: as
in LawAt.lean, with Yt := the file's oracles; fb; the piece's base and extractor.
Limits: those of LawAt.lean. The extractor ext is a letter that no statement here reads. It is no
soundness of the protocol. On hiding nothing.
`shownP` shows nothing where the step's own tests on the rounds and the columns (`Block.Fits`) fail:
there the step refuses before it decides, so the piece's reduction and `lawOut` at `shownP` still
say yes together (`piece_is_lawOut`); it is the law's letter «shown», no field of the piece.
`k2_leads` and `BehindIs` are overtaken by BehindAt.lean.

-/
import Johnson.Top.H0.K2Caller.LawAt
import Johnson.Top.H0.MergeLaw.AtPiece

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open OnBytes.Tie.Pv.Row (rvOne okT okT_cons)
open VerifiableInference.Desc (Block Claim noDigest chainAt viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.MergeLaw (chainAt_one)
open _root_.Run (ckP)
open scoped ENNReal

variable {F : Frame} {W : Type}

/-- **What a yes of a piece's reduction holds, with the columns named.** -/
theorem piece_yes_shown {S Cl : Type} (b : Block S Cl) (p : Piece (ckP .two) F S Cl W)
    (hb : p.b = below b) (hback : p.back = []) (a a' : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) p.ds)) (h : p.ior.red.out a τ = some a') :
    passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true ∧
      (below b).Fits F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened ∧
      b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest)
        ((below b).shown F.ft (rvT (ckP .two) p.ds τ)
          (sView (ckP .two) p.stage a.2 τ).opened) = .ok a'.1 := by
  have h1 : (if sTests (ckP .two) p.stage a.2 τ = true
      then p.run a.1 (sView (ckP .two) p.stage a.2 τ) else none).map
        (fun xo => (xo, p.ior.imp a.2 τ)) = some a' := h
  obtain ⟨s', h2, h3⟩ := Option.map_eq_some_iff.1 h1
  split at h2
  · rename_i ht
    have hp : passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true := by
      unfold sTests at ht
      simp only [Bool.and_eq_true] at ht
      exact ht.1.1
    have h4 : (chainAt p.b.name F.ft [p.b] a.1
        ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
          (sView (ckP .two) p.stage a.2 τ).opened⟩).toOption = some s' := h2
    have h5 : chainAt p.b.name F.ft [p.b] a.1
        ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
          (sView (ckP .two) p.stage a.2 τ).opened⟩ = .ok s' := by
      cases hc : chainAt p.b.name F.ft [p.b] a.1
          ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
            (sView (ckP .two) p.stage a.2 τ).opened⟩ with
      | error e => rw [hc] at h4; exact absurd h4 (by simp [Except.toOption])
      | ok x =>
        rw [hc] at h4
        have : x = s' := by simpa [Except.toOption] using h4
        rw [this]
    obtain ⟨k, h6⟩ := chainAt_one _ _ _ _ _ _ h5
    rw [hb, hback, List.append_nil] at h6
    obtain ⟨hfit, hdec, _⟩ := (step_iff _ _ _ _ _ _ _).1 h6
    have hr : (sView (ckP .two) p.stage a.2 τ).rounds = rvT (ckP .two) p.ds τ := rfl
    rw [hr] at hdec hfit
    have hdec' : (if viewWordsBelowPrime ⟨(rvT (ckP .two) p.ds τ).map noDigest, _⟩ = true
        then b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest)
          ((below b).shown F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened)
        else .error _) = .ok s' := hdec
    split at hdec'
    · subst h3
      exact ⟨hp, hfit, hdec'⟩
    · exact absurd hdec' (by simp)
  · exact absurd h2 (by simp)

section
variable {r : SwRow} {H : r.OK} (X : Letters r H)
  (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (p : K2.P2) (base : ℕ)
  (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)

/-- **The code switch as a piece.** -/
noncomputable def k2Piece : Piece (ckP .two) F Rec Claim W :=
  ⟨below (K2.codeSwitchKind p), base, [d₁, d₂], [], ext,
    (switchMaps (X.withSel iJ iQ) d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps (selZ X iJ iQ))⟩

open Classical in
/-- The columns that the piece's step shows, where the step's own tests on the rounds and the
    columns
pass; none elsewhere: there the step refuses before it decides. -/
noncomputable def shownP (a : Rec × F.E.Str) (τ : Tr [wT d₁, wT d₂]) : Gs :=
  if (below (K2.codeSwitchKind (Cl := Claim) p)).Fits F.ft (rvT (ckP .two) [d₁, d₂] τ)
      (sView (ckP .two) (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage a.2 τ).opened then
    (below (K2.codeSwitchKind (Cl := Claim) p)).shown F.ft (rvT (ckP .two) [d₁, d₂] τ)
      (sView (ckP .two) (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage a.2 τ).opened
  else []

variable (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
  (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X)

set_option maxHeartbeats 1000000 in
/-- **The piece's yes is `lawOut`'s yes**, with the same record behind. -/
theorem piece_is_lawOut (w : K2Wr r d₁ d₂) (a a' : Rec × F.E.Str)
    (τ : Tr (uLT (ckP .two) [d₁, d₂]))
    (h : (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some a') :
    ∃ b₂, lawOut X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) a τ =
      some (a'.1, b₂) := by
  obtain ⟨hp, hf, hd⟩ := piece_yes_shown (K2.codeSwitchKind p) (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext) rfl
    rfl a a' τ h
  have hsh : shownP X iJ iQ d₁ d₂ ρ p base ext a τ =
      (below (K2.codeSwitchKind (Cl := Claim) p)).shown F.ft (rvT (ckP .two) [d₁, d₂] τ)
        (sView (ckP .two) (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).stage a.2 τ).opened :=
    if_pos hf
  obtain ⟨m₁, c₁, m₂, c₂, u⟩ := τ
  have hp' : okT [d₁, d₂] (m₁, c₁, m₂, c₂, u) := hp
  obtain ⟨q1, hp2⟩ := (okT_cons d₁ [d₂] m₁ c₁ (m₂, c₂, u)).1 hp'
  obtain ⟨q2, _⟩ := (okT_cons d₂ [] m₂ c₂ u).1 hp2
  have ht : textT p (vN d₁) (vN d₂) (shownP X iJ iQ d₁ d₂ ρ p base ext) a (m₁, c₁, m₂, c₂, u) =
      .ok a'.1 :=
    (congrArg (fun g => K2.decideWith _root_.Tw.K2.sendByL8 p a.1 [vN d₁ m₁ c₁, vN d₂ m₂ c₂] g =
      Except.ok a'.1) hsh).mpr hd
  have hs := (lawOut_yes X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) w a
    (m₁, c₁, m₂, c₂, u)).2 ⟨q1, q2, _, ht⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨_, _, h3, _⟩ := outT_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb
  have e : b.1 = a'.1 := Except.ok.inj (h3.symm.trans ht)
  exact ⟨b.2, hb.trans (congrArg some (Prod.ext e rfl))⟩

/-- **The named premise**: fb reads the typed statement behind off the piece's statement behind. -/
def BehindIs (on : Rec × F.E.Str → Prop)
    (fb : Rec × F.E.Str → (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.Ex.prod (portCode r.cs r.rider).nat).Str) : Prop :=
  ∀ (a a' : Rec × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])) b₂, on a →
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.out a τ = some a' →
    lawOut X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) a τ = some (a'.1, b₂) →
    fb a' = b₂

end

set_option maxHeartbeats 2000000 in
/-- **The law of the code switch, of the piece's own reduction, with its level.** -/
theorem k2_leads {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W)
    (strs : Rec × F.E.Str → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).Ex.Str)
    (inX : Rec → (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).X) (on : Rec × F.E.Str → Prop)
    (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (selZ X iJ iQ)).on (lawFa X iJ iQ strs inX a))
    (hpr : ∀ a, on a → ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
      (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).on (lawFa X iJ iQ strs inX a))
    (hA : LawAfter X iJ iQ d₁ d₂ ρ p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on)
    (fb : Rec × F.E.Str → (Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (selZ X iJ iQ).sw).tgt.Ex.prod (portCode r.cs r.rider).nat).Str)
    (hB : BehindIs X iJ iQ d₁ d₂ ρ p base ext strs inX on fb) :
    (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).ior.red.Leads on
      (fun a a' => ∀ wt, lawRb X iJ iQ p F.E.Str a (a'.1, fb a') wt →
        ((Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).S.over
          (Cb.Pv.SendLoc.stage (selZ X iJ iQ).sw).A).relR (lawFa X iJ iQ strs inX a)
            (selBk X iJ iQ wt) ∧
        ∀ k : (selHd X iJ iQ).K,
          ((selHd X iJ iQ).o k).decW ((selHd X iJ iQ).sW k (lawFa X iJ iQ strs inX a).2.1.1)
              ((lawFa X iJ iQ strs inX a).1.1.1.2 k) =
            some ((selHd X iJ iQ).msg (cutSel r.cs r.l iJ iQ (selNew X iJ iQ wt)).1 k))
      (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ∧
    Err.Below (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) := by
  have L := law_at h hW X iJ iQ d₁ d₂ ρ w p strs inX (shownP X iJ iQ d₁ d₂ ρ p base ext) on hon hpr
    hA
  refine ⟨fun a ha => Doomed.mono _ _ ?_ (L.1 a ha), L.2⟩
  intro τ hτ a' ha' wt hw
  obtain ⟨b₂, hb⟩ := piece_is_lawOut X iJ iQ d₁ d₂ ρ p base ext strs inX w a a' τ ha'
  have e := hB a a' τ b₂ ha ha' hb
  exact hτ (a'.1, b₂) hb wt (e ▸ hw)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.piece_yes_shown
#print axioms VerifiableInference.Desc.First.K2Caller.piece_is_lawOut
#print axioms VerifiableInference.Desc.First.K2Caller.k2_leads
