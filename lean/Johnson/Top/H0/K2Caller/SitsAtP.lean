-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SitsAtP.lean: code switching: IN THE GOALS' SCOPE, AT ALL 25 PLACES OF THE
KIND, THE SUB-PROTOCOL OF THE FIRST CHAIN THAT STANDS THERE SITS ON THE KIND's OWN AT THE NUMBERS
ProofFile.pAtK2 Z m (Johnson/Desc/ProofFile/CarryAt.lean): THE NUMBERS AT WHICH THE SENTENCE ON THE
CARRIED CLAIM IS SPENT: AND IN ONE DRESS. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. The row k02_sits_step (Johnson/P1K2R/SitsStep.lean) hands the like at the lot's own numbers
(IM.k2P Z a nm st n), and at a link under «the head's dress or the link's». The ties want one letter
for both numbers, and one dress.
  place_of_is     a live member of the lot's table stands at the place at which it is spoken of
  sits_link_at · sits_head_at · sits_finish_at   k02_sits_step's three arms, at whatever numbers p
  seatStep_of_sits  from «sits» to the two premises that the ties take: as many rounds; SeatStep
  k02_sits_pAt    THE STATEMENT, with the ways in and out of k02_sits_step, letter for letter
TWO PREMISES BESIDE THE SCOPE: the test spotsFitB Z (K2Caller/PAtSeated.lean) accepts; the request's
shape has 25 links.
LIMITS. ONE DIRECTION, as in SitsStep.lean. THE TEST HAS BEEN EVALUATED AT NO Z. «25 links» is,
in scope, a theorem of other files: not called here. No soundness is claimed.
-/
import Johnson.P1K2R.SitsStep
import Johnson.Top.H0.K2Caller.PAtSeated
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Top.H0.K2Caller.SeatedAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S hearsReply)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened finishFrontQ
  finishBehindQ headOpenQ HeadPar)
open VerifiableInference.Desc.First.K2Caller (spotsFitB seated_is_pAt dressOf)
open ProofFile (Cl)
open IM (K2Is k2P under LaidAlone Joined Open openedOf)
open H2K.JointK (Sits)

/-- A live member of the lot's table stands at the place at which it is spoken of. -/
theorem place_of_is {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : K2Is Z G a nm x) (hp : x.planOk = true) : x.place = a := by
  obtain ⟨_, _, _, _, h⟩ := h.live hp
  rcases h with ⟨_, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, e⟩ <;> exact congrArg (fun b => b.place) e

theorem sits_link_at {Z : ProofFile.Pub} {l : Nat} {a : Place} {b : Block S Cl} {x : Block S Unit}
    {nm : String} {p : P2} (hl : Joined Z l b x.retype a) (hk : a.kind ≠ KindName.K7)
    (hx : x = under nm a (codeSwitchKind p)) :
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧
      Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) (fun s t => leaveOpened f s t) := by
  obtain ⟨fs, f, hfs, hf, hb⟩ := hl
  refine ⟨fs, f, hfs, hf, ?_⟩
  have hq : (ProofFile.guardMark ((openedOf f).retype : Block S Cl)).rounds = [] := rfl
  have hh : hearsReply a = false := by
    unfold hearsReply
    cases hka : a.kind <;> first | rfl | exact absurd hka hk
  rw [hb, hx]
  refine sits_mono (sits_with hh hq (sits_under_link _ _ _)) (fun _ _ e => e) fun s t s' e => ?_
  obtain ⟨m, e1, e2⟩ := leaveWith_opened e
  cases e1
  exact e2

theorem sits_head_at {a : Place} {b : Block S Cl} {x : Block S Unit} {nm : String} {p : P2}
    {HP : HeadPar} (hl : LaidAlone ProofFile.sameReply b x.retype b.name a)
    (hk : a.kind ≠ KindName.K7)
    (hx : x = under nm a ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm a HP))) :
    Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s)
      (fun s t => (headOpenQ HP t).bind (guards s)) := by
  rw [hx] at hl
  exact sits_alone hl hk (sits_under_head _ _ _ _)

theorem sits_finish_at {a : Place} {b : Block S Cl} {x : Block S Unit} {nm : String} {p : P2}
    (hl : LaidAlone ProofFile.sameReply b x.retype b.name a) (hk : a.kind ≠ KindName.K7)
    (hx : x = under nm a (finishPlace p)) :
    Sits b (codeSwitchKind p : Block S Unit) finishFrontQ (fun s t => (finishBehindQ t).bind (guards s)) := by
  rw [hx] at hl
  exact sits_alone hl hk (sits_under_finish _ _ _)

/-- **From «sits» to the ties' two premises**: as many rounds; the clause at the step (SeatStep,
K2Caller/SeatedAt.lean), which is the third field letter for letter. -/
theorem seatStep_of_sits {σ τ C C' : Type} {B : Block σ C} {K : Block τ C'}
    {enter : σ → Except String τ} {leave : σ → τ → Except String σ} (h : Sits B K enter leave) :
    B.rounds = K.rounds ∧
      VerifiableInference.Desc.First.K2Caller.SeatStep B K enter leave :=
  ⟨h.rounds, h.step⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **The row K02_sits at the sentence's own numbers, in one dress.** -/
theorem k02_sits_pAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (spotsFitB Z = true → Z.s₀.check.frame.shape.link.length = 25 →
        (∀ l, 1 ≤ l → l < 24 → ∃ b : Block S Cl, c.blocksInOrder[14 * l + 0 + 2]? = some b ∧
          (b.planOk = true → (ProofFile.pAtK2 Z (l - 1)).stands = .link ∧
            ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
              fs[l]? = some f ∧ Sits b (codeSwitchKind (ProofFile.pAtK2 Z (l - 1)) : Block S Unit)
                (fun s => .ok s) (fun s t => leaveOpened f s t))) ∧
        (∃ b : Block S Cl, c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧
          (b.planOk = true → (ProofFile.pAtK2 Z 23).stands = .head ∧
            ∃ HP, pureLetters Bs.G₀ 24 = some HP ∧ Sits b (codeSwitchKind (ProofFile.pAtK2 Z 23) : Block S Unit)
              (fun s => .ok s) (fun s t => (headOpenQ HP t).bind (guards s)))) ∧
        (∃ b : Block S Cl, c.back[0]? = some b ∧
          (b.planOk = true → (ProofFile.pAtK2 Z 24).stands = .finish ∧
            Sits b (codeSwitchKind (ProofFile.pAtK2 Z 24) : Block S Unit) finishFrontQ
              (fun s t => (finishBehindQ t).bind (guards s))))) := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits hS hR hF
  refine ⟨Z, Bs, base, c, A, B, O, fun hT hL => ⟨fun l a1 a24 => ?_, ?_, ?_⟩⟩
  · obtain ⟨b, x, hf, hx, hl, hi⟩ := h1 l a1 a24
    refine ⟨b, hf, fun hp => ?_⟩
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hp)).1
    have hpl := place_of_is hi hxp
    obtain ⟨Q, n, hQ, hn, e, arms⟩ := seated_is_pAt O.blank hT hx hxp
    rw [hpl] at hn e arms
    have hg : n.grp = l := numsAt_grp hn
    have hm : n.grp - 1 = l - 1 := by rw [hg]
    rw [hm] at e arms
    rw [hL] at e
    have hst : (ProofFile.pAtK2 Z (l - 1)).stands = .link := by
      rw [e]
      show (if l + 1 == 25 then At.head else At.link) = At.link
      rw [if_neg (by simp; omega)]
    rcases arms with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, hx'⟩
    · rw [hst] at h0
      cases h0
    · rw [hst] at h0
      cases h0
    · exact ⟨hst, sits_link_at hl (fun e => by cases e) hx'⟩
  · obtain ⟨b, x, hf, hx, hl, hi⟩ := h2
    refine ⟨b, hf, fun hp => ?_⟩
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hp)).1
    have hpl := place_of_is hi hxp
    obtain ⟨Q, n, hQ, hn, e, arms⟩ := seated_is_pAt O.blank hT hx hxp
    rw [hpl] at hn e arms
    have hg : n.grp = 24 := numsAt_grp hn
    have hm : n.grp - 1 = 23 := by rw [hg]
    rw [hm] at e arms
    rw [hL] at e
    have hst : (ProofFile.pAtK2 Z 23).stands = .head := by
      rw [e]
      rfl
    rcases arms with ⟨h0, _⟩ | ⟨_, l', HP, hl', hH, hx'⟩ | ⟨h0, _⟩
    · rw [hst] at h0
      cases h0
    · obtain rfl : 24 = l' := Option.some.inj hl'
      exact ⟨hst, HP, hH, sits_head_at hl (by decide) hx'⟩
    · rw [hst] at h0
      cases h0
  · obtain ⟨b, x, hf, hx, hl, hi⟩ := h3
    refine ⟨b, hf, fun hp => ?_⟩
    have hxp : x.planOk = true := (IM.retype_planOk x (IM.laid_planOk hl.laid hp)).1
    have hpl := place_of_is hi hxp
    obtain ⟨Q, n, hQ, hn, e, arms⟩ := seated_is_pAt O.blank hT hx hxp
    rw [hpl] at hn e arms
    have hg : n.grp = 25 := by
      rw [numsAt_grp hn]
      show Q.z.request.link.length = 25
      rw [(prepOf_request hQ).1, hL]
    have hm : n.grp - 1 = 24 := by rw [hg]
    rw [hm] at e arms
    have hst : (ProofFile.pAtK2 Z 24).stands = .finish := by
      rw [e]
      rfl
    rcases arms with ⟨_, hx'⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
    · exact ⟨hst, sits_finish_at hl (by decide) hx'⟩
    · rw [hst] at h0
      cases h0
    · rw [hst] at h0
      cases h0

end

end P1K2

#print axioms P1K2.place_of_is
#print axioms P1K2.sits_link_at
#print axioms P1K2.sits_head_at
#print axioms P1K2.sits_finish_at
#print axioms P1K2.seatStep_of_sits
#print axioms P1K2.k02_sits_pAt
