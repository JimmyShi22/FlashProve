-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameCarryEnds.lean: THE CARRIED WORD's SENTENCE (`K2Caller.carryAtZ`,
Johnson/Top/H0/K2Caller/CarryClosed.lean) GOES BACK ALSO WHERE
THE NEXT SWITCH STANDS AT THE OUTPUT HEAD's LINK OR AT THE FINISH: over "laid", over an accepting
"cleared", and over the closing's third sub-protocol ("the segment is shut"). FrameCarryBack.lean
has the like where the switch stands at a link. Statements and proofs.

What is said.
  `FrontsLike p u t`: u and t have one book and one number of roots, and where the switch's front is
    there at t it is there at u, with the same frame, notices and target and statements that are
    `StLike`. `carryRow_fronts`: **the sentence at a typed row passes from t to u**: GENERAL IN
    WHERE THE SWITCH STANDS.
  `DoorLike Z m s t`: whatever the way in `doorZ Z m` lets in of t, it lets in of s a state with
    `FrontsLike`. `carry_back_door`, `carry_goesBack_door`: **THE RULE**, at every segment; the
    fence `CarryFence` is asked at the state that the way in returns.
  `WayLike u v`: two states between the links with one mark, one book, one number of roots,
    statements that are `StLike`, and, where v's copy of the calls' state says "no link is under
    way", the same copy. `headFrontQ_like`, `finishFrontQ_like`: the head's and the finish's fronts
    at two such states. `finishFront_like`.
  `wayLike_cleared`, `wayLike_shut`: an accepting "cleared" and "the segment is shut" have it at
    `rest s` and `rest t`.
  `doorLike_refl`, `doorLike_head`, `doorLike_finish`; `carry_goesBack_head`,
    `carry_goesBack_finish`, `carry_goesBack_sameZ`: **the sentence goes back.**

Limits. At `.head` the state in front and the state behind must not stand at the head's link
(`∀ a, s.here ≠ .head a`): a premise, had from what is known in front: at a head's link that is
opened the way in answers nothing and the sentence is false. The fence is a premise. No soundness
statement.

-/
import Johnson.Top.H0.Walk.FrameCarryBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Sound (GoesBack)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 frontAt longFront frameAt headFrontQ finishFrontQ
  headFrontOf finFrontOf)
open VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First.Pend (pendingRowO)
open _root_.Tw.K2 (firstFront finishFront Front)

/-- The switch's front at u is as at t. -/
structure FrontsLike (p : P2) (u t : S) : Prop where
  book : t.book = u.book
  roots : t.roots = u.roots
  front : ∀ fx, frontAt p t = some fx → ∃ fx', frontAt p u = some fx' ∧ fx'.f = fx.f ∧
    fx'.others = fx.others ∧ fx'.T = fx.T ∧ StLike fx.st fx'.st

theorem FrontsLike.refl (p : P2) (u : S) : FrontsLike p u u :=
  ⟨rfl, rfl, fun fx h => ⟨fx, h, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩⟩

/-- **The sentence at a typed row, wherever the switch stands.** -/
theorem carryRow_fronts (r : SwRow) (H : r.OK) {p : P2} (orc : Strs → ℕ → ℕ → List UInt64)
    {u t : S} (h : FrontsLike p u t) {y y' : Strs}
    (hy : ∀ fx q, frontAt p u = some fx → longFront p u fx (orc y) q = longFront p u fx (orc y') q)
    (hc : carryRow r H p orc (smpK2 r H) t y') : carryRow r H p orc (smpK2 r H) u y := by
  obtain ⟨fx, W₀, h1, h2, h3⟩ := hc
  obtain ⟨fx', hfu, hf, ho, hT, hst⟩ := h.front fx h1
  refine ⟨fx', W₀, hfu, by rw [frameAt_like hf ho hT hst]; exact h2, ?_⟩
  have ea : faAt r H p orc (smpK2 r H) (u, fx', W₀) y =
      faAt r H p orc (smpK2 r H) (t, fx, W₀) y' := by
    unfold faAt
    simp only [hf, smpK2_like hst, hy fx' _ hfu, longFront_like hf ho hT hst p h.book h.roots]
  unfold VerifiableInference.Desc.First.K2Hands.carryOf at h3 ⊢
  rw [ea]
  exact h3

/-- What the way in lets in of t, it lets in of s, alike. -/
def DoorLike (Z : ProofFile.Pub) (m : ℕ) (s t : S) : Prop :=
  ∀ t', doorZ Z m t = some t' → ∃ s', doorZ Z m s = some s' ∧ FrontsLike (ProofFile.pAtK2 Z m) s' t'

theorem doorLike_refl (Z : ProofFile.Pub) (m : ℕ) (s : S) : DoorLike Z m s s :=
  fun t' h => ⟨t', h, FrontsLike.refl _ _⟩

/-- **THE RULE.** -/
theorem carry_back_door {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ) {s t : S}
    (h : DoorLike Z m s t) {y y' : Strs}
    (hy : ∀ s' fx q, doorZ Z m s = some s' → frontAt (ProofFile.pAtK2 Z m) s' = some fx →
      longFront (ProofFile.pAtK2 Z m) s' fx
          (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y) q =
        longFront (ProofFile.pAtK2 Z m) s' fx
          (VerifiableInference.Desc.First.K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) y') q)
    (p : P) (w : W) (hc : carryAtZ Z layF m (p, t) y' w) : carryAtZ Z layF m (p, s) y w := by
  rw [carryAtZ_iff] at hc ⊢
  obtain ⟨r, t', hr, hd, hok, hrow⟩ := hc
  obtain ⟨s', hs', hl⟩ := h t' hd
  exact ⟨r, s', hr, hs', hok, carryRow_fronts r _ _ hl (fun fx q => hy s' fx q hs') hrow⟩

/-- **THE RULE, AS A SENTENCE THAT GOES BACK.** -/
theorem carry_goesBack_door {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (rel : S → S → Prop) (base : Nat) (In : P × S → Strs → Prop)
    (hrel : ∀ p s t y, rel s t → In (p, s) y → DoorLike Z m s t)
    (hF : ∀ p s y s', In (p, s) y → doorZ Z m s = some s' → CarryFence Z m base s') :
    GoesBack (StepRel rel base In) (carryAtZ (P := P) (W := W) Z layF m) := by
  intro a y b y' w hr hb
  obtain ⟨p, s⟩ := a
  obtain ⟨p', t⟩ := b
  obtain ⟨e, hc, hy, hI⟩ := hr
  obtain rfl : p' = p := e
  exact carry_back_door Z layF m (hrel p' s t y hc hI)
    (fun s' fx q hs' hfx => longFront_stays (hF p' s y s' hI hs') hy fx q hfx) p' w hb

/-- **At a step that leaves the verifier's state, wherever the switch stands.** -/
theorem carry_goesBack_sameZ {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (rel : S → S → Prop) (hrel : ∀ s t, rel s t → t = s) (base : Nat)
    (In : P × S → Strs → Prop)
    (hF : ∀ p s y s', In (p, s) y → doorZ Z m s = some s' → CarryFence Z m base s') :
    GoesBack (StepRel rel base In) (carryAtZ (P := P) (W := W) Z layF m) :=
  carry_goesBack_door Z layF m rel base In
    (fun _ s t _ h _ => by rw [hrel s t h]; exact doorLike_refl Z m s) hF

/-! ### the two fronts -/

/-- Two states between the links that part in ledgers and in what is put out. -/
structure WayLike (u v : S) : Prop where
  hereU : u.here = .between
  hereV : v.here = .between
  check : v.check.inLink = false → u.check = v.check
  failed : u.failed = v.failed
  book : v.book = u.book
  roots : v.roots = u.roots
  st : StLike v.st u.st

/-- The finish's front's maker at two statements that are `StLike`. -/
theorem finishFront_like {S₁ S₂ : Statement} (h : StLike S₁ S₂) (f : ReqFrame) {x : Front}
    (hx : finishFront S₁ f = .ok x) :
    ∃ x', finishFront S₂ f = .ok x' ∧ x'.f = x.f ∧ StLike x.st x'.st := by
  unfold finishFront at hx ⊢
  split at hx
  · cases hx
  · rename_i h1
    rw [if_neg h1]
    split at hx
    · cases hx
    · rename_i G hG
      cases hg : _root_.Tw.K2.newGroupG S₁ f.shape.code f.shape.maskCode with
      | error e =>
        rw [hg] at hx
        cases hx
      | ok z =>
        obtain ⟨S', g⟩ := z
        rw [hg] at hx
        dsimp only at hx
        obtain ⟨hk, rfl, rfl⟩ := newGroupG_ok hg
        rw [newGroupG_of (by rw [h.codes]; exact hk)]
        dsimp only
        obtain rfl : _ = x := Except.ok.inj hx
        refine ⟨_, rfl, ?_, ?_⟩
        · dsimp only
          rw [h.groups]
        · exact ⟨h.codes, by
            show (S₂.groups.push _) = (S₁.groups.push _)
            rw [h.groups], h.size, h.msgs⟩

/-- **The head's front at two such states.** -/
theorem headFrontQ_like {p : P2} (hp : p.stands = .head) {u v : S} (h : WayLike u v)
    (tl : HTailF2) {t' : S} (hv : headFrontQ tl v = .ok t') :
    ∃ s', headFrontQ tl u = .ok s' ∧ FrontsLike p s' t' := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := u
  obtain ⟨st', book', roots', rowsOwed', failed', check', out', here', req'⟩ := v
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h
  dsimp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e4 e5 e6
  unfold headFrontQ at hv ⊢
  simp only [S.atBetween, Bool.not_true, Bool.false_eq_true, if_false] at hv ⊢
  by_cases hd : firstDue check' = true
  · have hin : check'.inLink = false := by
      unfold firstDue at hd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    obtain rfl := e3 hin
    simp only [hd, Bool.not_true, Bool.false_eq_true, if_false] at hv ⊢
    cases hx : firstFront st' check.frame with
    | error e =>
      rw [hx] at hv
      cases hv
    | ok x =>
      obtain ⟨x', hx', hf, -, -, -, -, hst⟩ := firstFront_like e7 check.frame hx
      rw [hx] at hv
      rw [hx']
      cases hm : failed with
      | some mk =>
        simp [Except.bind, S.enterHead?, S.enterHead, S.atBetween, S.unmarked, hm] at hv
      | none =>
        simp only [Except.bind, S.enterHead?, S.enterHead, S.atBetween, S.unmarked, hm,
          if_true] at hv ⊢
        obtain rfl := Except.ok.inj hv
        refine ⟨_, rfl, rfl, rfl, fun fx hfx => ?_⟩
        unfold frontAt at hfx ⊢
        simp only [hp] at hfx ⊢
        obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 hfx
        rw [hG]
        exact ⟨_, rfl, hf, rfl, rfl, hst⟩
  · simp [hd] at hv

/-- **The finish's front at two such states.** -/
theorem finishFrontQ_like {p : P2} (hp : p.stands = .finish) {u v : S} (h : WayLike u v)
    {t' : S} (hv : finishFrontQ v = .ok t') :
    ∃ s', finishFrontQ u = .ok s' ∧ FrontsLike p s' t' := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := u
  obtain ⟨st', book', roots', rowsOwed', failed', check', out', here', req'⟩ := v
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := h
  dsimp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e4 e5 e6
  unfold finishFrontQ at hv ⊢
  simp only [S.atBetween, Bool.not_true, Bool.false_eq_true, if_false] at hv ⊢
  by_cases hd : finishDue check' = true
  · have hin : check'.inLink = false := by
      unfold finishDue at hd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
      exact hd.1
    obtain rfl := e3 hin
    simp only [hd, Bool.not_true, Bool.false_eq_true, if_false] at hv ⊢
    cases hG : check.frame.groups[check.frame.link]? with
    | none =>
      rw [hG] at hv
      cases hx : finishFront st' check.frame <;> simp [hx] at hv
    | some G =>
      cases hx : finishFront st' check.frame with
      | error e =>
        rw [hG, hx] at hv
        cases hv
      | ok x =>
        obtain ⟨x', hx', hf, hst⟩ := finishFront_like e7 check.frame hx
        rw [hG, hx] at hv
        rw [hx']
        cases hm : failed with
        | some mk =>
          simp [Except.bind, S.enterFin?, S.enterFin, S.atBetween, S.unmarked, hm] at hv
        | none =>
          simp only [Except.bind, S.enterFin?, S.enterFin, S.atBetween, S.unmarked, hm,
            if_true] at hv ⊢
          obtain rfl := Except.ok.inj hv
          refine ⟨_, rfl, rfl, rfl, fun fx hfx => ?_⟩
          unfold frontAt at hfx ⊢
          simp only [hp, Option.map_some, Option.some.injEq] at hfx ⊢
          subst hfx
          exact ⟨_, rfl, hf, by simp only [finFrontOf, hf], rfl, hst⟩
  · simp [hd] at hv

/-! ### the steps -/

/-- An accepting "cleared". -/
theorem wayLike_cleared {L : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith L counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t) :
    WayLike (rest s) (rest t) := by
  obtain ⟨e1, e2⟩ := rest_cleared h
  obtain ⟨k1, k2, -, k4, k5, -, k7, -, k9, k10, k11, k12, -⟩ :=
    clearedGives L counts left lay lin s t h
  rw [e1, e2]
  refine ⟨rfl, ?_, fun hi => ?_, k7.symm, k4, k5, k9.symm, k10.symm, k11.symm,
    fun i => (k12 i).symm⟩
  · unfold S.atBetween at k1
    cases hh : t.here <;> simp [hh] at k1 ⊢
  · show ({ s.live with inLink := false } : ChainCheck) = t.check
    rw [k2] at hi ⊢
    rw [← hi]

/-- The closing's third sub-protocol ("the segment is shut"). -/
theorem wayLike_shut {Cl : Type} (p : VerifiableInference.Desc.K9.Where) (piece : Nat) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.shut (Cl := Cl) p piece).decide s rs gs = .ok t) :
    WayLike (rest s) (rest t) := by
  have h' : (do
      let L ← VerifiableInference.Desc.K9.there "K9.in-a-segment" s.link?
      pure (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) :
        Except String S) = .ok t := h
  cases hl : s.link? with
  | none =>
    rw [hl] at h'
    cases h'
  | some L =>
    rw [hl] at h'
    obtain rfl : s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame) = t :=
      Except.ok.inj h'
    cases hh : s.here with
    | lay a =>
      simp [S.link?, hh] at hl
      subst hl
      refine ⟨?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;>
        simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, hh,
          VerifiableInference.Desc.K9.closed]
    | att a =>
      simp [S.link?, hh] at hl
      subst hl
      refine ⟨?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;>
        simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, hh,
          VerifiableInference.Desc.K9.closed]
    | head a =>
      simp [S.link?, hh] at hl
      obtain ⟨ho, rfl⟩ := hl
      refine ⟨?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_⟩ <;>
        simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, hh, ho,
          VerifiableInference.Desc.K9.closed]
    | between => simp [S.link?, hh] at hl
    | fin a => simp [S.link?, hh] at hl
    | mem a => simp [S.link?, hh] at hl

/-- The way in at a segment whose switch stands at the head's link, at a state that does not stand
there. -/
theorem doorZ_head {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .head) {s : S}
    (hs : ∀ a, s.here ≠ .head a) : doorZ Z m s = (headFrontQ {} (rest s)).toOption := by
  unfold doorZ
  rw [hp]
  cases hh : s.here with
  | head a => exact absurd hh (hs a)
  | _ => rfl

theorem doorZ_finish {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .finish) (s : S) :
    doorZ Z m s = (finishFrontQ (rest s)).toOption := by
  unfold doorZ
  rw [hp]

theorem toOption_some {α : Type} {x : Except String α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => exact congrArg Except.ok (Option.some.inj h)

/-- **At the head's link's switch.** -/
theorem doorLike_head {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .head) {s t : S}
    (hs : ∀ a, s.here ≠ .head a) (ht : ∀ a, t.here ≠ .head a)
    (h : WayLike (rest s) (rest t)) : DoorLike Z m s t := by
  intro t' hd
  rw [doorZ_head hp ht] at hd
  obtain ⟨s', h1, h2⟩ := headFrontQ_like hp h {} (toOption_some hd)
  exact ⟨s', by rw [doorZ_head hp hs, h1]; rfl, h2⟩

/-- **At the finish's switch.** -/
theorem doorLike_finish {Z : ProofFile.Pub} {m : ℕ} (hp : (ProofFile.pAtK2 Z m).stands = .finish) {s t : S}
    (h : WayLike (rest s) (rest t)) : DoorLike Z m s t := by
  intro t' hd
  rw [doorZ_finish hp] at hd
  obtain ⟨s', h1, h2⟩ := finishFrontQ_like hp h (toOption_some hd)
  exact ⟨s', by rw [doorZ_finish hp, h1]; rfl, h2⟩

/-- **THE SENTENCE GOES BACK, the next switch at the head's link**: over every step with `WayLike`
at `rest`, neither state standing at the head's link. -/
theorem carry_goesBack_head {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .head) (rel : S → S → Prop)
    (hrel : ∀ s t, rel s t → WayLike (rest s) (rest t)) (base : Nat)
    (In : P × S → Strs → Prop)
    (hH : ∀ p s t y, rel s t → In (p, s) y → (∀ a, s.here ≠ .head a) ∧ ∀ a, t.here ≠ .head a)
    (hF : ∀ p s y s', In (p, s) y → doorZ Z m s = some s' → CarryFence Z m base s') :
    GoesBack (StepRel rel base In) (carryAtZ (P := P) (W := W) Z layF m) :=
  carry_goesBack_door Z layF m rel base In
    (fun p s t y h hI => doorLike_head hp (hH p s t y h hI).1 (hH p s t y h hI).2 (hrel s t h)) hF

/-- **THE SENTENCE GOES BACK, the next switch at the finish.** -/
theorem carry_goesBack_finish {P W : Type} (Z : ProofFile.Pub) (layF : ByteArray) (m : ℕ)
    (hp : (ProofFile.pAtK2 Z m).stands = .finish) (rel : S → S → Prop)
    (hrel : ∀ s t, rel s t → WayLike (rest s) (rest t)) (base : Nat)
    (In : P × S → Strs → Prop)
    (hF : ∀ p s y s', In (p, s) y → doorZ Z m s = some s' → CarryFence Z m base s') :
    GoesBack (StepRel rel base In) (carryAtZ (P := P) (W := W) Z layF m) :=
  carry_goesBack_door Z layF m rel base In
    (fun _ s t _ h _ => doorLike_finish hp (hrel s t h)) hF

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.carryRow_fronts
#print axioms Johnson.Desc.First.Walk.Tied.carry_back_door
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_door
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_sameZ
#print axioms Johnson.Desc.First.Walk.Tied.headFrontQ_like
#print axioms Johnson.Desc.First.Walk.Tied.finishFrontQ_like
#print axioms Johnson.Desc.First.Walk.Tied.wayLike_cleared
#print axioms Johnson.Desc.First.Walk.Tied.wayLike_shut
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_head
#print axioms Johnson.Desc.First.Walk.Tied.carry_goesBack_finish
