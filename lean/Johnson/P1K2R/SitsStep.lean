-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsStep.lean (over
Sits.lean and Johnson/Desc/K12/Law/Sits.lean): THE ROW «K02_sits» AT THE STEP (the form over the
files below it), in the form «Sits B K enter leave» (rounds · plan · step): at
each of the 25 places of the kind «the code switch» in the proof file's written description the
SEATED, GUARDED block sits on the kind's own block K2.codeSwitchKind p, at the plan's numbers, behind a door. NO
BLOCK IMPORTS THIS FILE. Sits (general in the kind; another file's): B declares K's rounds; B's yes
on the plan gives K's; wherever B's STEP says yes at s, enter s = .ok t, K's step says yes at t at
the same rounds and columns and takes as many columns, and leave s t' gives B's record.
THE DOORS, by the sort of place:
  a link               enter: the record as it is · leave (leaveOpened f): no mark behind the
                       switch; then THE LINK's OWN «opened» (f.opened, f the l-th row of
                       framesOf); no mark; the reply as it was
  the head's link      enter: the record as it is · leave: "H.1.quiet" (headOpenQ HP), then the
                       guards (no mark; the reply as it was)
  the finish           enter: "F.0.front" (finishFrontQ) · leave: "F.0.quiet" (finishBehindQ),
                       then the guards
  sits_self · sits_mono · sits_fronted   three rules that lacked: a block sits on itself; a door
                                         may be widened; a block without a round joined IN FRONT
                                         goes into the way in
  sits_alone · sits_with                 through the seat's wrappers: alone (by
                                         step_alone); with a block without a round joined behind
  blocksOf_quiet                         no block of the frames' lot has a round
  sits_of_alone · sits_of_joined         from Dressed (Sits.lean) and the wrappers to Sits,
                                         dress by dress: SitsAt (alone) · SitsJoined (at a link's
                                         first place, by Joined, Johnson/IMR/SameSpot.lean)
  leaveOpened · leaveWith_opened         the way out at a link, written out; what the wrappers'
                                         way out gives of it
  SitsFramed · sits_of_framed            the elder, weaker form at a link (alone, or with some
                                         block of the frames' lot behind): kept for whoever calls
                                         it
  k02_sits_step                          in the goals' scope, at onlineDescription's value: at all 25
                                         places: where the seated block's test on the plan says
                                         yes, it sits on K2.codeSwitchKind p at p := k2P Z a nm ‹stands› n, n
                                         the lot's own numbers; at a link 1 ≤ l < 24 with the row
                                         f := fs[l] of framesOf by name: no arm «alone or framed»
                                         is left
LIMITS. As in Sits.lean. ONE DIRECTION. In a link both dresses «link» and «head» stay
possible by the plan alone (the lot's maker goes by the spelling of the plan's looks): the
statement says «one of the two»; K2's own guard [B2] refuses the wrong one at the record. Nothing
is said of oracles, «before», name or place (for the oracles: K2C/Fields.lean · SentTrees.lean).
No soundness is claimed.
-/
import Johnson.P1K2R.Sits
import Johnson.Desc.K12.Law.Sits

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock seatSame OpenedColumn
  step_iff andThen_step)
open VerifiableInference.Desc.First (S hearsReply)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened decideWith finishFrontQ
  finishBehindQ headOpenQ HeadPar)
open ProofFile (Cl)
open IM (K2Is k2P under LaidAlone LaidFramed Joined Open seatedAs seatedWith marked openedOf)
open H2K.JointK (Sits)

/-! ## Three rules on Sits -/

theorem sits_self {σ C : Type} (K : Block σ C) : Sits K K (fun s => .ok s) (fun _ t => .ok t) where
  rounds := rfl
  plan := id
  step := fun _ s s' _ _ _ h => ⟨s, s', rfl, h, rfl⟩

theorem sits_mono {σ τ C C' : Type} {B : Block σ C} {K : Block τ C'}
    {enter enter' : σ → Except String τ} {leave leave' : σ → τ → Except String σ}
    (h : Sits B K enter leave) (he : ∀ s t, enter s = .ok t → enter' s = .ok t)
    (hl : ∀ s t s', leave s t = .ok s' → leave' s t = .ok s') : Sits B K enter' leave' where
  rounds := h.rounds
  plan := h.plan
  step := fun ft s s' rs cols k a => by
    obtain ⟨t, t', e1, e2, e3⟩ := h.step ft s s' rs cols k a
    exact ⟨t, t', he _ _ e1, e2, hl _ _ _ e3⟩

/-- A block without a round joined in front: its decision, on no round, goes into the way in. -/
theorem sits_fronted {σ τ C C' : Type} {B : Block σ C} {K : Block τ C'}
    {enter : σ → Except String τ} {leave : σ → τ → Except String σ} (h : Sits B K enter leave)
    (name : String) (q : Block σ C) (hq : q.rounds = []) :
    Sits (q.andThen name B) K (fun s => (q.decide s [] []).bind enter)
      (fun s t => (q.decide s [] []).bind fun m => leave m t) where
  rounds := by
    show q.rounds ++ B.rounds = K.rounds
    rw [hq, List.nil_append]
    exact h.rounds
  plan := fun a => by
    simp only [Block.andThen, Bool.and_eq_true] at a
    exact h.plan a.2
  step := fun ft s s' rs cols k a => by
    obtain ⟨m, k1, k2, h1, h2, rfl⟩ := (andThen_step name q B ft s s' rs cols k).1 a
    obtain ⟨_, hd, hk⟩ := (step_iff ft q s m _ cols k1).1 h1
    have h0 : k1 = 0 := by
      rw [hk]
      simp [Block.want, hq, VerifiableInference.Desc.groupsOf]
    have hd' : q.decide s [] [] = .ok m := by
      simpa [Block.shown, hq, VerifiableInference.Desc.groupsOf,
        VerifiableInference.Desc.regroup] using hd
    subst h0
    rw [hq] at h2
    simp only [List.length_nil, List.drop_zero, Nat.zero_add] at h2 ⊢
    obtain ⟨t, t', e1, e2, e3⟩ := h.step ft m s' rs cols k2 h2
    exact ⟨t, t', by rw [hd']; exact e1, e2, by rw [hd']; exact e3⟩

/-! ## Through the seat's wrappers -/

/-- The mark's guard. -/
def noMark (t : S) : Except String S :=
  match t.failed with
  | none => .ok t
  | some m => .error ("marked: " ++ m)

/-- Both guards of the seat: no mark; the reply as it was. -/
def guards (s t : S) : Except String S := (noMark t).bind (seatSame ProofFile.sameReply s)

theorem sits_alone {τ C' : Type} {K : Block τ C'} {enter : S → Except String τ}
    {leave : S → τ → Except String S} {b b' : Block S Cl} {name : String} {a : Place}
    (hl : LaidAlone ProofFile.sameReply b b' name a) (hk : a.kind ≠ KindName.K7)
    (h : Sits b' K enter leave) : Sits b K enter (fun s t => (leave s t).bind (guards s)) where
  rounds := (IM.alone_rounds hl).trans h.rounds
  plan := fun p => h.plan (by rw [← IM.alone_planOk hl]; exact p)
  step := fun ft s s' rs cols k a' => by
    obtain ⟨h1, h2, h3⟩ := (IM.step_alone hl hk ft s s' k rs cols).1 a'
    obtain ⟨t, t', e1, e2, e3⟩ := h.step ft s s' rs cols k h1
    refine ⟨t, t', e1, e2, (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨s', e3, ?_⟩⟩
    simp [guards, noMark, h2, seatSame, h3, Except.bind]

/-- The way out where a block q without a round is joined behind. -/
def leaveWith {τ : Type} (leave : S → τ → Except String S) (q : Block S Cl) (s : S) (t : τ) :
    Except String S :=
  ((((leave s t).bind fun m => noMark m).bind fun m =>
    (q.guarded ProofFile.sameReply fun _ => false).decide m [] [])).bind (seatSame ProofFile.sameReply s)

theorem sits_with {τ C' : Type} {K : Block τ C'} {enter : S → Except String τ}
    {leave : S → τ → Except String S} {b' q : Block S Cl} {name : String} {a : Place}
    (hk : hearsReply a = false) (hq : q.rounds = []) (h : Sits b' K enter leave) :
    Sits (seatedWith ProofFile.sameReply b' q name a) K enter (leaveWith leave q) := by
  have h1 : Sits (ProofFile.guardMark b') K enter (fun s t => (leave s t).bind fun m => noMark m) :=
    h.behind (ProofFile.guardMark b') (fun _ m => noMark m) rfl (fun _ _ _ => rfl) id
  have h2 : Sits (marked b' name) K enter (fun s t => (leave s t).bind fun m => noMark m) :=
    h1.same _ rfl rfl id
  have h3 := h2.withRoundlessBlockBehind name (q.guarded ProofFile.sameReply fun _ => false) hq
  have h4 := h3.same ({ (marked b' name).andThen name (q.guarded ProofFile.sameReply fun _ => false) with
    place := a } : Block S Cl) rfl rfl id
  exact h4.guarded ProofFile.sameReply hearsReply hk

theorem blocksOf_quiet (Z : ProofFile.Pub) : ∀ fb ∈ P1L20.blocksOf Z, fb.rounds = [] := by
  intro fb h
  unfold P1L20.blocksOf at h
  split at h
  · obtain ⟨f, _, hf⟩ := List.mem_flatMap.1 h
    simp only [ProofFile.frameBlocks, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with e | e | e <;> subst e <;> rfl
  · simp only [List.mem_singleton] at h
    subst h
    rfl

/-! ## The kind's block under its three dresses -/

theorem sits_under_link (nm : String) (a : Place) (p : P2) :
    Sits ((under nm a (codeSwitchKind p)).retype : Block S Cl) (codeSwitchKind p : Block S Unit) (fun s => .ok s)
      (fun _ t => .ok t) :=
  ((sits_self (codeSwitchKind p : Block S Unit)).same (under nm a (codeSwitchKind p)) rfl rfl id).retype

theorem sits_under_head (nm : String) (a : Place) (p : P2) (HP : HeadPar) :
    Sits ((under nm a ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm a HP))).retype : Block S Cl)
      (codeSwitchKind p : Block S Unit) (fun s => .ok s) (fun _ t => headOpenQ HP t) :=
  sits_mono ((((sits_self (codeSwitchKind p : Block S Unit)).withRoundlessBlockBehind nm (headOpened nm a HP) rfl).same
    (under nm a ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm a HP))) rfl rfl id).retype)
    (fun _ _ e => e) (fun _ _ _ e => e)

theorem sits_under_finish (nm : String) (a : Place) (p : P2) :
    Sits ((under nm a (finishPlace p)).retype : Block S Cl) (codeSwitchKind p : Block S Unit) finishFrontQ
      (fun _ t => finishBehindQ t) := by
  have h1 := sits_fronted (sits_self (codeSwitchKind p : Block S Unit)) p.name
    (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece finishFrontQ) rfl
  have h2 := h1.withRoundlessBlockBehind p.name
    (roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece finishBehindQ) rfl
  have h3 := (h2.same (under nm a (finishPlace p)) rfl rfl id).retype (Cl'' := Cl)
  refine sits_mono h3 (fun s t e => ?_) (fun s t s' e => ?_)
  · obtain ⟨m, e1, e2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    cases e2
    exact e1
  · obtain ⟨m, e1, e2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
    obtain ⟨m', _, e4⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e1
    cases e4
    exact e2

/-- What the row says of one seated block b at the address a. -/
def SitsAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (b : Block S Cl) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((a.link = none ∧ Sits b (codeSwitchKind (k2P Z a nm .finish n) : Block S Unit) finishFrontQ
        (fun s t => (finishBehindQ t).bind (guards s))) ∨
      (∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        Sits b (codeSwitchKind (k2P Z a nm .head n) : Block S Unit) (fun s => .ok s)
          (fun s t => (headOpenQ HP t).bind (guards s))) ∨
      (∃ l, a.link = some l ∧ Sits b (codeSwitchKind (k2P Z a nm .link n) : Block S Unit) (fun s => .ok s)
        (fun s t => guards s t)))

theorem sits_of_alone {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {b : Block S Cl}
    {x : Block S Unit} (hl : LaidAlone ProofFile.sameReply b x.retype b.name a)
    (hk : a.kind ≠ KindName.K7) (hd : Dressed Z G a x.name x) : SitsAt Z G a x.name b := by
  obtain ⟨P, n, hP, hn, h⟩ := hd
  refine ⟨P, n, hP, hn, ?_⟩
  rcases h with ⟨ha, hx⟩ | ⟨l, HP, ha, hH, hx⟩ | ⟨l, ha, hx⟩
  · refine Or.inl ⟨ha, ?_⟩
    rw [hx] at hl
    exact sits_alone hl hk (sits_under_finish _ _ _)
  · refine Or.inr (Or.inl ⟨l, HP, ha, hH, ?_⟩)
    rw [hx] at hl
    exact sits_alone hl hk (sits_under_head _ _ _ _)
  · refine Or.inr (Or.inr ⟨l, ha, ?_⟩)
    rw [hx] at hl
    exact sits_mono (sits_alone hl hk (sits_under_link _ _ _)) (fun _ _ e => e) (fun _ _ _ e => e)

/-- At a link's first place with a block fb of the frames' lot joined behind. -/
def SitsFramed (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (b : Block S Cl)
    (fb : Block S Unit) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((a.link = none ∧ Sits b (codeSwitchKind (k2P Z a nm .finish n) : Block S Unit) finishFrontQ
        (leaveWith (fun _ t => finishBehindQ t) (ProofFile.guardMark fb.retype))) ∨
      (∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        Sits b (codeSwitchKind (k2P Z a nm .head n) : Block S Unit) (fun s => .ok s)
          (leaveWith (fun _ t => headOpenQ HP t) (ProofFile.guardMark fb.retype))) ∨
      (∃ l, a.link = some l ∧ Sits b (codeSwitchKind (k2P Z a nm .link n) : Block S Unit) (fun s => .ok s)
        (leaveWith (fun _ t => .ok t) (ProofFile.guardMark fb.retype))))

theorem sits_of_framed {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {b : Block S Cl}
    {x : Block S Unit} (hl : LaidFramed Z b x.retype b.name a) (hk : a.kind ≠ KindName.K7)
    (hd : Dressed Z G a x.name x) :
    SitsAt Z G a x.name b ∨ ∃ fb ∈ P1L20.blocksOf Z, SitsFramed Z G a x.name b fb := by
  rcases hl with hl | ⟨fb, hfb, hb⟩
  · exact Or.inl (sits_of_alone hl hk hd)
  · refine Or.inr ⟨fb, hfb, ?_⟩
    have hq : (ProofFile.guardMark (fb.retype : Block S Cl)).rounds = [] := blocksOf_quiet Z fb hfb
    have hh : hearsReply a = false := by
      unfold hearsReply
      cases hka : a.kind <;> first | rfl | exact absurd hka hk
    obtain ⟨P, n, hP, hn, h⟩ := hd
    refine ⟨P, n, hP, hn, ?_⟩
    rcases h with ⟨ha, hx⟩ | ⟨l, HP, ha, hH, hx⟩ | ⟨l, ha, hx⟩
    · refine Or.inl ⟨ha, ?_⟩
      rw [hb, hx]
      exact sits_with hh hq (sits_under_finish _ _ _)
    · refine Or.inr (Or.inl ⟨l, HP, ha, hH, ?_⟩)
      rw [hb, hx]
      exact sits_with hh hq (sits_under_head _ _ _ _)
    · refine Or.inr (Or.inr ⟨l, ha, ?_⟩)
      rw [hb, hx]
      exact sits_with hh hq (sits_under_link _ _ _)

/-- The way out at a link's first place: no mark behind the switch; the link's own «opened»; no
mark;
the reply as it was. -/
def leaveOpened (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (s t : S) : Except String S :=
  (noMark t).bind fun m => (f.opened m).bind fun u => (noMark u).bind fun u =>
    (seatSame ProofFile.sameReply m u).bind (seatSame ProofFile.sameReply s)

theorem leaveWith_opened {τ : Type} {leave : S → τ → Except String S}
    {f : Johnson.Desc.First.Walk.Seat.LinkFrame} {s : S} {t : τ} {s' : S}
    (h : leaveWith leave (ProofFile.guardMark (openedOf f).retype) s t = .ok s') :
    ∃ m, leave s t = .ok m ∧ leaveOpened f s m = .ok s' := by
  unfold leaveWith at h
  obtain ⟨u₃, h, e4⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨m₁, h, e3⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  obtain ⟨m, e1, e2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 h
  refine ⟨m, e1, ?_⟩
  obtain ⟨d3, d4⟩ := (VerifiableInference.Desc.guarded_yes ProofFile.sameReply (fun _ => false) _ rfl m₁ _
    _ u₃).1 e3
  obtain ⟨d5, d6⟩ := (IM.guardMark_yes _ m₁ u₃ _ _).1 d3
  have d5' : f.opened m₁ = .ok u₃ := d5
  unfold leaveOpened
  rw [e2]
  show (f.opened m₁).bind _ = _
  rw [d5']
  show (noMark u₃).bind _ = _
  have : noMark u₃ = .ok u₃ := by simp [noMark, d6]
  rw [this]
  show (seatSame ProofFile.sameReply m₁ u₃).bind _ = _
  have : seatSame ProofFile.sameReply m₁ u₃ = .ok u₃ := by simp [seatSame, d4]
  rw [this]
  exact e4

/-- At a link's first place, with the link's own row f of framesOf. -/
def SitsJoined (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (b : Block S Cl)
    (f : Johnson.Desc.First.Walk.Seat.LinkFrame) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        Sits b (codeSwitchKind (k2P Z a nm .head n) : Block S Unit) (fun s => .ok s)
          (fun s t => (headOpenQ HP t).bind (leaveOpened f s))) ∨
      (∃ l, a.link = some l ∧ Sits b (codeSwitchKind (k2P Z a nm .link n) : Block S Unit) (fun s => .ok s)
        (fun s t => leaveOpened f s t)))

theorem sits_of_joined {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {a : Place} {b : Block S Cl}
    {x : Block S Unit} (hl : Joined Z l b x.retype a) (hk : a.kind ≠ KindName.K7)
    (ha : a.link = some l) (hd : Dressed Z G a x.name x) :
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ SitsJoined Z G a x.name b f := by
  obtain ⟨fs, f, hfs, hf, hb⟩ := hl
  refine ⟨fs, f, hfs, hf, ?_⟩
  have hq : (ProofFile.guardMark ((openedOf f).retype : Block S Cl)).rounds = [] := rfl
  have hh : hearsReply a = false := by
    unfold hearsReply
    cases hka : a.kind <;> first | rfl | exact absurd hka hk
  obtain ⟨P, n, hP, hn, h⟩ := hd
  refine ⟨P, n, hP, hn, ?_⟩
  rcases h with ⟨h0, _⟩ | ⟨l', HP, h1, hH, hx⟩ | ⟨l', h1, hx⟩
  · rw [ha] at h0
    cases h0
  · refine Or.inl ⟨l', HP, h1, hH, ?_⟩
    rw [hb, hx]
    refine sits_mono (sits_with hh hq (sits_under_head _ _ _ _)) (fun _ _ e => e) fun s t s' e => ?_
    obtain ⟨m, e1, e2⟩ := leaveWith_opened e
    exact (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨m, e1, e2⟩
  · refine Or.inr ⟨l', h1, ?_⟩
    rw [hb, hx]
    refine sits_mono (sits_with hh hq (sits_under_link _ _ _)) (fun _ _ e => e) fun s t s' e => ?_
    obtain ⟨m, e1, e2⟩ := leaveWith_opened e
    cases e1
    exact e2

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **THE ROW K02_sits, AT THE STEP.** -/
theorem k02_sits_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (∀ l, 1 ≤ l → l < 24 → ∃ (b : Block S Cl) (nm : String),
        c.blocksInOrder[14 * l + 0 + 2]? = some b ∧ (b.planOk = true →
                   ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
                     fs[l]? = some f ∧
                     SitsJoined Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } nm b f)) ∧
      (∃ (b : Block S Cl) (nm : String), c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧ (b.planOk = true →
                   SitsAt Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } nm b)) ∧
      (∃ (b : Block S Cl) (nm : String), c.back[0]? = some b ∧ (b.planOk = true →
          SitsAt Z Bs.G₀ IM.k2PlaceF nm b)) := by
  obtain ⟨Z, Bs, base, c, A, B, O, h1, h2, h3⟩ := k02_sits hS hR hF
  refine ⟨Z, Bs, base, c, A, B, O, fun l a1 a24 => ?_, ?_, ?_⟩
  · obtain ⟨b, x, hf, _, hl, hi⟩ := h1 l a1 a24
    refine ⟨b, x.name, hf, fun hp => ?_⟩
    exact sits_of_joined hl (fun e => by cases e) rfl
      (is_planOk hi (IM.retype_planOk x (IM.laid_planOk hl.framed.laid hp)).1)
  · obtain ⟨b, x, hf, _, hl, hi⟩ := h2
    refine ⟨b, x.name, hf, fun hp => ?_⟩
    exact sits_of_alone hl (by decide)
      (is_planOk hi (IM.retype_planOk x (IM.laid_planOk hl.laid hp)).1)
  · obtain ⟨b, x, hf, _, hl, hi⟩ := h3
    refine ⟨b, x.name, hf, fun hp => ?_⟩
    exact sits_of_alone hl (by decide)
      (is_planOk hi (IM.retype_planOk x (IM.laid_planOk hl.laid hp)).1)

end

end P1K2

#print axioms P1K2.sits_of_framed
#print axioms P1K2.sits_of_joined
#print axioms P1K2.k02_sits_step
#print axioms P1K2.sits_fronted
#print axioms P1K2.sits_alone
#print axioms P1K2.sits_with
#print axioms P1K2.blocksOf_quiet
#print axioms P1K2.sits_under_finish
#print axioms P1K2.sits_of_alone
