-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Wrap2.lean: the closing of a segment (K10): the properties of
Honest/K10/Wipe/Alike.lean go through makers of a member out of a member. A lemma for each maker named below. Sections 1
to 3 are general in the state's type σ and in a function w : σ → σ; section 4 is at the first chain's state and general
in w. One definition with code; the rest are theorems.

  1 quiet_whole2, quietBlock_whole2, refuses2, whole_same2, retype_whole2, andThen_decides2, andThen_whole2
  2 lift_whole2, liftPart_whole2, liftPart_clean, inside_whole2: a member typed at a part, or at a state of its own
  3 seatSame2, guarded_decides2, guarded_whole2, guardedFn2: the guard on a seat; atClaims_whole2
  4 guardMark_decides2, guardMark_whole2, orLoud_whole2, tested_whole2, openedAt, entered_decide, entered_whole2

By what. Each maker's text (Johnson/Desc/Block.lean, Johnson/Desc/SeatGuard.lean, Johnson/Desc/First/K4/AtC.lean,
Johnson/Desc/ProofFile/Frames1.lean, Johnson/Desc/ProofFile/Lots/Makers.lean, Johnson/Stored/HeadSeatAt.lean,
Johnson/Stored/ReplySeatAt.lean) is shown as a bind, a map or a choice and followed by the laws of Alike.lean. What a
guard or a test in front reads of the state is a premise: that it is the same at two states that are one under w
(guarded, guardMark), or the same at w s and at s (tested, entered).

Limits. The properties are shown of no member of the protocol here. Nothing says what w is. No property of the protocol
is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.SeatGuard
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.ProofFile.Lots.Makers
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Place roundlessBlock seatSame)
open VerifiableInference.Desc.First (S)

variable {σ τ Cl : Type} {w : σ → σ}

/-! ## 1 Members that are read through decide, claims and after alone -/

/-- A member whose decide is a change of the state alone, and which states no run, has Whole2 where the change has
Fn2. -/
theorem quiet_whole2 {b : Block σ Cl} {f : σ → Except String σ} (hf : Fn2 w f)
    (hd : ∀ s rs gs, b.decide s rs gs = f s) (hc : b.claims = []) (ha : b.after = []) : Whole2 w b := by
  refine ⟨fun s s' rs gs gs' hs _ => ?_, fun c k => ?_, fun c k => ?_⟩
  · rw [hd, hd]
    exact hf s s' hs
  · rw [hc] at k
    cases k
  · rw [ha] at k
    cases k

/-- The fold's own member without a round has Whole2 where its change of the state has Fn2. -/
theorem quietBlock_whole2 (n : String) (chain : Nat) (link : Option Nat) (piece : Nat)
    {f : σ → Except String σ} (hf : Fn2 w f) : Whole2 w (roundlessBlock (Cl := Cl) n chain link piece f) :=
  quiet_whole2 hf (fun _ _ _ => rfl) rfl rfl

/-- A change of the state that refuses everywhere with one word has Fn2. -/
theorem refuses2 {e : String} : Fn2 w fun _ => (Except.error e : Except String σ) :=
  fun _ _ _ => AlikeE.error e

/-- Whole2 reads a member through decide, claims and after alone. -/
theorem whole_same2 {b c : Block σ Cl} (W : Whole2 w b) (e1 : c.decide = b.decide)
    (e2 : ∀ x ∈ c.claims, x ∈ b.claims) (e3 : c.after = b.after) : Whole2 w c := by
  refine ⟨fun s s' rs gs gs' hs hg => ?_, fun x hx => W.2.1 x (e2 x hx), fun x hx => W.2.2 x (e3 ▸ hx)⟩
  rw [e1]
  exact W.1 s s' rs gs gs' hs hg

/-- A member laid at another type of claims, without its runs of claims, keeps Whole2. -/
theorem retype_whole2 {Cl' : Type} {b : Block σ Cl} (W : Whole2 w b) : Whole2 w (b.retype : Block σ Cl') :=
  ⟨fun s s' rs gs gs' hs hg => W.1 s s' rs gs gs' hs hg, (fun _ hc => nomatch hc), W.2.2⟩

/-- Two members as one have Decides2 where both have. -/
theorem andThen_decides2 (n : String) (p q : Block σ Cl) (P : Decides2 w p) (Q : Decides2 w q) :
    Decides2 w (p.andThen n q) := by
  intro s s' rs gs gs' hs hg
  show AlikeE w
    ((p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun t =>
      q.decide t (rs.drop p.rounds.length) (gs.drop p.openings))
    ((p.decide s' (rs.take p.rounds.length) (gs'.take p.openings)).bind fun t =>
      q.decide t (rs.drop p.rounds.length) (gs'.drop p.openings))
  exact (P s s' _ _ _ hs (hg.take _)).bind fun t t' ht => Q t t' _ _ _ ht (hg.drop _)

/-- Two members as one have Whole2 where both have. -/
theorem andThen_whole2 (n : String) (p q : Block σ Cl) (P : Whole2 w p) (Q : Whole2 w q) :
    Whole2 w (p.andThen n q) :=
  ⟨andThen_decides2 n p q P.1 Q.1,
    fun c hc => (List.mem_append.1 hc).elim (P.2.1 c) (Q.2.1 c),
    fun c hc => (List.mem_append.1 hc).elim (P.2.2 c) (Q.2.2 c)⟩

/-! ## 2 Members that are typed at a part of the state -/

/-- A member with Whole2 v at a part has Whole2 w once lifted, where get and set carry "one under" between w and v. -/
theorem lift_whole2 {v : τ → τ} (get : σ → τ) (set : σ → τ → σ)
    (hg : ∀ s s', w s = w s' → v (get s) = v (get s'))
    (hs : ∀ s s' e e', w s = w s' → v e = v e' → w (set s e) = w (set s' e'))
    {b : Block τ Cl} (B : Whole2 v b) : Whole2 w (b.lift get set) := by
  refine ⟨fun s s' rs gs gs' h hgs => ?_, fun c hc n s s' h => ?_, fun c hc s s' h => ?_⟩
  · show AlikeE w ((b.decide (get s) rs gs).map (set s)) ((b.decide (get s') rs gs').map (set s'))
    exact (B.1 _ _ rs gs gs' (hg s s' h) hgs).map fun e e' he => hs s s' e e' h he
  · obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
    show AlikeE (wCl w) ((c₀.2 n (get s)).map fun y => (y.1, set s y.2))
      ((c₀.2 n (get s')).map fun y => (y.1, set s' y.2))
    refine (B.2.1 c₀ h₀ n _ _ (hg s s' h)).map fun y y' hy => ?_
    show (y.1, w (set s y.2)) = (y'.1, w (set s' y'.2))
    rw [(Prod.mk.inj hy).1, hs s s' y.2 y'.2 h (Prod.mk.inj hy).2]
  · obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
    show AlikeE w ((c₀.2 (get s)).map (set s)) ((c₀.2 (get s')).map (set s'))
    exact (B.2.2 c₀ h₀ _ _ (hg s s' h)).map fun e e' he => hs s s' e e' h he

/-- The like for a part that is there only at times. -/
theorem liftPart_whole2 {v : τ → τ} (get? : σ → Option τ) (set : σ → τ → σ)
    (hg : ∀ s s', w s = w s' → (get? s).map v = (get? s').map v)
    (hs : ∀ s s' e e', w s = w s' → v e = v e' → w (set s e) = w (set s' e'))
    {b : Block τ Cl} (B : Whole2 v b) : Whole2 w (b.liftPart get? set) := by
  refine ⟨fun s s' rs gs gs' h hgs => ?_, fun c hc n s s' h => ?_, fun c hc s s' h => ?_⟩
  · show AlikeE w
      ((VerifiableInference.Desc.named "the part is not there" (get? s)).bind fun p =>
        (b.decide p rs gs).map (set s))
      ((VerifiableInference.Desc.named "the part is not there" (get? s')).bind fun p =>
        (b.decide p rs gs').map (set s'))
    exact (AlikeE.named_alone (hg s s' h)).bind fun p p' hp =>
      (B.1 p p' rs gs gs' hp hgs).map fun e e' he => hs s s' e e' h he
  · obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
    show AlikeE (wCl w)
      ((VerifiableInference.Desc.named "the part is not there" (get? s)).bind fun p =>
        (c₀.2 n p).map fun y => (y.1, set s y.2))
      ((VerifiableInference.Desc.named "the part is not there" (get? s')).bind fun p =>
        (c₀.2 n p).map fun y => (y.1, set s' y.2))
    refine (AlikeE.named_alone (hg s s' h)).bind fun p p' hp =>
      (B.2.1 c₀ h₀ n p p' hp).map fun y y' hy => ?_
    show (y.1, w (set s y.2)) = (y'.1, w (set s' y'.2))
    rw [(Prod.mk.inj hy).1, hs s s' y.2 y'.2 h (Prod.mk.inj hy).2]
  · obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
    show AlikeE w
      ((VerifiableInference.Desc.named "the part is not there" (get? s)).bind fun p => (c₀.2 p).map (set s))
      ((VerifiableInference.Desc.named "the part is not there" (get? s')).bind fun p => (c₀.2 p).map (set s'))
    exact (AlikeE.named_alone (hg s s' h)).bind fun p p' hp =>
      (B.2.2 c₀ h₀ p p' hp).map fun e e' he => hs s s' e e' h he

/-- **A clean part**: w does not touch the part, and laying the part back goes through w: then the lifted member has
Whole2 w. The member at the part is not opened; of its decide it is asked only that it looks at no column. -/
theorem liftPart_clean (get? : σ → Option τ) (set : σ → τ → σ) (hg : ∀ s, get? (w s) = get? s)
    (hs : ∀ s e, set (w s) e = w (set s e)) (b : Block τ Cl) (hn : NoCols b) :
    Whole2 w (b.liftPart get? set) := by
  have B : Whole2 (id : τ → τ) b := by
    refine ⟨fun p p' rs gs gs' hp _ => ?_, fun c _ n p p' hp => ?_, fun c _ p p' hp => ?_⟩
    · have e : p = p' := hp
      subst e
      exact AlikeE.of_same (hn p rs gs gs')
    · have e : p = p' := hp
      subst e
      exact AlikeE.rfl'
    · have e : p = p' := hp
      subst e
      exact AlikeE.rfl'
  refine liftPart_whole2 get? set (fun s s' h => ?_) (fun s s' e e' h he => ?_) B
  · rw [← hg s, ← hg s', h]
  · have e0 : e = e' := he
    subst e0
    rw [← hs s e, ← hs s' e, h]

/-- A member whose own state is born and dies inside it has Whole2 w where enter, its decide and leave have like
outcomes. -/
theorem inside_whole2 {v : τ → τ} (enter : σ → Except String τ) (leave : σ → τ → Except String σ)
    (he : ∀ s s', w s = w s' → AlikeE v (enter s) (enter s'))
    (hl : ∀ s s' t t', w s = w s' → v t = v t' → AlikeE w (leave s t) (leave s' t'))
    {b : Block τ Cl} (B : Decides2 v b) : Whole2 w (b.inside enter leave) := by
  refine ⟨fun s s' rs gs gs' h hgs => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  show AlikeE w ((enter s).bind fun t => (b.decide t rs gs).bind (leave s))
    ((enter s').bind fun t => (b.decide t rs gs').bind (leave s'))
  exact (he s s' h).bind fun t t' ht =>
    (B t t' rs gs gs' ht hgs).bind fun u u' hu => hl s s' u u' h hu

/-! ## 3 The guard on a seat; claims at another type -/

/-- The guard's test has like outcomes where what it reads is the same at states that are one under w. -/
theorem seatSame2 (same : σ → σ → Bool)
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {t t' s s' : σ}
    (ht : w t = w t') (hs : w s = w s') : AlikeE w (seatSame same t s) (seatSame same t' s') := by
  unfold VerifiableInference.Desc.seatSame
  rw [hr t t' s s' ht hs]
  cases same t' s' with
  | true => exact AlikeE.ok hs
  | false => exact AlikeE.error _

/-- A guarded member keeps Decides2, under that premise on the guard. -/
theorem guarded_decides2 (same : σ → σ → Bool) (but : Place → Bool)
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {b : Block σ Cl}
    (W : Decides2 w b) : Decides2 w (b.guarded same but) := by
  intro t t' rs gs gs' ht hg
  show AlikeE w (if but b.place then b.decide t rs gs else (b.decide t rs gs).bind (seatSame same t))
    (if but b.place then b.decide t' rs gs' else (b.decide t' rs gs').bind (seatSame same t'))
  cases but b.place with
  | true => exact W t t' rs gs gs' ht hg
  | false => exact (W t t' rs gs gs' ht hg).bind fun s s' hs => seatSame2 same hr ht hs

/-- A guarded member keeps Whole2, under that premise on the guard. -/
theorem guarded_whole2 (same : σ → σ → Bool) (but : Place → Bool)
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {b : Block σ Cl}
    (W : Whole2 w b) : Whole2 w (b.guarded same but) := by
  refine ⟨guarded_decides2 same but hr W.1, fun c hc n t t' ht => ?_, fun c hc t t' ht => ?_⟩
  · obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
    show AlikeE (wCl w) ((c₀.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y)
      ((c₀.2 n t').bind fun y => (seatSame same t' y.2).map fun _ => y)
    exact (W.2.1 c₀ h₀ n t t' ht).bind fun y y' hy =>
      (seatSame2 same hr ht (Prod.mk.inj hy).2).map fun _ _ _ => hy
  · obtain ⟨c₀, h₀, rfl⟩ := List.mem_map.1 hc
    show AlikeE w ((c₀.2 t).bind (seatSame same t)) ((c₀.2 t').bind (seatSame same t'))
    exact (W.2.2 c₀ h₀ t t' ht).bind fun s s' hs => seatSame2 same hr ht hs

/-- A guarded change of the state keeps Fn2, under that premise on the guard. -/
theorem guardedFn2 (same : σ → σ → Bool)
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {f : σ → Except String σ}
    (F : Fn2 w f) : Fn2 w fun t => (f t).bind (seatSame same t) :=
  fun t t' ht => (F t t' ht).bind fun _ _ hs => seatSame2 same hr ht hs

/-- A member whose runs list forms keeps Whole2 once laid at the one type of a claim. -/
theorem atClaims_whole2 {b : Block σ OnBytes.Model.Aff} (W : Whole2 w b) :
    Whole2 w (OnBytes.Desc.First.K4.atClaims b) := by
  refine ⟨fun s s' rs gs gs' hs hg => W.1 s s' rs gs gs' hs hg, fun c hc n s s' h => ?_, W.2.2⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  show AlikeE (wCl w) ((x.2 n s).map fun y => (y.1.map OnBytes.Desc.First.K4.claimOf, y.2))
    ((x.2 n s').map fun y => (y.1.map OnBytes.Desc.First.K4.claimOf, y.2))
  refine (W.2.1 x hx n s s' h).map fun y y' hy => ?_
  show (y.1.map OnBytes.Desc.First.K4.claimOf, w y.2) = (y'.1.map OnBytes.Desc.First.K4.claimOf, w y'.2)
  rw [(Prod.mk.inj hy).1, (Prod.mk.inj hy).2]

/-! ## 4 At the first chain's state -/

section atS
variable {w : S → S}

/-- A member under the test on the mark of failure keeps Decides2 where states that are one under w bear one mark. -/
theorem guardMark_decides2 (hf : ∀ s s', w s = w s' → s.failed = s'.failed) {b : Block S ProofFile.Cl}
    (W : Decides2 w b) : Decides2 w (ProofFile.guardMark b) := by
  intro s s' rs gs gs' hs hg
  unfold ProofFile.guardMark
  refine AlikeE.bind (W s s' rs gs gs' hs hg) fun t t' ht => ?_
  rw [hf t t' ht]
  cases t'.failed with
  | none => exact AlikeE.ok ht
  | some m => exact AlikeE.error _

/-- A member under the test on the mark of failure keeps Whole2, under the same premise. -/
theorem guardMark_whole2 (hf : ∀ s s', w s = w s' → s.failed = s'.failed) {b : Block S ProofFile.Cl}
    (W : Whole2 w b) : Whole2 w (ProofFile.guardMark b) :=
  ⟨guardMark_decides2 hf W.1, W.2.1, W.2.2⟩

/-- The member, or where there is none the one that refuses every file, has Whole2 where the member has. -/
theorem orLoud_whole2 {n : String} {a : Place} {what : String} {o : Option (Block S Unit)}
    (h : ∀ b, o = some b → Whole2 w b) : Whole2 w (ProofFile.orLoud n a what o) := by
  cases o with
  | some b => exact h b rfl
  | none => exact quiet_whole2 refuses2 (fun _ _ _ => rfl) rfl rfl

/-- A member with a test on the state in front of its decide keeps Whole2 where the test is the same at w s and at s. -/
theorem tested_whole2 {Cl' : Type} (ok : Bool) (start : S → Bool) (before : List (Nat × Nat))
    (hst : ∀ s, start (w s) = start s) {b : Block S Cl'} (W : Whole2 w b) :
    Whole2 w (VerifiableInference.Desc.Kinds.Head.tested ok start before b) := by
  refine ⟨fun s s' rs gs gs' hs hg => ?_, W.2.1, W.2.2⟩
  have e : start s = start s' := by rw [← hst s, ← hst s', hs]
  show AlikeE w (if start s then b.decide s rs gs else Except.error "the request: rows and tokens")
    (if start s' then b.decide s' rs gs' else Except.error "the request: rows and tokens")
  rw [e]
  cases start s' with
  | true => exact W.1 s s' rs gs gs' hs hg
  | false => exact AlikeE.error _

/-- Whether the state stands in the head's segment, and if so whether that is opened. -/
def openedAt (s : S) : Option Bool :=
  match s.here with
  | .head o => some o.opened
  | _ => none

/-- The test in front of the reply's member reads openedAt alone. -/
theorem entered_decide (b : Block S Unit) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (VerifiableInference.Desc.Kinds.Reply.entered b).decide s rs gs =
      match openedAt s with
      | some true => Except.error "the next token: the head's link is not yet opened"
      | some false => b.decide s rs gs
      | none => Except.error "the next token: the head's link is entered" := by
  show (match s.here with
    | .head o =>
      if o.opened then Except.error "the next token: the head's link is not yet opened" else b.decide s rs gs
    | _ => Except.error "the next token: the head's link is entered" : Except String S) = _
  unfold openedAt
  cases s.here with
  | head o =>
    dsimp only
    cases o.opened <;> rfl
  | _ => rfl

/-- A member under the test that the head's segment is entered and not yet opened keeps Whole2 where openedAt is the
same at w s and at s. -/
theorem entered_whole2 (ho : ∀ s, openedAt (w s) = openedAt s) {b : Block S Unit} (W : Whole2 w b) :
    Whole2 w (VerifiableInference.Desc.Kinds.Reply.entered b) := by
  refine ⟨fun s s' rs gs gs' hs hg => ?_, W.2.1, W.2.2⟩
  have e : openedAt s = openedAt s' := by rw [← ho s, ← ho s', hs]
  rw [entered_decide, entered_decide, e]
  cases openedAt s' with
  | none => exact AlikeE.error _
  | some o =>
    cases o with
    | true => exact AlikeE.error _
    | false => exact W.1 s s' rs gs gs' hs hg

end atS

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.quiet_whole2
#print axioms ProofFile.Honest.K10.quietBlock_whole2
#print axioms ProofFile.Honest.K10.refuses2
#print axioms ProofFile.Honest.K10.whole_same2
#print axioms ProofFile.Honest.K10.retype_whole2
#print axioms ProofFile.Honest.K10.andThen_decides2
#print axioms ProofFile.Honest.K10.andThen_whole2
#print axioms ProofFile.Honest.K10.lift_whole2
#print axioms ProofFile.Honest.K10.liftPart_whole2
#print axioms ProofFile.Honest.K10.liftPart_clean
#print axioms ProofFile.Honest.K10.inside_whole2
#print axioms ProofFile.Honest.K10.seatSame2
#print axioms ProofFile.Honest.K10.guarded_decides2
#print axioms ProofFile.Honest.K10.guarded_whole2
#print axioms ProofFile.Honest.K10.guardedFn2
#print axioms ProofFile.Honest.K10.atClaims_whole2
#print axioms ProofFile.Honest.K10.guardMark_decides2
#print axioms ProofFile.Honest.K10.guardMark_whole2
#print axioms ProofFile.Honest.K10.orLoud_whole2
#print axioms ProofFile.Honest.K10.tested_whole2
#print axioms ProofFile.Honest.K10.openedAt
#print axioms ProofFile.Honest.K10.entered_decide
#print axioms ProofFile.Honest.K10.entered_whole2
