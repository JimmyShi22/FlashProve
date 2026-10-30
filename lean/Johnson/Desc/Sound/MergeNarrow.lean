-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeNarrow.lean: A BLOCK THAT REFUSES MORE OWES NO MORE, AND WHAT ITS YES ADDS
MAY BE PROMISED BEHIND IT. Small lemmas and one rule.

Why. A seat lays guards around a kind's block: a yes only if the record behind bears no mark; only
if a field is left as it was; only if every word that was shown is written canonically (`below`).
Each such block has the kind's declared rounds, and says yes only where the kind's block says yes,
with the same record. What a piece owes (`Piece.GoodIn`) speaks of the verifier's yes alone: so the
law that was proved of the kind's block holds of the guarded one, at the same errors and extractor;
and whatever the guard's yes gives of the record behind may be added to the promise there.

Main names:
  `Block.Narrows b' b`: the same declared rounds; where `b'.decide` gives `.ok s'`, so does
    `b.decide`.
  `lift_narrows`, `liftPart_narrows`: narrowing passes `Block.lift` and `Block.liftPart`.
  `step_narrows`, `chainAt_narrows`; `chainAt_yes`: a yes of the fold over one block is a yes of its
    `decide`.
  `out_narrow`: where the piece at the narrower block puts out, the piece itself puts out the same.
  `out_yes`: where a piece puts out, its block's `decide` has returned that record.
  **`goodIn_narrow`**: `p.GoodIn on on' R R'`, `B'.Narrows p.b`, and G of every record that
    `B'.decide` returns: then `{ p with b := B' }.GoodIn on (fun b => on' b ∧ G b.1) R R'`.
  `below_narrows`: the strict reading `below b` narrows b. `bind_narrows`: so does b with a test
    behind its `decide` that hands the record on as it is or refuses.

Limits: the way back does not hold: a law of the guarded block says nothing of the bare one. G READS
THE RECORD BEHIND ALONE: what a guard gains on both records ("the field is as it was in front") is
not promised by this rule: the law carries over, that gain does not. Of a piece's debt alone, as
Johnson/Desc/Sound/MergeSame.lean. THE RULE MAKES NO BLOCK COMPLETE: a guard
that refuses an honest run passes this rule as any other. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeSameYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- b' has b's declared rounds and says yes only where b does, with the same record. -/
def Block.Narrows (b' b : Block S Cl) : Prop :=
  b'.rounds = b.rounds ∧ ∀ s rs gs s', b'.decide s rs gs = .ok s' → b.decide s rs gs = .ok s'

theorem step_narrows {b' b : Block S Cl} (h : b'.Narrows b) (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    b'.step ft s rs cols = .ok (s', k) → b.step ft s rs cols = .ok (s', k) := by
  rw [step_iff, step_iff]
  unfold Block.Fits Block.shown Block.want
  rw [h.1]
  rintro ⟨hf, hd, hk⟩
  exact ⟨hf, h.2 _ _ _ _ hd, hk⟩

theorem chainAt_narrows (n n' : String) (ft : Nat) {b' b : Block S Cl} (h : b'.Narrows b)
    (s s' : S) (v : Fmt.View) :
    chainAt n' ft [b'] s v = .ok s' → chainAt n ft [b] s v = .ok s' := by
  rw [Merges.chainAt_iff, Merges.chainAt_iff, Merges.foldCons_iff, Merges.foldCons_iff, h.1]
  rintro ⟨-, hl, s₁, k, hs, hr⟩
  exact ⟨rfl, hl, s₁, k, step_narrows h ft _ _ _ _ _ hs, hr⟩

/-- Narrowing passes a lift. -/
theorem lift_narrows {T : Type} (get : T → S) (set : T → S → T) {b' b : Block S Cl}
    (h : b'.Narrows b) : (b'.lift get set).Narrows (b.lift get set) := by
  refine ⟨h.1, fun t rs gs t' e => ?_⟩
  have e' : (b'.decide (get t) rs gs).map (set t) = .ok t' := e
  obtain ⟨s', hs, rfl⟩ := (Except.map_eq_ok _ _ _).1 e'
  show (b.decide (get t) rs gs).map (set t) = .ok (set t s')
  rw [h.2 _ _ _ _ hs]
  rfl

/-- Narrowing passes a lift from a part that is there only at times. -/
theorem liftPart_narrows {T : Type} (get? : T → Option S) (set : T → S → T) {b' b : Block S Cl}
    (h : b'.Narrows b) : (b'.liftPart get? set).Narrows (b.liftPart get? set) := by
  refine ⟨h.1, fun t rs gs t' e => ?_⟩
  have e' : (named "the part is not there" (get? t)).bind
      (fun p => (b'.decide p rs gs).map (set t)) = .ok t' := e
  obtain ⟨p, hp, hq⟩ := (Except.bind_eq_ok _ _ _).1 e'
  obtain ⟨s', hs, rfl⟩ := (Except.map_eq_ok _ _ _).1 hq
  show (named "the part is not there" (get? t)).bind
      (fun p => (b.decide p rs gs).map (set t)) = .ok (set t s')
  rw [hp]
  show (b.decide p rs gs).map (set t) = .ok (set t s')
  rw [h.2 _ _ _ _ hs]
  rfl

/-- A yes of the fold over one block is a yes of the block's `decide`, with that record. -/
theorem chainAt_yes (n : String) (ft : Nat) (b : Block S Cl) (s s' : S) (v : Fmt.View) :
    chainAt n ft [b] s v = .ok s' → ∃ rs gs, b.decide s rs gs = .ok s' := by
  rw [Merges.chainAt_iff, Merges.foldCons_iff]
  rintro ⟨-, -, s₁, k, hs, hr⟩
  rw [foldBlocks] at hr
  have e : s₁ = s' := congrArg Prod.fst (Except.ok.inj hr)
  subst e
  exact ⟨_, _, ((step_iff ft b s s₁ _ _ k).1 hs).2.1⟩

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

variable {S Cl W : Type} {C : CK} {F : Frame}

private theorem toOption_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | ok b => cases h; rfl
  | error e => cases h

/-- Where a stage puts out, its decision has returned the record that is put out. -/
theorem stage_run (St : StageD) (r : S → Fmt.View → Option S) (a : S × St.Ei.Str)
    (b : S × St.Eo.Str) (τ : Iop.Tr (uLT C St.ds))
    (h : (stageIOR C St r).red.out a τ = some b) : r a.1 (sView C St a.2 τ) = some b.1 := by
  have h' : ((stageIOR C St r).out a.1 a.2 τ).map
      (fun xo => (xo, (stageIOR C St r).imp a.2 τ)) = some b := h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h'
  have hx' : (if sTests C St a.2 τ then r a.1 (sView C St a.2 τ) else none) = some x := hx
  split at hx'
  · exact hx'
  · cases hx'

/-- A decision that returns less puts out less. -/
theorem stage_narrow (St : StageD) (r r' : S → Fmt.View → Option S)
    (h : ∀ s v t, r' s v = some t → r s v = some t) (a : S × St.Ei.Str) (b : S × St.Eo.Str)
    (τ : Iop.Tr (uLT C St.ds)) (e : (stageIOR C St r').red.out a τ = some b) :
    (stageIOR C St r).red.out a τ = some b := by
  have e' : ((stageIOR C St r').out a.1 a.2 τ).map
      (fun xo => (xo, (stageIOR C St r').imp a.2 τ)) = some b := e
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 e'
  have hx' : (if sTests C St a.2 τ then r' a.1 (sView C St a.2 τ) else none) = some x := hx
  show ((if sTests C St a.2 τ then r a.1 (sView C St a.2 τ) else none).map _) = _
  split at hx'
  · rename_i ht
    rw [if_pos ht, h _ _ _ hx']
    rfl
  · cases hx'

/-- **Where the piece at the narrower block puts out, the piece itself puts out the same.** For
every notion that reads a piece through "out a τ = some b" alone. -/
theorem out_narrow (p : Piece C F S Cl W) (B' : Block S Cl) (h : B'.Narrows p.b)
    (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : ({ p with b := B' } : Piece C F S Cl W).ior.red.out a τ = some b) :
    p.ior.red.out a τ = some b := by
  have hb₁ :
      (stageIOR C p.stage ({ p with b := B' } : Piece C F S Cl W).run).red.out a τ = some b := hb
  have hn : ∀ s v t, ({ p with b := B' } : Piece C F S Cl W).run s v = some t →
      p.run s v = some t := by
    intro s v t e
    have e₁ : chainAt B'.name F.ft [B'] s ⟨v.rounds ++ p.back, v.opened⟩ = .ok t := toOption_some e
    show (chainAt p.b.name F.ft [p.b] s ⟨v.rounds ++ p.back, v.opened⟩).toOption = some t
    rw [chainAt_narrows p.b.name B'.name F.ft h s t _ e₁]
    rfl
  exact stage_narrow p.stage p.run _ hn a b τ hb₁

/-- Where a piece puts out, its block's `decide` has returned the record that is put out. -/
theorem out_yes (p : Piece C F S Cl W) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) : ∃ rs gs, p.b.decide a.1 rs gs = .ok b.1 :=
  chainAt_yes p.b.name F.ft p.b a.1 b.1 _ (toOption_some (stage_run p.stage p.run a b τ hb))

/-- **A BLOCK THAT REFUSES MORE OWES NO MORE; WHAT ITS YES ADDS MAY BE PROMISED BEHIND IT.** -/
theorem goodIn_narrow (p : Piece C F S Cl W) (B' : Block S Cl) (h : B'.Narrows p.b)
    (G : S → Prop) (hG : ∀ s rs gs s', B'.decide s rs gs = .ok s' → G s')
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R') :
    ({ p with b := B' } : Piece C F S Cl W).GoodIn on (fun b => on' b ∧ G b.1) R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (g a ha)
  intro τ hτ b hb
  have hb₂ : p.ior.red.out a τ = some b := out_narrow p B' h a b τ hb
  obtain ⟨rs, gs, hd⟩ := out_yes ({ p with b := B' } : Piece C F S Cl W) a b τ hb
  exact ⟨⟨(hτ b hb₂).1, hG _ _ _ _ hd⟩, (hτ b hb₂).2⟩

/-- The strict reading narrows. -/
theorem below_narrows (b : Block S Cl) : (below b).Narrows b := by
  refine ⟨rfl, fun s rs gs s' h => ?_⟩
  have h' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide s rs gs
      else .error "a word is not below the prime") = .ok s' := h
  split at h'
  · exact h'
  · cases h'

/-- A test behind `decide` that hands the record on as it is, or refuses, narrows. k: from the
record in front and the record behind. -/
theorem bind_narrows (b : Block S Cl) (k : S → S → Except String S)
    (hk : ∀ s t t', k s t = .ok t' → t' = t) :
    ({ b with decide := fun s rs gs => (b.decide s rs gs).bind (k s) } : Block S Cl).Narrows b := by
  refine ⟨rfl, fun s rs gs s' h => ?_⟩
  have h' : (b.decide s rs gs).bind (k s) = .ok s' := h
  cases hd : b.decide s rs gs with
  | error e => rw [hd] at h'; cases h'
  | ok t =>
    rw [hd] at h'
    have e : s' = t := hk s t s' h'
    rw [e]


end VerifiableInference.Desc.Sound
