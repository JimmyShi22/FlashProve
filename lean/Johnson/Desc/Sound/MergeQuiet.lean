-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeQuiet.lean: A BLOCK, AND BEHIND IT A STEP WITHOUT A ROUND, AS ONE BLOCK:
what a piece owes at the block gives what it owes at the two joined, at the same rounds, errors and
extractor. Small lemmas and one rule.

Why. A place of a chain can hold more than its kind's rounds: behind the hearing the verifier
compares public numbers or lays a claim, without hearing anything
(`b.andThen n (roundlessBlock … f)`; Johnson/Desc/First/Look/K3Whole.lean is such a text). A kind's law
is proved of b. Johnson/Desc/Sound/MergeFuse.lean carries it to the joined block at a piece of its
own make, with casts; a row's real piece is GIVEN, with the errors and the extractor that it has.
This rule speaks of the given piece: the block alone is exchanged.

Main names:
  `chainAt_thenQuiet`: a yes of the fold over the joined block is a yes of the fold over b, at the
    same view, with a record s', and f s' returns the joined block's record.
  `out_thenQuiet`: the like for a piece's output: the strings behind are the same.
  **`goodIn_thenQuiet`**: `p.GoodIn on on' R R'`, and of the step: where f s' = .ok t, the promise
    on' at (s', y) gives on'' at (t, y), and every witness of R'' at (t, y) is one of R' at (s', y):
    then `{ p with b := p.b.andThen n (roundlessBlock …) }.GoodIn on on'' R R''`.
  `below_thenQuiet_narrows`, **`goodIn_below_thenQuiet`**: the same from a law of `below b` to the
    law of `below (b.andThen n (roundlessBlock …))`: the form that a description's piece holds.

Limits: one step without a round, BEHIND the block; a step in front is not served. What is asked of
the step is asked at every record s' and all strings y, reached or not: a step whose law needs more
takes it into on'. Of a piece's debt alone, as Johnson/Desc/Sound/MergeSame.lean. Nothing on
acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- A yes of the fold over `b.andThen n (roundlessBlock … f)` is a yes of the fold over b, then of f. -/
theorem chainAt_thenQuiet (n' n₀ : String) (ft : Nat) (b : Block S Cl) (n nq : String) (c : Nat)
    (link : Option Nat) (piece : Nat) (f : S → Except String S) (s t : S) (v : Fmt.View)
    (h : chainAt n' ft [b.andThen n (roundlessBlock nq c link piece f)] s v = .ok t) :
    ∃ s', chainAt n₀ ft [b] s v = .ok s' ∧ f s' = .ok t := by
  have hm : Merges [b, roundlessBlock nq c link piece f] [b.andThen n (roundlessBlock nq c link piece f)] :=
    Merges.step [] n b (roundlessBlock nq c link piece f) [] _ (Merges.refl _)
  have h2 := (hm.chainAt n' ft s t v).2 h
  rw [Merges.chainAt_iff, Merges.foldCons_iff] at h2
  obtain ⟨-, hl, s', k, hs, hr⟩ := h2
  rw [Merges.foldCons_iff] at hr
  obtain ⟨-, t', k', hq, he⟩ := hr
  rw [foldBlocks] at he
  have he' := Except.ok.inj he
  have e1 : t' = t := congrArg Prod.fst he'
  have e2 : ((v.rounds.drop b.rounds.length).drop
      (roundlessBlock nq c link piece f : Block S Cl).rounds.length) = [] :=
    congrArg (fun x => x.2.1) he'
  have e3 : ((v.opened.drop k).drop k') = [] := congrArg (fun x => x.2.2) he'
  obtain ⟨-, hd, hk'⟩ := (step_iff ft _ s' t' _ _ k').1 hq
  have hk0 : k' = 0 := hk'
  subst hk0
  subst e1
  refine ⟨s', ?_, hd⟩
  rw [Merges.chainAt_iff, Merges.foldCons_iff]
  refine ⟨rfl, hl, s', k, hs, ?_⟩
  rw [foldBlocks]
  have e2' : v.rounds.drop b.rounds.length = [] := e2
  have e3' : v.opened.drop k = [] := e3
  rw [e2', e3']

/-- The test on the words holds of a front part of what it holds of. -/
theorem okViewW_take (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (n m : Nat)
    (h : viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true) :
    viewWordsBelowPrime ⟨rs.take n, ((gs.take m).flatMap id).map fun c => (0, c.1, c.2)⟩ = true := by
  unfold viewWordsBelowPrime at h ⊢
  dsimp only at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [List.all_eq_true] at h1 ⊢
    intro r hr
    exact h1 r (List.mem_of_mem_take hr)
  · rw [List.all_eq_true] at h2 ⊢
    intro o ho
    apply h2 o
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    obtain ⟨g, hg, hcg⟩ := List.mem_flatMap.1 hc
    exact List.mem_map.2 ⟨c, List.mem_flatMap.2 ⟨g, List.mem_of_mem_take hg, hcg⟩, rfl⟩

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

variable {S Cl W : Type} {C : CK} {F : Frame}

private theorem ok_of_toOption {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | ok b => cases h; rfl
  | error e => cases h

/-- A decision that is another one's, then a step: so is what the stage puts out; the strings behind
are the same. -/
theorem stage_then (St : StageD) (r r' : S → Fmt.View → Option S) (P : S → S → Prop)
    (h : ∀ s v t, r' s v = some t → ∃ s', r s v = some s' ∧ P s' t) (a : S × St.Ei.Str)
    (b : S × St.Eo.Str) (τ : Iop.Tr (uLT C St.ds))
    (e : (stageIOR C St r').red.out a τ = some b) :
    ∃ s', (stageIOR C St r).red.out a τ = some (s', b.2) ∧ P s' b.1 := by
  have e' : ((stageIOR C St r').out a.1 a.2 τ).map
      (fun xo => (xo, (stageIOR C St r').imp a.2 τ)) = some b := e
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 e'
  have hx' : (if sTests C St a.2 τ then r' a.1 (sView C St a.2 τ) else none) = some x := hx
  split at hx'
  · rename_i ht
    obtain ⟨s', hs', hP⟩ := h _ _ _ hx'
    refine ⟨s', ?_, hP⟩
    show ((if sTests C St a.2 τ then r a.1 (sView C St a.2 τ) else none).map _) = _
    rw [if_pos ht, hs']
    rfl
  · cases hx'

/-- Where the piece at the joined block puts out, the piece itself puts out, with the same strings,
a record from which the step returns the joined block's. -/
theorem out_thenQuiet (p : Piece C F S Cl W) (n nq : String) (c : Nat) (link : Option Nat)
    (piece : Nat) (f : S → Except String S) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : ({ p with b := p.b.andThen n (roundlessBlock nq c link piece f) } :
      Piece C F S Cl W).ior.red.out a τ = some b) :
    ∃ s', p.ior.red.out a τ = some (s', b.2) ∧ f s' = .ok b.1 := by
  have hn : ∀ s v t, ({ p with b := p.b.andThen n (roundlessBlock nq c link piece f) } :
      Piece C F S Cl W).run s v = some t → ∃ s', p.run s v = some s' ∧ f s' = .ok t := by
    intro s v t e
    obtain ⟨s', h1, h2⟩ := chainAt_thenQuiet _ p.b.name F.ft p.b n nq c link piece f s t
      ⟨v.rounds ++ p.back, v.opened⟩ (ok_of_toOption e)
    refine ⟨s', ?_, h2⟩
    show (chainAt p.b.name F.ft [p.b] s ⟨v.rounds ++ p.back, v.opened⟩).toOption = some s'
    rw [h1]
    rfl
  exact stage_then p.stage p.run _ (fun s' t => f s' = .ok t) hn a b τ hb

/-- **WHAT A PIECE OWES AT A BLOCK GIVES WHAT IT OWES AT THE BLOCK WITH A STEP WITHOUT A ROUND
BEHIND IT.** -/
theorem goodIn_thenQuiet (p : Piece C F S Cl W) (n nq : String) (c : Nat) (link : Option Nat)
    (piece : Nat) (f : S → Except String S) (on on' on'' : S × F.E.Str → Prop)
    (R R' R'' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R')
    (hq : ∀ s' t y, f s' = .ok t → on' (s', y) →
      on'' (t, y) ∧ ∀ w, R'' (t, y) w → R' (s', y) w) :
    ({ p with b := p.b.andThen n (roundlessBlock nq c link piece f) } :
      Piece C F S Cl W).GoodIn on on'' R R'' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (g a ha)
  intro τ hτ b hb
  obtain ⟨s', h1, h2⟩ := out_thenQuiet p n nq c link piece f a b τ hb
  obtain ⟨ho, hw⟩ := hτ (s', b.2) h1
  obtain ⟨ho', hw'⟩ := hq s' b.1 b.2 h2 ho
  exact ⟨ho', fun w hR => hw w (hw' w hR)⟩

/-- The strict reading of the joined block narrows the strict reading of the block, joined. -/
theorem below_thenQuiet_narrows (b : Block S Cl) (n nq : String) (c : Nat) (link : Option Nat)
    (piece : Nat) (f : S → Except String S) :
    (below (b.andThen n (roundlessBlock nq c link piece f))).Narrows
      ((below b).andThen n (roundlessBlock nq c link piece f)) := by
  refine ⟨rfl, fun s rs gs t h => ?_⟩
  have h' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then
      (b.andThen n (roundlessBlock nq c link piece f)).decide s rs gs
      else .error "a word is not below the prime") = .ok t := h
  split at h'
  · rename_i hk
    have h2 : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s' => f s') = .ok t := h'
    have e : (below b).decide s (rs.take b.rounds.length) (gs.take b.openings) =
        b.decide s (rs.take b.rounds.length) (gs.take b.openings) := by
      show (if viewWordsBelowPrime ⟨rs.take b.rounds.length,
                      ((gs.take b.openings).flatMap id).map fun c => (0, c.1, c.2)⟩ then
          b.decide s (rs.take b.rounds.length) (gs.take b.openings)
          else .error "a word is not below the prime") = _
      rw [if_pos (okViewW_take rs gs _ _ hk)]
    show ((below b).decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s' => f s') = .ok t
    rw [e]
    exact h2
  · cases h'

/-- **The rule at the strict readings**: a law of `below b` gives the law of `below` of the joined
block: what a description's piece holds where a place's block is a hearing and a step behind it. -/
theorem goodIn_below_thenQuiet (p : Piece C F S Cl W) (b : Block S Cl) (hb : p.b = below b)
    (n nq : String) (c : Nat) (link : Option Nat) (piece : Nat) (f : S → Except String S)
    (on on' on'' : S × F.E.Str → Prop) (R R' R'' : S × F.E.Str → W → Prop)
    (g : p.GoodIn on on' R R')
    (hq : ∀ s' t y, f s' = .ok t → on' (s', y) →
      on'' (t, y) ∧ ∀ w, R'' (t, y) w → R' (s', y) w) :
    ({ p with b := below (b.andThen n (roundlessBlock nq c link piece f)) } :
      Piece C F S Cl W).GoodIn on on'' R R'' := by
  have g2 := goodIn_thenQuiet p n nq c link piece f on on' on'' R R' R'' g hq
  rw [hb] at g2
  intro a ha
  refine Doomed.mono _ _ ?_ (g2 a ha)
  intro τ hτ b' hb'
  exact hτ b' (out_narrow
    ({ p with b := (below b).andThen n (roundlessBlock nq c link piece f) } : Piece C F S Cl W)
    (below (b.andThen n (roundlessBlock nq c link piece f)))
    (below_thenQuiet_narrows b n nq c link piece f) a b' τ hb')


end VerifiableInference.Desc.Sound
