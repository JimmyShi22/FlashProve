-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoRds.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoRds.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  took_nil, took_cons, evs_two, evs_head, rds_took, HCout2R, HCout2V, hcOut2V_of, hcOut2_of
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  HeardIs, PadLeft, ShapeOf, Sized, drawnOf, endsOf, flEv, planF, rdRV, sentOf
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoHeard

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem took_nil {c : Tape} (h : Clean c) : Took c [] c := ⟨h, h, rfl⟩

theorem took_cons {c c₁ c' : Tape} {rv : FlatRound} {rvs : List FlatRound} (h1 : Round c rv c₁)
    (h2 : Took c₁ rvs c') : Took c (rv :: rvs) c' :=
  ⟨h1.1, h2.2.1, by rw [h1.2.2, h2.2.2]; rfl⟩

/-- Two calls, then the rest. -/
theorem evs_two {e₁ e₂ : Ev} {l : List Ev} {c c' : Tape} (h : Evs (e₁ :: e₂ :: l) c c') :
    ∃ c₁, Evs [e₁, e₂] c c₁ ∧ Evs l c₁ c' :=
  (evs_append [e₁, e₂] l c c').1 h

theorem evs_head {e : Ev} {l : List Ev} {c c' : Tape} (h : Evs (e :: l) c c') :
    ∃ c₁, Evs [e] c c₁ ∧ Evs l c₁ c' :=
  (evs_append [e] l c c').1 h

/-- A row of rounds takes its rounds off the view. -/
theorem rds_took {l : List Ev} (hl : Rds l) : ∀ {c c' : Tape}, Clean c → Evs l c c' →
    ∃ rv, Took c rv c' ∧ flEv ρ l = rv.map (rdRV ρ) := by
  induction hl with
  | nil =>
    intro c c' hc h
    obtain rfl : c' = c := h
    exact ⟨[], took_nil hc, rfl⟩
  | read n v r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_read n v r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ v.toList.map ρ.val, [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | readNZ n v r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_readNZ n v r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ v.toList.map ρ.val, [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | values n v r _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_values n v r c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ v.toList.map ρ.val, []) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | sum mu r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_two h
    obtain ⟨rv, hr, hs, hd⟩ := round_sum mu r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([] ++ [ρ.val mu], [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | ans r x _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_head h
    obtain ⟨rv, hr, hs, hd⟩ := round_ans r x c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([], [ρ.val x]) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl
  | point r n v _ ih =>
    intro c c' hc h
    obtain ⟨c₁, h1, h2⟩ := evs_head h
    obtain ⟨rv, hr, hs, hd, _⟩ := round_point r n v c c₁ hc h1
    obtain ⟨rvs, ht, he⟩ := ih hr.2.1 h2
    refine ⟨rv :: rvs, took_cons hr ht, ?_⟩
    show ([], v.toList.map ρ.val) :: flEv ρ _ = rdRV ρ rv :: rvs.map (rdRV ρ)
    rw [he, rdRV, hs, hd]
    rfl

end

/-- Over the calls of a run, which are a row of rounds. -/
def HCout2R : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (F F' : Fork) (c c' : Tape) (g : Forest.Heard),
    lkPad calls pub lid F c = .ok ((g, F'), c') → Sized F → Clean c →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    ∃ l : List Ev, Evs l c c' ∧ Rds l ∧
      (flEv ρ l).map (fun r => (r.1.length, r.2.length)) = planF g.shape ∧
      HeardIs ρ g F' (endsOf g.shape lm F.next (flEv ρ l))

/-- Over the view, from a context on a view with no message open. -/
def HCout2V : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : Reading K) (calls : Array Call) (pub : Array Nat) (lid lm : ℕ)
    (F F' : Fork) (c c' : Tape) (g : Forest.Heard),
    lkPad calls pub lid F c = .ok ((g, F'), c') → Sized F → Clean c →
    ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
    ∃ rv : List FlatRound, Took c rv c' ∧
      rv.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      HeardIs ρ g F' (endsOf g.shape lm F.next (rv.map (rdRV ρ)))

theorem hcOut2V_of (h : HCout2R) : HCout2V := by
  intro K _ ρ calls pub lid lm F F' c c' g hr hF hc
  obtain ⟨h1, h2, l, hl, hR, hs, hH⟩ := h K ρ calls pub lid lm F F' c c' g hr hF hc
  obtain ⟨rv, ht, he⟩ := rds_took ρ hR hc hl
  refine ⟨h1, h2, rv, ht, ?_, he ▸ hH⟩
  rw [he, List.map_map] at hs
  rw [← hs]
  refine List.map_congr_left fun r _ => ?_
  simp [rdRV]

/-- HCout2 (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean), in which the rounds taken are given, follows.
-/
theorem hcOut2_of (h : HCout2V) : HCout2 := by
  intro K _ ρ calls pub lid lm F F' c c' g rv hr hF ht
  obtain ⟨h1, h2, rv', ht', _, hH⟩ := h K ρ calls pub lid lm F F' c c' g hr hF ht.1
  have e : rv' = rv := List.append_cancel_right (ht'.2.2.symm.trans ht.2.2)
  exact ⟨h1, h2, e ▸ hH⟩


end Fo.Tp
