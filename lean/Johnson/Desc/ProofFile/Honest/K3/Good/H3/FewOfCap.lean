-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/FewOfCap.lean: the kind "lookup" (K3): the hypotheses of
the marks' bounds on single events (`FewAt`, `FewAll`, Honest/K3/Good/MarkShare.lean; the first half
of `FewOut`, Honest/K3/Good/MarkOut.lean), from a hypothesis on the kit (`KitCap`) and one on the
letter kap (`CapsUnder`; both Honest/K3/Good/H3/Defs.lean). Conditional. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), spot, event, sample, share and
kit. In this file: f is a lookup's face, C a kit, es the plan's entries at the lookup, dsb the data
of the rounds of the lookup's member; cap and kap are letters.

What is shown.
  `fewAt_of_cap`: one event.
  `fewAll_of_cap`: all events of the first mark.
  `fewOutEvents_of_cap`: all events of the second mark that read one round's sample.
Helpers: `fits_at` (the datum at a round's number), `spot_of_mem`.

Hypotheses that remain.
  `hcap`: `KitCap C cap`. At strings of hash blocks it can be had by one call of
    `P1K8.kit_count_blocks` (Johnson/P1K8R/KitCount.lean); not called here.
  `hes`, `hk`: the plan's entries pass the verifier's test; the data bear them.
  `hkap`: `CapsUnder cap f es kap`: not shown by anybody; kap is a letter.
  `hl`: (in `fewAt_of_cap`) the event's spot is laid. `h2`, `h1`: as in Spots.lean.

The default. An event reads its round's sample as `(R.elems.map E.ofTriple).getD e.spot.draw zeroE`
(`Event.shows`, Honest/K3/Good/MarkEvents.lean). In `fewAt_of_cap` that number is bounded by `hl`,
with `hes` and `hk`: the datum's entry draws more elements, all by the even rule.

Imported: the files of Honest/K3/Good/ beneath.

Users. Honest/K3/Good/H3/Member.lean.

Limits. Implications. cap and kap are letters: no number is named or evaluated. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Spots
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Entries
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.IsElAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open scoped ENNReal
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-- The datum at a declared round's number bears that round. -/
theorem fits_at {dsb : List RDT} {zs : List Fmt.DeclaredRound} (h : List.Forall₂ KindFits dsb zs) :
    ∀ (n : Nat) (z : Fmt.DeclaredRound), zs[n]? = some z →
      ∃ (a : List RDT) (d : RDT) (b : List RDT),
        dsb = a ++ d :: b ∧ a.length = n ∧ KindFits d z := by
  induction h with
  | nil =>
    intro n z hz
    simp at hz
  | @cons x y l₁ l₂ h1 _ ih =>
    intro n z hz
    cases n with
    | zero =>
      rw [List.getElem?_cons_zero] at hz
      obtain rfl := Option.some.inj hz
      exact ⟨[], x, l₁, rfl, rfl, h1⟩
    | succ n =>
      rw [List.getElem?_cons_succ] at hz
      obtain ⟨a, d, b, e1, e2, e3⟩ := ih n z hz
      exact ⟨x :: a, d, b, by rw [e1]; rfl, by rw [List.length_cons, e2], e3⟩

/-- An event at a spot is that spot's. -/
theorem spot_of_mem {p : Spot} {e : Event} (h : e ∈ eventsAtSpot p) : e.spot = p := by
  unfold eventsAtSpot at h
  rcases List.mem_cons.1 h with rfl | h
  · rfl
  · split at h
    · obtain rfl := List.mem_singleton.1 h
      rfl
    · exact absurd h List.not_mem_nil

/-- CONDITIONAL on KitCap, on the plan's entries, on the data, on CapsUnder and on the spot being
laid: of its round's challenges at most the share kap show the event. -/
theorem fewAt_of_cap (C : CK) (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (hcap : KitCap C cap)
    (f : LFace) (es : List Fmt.Entry) (hes : entriesFit f es = true) (dsb : List RDT)
    (hk : List.Forall₂ KindFits dsb (es.map Law.declOf)) (kap : ℝ≥0∞)
    (hkap : CapsUnder cap f es kap) (e : Event) (he : e ∈ eventsOf f ++ outEvents f)
    (hl : SpotLaid f e.spot) : FewAt C f dsb kap e := by
  unfold SpotLaid at hl
  obtain ⟨en, hen, hz, hd⟩ := hl
  obtain ⟨e', he', e2⟩ := fit_at f es hes _ en hen
  have hzs : (es.map Law.declOf)[e.round f]? = some (Law.declOf e') := by
    unfold Event.round
    rw [List.getElem?_map, he']
    rfl
  obtain ⟨a, d, b, e1, ea, hd1, hd2⟩ := fits_at hk _ _ hzs
  have hd1' : d.entry = e' := hd1
  have hd2' : Fmt.kindOf e'.name = some d.kind := hd2
  obtain ⟨t1, _, k0, t3, _, t4⟩ := entriesV_tame f en (List.mem_of_getElem? hen)
  have n1 : e'.name = en.name := congrArg (·.name) e2
  have n2 : e'.drawE = en.drawE := congrArg (·.drawE) e2
  have n3 : e'.drawNZ = en.drawNZ := congrArg (·.drawNZ) e2
  have n4 : e'.logN = en.logN := congrArg (·.logN) e2
  have hk0 : d.kind = k0 := by
    rw [n1, t3] at hd2'
    exact (Option.some.inj hd2').symm
  have hi : P1K8.IsEl (Fmt.dsOf d.entry d.kind) e.spot.draw := by
    refine isEl_dsOf _ _ (by rw [hk0]; exact t4) _ ?_
    rw [hd1', n2, n3, hz]
    exact hd
  have hlog : d.entry.logN ≤ 64 := by
    rw [hd1', n4, t1]
    exact Nat.zero_le _
  have hmem : e.round f ∈ capRounds f := by
    unfold capRounds
    exact List.mem_append_left _ (List.mem_map.2 ⟨e, he, rfl⟩)
  have hcapk : cap d.entry d.kind ≤ kap := by
    rw [hd1']
    exact hkap (e.round f) hmem e' he' d.kind hd2'
  unfold FewAt
  refine ⟨a, d, b, e1, ea, le_trans ?_ hcapk⟩
  cases ho : e.atOne with
  | false =>
    exact hcap d.entry d.kind hlog e.spot.draw hi 0 (fun R => e.shows R = true)
      (fun R _ hlen hs => by
        refine P1K8.atEl_zero e.spot.draw R hlen ?_
        unfold Event.shows Event.test at hs
        rw [ho] at hs
        exact hs)
  | true =>
    exact hcap d.entry d.kind hlog e.spot.draw hi 1 (fun R => e.shows R = true)
      (fun R _ hlen hs => by
        refine P1K8.atEl_one e.spot.draw R hlen ?_
        unfold Event.shows Event.test at hs
        rw [ho] at hs
        exact hs)

theorem fewAll_of_cap (C : CK) (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (hcap : KitCap C cap)
    (f : LFace) (h2 : 2 ≤ f.planes) (es : List Fmt.Entry) (hes : entriesFit f es = true)
    (dsb : List RDT) (hk : List.Forall₂ KindFits dsb (es.map Law.declOf)) (kap : ℝ≥0∞)
    (hkap : CapsUnder cap f es kap) : FewAll C f dsb kap := by
  intro e he
  obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 he
  refine fewAt_of_cap C cap hcap f es hes dsb hk kap hkap e (List.mem_append_left _ he) ?_
  rw [spot_of_mem hep]
  exact spot_laid f h2 p hp

theorem fewOutEvents_of_cap (C : CK) (cap : Fmt.Entry → Fmt.Kind → ℝ≥0∞) (hcap : KitCap C cap)
    (f : LFace) (h2 : 2 ≤ f.planes) (h1 : ∀ v ∈ f.parts, 1 ≤ v) (es : List Fmt.Entry)
    (hes : entriesFit f es = true) (dsb : List RDT)
    (hk : List.Forall₂ KindFits dsb (es.map Law.declOf)) (kap : ℝ≥0∞)
    (hkap : CapsUnder cap f es kap) : ∀ e ∈ outEvents f, FewAt C f dsb kap e := by
  intro e he
  obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 he
  refine fewAt_of_cap C cap hcap f es hes dsb hk kap hkap e (List.mem_append_right _ he) ?_
  rw [spot_of_mem hep]
  exact spotOut_laid f h2 h1 p hp

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.fits_at
#print axioms ProofFile.Honest.K3.Good.spot_of_mem
#print axioms ProofFile.Honest.K3.Good.fewAt_of_cap
#print axioms ProofFile.Honest.K3.Good.fewAll_of_cap
#print axioms ProofFile.Honest.K3.Good.fewOutEvents_of_cap
