-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigRounds.lean: the lookup on the digits of a link's smallness test: THE
PREMISES ON THE WRITTEN ROUNDS FROM ONE: «each written round is the declared one». Definitions and
statements with their proofs. It imports nothing of the rule of composition. NO SOUNDNESS IS
CLAIMED.

Why. The lemmas on the lookup's written rounds (Johnson/Desc/First/Look/K3CallerErrW.lean) ask that
the rounds hold elements alone and have the declared entries. Both follow from one sentence on the
written rounds against the kind's own declared rounds.

Main names.
  TwRound.EntPlain e: what the lookup's entries have in common: answers, roots, poss, logN and trits
    are 0; those of its elements that must not be 0 are among them (drawNZ ≤ drawE); the name's kind
    is neither «sealed» nor «seeds» · entPlain_forEnts: every entry of the lookup's list has it.
  SameAs d r: the written round d is the declared round r: the same entry; its kind is the kind of
    the entry's name; its items are the cut of the entry's message.
  plain_of_same, same_all, same_entries.
  dig_rounds: under DigOK, written rounds that are the declared ones, one by one, hold elements
    alone, hold no answers, and have the declared entries.
  dig_err, dig_err128: so the least errors that bear the proved block's are at most 2^-157, and so
    at most 2^-128, of each written round's own challenge values.
Limits. That the written rounds of a piece are the declared ones is owed by whoever cuts the file's
rounds. Those of K3CallerErrW.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerErr128
import Johnson.Desc.First.Look.K3CallerTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TwRound
open TwPlan

/-- The name's kind is neither «sealed» nor «seeds». -/
def nameB (name : String) : Bool :=
  match Fmt.kindOf name with
  | some .sealed => false
  | some .seeds => false
  | _ => true

/-- What the lookup's entries have in common. -/
structure EntPlain (e : Fmt.Entry) : Prop where
  answers : e.answers = 0
  roots : e.roots = 0
  poss : e.poss = 0
  logN : e.logN = 0
  trits : e.trits = 0
  nz : e.drawNZ ≤ e.drawE
  name : nameB e.name = true

/-- Evaluates nameB at a written name. -/
local macro "nm" : tactic => `(tactic| first
  | decide
  | simp [nameB, Fmt.kindOf, Fmt.namesElems, Fmt.namesJoin, Fmt.namesSeeds, Fmt.namesPositions,
      Fmt.namesEntries, Fmt.namesSealed, Fmt.namesNothing])

theorem ok_rd (wk : ℕ) (name : String) (s k : ℕ) (h : nameB name = true) :
    EntPlain (rd wk name s k) := ⟨rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, h⟩
theorem ok_Y (wk s : ℕ) : EntPlain (rd wk "PSC Y" s 1 1) :=
  ⟨rfl, rfl, rfl, rfl, rfl, le_refl 1, (by nm : nameB "PSC Y" = true)⟩
theorem ok_none (name : String) (s : ℕ) (h : nameB name = true) : EntPlain (rdNone name s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, le_refl 0, h⟩

theorem ok_psc (wk : ℕ) (degs : List ℕ) (withY : Bool) (gY vals : ℕ) :
    ∀ e ∈ pscN wk degs withY gY vals, EntPlain e := by
  intro e he
  unfold pscN at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl := List.mem_singleton.1 he
      exact ok_rd _ _ _ _ (by nm)
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 he
      exact ok_rd _ _ _ _ (by nm)
  · cases withY with
    | true =>
      simp only [if_true, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · exact ok_Y _ _
      · exact ok_none _ _ (by nm)
    | false => simp at he

theorem ok_entN (wk v' d w n : ℕ) : ∀ e ∈ entN wk v' d w n, EntPlain e := by
  intro e he
  unfold entN at he
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at he
  rcases he with (((((((rfl | he) | ⟨_, -, he⟩) | rfl) | ⟨_, -, he⟩) | ⟨_, -, he⟩) | he) | rfl) | he
  · exact ok_rd _ _ _ _ (by nm)
  · exact ok_psc _ _ _ _ _ e he
  · exact ok_psc _ _ _ _ _ e he
  · exact ok_rd _ _ _ _ (by nm)
  · rcases he with he | rfl
    · exact ok_psc _ _ _ _ _ e he
    · exact ok_rd _ _ _ _ (by nm)
  · rcases he with he | rfl
    · exact ok_psc _ _ _ _ _ e he
    · exact ok_rd _ _ _ _ (by nm)
  · exact ok_psc _ _ _ _ _ e he
  · exact ok_rd _ _ _ _ (by nm)
  · exact ok_psc _ _ _ _ _ e he

/-- **Every entry of the lookup's list.** -/
theorem entPlain_forEnts (wk : ℕ) (h : FoNums.Sh) : ∀ e ∈ Cb.Fo.forEnts wk h, EntPlain e := by
  intro e he
  unfold Cb.Fo.forEnts at he
  rcases List.mem_append.1 he with he | he
  · unfold shHead at he
    split at he
    · obtain rfl := List.mem_singleton.1 he
      exact ok_rd _ _ _ _ (by nm)
    · simp at he
  · exact ok_entN _ _ _ _ _ e he

end TwRound

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look
open scoped ENNReal

/-- A written round is the declared one: the same entry; its kind is the kind of the entry's name;
its items are the cut of the entry's message. -/
def SameAs (d : RDT) (r : Fmt.DeclaredRound) : Prop :=
  d.entry = r.entry ∧ Fmt.kindOf r.entry.name = some d.kind ∧ d.items = r.items

/-- Such a round, at an entry of the lookup's sort, holds elements alone. -/
theorem plain_of_same {d : RDT} {r : Fmt.DeclaredRound} (h : SameAs d r) (ho : EntPlain r.entry) :
    Plain (toRD d) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hi : d.items = List.replicate (r.entry.msg / 24) Fmt.Item.e := by
    rw [h3]
    unfold Fmt.DeclaredRound.items Fmt.Entry.cut
    rw [ho.answers, ho.roots]
    simp
  have hk : nameB r.entry.name = true := ho.name
  unfold nameB at hk
  rw [h2] at hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro it hit
    have hit' : it ∈ d.items := hit
    rw [hi] at hit'
    exact List.eq_of_mem_replicate hit'
  · show d.items.length = d.entry.msg / 24
    rw [hi, h1, List.length_replicate]
  · show d.entry.poss = 0
    rw [h1]
    exact ho.poss
  · show d.entry.logN = 0
    rw [h1]
    exact ho.logN
  · show d.entry.trits = 0
    rw [h1]
    exact ho.trits
  · intro e
    have e' : d.kind = .sealed := e
    rw [e'] at hk
    cases hk
  · intro e
    have e' : d.kind = .seeds := e
    rw [e'] at hk
    cases hk
  · show d.entry.drawNZ ≤ d.entry.drawE
    rw [h1]
    exact ho.nz

theorem same_all : ∀ {ds : List RDT} {rs : List Fmt.DeclaredRound}, List.Forall₂ SameAs ds rs →
    (∀ r ∈ rs, EntPlain r.entry) → ∀ d ∈ ds, Plain (toRD d)
  | _, _, .nil, _, _, hd => by cases hd
  | _, _, .cons hab t, hok, d, hd => by
    rcases List.mem_cons.1 hd with rfl | hd
    · exact plain_of_same hab (hok _ List.mem_cons_self)
    · exact same_all t (fun r hr => hok r (List.mem_cons_of_mem _ hr)) d hd

theorem same_entries : ∀ {ds : List RDT} {rs : List Fmt.DeclaredRound}, List.Forall₂ SameAs ds rs →
    ds.map (·.entry) = rs.map (·.entry)
  | _, _, .nil => rfl
  | _, _, .cons hab t => by rw [List.map_cons, List.map_cons, hab.1, same_entries t]

section
variable {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {set : Params.Setting} {pp : ℕ}

/-- **The three premises on the written rounds, from one.** -/
theorem dig_rounds (H : DigOK set x tl D rad pp) (ds : List RDT)
    (hR : List.Forall₂ SameAs ds (Desc.First.Look.P.ofPlace set true x).rounds) :
    (∀ d ∈ ds, Plain (toRD d)) ∧ (∀ d ∈ ds, NoAns d.items) ∧
      ds.map (·.entry) = (Desc.First.Look.P.ofPlace set true x).rounds.map (·.entry) := by
  have hE := entries_forEnts H.shape (dig_foOk H)
    (by
      rw [(DgP.shape2_parts H.tail).2.1.nc]
      decide) H.rounds
  have hok : ∀ r ∈ (Desc.First.Look.P.ofPlace set true x).rounds, EntPlain r.entry := fun r hr =>
    entPlain_forEnts _ _ _ (by
      rw [← hE]
      exact List.mem_map.2 ⟨r, hr, rfl⟩)
  exact ⟨same_all hR hok, fun d hd => (same_all hR hok d hd).noAns, same_entries hR⟩

/-- **The errors of the written rounds, as a number.** -/
theorem dig_err (H : DigOK set x tl D rad pp) (ds : List RDT)
    (hR : List.Forall₂ SameAs ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (ε' : Iop.Err (uLT (ckP .two) ds))
    (hb : bearT ds _ ((kLookupCR [noRider (digCaller x tl D rad extNone Unit)]).ε
      (noRider (digCaller x tl D rad extNone Unit))) = some ε') :
    Iop.Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 157) :=
  dig_written extNone Unit H ds (dig_rounds H ds hR).1 (dig_rounds H ds hR).2.2 ε' hb

/-- **The same at the level of 128 bits a round.** -/
theorem dig_err128 (H : DigOK set x tl D rad pp) (ds : List RDT)
    (hR : List.Forall₂ SameAs ds (Desc.First.Look.P.ofPlace set true x).rounds)
    (ε' : Iop.Err (uLT (ckP .two) ds))
    (hb : bearT ds _ ((kLookupCR [noRider (digCaller x tl D rad extNone Unit)]).ε
      (noRider (digCaller x tl D rad extNone Unit))) = some ε') :
    Iop.Err.Below ε' ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Iop.Err.Below.mono_bound pow157_le (dig_err H ds hR ε' hb)

end

end VerifiableInference.OnPublicFiles

#print axioms TwRound.entPlain_forEnts
#print axioms VerifiableInference.OnPublicFiles.plain_of_same
#print axioms VerifiableInference.OnPublicFiles.dig_rounds
#print axioms VerifiableInference.OnPublicFiles.dig_err
#print axioms VerifiableInference.OnPublicFiles.dig_err128
