-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Sound.lean: the joined law of the kind, general in the decision; the kind's own
decision meets it; three silly decisions fail it.

Main names: Kept, CommitSound, kept_behind, commitSound; reads_exists; yesAll_fails_sound,
noAll_fails_sound; strike, lazyDec, lazy_fails_sound.

What is not claimed. The law is of the decision bare, at two rounds that fit; the blocks around it
are not treated but for Step.lean. The lazy copy fails at the clause that a sampled message is
marked; the last clause is tried in Tries2.lean. From a hash's blocks to seeds: not here. The
condition's three premises on lists stay premises. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Joined2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Cb Cb.Ood Prob

/-- What stood in the statement stands: the codes, the groups with their rows, every older
message. -/
def Kept {L : Type} (d d' : DState L) : Prop :=
  d'.st.codes = d.st.codes ∧ d'.st.groups = d.st.groups ∧
    ∀ j, j < d.st.oracles.size → d'.st.oracles[j]? = d.st.oracles[j]?

/-- **The joined law's form.** WHEN; and under the condition there is a set of bad seeds, within the
stated number, that hangs on the lists alone, such that behind a yes at rounds that fit, whose drawn
seeds read as joint seeds that are not bad: what stood in the statement stands; and for each sampled
message and any two members of its list: the message is marked, and if both members meet all rows
laid on it they are one vector of the sample map. Nothing is said where the drawn seeds do not read
(a factor spelt by a word that is not below the prime). What a row says, and that the rows are the
kind's, is not in this form: WritesLaw and says_iff stand beside it. -/
def CommitSound (dec : Dec) : Prop :=
  WhenLaw dec ∧
  ∀ (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (Lb : Nat → Nat), Condition P Lst Lb →
    ∃ bad : Seeds P → Prop, cnt bad ≤ errOf P Lb ∧
      ∀ (L : Type) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat)
        (ρ : Seeds P), roundsFit (rounds P) [r₁, r₂] = true →
        dec L P owed d [r₁, r₂] = .ok (ids, d') → ReadsAs P r₁ ρ → ¬ bad ρ →
        Kept d d' ∧ ∀ k, sampledAt P k → ∀ w w' : Means.Words GE,
          Lst k.val (w (d.st.oracles.size + k.val)) → Lst k.val (w' (d.st.oracles.size + k.val)) →
          ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧ x.sampled = true ∧
            (Means.AllSay rdE d'.st x.sampleRows.toList w →
              Means.AllSay rdE d'.st x.sampleRows.toList w' →
              (msgAt P k).vec (w (d.st.oracles.size + k.val)) =
                (msgAt P k).vec (w' (d.st.oracles.size + k.val)))

theorem kept_behind {L : Type} (P : Par) (d : DState L) (seeds : List (List E × E))
    (ys : List E) : Kept d (behind P d seeds ys) := by
  refine ⟨rfl, rfl, fun j hj => ?_⟩
  show (d.st.oracles.toList ++ outs P.codes seeds d.st.oracles.size (shapesOf P)
    ys).toArray[j]? = _
  rw [List.getElem?_toArray, List.getElem?_append_left (by simpa using hj),
    Array.getElem?_toList]

/-- **The kind's own decision meets the joined law.** -/
theorem commitSound : CommitSound fun _ => decideSend := by
  refine ⟨whenLaw, fun P Lst Lb hC => ⟨Bad P Lst, bad_count P Lst Lb hC, ?_⟩⟩
  intro L owed d d' r₁ r₂ ids ρ hfit hyes hρ hgood
  refine ⟨?_, fun k hk w w' hw hw' =>
    unique_behind P Lst owed d d' r₁ r₂ ids hC.onPlan hfit hyes ρ hρ hgood k hk w w' hw hw'⟩
  obtain ⟨_, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  exact kept_behind P d _ _

/-! ## The seeds can be read -/

/-- Where the rounds fit and every factor is spelt by words below the prime and is not 0, the seeds
read as joint seeds of the field. -/
theorem reads_exists (P : Par) (r₁ : Fmt.RoundView)
    (hok : ∀ s ∈ seedsOf P r₁, okE s.2 = true) (hnz : ∀ s ∈ seedsOf P r₁, isZeroE s.2 = false) :
    ∃ ρ : Seeds P, ReadsAs P r₁ ρ := by
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hne : ∀ i : Fin P.seeds, readE ((seedsOf P r₁)[i.val]'(by rw [hlen]; exact i.isLt)).2 ≠ 0 :=
    fun i h0 => by
      have hm : (seedsOf P r₁)[i.val]'(by rw [hlen]; exact i.isLt) ∈ seedsOf P r₁ :=
        List.getElem_mem _
      have := (isZeroE_iff _ (hok _ hm)).2 h0
      rw [hnz _ hm] at this
      cases this
  exact ⟨fun i => (fun t => readL ((seedsOf P r₁)[i.val]'(by rw [hlen]; exact i.isLt)).1 t.val,
    Units.mk0 (readE ((seedsOf P r₁)[i.val]'(by rw [hlen]; exact i.isLt)).2) (hne i)),
    fun i => ⟨(seedsOf P r₁)[i.val]'(by rw [hlen]; exact i.isLt), List.getElem?_eq_getElem _,
      fun _ => rfl, (Units.val_mk0 (hne i)).symm⟩⟩

/-! ## Three silly decisions -/

theorem yesAll_fails_sound : ¬ CommitSound yesAll := fun h => yesAll_fails_when h.1
theorem noAll_fails_sound : ¬ CommitSound noAll := fun h => noAll_fails_when h.1

/-- The record with every mark of a sample and every sample row struck. -/
def strike {L : Type} (d : DState L) : DState L :=
  { d with st := { d.st with
      oracles := d.st.oracles.map fun o => { o with sampled := false, sampleRows := #[] } } }

/-- A lazy copy: it asks all that the kind's decision asks, and then strikes every mark of a sample
and every sample row. -/
def lazyDec : Dec := fun _ P owed d rs => (decideSend P owed d rs).map fun x => (x.1, strike x.2)

theorem toy_seeds : toyP.seeds = 1 := by decide
theorem toy_coordinates : toyP.coordinates = 0 := by decide
theorem toy_shapes : (shapesOf toyP).length = 1 := by decide

theorem toy_condition : Condition toyP (fun _ u => u = fun _ _ => 0) fun _ => 1 := by
  refine ⟨toy_plan, fun k _ S hS => ?_, ?_⟩
  · refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨u, rfl, rfl⟩ := hS a ha
    obtain ⟨u', rfl, rfl⟩ := hS b hb
    rfl
  · rintro k _ _ u u' rfl rfl x _
    exact ⟨0, by simp⟩

theorem toy_reads : ReadsAs toyP toyR₁ fun _ => (fun _ => 0, 1) := by
  intro i
  have hi : i.val = 0 := by
    have h1 := i.isLt
    have h2 := toy_seeds
    omega
  refine ⟨([], E.ofTriple (1, 0, 0)), ?_, fun t => ?_, ?_⟩
  · rw [hi]
    simp [seedsOf, toy_seeds, toy_coordinates, cutSeeds, toyR₁]
  · have h1 := t.isLt
    have h2 := toy_coordinates
    omega
  · exact readE_one

theorem lazy_fails_sound : ¬ CommitSound lazyDec := by
  intro h
  obtain ⟨bad, hcnt, hb⟩ := h.2 toyP _ _ toy_condition
  have herr : errOf toyP (fun _ => 1) = 0 := by
    unfold errOf
    refine Finset.sum_eq_zero fun k _ => ?_
    split <;> simp
  have hgood : ¬ bad fun _ => (fun _ => 0, 1) := fun hbad => by
    have := card_le_cnt {(fun _ => (fun _ => 0, 1) : Seeds toyP)} (P := bad)
      (fun x hx => by rw [Finset.mem_singleton.1 hx]; exact hbad)
    rw [Finset.card_singleton] at this
    omega
  have hyes := (decideSend_iff toyP none toyD _ toyR₁ toyR₂ _).2 ⟨toy_asks, rfl, rfl⟩
  have hlazy : lazyDec Unit toyP none toyD [toyR₁, toyR₂] =
      .ok ((Array.range toyP.sent.size).map (· + toyD.st.oracles.size),
        strike (behind toyP toyD (seedsOf toyP toyR₁) (answersIn toyR₂))) := by
    unfold lazyDec
    rw [hyes]
    rfl
  obtain ⟨_, hu⟩ := hb Unit none toyD _ toyR₁ toyR₂ _ _ toy_fit hlazy toy_reads hgood
  obtain ⟨x, hx, hs, _⟩ := hu ⟨0, by rw [toy_shapes]; exact Nat.one_pos⟩ (by decide)
    (fun _ _ _ => 0) (fun _ _ _ => 0) rfl rfl
  unfold strike at hx
  rw [Array.getElem?_map] at hx
  obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 hx
  cases hs

end VerifiableInference.Desc.K1
