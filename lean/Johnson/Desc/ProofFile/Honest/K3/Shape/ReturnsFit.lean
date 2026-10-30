-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ReturnsFit.lean: what gives the two hypotheses of
`hearV_returns` (Honest/K3/Shape/Returns.lean): the stretch, from a sub-protocol's own test on its
rounds (`roundsFit`, Johnson/Desc/Block.lean); the window, at a fresh ledger; and an instance at
every face that passes its own test. One structure, two definitions with code; theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, round, entry, stretch, window (of the ledger's
slots), ledger, sub-protocol and face. In this file: rounds are declared bare if each declaration
holds its entry and nothing else.

What is shown.
  `Plain e`: an entry of scalars and sampled elements alone, under a name that the format knows.
  `plain_entriesV`: every entry of a lookup's rounds is such an entry.
  `str_of_roundsFit`: rounds that pass the library's test at plain entries, declared bare, are a
    stretch.
  `str_noDigest`: and so are they without the sealed digest: as a decision is shown them.
  `str_of_fit`: from the test at the planner's own entries, where these are the hearing's but for
    the work bits (`entriesFit`, Johnson/Desc/First/Look/Via/Rounds.lean): a stretch at the
    hearing's entries.
  `hearV_returns_fit`: the hearing returns on the rounds that a decision is shown, behind the
    sub-protocol's own test on its rounds.
  `win_fresh`, `win_at`: the window at a ledger of n fresh slots; at one whose count stands at
    first, with n more (`ledgerR`, which has the text of `ledgerAt`, Honest/K3/RowGuards.lean
    [not in this library]).
  `str_work`: a stretch reads no work bits.
  `blankR`, `str_blank`, `hearV_returns_blank`: an instance at every face that passes its own test,
    by proof: rounds in which every scalar is 0 and every sample is 1. No hypothesis but the face's
    test.

Hypotheses that remain, in `hearV_returns_fit`.
  `hok`: the face passes its own test.
  `W`: the window (`Win`, Honest/K3/Shape/Window.lean).
  `hfit`, `h`: the two tests on the declared rounds: `entriesFit`; `roundsFit`.
In the helpers: `hk`: the format knows the name; `P`: `Plain e`.

Users. Honest/K3/Shape/ReturnsStep.lean imports this file.

Limits. The declared rounds are bare: no stored part and no tree is opened in them, as in a
lookup's. The rounds of the instance are no honest prover's: the hearing tests no value. No instance
at a planner's entries is exhibited in this file. Shown in part: `hearV_returns_at_blank`
(Honest/K3/Shape/ReturnsStep.lean): an instance at every face that passes its own test, every list
of entries that passes `entriesFit` at it, and every sub-protocol that declares them bare. What
stays open: it is not stated at a planner's own entries. That these pass `entriesFit` follows where
the sub-protocol's own test on the plan accepts (`PlanGives`, `theStated_plan`,
Honest/K3/Law/PlanOkGives.lean); that test is a test with code.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (roundsFit drawsMarkedNonzeroHaveNonzeroWords itemOf noDigest)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Fits Fit entries entry scalars)
open VerifiableInference.Desc.K3 (hearV entriesV entriesFit drawEntry noVar bitsCall leafVars)
open VerifiableInference.Desc.First.ProdV (elementsAlone levelEntries runEntries)

local notation "KFace" => VerifiableInference.Desc.K3.Face

/-! ## Plain entries -/

/-- **An entry of scalars and sampled elements alone**, under a name that the format knows. -/
structure Plain (e : Fmt.Entry) : Prop where
  answers : e.answers = 0
  roots : e.roots = 0
  poss : e.poss = 0
  trits : e.trits = 0
  msg : e.msg = 24 * (e.msg / 24)
  kind : (Fmt.kindOf e.name).isSome = true

theorem plain_entry (name : String) (a b c : Nat) (hk : (Fmt.kindOf name).isSome = true) :
    Plain (entry name a b c) :=
  ⟨rfl, rfl, rfl, rfl, by show 24 * a = 24 * (24 * a / 24); omega, hk⟩

theorem plain_entries (k : Call) : ∀ e ∈ entries k, Plain e := by
  intro e he
  unfold entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl : e = _ := List.mem_singleton.1 he
      exact plain_entry _ _ _ _ (by decide)
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 he
      exact plain_entry _ _ _ _ (by decide)
  · cases hk : k.ends with
    | none => rw [hk] at he; cases he
    | some x =>
      rw [hk] at he
      rcases List.mem_cons.1 he with rfl | he
      · exact plain_entry _ _ _ _ (by decide)
      · obtain rfl : e = _ := List.mem_singleton.1 he
        exact plain_entry _ _ _ _ (by decide)

theorem plain_level (m : Nat) : ∀ e ∈ levelEntries m, Plain e := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact plain_entries _ e he
  · obtain rfl : e = _ := List.mem_singleton.1 he
    exact plain_entry _ _ _ _ (by decide)

theorem plain_run (m0 n : Nat) : ∀ e ∈ runEntries m0 n, Plain e := by
  intro e he
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 he
  exact plain_level _ e hi

/-- **Every entry of a lookup's rounds is plain.** No hypothesis. -/
theorem plain_entriesV (f : KFace) : ∀ e ∈ entriesV f, Plain e := by
  intro e he
  rw [entriesV_eq] at he
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at he
  rcases he with he | rfl | (he | ⟨_, _, he⟩) | ⟨_, _, he⟩ | rfl | ⟨_, _, he⟩ | he | he | rfl | he
  · cases hs : f.shifted with
    | true =>
      rw [hs] at he
      obtain rfl : e = _ := List.mem_singleton.1 he
      exact plain_entry _ _ _ _ (by decide)
    | false => rw [hs] at he; cases he
  · exact plain_entry _ _ _ _ (by decide)
  · exact plain_entries _ e he
  · exact plain_entries _ e he
  · exact plain_entries _ e he
  · exact plain_entry _ _ _ _ (by decide)
  · exact plain_run _ _ e he
  · exact plain_run _ _ e he
  · exact plain_entries _ e he
  · exact plain_entry _ _ _ _ (by decide)
  · exact plain_entries _ e he

/-! ## From the library's test on a sub-protocol's rounds -/

theorem scalars_of_items : ∀ (vals : List Fmt.ItemValue) (n : Nat),
    vals.map itemOf = List.replicate n Fmt.Item.e → ∃ s, scalars vals = some s ∧ s.length = n
  | [], 0, _ => ⟨[], rfl, rfl⟩
  | [], _ + 1, h => by simp [List.replicate_succ] at h
  | _ :: _, 0, h => by simp at h
  | v :: l, n + 1, h => by
    rw [List.map_cons, List.replicate_succ] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨s, e1, e2⟩ := scalars_of_items l n h2
    cases v with
    | e x => exact ⟨E.ofTriple x :: s, by simp [scalars, e1], by simp [e2]⟩
    | f _ => cases h1
    | word _ => cases h1
    | root _ => cases h1
    | answer _ => cases h1

theorem cut_plain {e : Fmt.Entry} (P : Plain e) :
    (({ entry := e } : Fmt.DeclaredRound).items.filter (· != .root)) =
      List.replicate (e.msg / 24) Fmt.Item.e := by
  show (e.cut.filter (· != .root)) = _
  unfold Fmt.Entry.cut
  rw [P.answers, P.roots]
  simp

/-- **Rounds that pass the library's test at plain entries, declared bare, are a stretch.**
Conditional on the entries being plain and on the test; an instance: `str_blank` (by proof). -/
theorem str_of_roundsFit : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView), (∀ e ∈ es, Plain e) →
    roundsFit (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) rs = true → Str es rs
  | [], [], _, _ => Str.nil
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | e :: es, r :: rs, hP, h => by
    have h' : (r.vals.map itemOf == ({ entry := e } : Fmt.DeclaredRound).items.filter (· != .root) &&
      r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
      r.drawn.trits.length == e.trits && r.drawn.poss.all (· < 2 ^ e.logN) &&
      r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) && drawsMarkedNonzeroHaveNonzeroWords { entry := e } r &&
      roundsFit (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) rs) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, _⟩, a7⟩, a8⟩ := h'
    have P := hP e (List.mem_cons_self ..)
    have ih := str_of_roundsFit es rs (fun x hx => hP x (List.mem_cons_of_mem _ hx)) a8
    rw [cut_plain P] at a1
    obtain ⟨s, s1, s2⟩ := scalars_of_items _ _ a1
    rw [P.poss] at a3
    rw [P.trits] at a4
    refine ⟨⟨⟨⟨s, s1, by rw [s2]; exact P.msg⟩, a2⟩, ih.fits⟩, ?_, ?_⟩
    · show ((r.drawn.poss.isEmpty && r.drawn.trits.isEmpty) && elementsAlone rs) = true
      rw [List.eq_nil_of_length_eq_zero a3, List.eq_nil_of_length_eq_zero a4, ih.alone]
      rfl
    · show (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll es rs) = true
      rw [a7, ih.nz]
      rfl

/-- A stretch reads no sealed digest. Conditional on the stretch. -/
theorem str_noDigest : ∀ {es : List Fmt.Entry} {rs : List Fmt.RoundView}, Str es rs →
    Str es (rs.map noDigest)
  | [], [], _ => Str.nil
  | [], _ :: _, h => h.fits.elim
  | _ :: _, [], h => h.fits.elim
  | e :: es, r :: rs, h => by
    have ha : ((r.drawn.poss.isEmpty && r.drawn.trits.isEmpty) && elementsAlone rs) = true :=
      h.alone
    have hn : (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll es rs) = true := h.nz
    rw [Bool.and_eq_true] at ha hn
    have ih := str_noDigest (es := es) (rs := rs) ⟨h.fits.2, ha.2, hn.2⟩
    refine ⟨⟨h.fits.1, ih.fits⟩, ?_, ?_⟩
    · show ((r.drawn.poss.isEmpty && r.drawn.trits.isEmpty) &&
        elementsAlone (rs.map noDigest)) = true
      rw [ha.1, ih.alone]
      rfl
    · show (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll es (rs.map noDigest)) = true
      rw [hn.1, ih.nz]
      rfl

/-- A stretch reads no work bits. Conditional on the stretch. -/
theorem str_work : ∀ {es : List Fmt.Entry} {rs : List Fmt.RoundView}, Str es rs →
    Str (es.map fun e => { e with work := 0 }) rs
  | [], [], _ => Str.nil
  | [], _ :: _, h => h.fits.elim
  | _ :: _, [], h => h.fits.elim
  | e :: es, r :: rs, h => by
    have ha : ((r.drawn.poss.isEmpty && r.drawn.trits.isEmpty) && elementsAlone rs) = true :=
      h.alone
    have hn : (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll es rs) = true := h.nz
    rw [Bool.and_eq_true] at ha hn
    have ih := str_work (es := es) (rs := rs) ⟨h.fits.2, ha.2, hn.2⟩
    exact ⟨⟨h.fits.1, ih.fits⟩, h.alone, by
      show (drawsMarkedNonzeroHaveNonzeroWords { entry := e } r && nzAll (es.map fun e => { e with work := 0 }) rs) = true
      rw [hn.1, ih.nz]
      rfl⟩

theorem fit_eq {f : KFace} {es : List Fmt.Entry} (h : entriesFit f es = true) :
    (es.map fun e => { e with work := 0 }) = entriesV f := by
  unfold entriesFit at h
  exact of_decide_eq_true (by simpa using h)

/-- **From the library's test at the planner's own entries to a stretch at the hearing's**, without
the sealed digest. Conditional on the two tests. No instance at a planner's entries is exhibited in
this file. -/
theorem str_of_fit {f : KFace} {es : List Fmt.Entry} {rs : List Fmt.RoundView}
    (hfit : entriesFit f es = true)
    (h : roundsFit (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) rs = true) :
    Str (entriesV f) (rs.map noDigest) := by
  have he := fit_eq hfit
  have hP : ∀ e ∈ es, Plain e := by
    intro e hm
    have P := plain_entriesV f { e with work := 0 } (by
      rw [← he]
      exact List.mem_map.2 ⟨e, hm, rfl⟩)
    exact ⟨P.answers, P.roots, P.poss, P.trits, P.msg, P.kind⟩
  rw [← he]
  exact str_work (str_noDigest (str_of_roundsFit es rs hP h))

/-- **The hearing returns on the rounds that a decision is shown.** Conditional on the face's own
test, the window, and the two tests on the declared rounds. No instance at a planner's entries is
exhibited in this file. -/
theorem hearV_returns_fit (f : KFace) (hok : f.ok = true) {F : Fork} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} (W : Win F.next F.next (F.next + f.slots) F)
    (hfit : entriesFit f es = true)
    (h : roundsFit (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) rs = true) :
    ∃ g G, hearV f F (rs.map noDigest) = some (g, G) :=
  hearV_returns f hok W (str_of_fit hfit h)

/-! ## The window at a ledger that is made anew -/

/-- A ledger whose count of slots stands at "first", with n more, none of them filled. -/
def ledgerR (first n : Nat) : Fork := { (({} : Fork).slots (first + n)) with next := first }

theorem win_at (first n : Nat) : Win first first (first + n) (ledgerR first n) := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, Nat.le_refl _, fun j _ _ => ?_, fun j h1 h2 => absurd h2 (by omega)⟩
  · exact Array.size_replicate
  · exact Array.size_replicate
  · exact Array.size_replicate
  · show ¬ (Array.replicate (first + n) false).getD j false = true
    simp [Array.getD]

/-- The window at a ledger of n fresh slots. No hypothesis. -/
theorem win_fresh (n : Nat) : Win 0 0 (0 + n) (({} : Fork).slots n) := by
  have h := win_at 0 n
  have e : ledgerR 0 n = ({} : Fork).slots n := by
    unfold ledgerR
    rw [Nat.zero_add]
    rfl
  rwa [e] at h

/-! ## An instance at every face that passes its own test -/

/-- A round of an entry's shape: every scalar 0, every sample 1. -/
def blankR (e : Fmt.Entry) : Fmt.RoundView :=
  ⟨List.replicate (e.msg / 24) (.e (0, 0, 0)), ⟨List.replicate e.drawE (1, 0, 0), [], [], none⟩⟩

theorem scalars_blank : ∀ n : Nat, ∃ s, scalars (List.replicate n (Fmt.ItemValue.e (0, 0, 0))) = some s ∧
    s.length = n
  | 0 => ⟨[], rfl, rfl⟩
  | n + 1 => by
    obtain ⟨s, e1, e2⟩ := scalars_blank n
    exact ⟨E.ofTriple (0, 0, 0) :: s, by simp [List.replicate_succ, scalars, e1], by simp [e2]⟩

theorem nz_blank {e : Fmt.Entry} (P : Plain e) : drawsMarkedNonzeroHaveNonzeroWords { entry := e } (blankR e) = true := by
  unfold drawsMarkedNonzeroHaveNonzeroWords
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 P.kind
  show ((Fmt.kindOf e.name).any fun k =>
    ((Fmt.dsElems e k).zip (List.replicate e.drawE ((1 : UInt64), (0 : UInt64), (0 : UInt64)))).all
      fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true
  rw [hk]
  show (((Fmt.dsElems e k).zip (List.replicate e.drawE ((1 : UInt64), (0 : UInt64),
    (0 : UInt64)))).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true
  rw [List.all_eq_true]
  intro x hx
  have h2 : x.2 = (1, 0, 0) := List.eq_of_mem_replicate (List.of_mem_zip hx).2
  rw [h2]
  simp

/-- **At plain entries the blank rounds are a stretch.** Conditional on the entries being plain;
an instance: `plain_entriesV` (by proof). -/
theorem str_blank : ∀ (es : List Fmt.Entry), (∀ e ∈ es, Plain e) → Str es (es.map blankR)
  | [], _ => Str.nil
  | e :: es, hP => by
    have P := hP e (List.mem_cons_self ..)
    have ih := str_blank es fun x hx => hP x (List.mem_cons_of_mem _ hx)
    obtain ⟨s, s1, s2⟩ := scalars_blank (e.msg / 24)
    refine ⟨⟨⟨⟨s, s1, by rw [s2]; exact P.msg⟩, List.length_replicate⟩, ih.fits⟩, ?_, ?_⟩
    · show (true && elementsAlone (es.map blankR)) = true
      rw [ih.alone]
      rfl
    · show (drawsMarkedNonzeroHaveNonzeroWords { entry := e } (blankR e) && nzAll es (es.map blankR)) = true
      rw [nz_blank P, ih.nz]
      rfl

/-- **An instance at every face that passes its own test**: from a ledger whose count stands
anywhere, with the lookup's slots free behind it, the hearing returns on the blank rounds. No
hypothesis but the face's test. -/
theorem hearV_returns_blank (f : KFace) (hok : f.ok = true) (first : Nat) :
    ∃ g G, hearV f (ledgerR first f.slots) ((entriesV f).map blankR) = some (g, G) :=
  hearV_returns f hok (win_at first f.slots) (str_blank _ (plain_entriesV f))

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.plain_entry
#print axioms ProofFile.Honest.K3.Shape.plain_entries
#print axioms ProofFile.Honest.K3.Shape.plain_level
#print axioms ProofFile.Honest.K3.Shape.plain_run
#print axioms ProofFile.Honest.K3.Shape.plain_entriesV
#print axioms ProofFile.Honest.K3.Shape.scalars_of_items
#print axioms ProofFile.Honest.K3.Shape.cut_plain
#print axioms ProofFile.Honest.K3.Shape.str_of_roundsFit
#print axioms ProofFile.Honest.K3.Shape.str_noDigest
#print axioms ProofFile.Honest.K3.Shape.str_work
#print axioms ProofFile.Honest.K3.Shape.fit_eq
#print axioms ProofFile.Honest.K3.Shape.str_of_fit
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_fit
#print axioms ProofFile.Honest.K3.Shape.win_at
#print axioms ProofFile.Honest.K3.Shape.win_fresh
#print axioms ProofFile.Honest.K3.Shape.scalars_blank
#print axioms ProofFile.Honest.K3.Shape.nz_blank
#print axioms ProofFile.Honest.K3.Shape.str_blank
#print axioms ProofFile.Honest.K3.Shape.hearV_returns_blank
