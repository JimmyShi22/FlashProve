-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/ObjectsOnAll.lean: THE SENTENCE OF THE OPEN CLAIM formsT m 3 "objects"
GOES FORWARD OVER A YES OF THE SUB-PROTOCOL "the output head's own rounds" (K6), AT THE COMPOSED
MEANING mgAll D Mg (Johnson/Desc/Sound/MgAll.lean), general in its data: from the verifier's state
in front to the state behind, at one witness. No piece of the proof of soundness, no string of a
file and no promise of the table is read. BOTH THEOREMS ARE CONDITIONAL.

  `objects_on_runs`  the sentence's first clause ("at each run under the name, `formsTQ`"), at any
                     reader rd of the witness's tables
  `objects_on_all`   THE SENTENCE: the mirror of the library's `objects_back`
                     (Johnson/Desc/Kinds/Law/K6RidersAtMgAll.lean)
CONDITIONAL, both: hreaders (the runs' readers at the segment are the link's, with the silent reader
in the hole) · hobj (which runs stand under the name) · hruns, hback (on the link's list of rounds)
· K (what a yes leaves of the state: `K6Keeps`, Honest/Law/Keeps.lean) · hled (the public test "a
ledger is open and has its sizes", in front) · hbare (no row that the lookup on the calls keeps
names an entry of an array) · the sentence in front.

How. That something is heard comes out of the sentence at the run "objects": there the reader
answers, and it answers the kept rows (`readers_kept`). Then `kept_fwd_keeps`
(Honest/Law/ObjectsOn.lean) at each of the two runs. The glue follows the proof of `objects_back`
line by line. The public part, and the strings, may differ in front and behind: at a name other
than "weights" the sentence reads neither.

Limits. THAT THE PREMISES CAN BE MET TOGETHER: NO EXAMPLE. NOTHING HERE SAYS THAT A FORM IS WORTH 0
AT ANY STATE: the sentence in front is a premise. At the run "guests" the reader's list of forms is
empty: there the sentence is its tests alone. Nothing on any property.
-/
import Johnson.Desc.K6.Honest.Law.ObjectsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open VerifiableInference.Desc (Link Claim Strs Wit)
open VerifiableInference.Desc.First (S Meaning ledgerB)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates ObjectsBack readers_kept)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink)
open VerifiableInference.Desc.Sound (MsgT MsgQ formsTQ mgAll)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : Sound.MgData Xi P Tok rows cols nR Wp)

/-- **At each run under the name the sentence goes forward.** CONDITIONAL: as the head's list
says. -/
theorem objects_on_runs (m : ℕ) {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH}
    {small : S → Option K9.Read}
    (hreaders : D.Rd m = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hobj : D.runs m 3 "objects" = [(2, "objects"), (2, "guests")])
    (hruns : ObjectsStates (statesOfLink Lk) 2) (hback : ObjectsBack (statesOfLink Lk) 2)
    {s s' : S} (K : K6Keeps s s') (hled : ledgerB s = true)
    (hbare : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (rd : ℕ × ℕ → MsgQ)
    (h : ∀ p ∈ D.runs m 3 "objects", formsTQ (D.Rd m) D.St (D.N.sent m 0) p.1 p.2 s rd) :
    ∀ p ∈ D.runs m 3 "objects", formsTQ (D.Rd m) D.St (D.N.sent m 0) p.1 p.2 s' rd := by
  -- something is heard: the reader of "objects" answers in front
  obtain ⟨g, hg⟩ : ∃ g, s.lookHeard? = some g := by
    obtain ⟨_, R, _, hR, _⟩ := h (2, "objects") (by rw [hobj]; simp)
    rw [hreaders] at hR
    have k0 := readers_kept hruns P8 small "objects" (Or.inl rfl) s R hR
    unfold Law.AtTable.keptOf at k0
    rw [if_pos rfl] at k0
    obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.1 k0
    exact ⟨g, hg⟩
  intro p hp
  have h1 := h p hp
  rw [hobj] at hp
  have hp' : p.1 = 2 ∧ (p.2 = "objects" ∨ p.2 = "guests") := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  rw [hreaders, hp'.1] at h1 ⊢
  exact kept_fwd_keeps hruns hback P8 small _ _ p.2 hp'.2 K hled g hg (hbare g hg) rd h1

/-- **THE SENTENCE OF THE OPEN CLAIM formsT m 3 "objects" GOES FORWARD.** CONDITIONAL: as the head's
list says. -/
theorem objects_on_all (Mg : Meaning P (Wit (Sound.CellsQ rows cols) Tok MsgT)) (m : ℕ)
    {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH} {small : S → Option K9.Read}
    (hreaders : D.Rd m = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hobj : D.runs m 3 "objects" = [(2, "objects"), (2, "guests")])
    (hruns : ObjectsStates (statesOfLink Lk) 2) (hback : ObjectsBack (statesOfLink Lk) 2)
    {s s' : S} (K : K6Keeps s s') (hled : ledgerB s = true)
    (hbare : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (z z' : P) (y y' : Strs) (w : Wit (Sound.CellsQ rows cols) Tok MsgT)
    (h : (mgAll D Mg).formsT m 3 "objects" (z, s) y w) :
    (mgAll D Mg).formsT m 3 "objects" (z', s') y' w :=
  ⟨objects_on_runs D m hreaders hobj hruns hback K hled hbare _ h.1,
    fun e => absurd e (by decide)⟩

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.objects_on_runs
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.objects_on_all
