-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkDebt.lean.

What is here. The mark of Law/Mark.lean in the form `MarkDebt` (Honest/Law/CoverJoin.lean): the
measure of the member's typed challenges at which the mark's test speaks is at most the mark's
stated share. A statement and its proof: one call of the law on a mark that speaks at listed rounds
alone (`markDebt_of_list_blocks`, Johnson/P1K8R/MarkRounds.lean), whose two premises on the mark's
text are shown here (`k4Mark_speaks`) and in Law/Mark.lean (`zeroOrOne_elem`). Its premise on the
rounds' data, (h1), is shown at data whose entries are those of the verifier's table of K4's rounds
and whose kinds are their names' (`k4_mark_h1`), where la ≤ muV; so the sentence stands at such data
under these three hypotheses (`k4_markDebt_table`); and la ≤ muV holds of every plan whose layout
and numbers of reads the program's functions return (Law/MarkPlan.lean): `k4_markDebt_plan`.

Not shown here. A BOUND ON THE MEASURE OF CHALLENGES AT WHICH A TEST SPEAKS: no run, no prover, no
coin, no input is in it. WHAT THE MARK's SILENCE GIVES AT ANY STATE OF THE VERIFIER IS NOT SHOWN.
`k4_markDebt` IS CONDITIONAL ON (h1): each listed round of the data ds samples one field element and
nothing else, and its word for the logarithm of a length is at most 64. `k4_markDebt_table` IS
CONDITIONAL ON: (hent) the data's entries are the table's; (hkind) each round's kind is its name's;
(hla) la ≤ muV. THAT THE DATA OF ANY DESCRIPTION's MEMBER MEET hent AND hkind IS NOT SHOWN. Where
hla fails a listed number falls on a row in front of the sumcheck's variables (the round of the
joining element; the point of several coordinates), and of (h1) at K4's own rounds nothing is said
then. AT ONE KIT OF TYPED CHALLENGES ALONE (the kit of that law). The bound is the mark's stated
share, a written product: NO NUMBER IS EVALUATED. MET FOR NOTHING: at P := fun _ => False.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
by a program's walk of import lines, which stops, unopened, at every module under Johnson/D/ or
ThirdParty/ and at the names RecCompile.Honest…, Both… and PassH…: its imports reach 102 modules
under Johnson/Goal/, all through Johnson/P1K8R/MarkRounds.lean; the walk stopped at 2 modules under
ThirdParty/ and nowhere else.

  `anyBad_at`, `k4Mark_speaks`   the test speaks only where the called law's own walk over the
      member's challenges does.
  `k4_markDebt`   **the sentence.**
  `k4_mark_h1`, `k4_markDebt_table`   **its premise on the data, and the sentence, at the table's
      own entries.**
  `k4_markDebt_plan`   **the same with la ≤ muV paid from the plan's makers' returns.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkPlan
import Johnson.P1K8R.MarkRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc.First.K8.Honest (OneElem oneElem_of)

/-- The called law's walk speaks where a listed round's challenge is bad. -/
theorem anyBad_at (bad : Fmt.Drawn → Bool) (mk : Nat → Bool) :
    ∀ (own : List Fmt.Drawn) (j i : Nat) (x : Fmt.Drawn), own[i]? = some x → mk (j + i) = true →
      bad x = true → P1K8.anyBad bad mk j own = true
  | [], _, _, _, h, _, _ => by cases h
  | y :: l, j, 0, x, h, hm, hb => by
    obtain rfl : y = x := Option.some.inj h
    show ((mk j && bad y) || P1K8.anyBad bad mk (j + 1) l) = true
    rw [show mk j = true from hm, hb]
    rfl
  | y :: l, j, i + 1, x, h, hm, hb => by
    show ((mk j && bad y) || P1K8.anyBad bad mk (j + 1) l) = true
    rw [anyBad_at bad mk l (j + 1) i x h (by rw [Nat.add_assoc, Nat.add_comm 1 i]; exact hm) hb,
      Bool.or_true]

/-- **The mark's test speaks only where that walk does.** -/
theorem k4Mark_speaks (Q : K4Pub) (fr own : List Fmt.Drawn)
    (h : ((k4Mark Q).test fr own).isSome = true) :
    P1K8.anyBad zeroOrOne (fun i => decide (i ∈ k4MarkRounds Q)) 0 own = true := by
  have h' : (k4MarkTest Q own).isSome = true := h
  unfold k4MarkTest at h'
  split at h'
  · rename_i hc
    obtain ⟨i, hi, hx⟩ := List.any_eq_true.1 hc
    cases ho : own[i]? with
    | none =>
      rw [ho] at hx
      cases hx
    | some x =>
      rw [ho] at hx
      exact anyBad_at _ _ own 0 i x ho (by rw [Nat.zero_add]; exact decide_eq_true hi) hx
  · cases h'

/-- **THE MARK's SENTENCE**, at every sentence P on the challenges in front. CONDITIONAL on (h1):
see the head. -/
theorem k4_markDebt (Q : K4Pub) (ds : List RDT)
    (h1 : ∀ i d, ds[i]? = some d → i ∈ k4MarkRounds Q →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (k4Mark Q) ds P (k4Mark Q).share.val :=
  P1K8.markDebt_of_list_blocks (k4Mark Q) zeroOrOne (k4MarkRounds Q) ds (k4Mark_speaks Q)
    zeroOrOne_elem h1 rfl P

/-- CONDITIONAL on hla, hent, hkind. **THE PREMISE (h1) AT THE TABLE's OWN ENTRIES**: each listed
round samples one field element and nothing else. -/
theorem k4_mark_h1 (Q : K4Pub) (hla : Q.P.y.h.la ≤ Q.P.rd.muV) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) :
    ∀ i d, ds[i]? = some d → i ∈ k4MarkRounds Q →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  intro i d hd hi
  have hrow := k4MarkRounds_rows Q hla i hi
  have he : (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)[i]? =
      some (OnBytes.Desc.First.K4.entryOf { name := .pscRound, sent := 2 }) := by
    unfold OnBytes.Desc.First.K4.entries
    rw [List.getElem?_map, hrow]
    rfl
  have he2 : (ds.map (·.entry))[i]? = some d.entry := by
    rw [List.getElem?_map, hd]
    rfl
  rw [hent, he] at he2
  have e : d.entry = OnBytes.Desc.First.K4.entryOf { name := .pscRound, sent := 2 } :=
    (Option.some.inj he2).symm
  have hk := hkind d (List.mem_of_getElem? hd)
  rw [e] at hk
  have hr : Fmt.kindOf "PSC round" = some .elems := by decide
  have hk' : d.kind = .elems := Option.some.inj (hk.symm.trans hr)
  rw [e, hk']
  exact ⟨oneElem_of _ _ rfl rfl rfl rfl (by decide) (by decide), Nat.zero_le _⟩

/-- CONDITIONAL on hla, hent, hkind. **THE MARK's SENTENCE AT THE TABLE's OWN ENTRIES.** -/
theorem k4_markDebt_table (Q : K4Pub) (hla : Q.P.y.h.la ≤ Q.P.rd.muV) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (k4Mark Q) ds P (k4Mark Q).share.val :=
  k4_markDebt Q ds (k4_mark_h1 Q hla ds hent hkind) P

/-- CONDITIONAL on hy, hp3, hrd, hent, hkind. **THE MARK's SENTENCE AT A PLAN WHOSE LAYOUT AND
NUMBERS OF READS THE PROGRAM's FUNCTIONS RETURN**, at the table's own entries. -/
theorem k4_markDebt_plan (Q : K4Pub) {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    (hy : OnBytes.Model.Layer.layout hS pc = .ok Q.P.y) (hp3 : hS.p3 = true)
    (hrd : OnBytes.Model.Layer.readsOf Q.P.y = .ok Q.P.rd) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (k4Mark Q) ds P (k4Mark Q).share.val :=
  k4_markDebt_table Q (la_le_muV hy hp3 hrd) ds hent hkind P

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.anyBad_at
#print axioms ProofFile.Honest.K4.k4Mark_speaks
#print axioms ProofFile.Honest.K4.k4_markDebt
#print axioms ProofFile.Honest.K4.k4_mark_h1
#print axioms ProofFile.Honest.K4.k4_markDebt_table
#print axioms ProofFile.Honest.K4.k4_markDebt_plan
