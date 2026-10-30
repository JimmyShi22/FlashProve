-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/CoinRow.lean: CONDITIONAL.

What is here. THE ROUND AT WHICH K4's FALL READS (`k4CoinZero`, `k4Fall`: Honest/K4/Part.lean)
SAMPLES ONE FIELD ELEMENT AND NOTHING ELSE, at data that fit K4's declared rounds. (1)
`k4_plain_h1`: at data whose entries are those made of the verifier's table of K4's rounds (the
table `rounds`: OnBytes/Desc/First/K4/Rounds.lean; `entries` and `entryOf`:
Johnson/Desc/First/K4/Block.lean) and whose kinds are their names', a round whose row draws one
element, and none by the rule that never gives 0, samples one field element and nothing else, and
its entry's field logN is at most 64. (2) `k4_coin_h1`: so at the round number `(starts Q).getD 2
0`, at which `k4CoinZero` reads and which the wider mark leaves out: its row is named `.pscEpsilon`
(`k4CoinRound_row`, Law/MarkWide.lean) and such a row draws one plain element (`k4_named_plain`,
Law/MarkWideTable.lean). (3) `ent_of_kindFits`: THE TWO HYPOTHESES hent AND hkind FOLLOW FROM THE
FRAME's OWN RELATION: where a list of rounds' data stands in `KindFits` (Honest/Law/Due.lean),
member by member, with the declared rounds made of a list of entries, its entries are that list and
each kind is its name's. (4) `k4_coin_of_kindFits`: the three joined: at data in `KindFits` with
K4's declared rounds THERE IS a member at that number, and it samples one field element and nothing
else: so at K4's own member the case «no such round» does not arise. AT EVERY PLAN: no hypothesis on
the plan's numbers. Statements with their proofs.

Not shown here. THAT ANY MEMBER OF A CHAIN HAS K4's DECLARED ROUNDS: `k4_rounds` (Law/Plays.lean)
has it under its own hypothesis; it is not called here. No measure, no bound, no kit is in this
file: what the measure of the challenges is at which the fall's test speaks is another file's.
No property is claimed.

  `k4_plain_h1`   a row of one plain element: its round samples one element and nothing else.
  `k4_coin_h1`   **so the round at which K4's fall reads.**
  `ent_of_kindFits`   **hent and hkind, from the frame's relation.**
  `k4_coin_of_kindFits`   **at data that fit K4's declared rounds that round is there, and samples
      one element and nothing else.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideElem
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideTable
import Johnson.Desc.ProofFile.Honest.Law.Due

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc.First.K8.Honest (OneElem oneElem_of)

/-- CONDITIONAL: on hent, hkind, hd, hrow, h1 and h2. At the table's own entries a round whose row
draws one element, and none by the never-zero rule, samples one field element and nothing else. -/
theorem k4_plain_h1 (Q : K4Pub) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) {i : Nat} {d : RDT}
    (hd : ds[i]? = some d) {row : OnBytes.Desc.First.K4.Rd}
    (hrow : (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)[i]? = some row) (h1 : row.drawn = 1)
    (h2 : row.notZero = 0) : OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  have he : (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)[i]? =
      some (OnBytes.Desc.First.K4.entryOf row) := by
    unfold OnBytes.Desc.First.K4.entries
    rw [List.getElem?_map, hrow]
    rfl
  have he2 : (ds.map (·.entry))[i]? = some d.entry := by
    rw [List.getElem?_map, hd]
    rfl
  rw [hent, he] at he2
  have e : d.entry = OnBytes.Desc.First.K4.entryOf row := (Option.some.inj he2).symm
  have hk := hkind d (List.mem_of_getElem? hd)
  rw [e] at hk
  have hk2 := k4_kind_plain row.name hk
  rw [e]
  exact ⟨oneElem_of _ _ h1 h2 rfl rfl hk2.1 hk2.2, Nat.zero_le _⟩

/-- CONDITIONAL: on hent, hkind and hd. **THE ROUND AT WHICH K4's FALL READS SAMPLES ONE FIELD
ELEMENT AND NOTHING ELSE.** -/
theorem k4_coin_h1 (Q : K4Pub) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) {d : RDT}
    (hd : ds[(starts Q).getD 2 0]? = some d) : OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  obtain ⟨row, hrow, hn⟩ := k4CoinRound_row Q
  obtain ⟨h1, h2⟩ := k4_named_plain Q.P Q.hp Q.g row (List.mem_of_getElem? hrow)
    (by rw [hn]; exact List.mem_cons_self)
  exact k4_plain_h1 Q ds hent hkind (i := k4CoinRound Q) hd hrow h1 h2

/-- CONDITIONAL: on the relation. **WHERE ROUNDS' DATA STAND IN THE FRAME's RELATION WITH THE
DECLARED ROUNDS MADE OF A LIST OF ENTRIES, THEIR ENTRIES ARE THAT LIST, AND EACH KIND IS ITS
NAME's.** -/
theorem ent_of_kindFits : ∀ (ds : List RDT) (es : List Fmt.Entry),
    List.Forall₂ ProofFile.Honest.KindFits ds (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) →
      ds.map (·.entry) = es ∧ ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind
  | [], [], _ => ⟨rfl, fun _ h => by cases h⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, e :: es, h => by
    have h' : List.Forall₂ ProofFile.Honest.KindFits (d :: ds)
        (({ entry := e } : Fmt.DeclaredRound) :: es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) := h
    obtain ⟨hd, ht⟩ := List.forall₂_cons.1 h'
    obtain ⟨a, b⟩ := ent_of_kindFits ds es ht
    have e1 : d.entry = e := hd.1
    have e2 : Fmt.kindOf e.name = some d.kind := hd.2
    refine ⟨by rw [List.map_cons, a, e1], fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with ex | hx
    · rw [ex, e1]
      exact e2
    · exact b x hx

/-- CONDITIONAL: on hK. **AT DATA THAT FIT K4's DECLARED ROUNDS THE ROUND AT WHICH K4's FALL READS
IS THERE, AND SAMPLES ONE FIELD ELEMENT AND NOTHING ELSE.** -/
theorem k4_coin_of_kindFits (Q : K4Pub) (ds : List RDT)
    (hK : List.Forall₂ ProofFile.Honest.KindFits ds
      ((OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).map
        fun e => ({ entry := e } : Fmt.DeclaredRound))) :
    ∃ d, ds[(starts Q).getD 2 0]? = some d ∧ OneElem d.entry d.kind ∧ d.entry.logN ≤ 64 := by
  obtain ⟨hent, hkind⟩ := ent_of_kindFits ds _ hK
  obtain ⟨row, hrow, -⟩ := k4CoinRound_row Q
  have hlt : k4CoinRound Q < ds.length := by
    have l1 : ds.length = (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).length := by
      rw [← hent, List.length_map]
    have l2 : (OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g).length =
        (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).length := by
      unfold OnBytes.Desc.First.K4.entries
      rw [List.length_map]
    rw [l1, l2]
    exact (List.getElem?_eq_some_iff.1 hrow).1
  have hd : ds[(starts Q).getD 2 0]? = some ds[k4CoinRound Q] := List.getElem?_eq_getElem hlt
  exact ⟨_, hd, k4_coin_h1 Q ds hent hkind hd⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_plain_h1
#print axioms ProofFile.Honest.K4.k4_coin_h1
#print axioms ProofFile.Honest.K4.ent_of_kindFits
#print axioms ProofFile.Honest.K4.k4_coin_of_kindFits
