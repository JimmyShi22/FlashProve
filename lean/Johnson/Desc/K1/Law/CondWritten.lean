-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/CondWritten.lean: the records of Johnson/Desc/K1/Law/CondLit.lean against the
library's written lists of
rounds of a key file and of a proof file at the full-size example: in each of the six lists the
rounds of seeds are, one by one and at the same numbers, the records of that chain; each has the
entry that the kind K1 declares at the record's numbers; and the round behind it holds the record's
answers, and, where it is named "SEND answer", has the entry that the kind declares for its second
round.

Johnson/G/DryKeyLit.lean and Johnson/G/DryProofLit.lean write out the three lists of rounds of a key
file (18851, 68 and 30 rounds) and of a proof file (48293, 68 and 30). So: at EVERY round of seeds
of these six lists there is a record at which the kind's test says yes and whose declared entry is
the written round's: 114 places: 6, 9 and 4 in the key file, 82, 9 and 4 in the proof file. The
records bear the numbers of the plans' entries; in the key file's first chain these are one above
the
numbers of the written list's rounds, in the five other chains they are the same: by the comparison.
  pairsIn R: the rounds of seeds of a list of written rounds: the number from 1, the entry, the
      entry
      of the round behind
  litAt: the records of a file's chain, each with the number of its entry "SEND seed"
  pairOk, fitsB: the comparison, as a test with code
  writtenFull: the six lists, each with its file's and its chain's number and that difference
  written_test: the test says yes at all six: one evaluation in Lean's kernel (decide +kernel)
  written_counts: 6, 9, 4, 82, 9, 4
  seedEntry_at, answerEntry_at: the two declared entries read of a place its codes, its messages and
      the work of its round alone
  k01_written: at every round of seeds of the six lists: a record of that chain at that number; the
      test's yes; what it promises; the two entries
  k01_written_place: the same in the letters of the kind's laws: at every place P with the record's
      codes and messages and no work

What is not claimed. The entry file's chain (5 sendings): the library has no written list of its
rounds. That the written lists are those of a description made of the release's files: that is asked
by a test at the time of running, or shown by a run, elsewhere. That the block that stands at a
round
of seeds in a description has the record's messages: an entry holds the number of trees, of seeds
and
of coordinates, not the messages. A list's last round is not looked at as a round of seeds (it has
none behind it). What Johnson/Desc/K1/Law/CondLit.lean and the two written files do not claim.
Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.CondLit
import Johnson.G.DryProofLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G

/-! ## Two tools on lists -/

theorem zip_all_left {α β : Type} (p : α → β → Bool) : ∀ (A : List α) (B : List β),
    A.length = B.length → ((A.zip B).all fun z => p z.1 z.2) = true →
      ∀ a ∈ A, ∃ b ∈ B, p a b = true
  | [], _, _, _, a, ha => by cases ha
  | _ :: _, [], h, _, _, _ => by cases h
  | x :: A, y :: B, h, hall, a, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hall.1⟩
    · obtain ⟨b, hb, hp⟩ := zip_all_left p A B (Nat.succ.inj h) hall.2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hp⟩

/-! ## The comparison -/

/-- The rounds of seeds: the number from 1, the entry, the entry of the round behind. -/
def pairsIn (R : Rounds) : List (Nat × Fmt.Entry × Fmt.Entry) :=
  ((R.zip (R.drop 1)).zipIdx.filter fun x => decide (x.1.1.1.kind = .seeds)).map fun x =>
    (x.2 + 1, x.1.1.1.entry, x.1.2.1.entry)

theorem mem_pairsIn {R : Rounds} {i : Nat} {d d' : Fmt.Round × List Fmt.Stored}
    (h : R[i]? = some d) (h' : R[i + 1]? = some d') (hk : d.1.kind = .seeds) :
    (i + 1, d.1.entry, d'.1.entry) ∈ pairsIn R := by
  refine List.mem_map.2 ⟨((d, d'), i), List.mem_filter.2 ⟨?_, by simp [hk]⟩, rfl⟩
  refine List.mem_zipIdx_iff_getElem?.2 (List.getElem?_zip_eq_some.2 ⟨h, ?_⟩)
  rw [List.getElem?_drop, Nat.add_comm]
  exact h'

/-- The records of a file's chain, each with the number of its entry "SEND seed". -/
def litAt (S : List SendLit) (Pk : List (Codes × List (OracleShape × Nat))) (file chain : Nat) :
    List (Nat × SendRow) :=
  ((S.zip Pk).filter fun x => x.1.1 == file && x.1.2.1 == chain).map fun x =>
    (x.1.2.2.1, ⟨x.2.1, x.1.2.2.2, x.2.2⟩)

theorem litAt_mem {S : List SendLit} {Pk : List (Codes × List (OracleShape × Nat))}
    {file chain : Nat} {y : Nat × SendRow} (h : y ∈ litAt S Pk file chain) :
    y.2 ∈ litRows S Pk := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact List.mem_map.2 ⟨x, (List.mem_filter.1 hx).1, rfl⟩

/-- A written round of seeds with the round behind it, against a record. off: by how much the number
of the plan's entry is above the number of the written round. -/
def pairOk (off : Nat) (x : Nat × Fmt.Entry × Fmt.Entry) (y : Nat × SendRow) : Bool :=
  decide (x.1 + off = y.1) && decide (x.2.1 = seedEntry y.2.par) &&
    decide (x.2.2.answers = y.2.par.answers) &&
    (decide (x.2.2.name ≠ "SEND answer") || decide (x.2.2 = answerEntry y.2.par))

/-- A list of written rounds against a chain's records. -/
def fitsB (off : Nat) (R : Rounds) (l : List (Nat × SendRow)) : Bool :=
  decide ((pairsIn R).length = l.length) && ((pairsIn R).zip l).all fun z => pairOk off z.1 z.2

/-- The six written lists, each with its file's and its chain's number, and by how much the plan's
entries are numbered above the list's rounds: by 1 in the key file's first chain, else by 0. -/
def writtenFull : List (Nat × Nat × Nat × Rounds) :=
  [(0, 0, 1, dryKeyFull.1), (0, 1, 0, dryKeyFull.2.1), (0, 2, 0, dryKeyFull.2.2),
   (2, 0, 0, dryProofFull.1), (2, 1, 0, dryProofFull.2.1), (2, 2, 0, dryProofFull.2.2)]

/-- **The six written lists' rounds of seeds are the records.** By evaluation in Lean's kernel. -/
theorem written_test : (writtenFull.all fun x =>
    fitsB x.2.2.1 x.2.2.2 (litAt sendsFullLit packFullLit x.1 x.2.1)) = true := by
  decide +kernel

theorem written_counts : (writtenFull.map fun x =>
    (litAt sendsFullLit packFullLit x.1 x.2.1).length) = [6, 9, 4, 82, 9, 4] := by
  decide +kernel

/-! ## The declared entries read the codes, the messages and the work alone -/

theorem seedEntry_at (r : SendRow) (P : Par) (h : r.At P) (hw : P.work = 0) :
    seedEntry P = seedEntry r.par := by
  have hs : P.sent = r.par.sent := h.2.trans r.par_sent.symm
  have hc : P.codes = r.par.codes := h.1
  have hw' : P.work = r.par.work := hw
  simp only [seedEntry, Par.trees, Par.seeds, Par.coordinates, Par.tuple, hs, hc, hw']

theorem answerEntry_at (r : SendRow) (P : Par) (h : r.At P) :
    answerEntry P = answerEntry r.par := by
  have hs : P.sent = r.par.sent := h.2.trans r.par_sent.symm
  simp only [answerEntry, Par.answers, Par.tuple, hs]

/-! ## At every round of seeds -/

/-- **At every round of seeds of the six written lists.** -/
theorem k01_written (x : Nat × Nat × Nat × Rounds) (hx : x ∈ writtenFull) (i : Nat)
    (d d' : Fmt.Round × List Fmt.Stored) (h : x.2.2.2[i]? = some d)
    (h' : x.2.2.2[i + 1]? = some d')
    (hk : d.1.kind = .seeds) :
    ∃ r : SendRow, (i + 1 + x.2.2.1, r) ∈ litAt sendsFullLit packFullLit x.1 x.2.1 ∧ r ∈ litFull ∧
      r.ok = true ∧ r.Holds ∧ d.1.entry = seedEntry r.par ∧
      d'.1.entry.answers = r.par.answers ∧
      (d'.1.entry.name = "SEND answer" → d'.1.entry = answerEntry r.par) := by
  have ht := List.all_eq_true.1 written_test x hx
  unfold fitsB at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨y, hy, hp⟩ := zip_all_left (pairOk x.2.2.1) _ _ ht.1 ht.2 _ (mem_pairsIn h h' hk)
  unfold pairOk at hp
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hp
  have hm : y.2 ∈ litFull := litAt_mem hy
  obtain ⟨n, r⟩ := y
  simp only at p1 p2 p3 p4 hm
  subst p1
  exact ⟨r, hy, hm, (k01_full r hm).1, (k01_full r hm).2, p2, p3, fun hn =>
    p4.resolve_left (fun c => c hn)⟩

/-- **In the letters of the kind's laws**: at every place with the record's codes and messages and
no work on the round of seeds. -/
theorem k01_written_place (x : Nat × Nat × Nat × Rounds) (hx : x ∈ writtenFull) (i : Nat)
    (d d' : Fmt.Round × List Fmt.Stored) (h : x.2.2.2[i]? = some d)
    (h' : x.2.2.2[i + 1]? = some d')
    (hk : d.1.kind = .seeds) :
    ∃ r : SendRow, (i + 1 + x.2.2.1, r) ∈ litAt sendsFullLit packFullLit x.1 x.2.1 ∧
      ∀ P : Par, r.At P → P.work = 0 →
        condPort P (radFrom P r.l) = true ∧ d.1.entry = seedEntry P ∧
          (d'.1.entry.name = "SEND answer" → d'.1.entry = answerEntry P) := by
  obtain ⟨r, h1, -, -, h4, h5, -, h7⟩ := k01_written x hx i d d' h h' hk
  exact ⟨r, h1, fun P hP hw => ⟨(h4.1 P hP).1, h5.trans (seedEntry_at r P hP hw).symm,
    fun hn => (h7 hn).trans (answerEntry_at r P hP).symm⟩⟩

end VerifiableInference.Desc.K1
