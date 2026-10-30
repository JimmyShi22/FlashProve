-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/KeptSeatsB.lean: the code switch: ONE TEST WITH CODE
ON PUBLIC LISTS, BY PLACE, FOR WHAT KeptSeatOf.lean's keptSeat_of_fold AND PinKeptJoin.lean's
KeptFacts ASK OF THE PLAN AT A KEPT MEMBER.
  keptSeatB    at one kept member: its shape sh, its seat (tree, tenant) and its message's number
               old: the plan's list of places has (a tree, the seat's tenant) at old · THAT TREE IS
               THE SEAT's TREE, AND IS BELOW THE NUMBER trees (so that the law on the oracles'
               reading by key, Johnson/Top/H0/K2Hears/OrcAtFrame.lean, applies) · the plan's list of
               trees' shapes has that tree · the tree is as long as the main code's positions ·
               where the description tells the seat's tree, the listed shape's skip in front of the
               tenant is the description's · the seat is one of the listed seats · its place in that
               list is old
  keptSeatB_says  a yes gives these eight: six in the words of the hypotheses hL, hLs, hlog, hskip
               of keptSeat_of_fold and, up to the unfolding of numAt (the place of the
               member's seat in the list), of the fields listed, num of KeptFacts; and the two of
               the clause on the seat's tree
  keptSeatsB   at a switch: by place n: the n-th kept member of the typed list lo (kept[n]) against
               the n-th number of olds
  keptSeatsB_at  a yes gives keptSeatB at every place
  plan_at_kept  at a held member k of a typed structure r: where olds has the number old at the
               member's place in r.kept, a yes at (r.lo, r.kept, olds) gives keptSeatB at k's shape,
               seat and old
LIMITS. A TEST AND WHAT ITS YES SAYS. IT HAS BEEN RUN NOWHERE: WHERE IT SAYS NO, EVERY LAW THAT
TAKES ITS YES AS A PREMISE IS EMPTY. In particular «the listed tree is the seat's tree» compares a
tree's place in the first chain's book with a tree's number through the file: they are one only if
the first chain's trees are numbered from 0: NOT CHECKED BY US. G, L, seats, seat, kept and olds are
letters for public lists. THAT olds ARE THE NUMBERS OF THE KEPT MEMBERS IN THE VERIFIER's STATE (the
frame's entries' own) IS NOT SAID HERE: it is the one fact on the state that these eight leave.
No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.KeptSeatOf
import Johnson.Top.H0.K2Caller.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.K12.Door (Laid)

variable {Xi : Type} (G : FileDescription Xi) (cs : Codes) (L : Laid) (seats : List (ℕ × ℕ)) (trees : ℕ)

/-- **The test at one kept member.** -/
def keptSeatB (sh : OracleShape) (seat : ℕ × ℕ) (old : ℕ) : Bool :=
  (match L.places[old]? with
    | some q => q.2 == seat.2 && q.1 == seat.1 && decide (q.1 < trees) &&
      (match L.shapes[q.1]? with
        | some sh0 => decide ((cMain cs sh).a ≤ sh0.logN) &&
          (match G.oracleAt seat.1 with
            | some o => (sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 == o.mainSkip seat.2
            | none => true)
        | none => false)
    | none => false) && seats.contains seat && seats.idxOf seat == old

/-- **What its yes says.** -/
theorem keptSeatB_says {sh : OracleShape} {seat : ℕ × ℕ} {old : ℕ}
    (h : keptSeatB G cs L seats trees sh seat old = true) :
    (∃ tp sh0, L.places[old]? = some (tp, seat.2) ∧ tp = seat.1 ∧ tp < trees ∧
      L.shapes[tp]? = some sh0 ∧
      2 ^ (cMain cs sh).a ≤ 2 ^ sh0.logN ∧
      ∀ o, G.oracleAt seat.1 = some o →
        (sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = o.mainSkip seat.2) ∧
      seat ∈ seats ∧ seats.idxOf seat = old := by
  unfold keptSeatB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, h2, h3⟩
  cases hp : L.places[old]? with
  | none => simp [hp] at h1
  | some q =>
    rw [hp] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨e, e1⟩, e2⟩, h1⟩ := h1
    cases hs : L.shapes[q.1]? with
    | none => simp [hs] at h1
    | some sh0 =>
      rw [hs] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      refine ⟨q.1, sh0, by rw [← e], e1, e2, hs, Nat.pow_le_pow_right (by decide) h1.1,
        fun o ho => ?_⟩
      have h4 := h1.2
      rw [ho] at h4
      simpa using h4

variable (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)

/-- **The test at a switch, by place.** -/
def keptSeatsB (kept olds : List ℕ) : Bool :=
  (List.range kept.length).all fun n =>
    match kept[n]?, olds[n]? with
    | some i, some old =>
      if h : i < lo.length then keptSeatB G cs L seats trees (lo.get ⟨i, h⟩).1 (seat ⟨i, h⟩) old
      else false
    | _, _ => false

theorem keptSeatsB_at {kept olds : List ℕ}
    (h : keptSeatsB G cs L seats trees lo seat kept olds = true)
    (n : ℕ) (i : Fin lo.length) (hi : kept[n]? = some i.val) :
    ∃ old, olds[n]? = some old ∧
      keptSeatB G cs L seats trees (lo.get i).1 (seat i) old = true := by
  unfold keptSeatsB at h
  have hn : n < kept.length := (List.getElem?_eq_some_iff.1 hi).1
  have e := List.all_eq_true.1 h n (List.mem_range.2 hn)
  rw [hi] at e
  cases ho : olds[n]? with
  | none => simp [ho] at e
  | some old =>
    rw [ho] at e
    simp only [dif_pos i.isLt] at e
    exact ⟨old, rfl, e⟩

/-- **At a held member of the typed structure r**: where olds has the number old at the member's
place in r.kept. -/
theorem plan_at_kept {r : SwRow} {H : r.OK} (seat : Fin r.lo.length → ℕ × ℕ) {olds : List ℕ}
    (h : keptSeatsB G r.cs L seats trees r.lo seat r.kept olds = true)
    (k : {a // (plainHd r H).cl a}) (old : ℕ)
    (ho : olds[r.kept.idxOf k.1.1.val]? = some old) :
    keptSeatB G r.cs L seats trees (r.lo.get k.1.1).1 (seat k.1.1) old = true := by
  have hk : k.1.1.val ∈ r.kept := k.2.snd
  obtain ⟨old', h1, h2⟩ := keptSeatsB_at G r.cs L seats trees r.lo seat h
    (r.kept.idxOf k.1.1.val) k.1.1 (List.getElem?_idxOf hk)
  rw [ho] at h1
  rw [Option.some.inj h1]
  exact h2

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.plan_at_kept

#print axioms VerifiableInference.Desc.First.K2Caller.keptSeatB_says
#print axioms VerifiableInference.Desc.First.K2Caller.keptSeatsB_at
