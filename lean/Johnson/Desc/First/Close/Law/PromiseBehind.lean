-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PromiseBehind.lean: THE TABLE's PROMISE BEHIND A BLOCK THAT CLOSES THE
LAST OPEN CLASSES OF ROWS, CLAUSE BY CLAUSE; AND THAT THE TABLE's ROWS AT THE PLACES OF THE KIND K10
ARE SUCH. A rule over letters; a test on the table, with its yes at two rows of segments. A file
BESIDE the table of joints: it turns nothing of it.

Why. A block's second tie to the table asks the WHOLE promise behind the block (`onAt`,
Johnson/Desc/First/Borders.lean). The table's files have the rule for a QUIET row (one that closes
and opens no class of rows and no pin with a sample: Johnson/Desc/First/PromiseRides.lean); at a row
that is not quiet that rule says nothing. K10's row closes the segment's classes of rows and its
pins, and opens "carry" and the kept pin: it is not quiet.
  `rowsHeld_none`, `membersHeld_none`: where no class of rows is open the two Bools say yes of every
    record.
  `onAt_step_close`: r any row; O' := `stepOpen O r`. IF NO CLASS OF ROWS IS OPEN BEHIND (hRows) AND
    EVERY SAMPLED TENANT WHOSE PIN IS OPEN BEHIND HAD AN OPEN PIN IN FRONT (hSub): the promise
    behind follows from the promise in front and: a mark stays; "decodes" rides; the book-keeping
    behind; "in order" rides; the public items behind; the book's numbers behind; `pubP` behind;
    "held" rides, "shown" and "no collision" ride as a pair, at the tenants in front. After the form
    of `onAt_step_held`: `rowsHeld` and `membersHeld` are asked of nobody.
  `mem_sampledIn`, `sampled_step_close`: hSub at a row that opens just "carry" and the kept pin of a
    segment whose three pins are open in front: from "what is kept lies in its group" (the last
    clause of the table's own test `numbersFit`).
  `closersFit links ps O`: A TEST ON THE TABLE: at every place of the kind K10: the row's outs are
    these two; the three pins are open in front; no class of rows is open behind. `closersFit_at`:
    what its yes gives at the k-th place, in the words of `openSets`. `sortsOf n`,
    `closersFit_real`: IT SAYS YES at 25 and at 5 segments (feed-forward and attention in turn, the
    head last), whichever way the blocks behind go: by the kernel. `closersFit_tooth`: it can say
    no.
Limits. `onAt_step_close` is a rule over letters: its eleven other premises are paid by nobody here;
those on the meaning's letters can be paid only at a filling. `sortsOf` is written in this file:
that `sortsOf 25` is the row of segments of a description in scope is held in a file of this
project that is not in this library (SortsAre.lean), against `subAt` (Johnson/IMR/LinkSeat.lean).
Today: `sorts_are_w` (Johnson/LPFK10R/CloseShare.lean) states sortsOf 25 = LW (LW := (List.range 25).map IM.subAt), under no premise, and `subs_scope` (Johnson/IMR/LinkSeat.lean) states ∀ l < 25, (ProofFile.subsOf Z)[l]? = some (subAt l), under hS : VerifierAndGoals.InScope P = true, hR : VerifierAndGoals.readFiles P = .ok pp and O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B. "What is kept lies in its group" is a premise. Nothing on soundness.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

section
variable {P W : Type} (N : Numbers)

/-- Where no class of rows is open, the Bool on the rows' lists says yes. -/
theorem rowsHeld_none (O : List Item) (s : S) (h : rowSegs O = []) : rowsHeld N O s = true := by
  unfold rowsHeld
  rw [h]
  rfl

/-- The like for the Bool on the groups' members. -/
theorem membersHeld_none (O : List Item) (s : S) (h : rowSegs O = []) :
    membersHeld N O s = true := by
  unfold membersHeld
  rw [h]
  rfl

/-- **THE PROMISE BEHIND A BLOCK THAT CLOSES THE LAST OPEN CLASSES OF ROWS.** -/
theorem onAt_step_close (Mg : Meaning P W) (links : List ModelPart) (p p' : Option Place)
    (O : List Item) (Q Q' : List Pub) (r : BlockRow) (a b : P × S) (y y' : Strs)
    (hRows : rowSegs (stepOpen O r) = [])
    (hSub : ∀ x ∈ sampledIn N (stepOpen O r), x ∈ sampledIn N O)
    (ha : onAt N Mg links p O Q a y)
    (hMark : a.2.failed ≠ none → b.2.failed ≠ none)
    (hDec : Mg.decodes a y → Mg.decodes b y')
    (hShape : a.2.failed = none → b.2.failed = none → shapeAt links p' b.2 = true)
    (hIn : a.2.failed = none → b.2.failed = none → Mg.inOrder a = true → Mg.inOrder b = true)
    (hPub : a.2.failed = none → b.2.failed = none → pubHeld Mg O Q a = true →
      pubHeld Mg (stepOpen O r) Q' b = true)
    (hBook : a.2.failed = none → b.2.failed = none → bookAt N p a.2 = true →
      bookAt N p' b.2 = true)
    (hPP : a.2.failed = none → b.2.failed = none → (∀ q ∈ Q, Mg.pubP q a) →
      ∀ q ∈ Q', Mg.pubP q b)
    (hHeld : a.2.failed = none → b.2.failed = none → ∀ x ∈ sampledIn N O,
      Mg.held x.1 x.2 a = true → Mg.held x.1 x.2 b = true)
    (hSN : a.2.failed = none → b.2.failed = none → ∀ x ∈ sampledIn N O,
      Mg.shown x.1 x.2 y ∧ Mg.noColl x.1 x.2 a y → Mg.shown x.1 x.2 y' ∧ Mg.noColl x.1 x.2 b y') :
    onAt N Mg links p' (stepOpen O r) Q' b y' := by
  refine ⟨hDec ha.1, ?_⟩
  by_cases hb : b.2.failed = none
  · have hm : a.2.failed = none := Classical.byContradiction fun h => hMark h hb
    rcases ha.2 with hx | ⟨hB, hs, hall, hpp⟩
    · exact absurd hm hx
    · right
      simp only [Bool.and_eq_true] at hB
      obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, h4⟩, h5⟩, h6⟩ := hB
      refine ⟨?_, ?_, ?_, hPP hm hb hpp⟩
      · rw [hShape hm hb, rowsHeld_none N _ _ hRows, membersHeld_none N _ _ hRows, hIn hm hb h4,
          hPub hm hb h5, hBook hm hb h6]
        rfl
      · unfold samplesHeld at hs ⊢
        apply List.all_eq_true.2
        intro x hx
        exact hHeld hm hb x (hSub x hx) (List.all_eq_true.1 hs x (hSub x hx))
      · intro x hx
        exact hSN hm hb x (hSub x hx) (hall x (hSub x hx))
  · left
    exact hb

/-- A tenant is sampled in a list of items just if it is in one of them. -/
theorem mem_sampledIn (O : List Item) (x : Nat × Nat) :
    x ∈ sampledIn N O ↔ ∃ i ∈ O, x ∈ sampledIn N [i] := by
  unfold sampledIn
  simp only [List.mem_flatMap, List.mem_singleton, exists_eq_left]

/-- **hSub at a row that opens "carry" and the kept pin of a segment whose three pins are open in
front**: from "what is kept lies in its group" (the last clause of the table's own test on its
numbers). -/
theorem sampled_step_close (O : List Item) (r : BlockRow) (m : Nat)
    (hr : r.outs = [.carry m, .pinKept m]) (hP : ∀ i ∈ pinsOf m, i ∈ O)
    (hK : ∀ x ∈ N.keptOf m, x ∈ N.group m) :
    ∀ x ∈ sampledIn N (stepOpen O r), x ∈ sampledIn N O := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := (mem_sampledIn N _ x).1 hx
  unfold stepOpen at hi
  rcases List.mem_append.1 hi with h | h
  · exact (mem_sampledIn N O x).2 ⟨i, (List.mem_filter.1 h).1, hxi⟩
  · have h' := (List.mem_filter.1 h).1
    rw [hr] at h'
    rcases List.mem_cons.1 h' with rfl | h'
    · simp [sampledIn] at hxi
    · obtain rfl := List.mem_singleton.1 h'
      have hk : x ∈ N.keptOf m := by simpa [sampledIn] using hxi
      have hg := hK x hk
      unfold Numbers.group at hg
      rcases List.mem_append.1 hg with hg | hg
      · rcases List.mem_append.1 hg with hg | hg
        · exact (mem_sampledIn N O x).2 ⟨.pin m 0, hP _ (by simp [pinsOf]), by simpa [sampledIn]⟩
        · exact (mem_sampledIn N O x).2 ⟨.pin m 1, hP _ (by simp [pinsOf]), by simpa [sampledIn]⟩
      · exact (mem_sampledIn N O x).2 ⟨.pin m 2, hP _ (by simp [pinsOf]), by simpa [sampledIn]⟩

end

/-- A TEST ON THE TABLE: at every place of the kind K10: the block's row opens just "carry" and the
kept pin of its segment; the segment's three pins are open in front; AND NO CLASS OF ROWS IS OPEN
BEHIND. -/
def closersFit (links : List ModelPart) : List Place → List Item → Bool
  | [], _ => true
  | p :: ps, O =>
    (p.kind != .K10 ||
      ((rowOf links p).outs == [.carry (p.link.getD 0), .pinKept (p.link.getD 0)] &&
        (pinsOf (p.link.getD 0)).all O.contains &&
        (rowSegs (stepOpen O (rowOf links p))).isEmpty)) &&
      closersFit links ps (stepOpen O (rowOf links p))

/-- **What a yes of the test gives at a place of the kind**: k: the place's number in the list. -/
theorem closersFit_at (links : List ModelPart) :
    ∀ (ps : List Place) (O : List Item) (k : Nat) (p : Place), closersFit links ps O = true →
      ps[k]? = some p → p.kind = .K10 →
      ∃ Ok, (openSets links ps O)[k]? = some Ok ∧
        (openSets links ps O)[k + 1]? = some (stepOpen Ok (rowOf links p)) ∧
        (rowOf links p).outs = [.carry (p.link.getD 0), .pinKept (p.link.getD 0)] ∧
        (∀ i ∈ pinsOf (p.link.getD 0), i ∈ Ok) ∧ rowSegs (stepOpen Ok (rowOf links p)) = []
  | [], _, _, _, _, h, _ => by simp at h
  | q :: ps, O, 0, p, hf, h, hk => by
    obtain rfl : q = p := by simpa using h
    unfold closersFit at hf
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      List.all_eq_true, List.contains_iff_mem, List.isEmpty_iff] at hf
    obtain ⟨h1 | ⟨⟨h1, h2⟩, h3⟩, -⟩ := hf
    · exact absurd hk h1
    · refine ⟨O, rfl, ?_, h1, h2, h3⟩
      cases ps <;> rfl
  | q :: ps, O, k + 1, p, hf, h, hk => by
    unfold closersFit at hf
    obtain ⟨Ok, e1, e2, e3⟩ := closersFit_at links ps _ k p (Bool.and_eq_true_iff.1 hf).2
      (by simpa using h) hk
    exact ⟨Ok, e1, e2, e3⟩

/-- The sorts of the segments of the two real plans: feed-forward and attention in turn, the head
last. -/
def sortsOf (n : Nat) : List ModelPart :=
  (List.range n).map fun l =>
    if l + 1 == n then .head else if l % 2 == 0 then .layers else .attention

set_option maxRecDepth 1000000 in
/-- **The test says yes at both real rows of segments**, whichever way the blocks behind go. -/
theorem closersFit_real : ∀ several : Bool,
    closersFit (sortsOf 25) (flatPlacesOf (sortsOf 25) several) (start (sortsOf 25)) = true ∧
      closersFit (sortsOf 5) (flatPlacesOf (sortsOf 5) several) (start (sortsOf 5)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A tooth: it can say no: at an open set in front in which a class of rows of a far segment stands
open from the start. -/
theorem closersFit_tooth :
    closersFit (sortsOf 5) (flatPlacesOf (sortsOf 5) true)
      (.row 99 .equation :: start (sortsOf 5)) = false := by
  decide +kernel

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.sampled_step_close
#print axioms VerifiableInference.Desc.First.closersFit_at
#print axioms VerifiableInference.Desc.First.closersFit_real
#print axioms VerifiableInference.Desc.First.closersFit_tooth
#print axioms VerifiableInference.Desc.First.rowsHeld_none
#print axioms VerifiableInference.Desc.First.membersHeld_none
#print axioms VerifiableInference.Desc.First.onAt_step_close
