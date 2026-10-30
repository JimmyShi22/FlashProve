-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawBefore.lean: THE SMALLNESS TEST, ITS FIRST HALF: "FIXED BEFORE THE DRAW",
FROM THE TEST ON THE PLAN.

The proved block's count for the draw (Cb/Pv/Tail/Know.lean) is for matrices and reads that do not
depend on the drawn matrix. On the typed side that is a condition on the caller, stated in no type
(Johnson/Top/H/TailRng.lean, Limits: "the messages of Sg are what is committed before the matrix is
drawn"). In a description made of blocks the order is a test on the plan alone: a block names, in
`before`, the oracle messages that must stand in front of its first draw, and `FileDescription.beforeOk` (a
conjunct of `FileDescription.planOk`, Johnson/Desc/Block.lean) asks it by `beforeAt`. This file says what a
yes of that test gives, for any block and then for the kind's, and names what a caller of the proved
block owes to spend it.
  `sendRound_roots`: the round that `sendRound` finds for a message sends a root.
  `beforeAt_at`: GENERAL IN THE BLOCK: if `beforeAt` says yes of a list of blocks, then each message
    that a block of the list names in `before` is sent, in its chain, in a round not later than the
    block's first drawing round (own chain), and the chain is the block's own or an earlier one.
  `first_draw`: the kind's one round draws, where the tests on the plan alone hold: so its first
    drawing round is its round.
  `before_draw`: THE KIND'S: every message that it names (those with the matrices; those with the
    reads) is sent in a round of the first chain STRICTLY in front of the round of the draw.
  `CallerAt p c`: what whoever lays a caller c of the proved block at the place with the numbers p
    owes. Data and three laws: a set `dep` of the caller's oracle messages; the symbols and the
    reads are read off these alone; each has a number in the first chain's order of sending, and
    that number is named by the block.
  `caller_before_draw`: then the number that the letters give to each of these is the number of a
    message that is sent strictly in front of the round of the draw.
  `file_before_draw`, `file_caller_before_draw`: the same from the file's ONE test on the plan,
    `FileDescription.planOk`, for a description whose first chain's flat list has the kind's block in it.
Definitions, statements and proofs.

Limits. `CallerAt.no` IS FREE DATA: that the number given to an oracle message of the typed
signature is the number of the message of the file that it stands for is the wiring's to say;
NOTHING HERE CHECKS IT, and `CallerAt p c` is inhabited for every caller c by a constant number: so
`caller_before_draw` and `file_caller_before_draw` say of the CALLER's messages only what that tie,
which is owed, would make of them. "Fixed before the draw" is had here AT THE PLAN
(`file_before_draw`) and is owed below it: a value of `CallerAt` at the real callers with that tie;
and that the arrays which the matrix multiplies LIE IN the messages that the block names. Until
these are paid the finer test of the program `verify-on-bytes` (each array looked up in the layout;
its message past and sampled) must go on standing in front of this place. "Sent in front" is of
rounds of the declared plan; that a file's bytes come in that order is the reading's. The clause of
`beforeAt` on sampled messages (an answer's round in between) is drawn out in
Johnson/Desc/First/K8/LawAnswers.lean, not here. `before` names messages, not which array lies in
which: coarser than the test of that program (Hear.lean's head says so).


-/
import Johnson.Desc.First.K8.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- The rounds of a list of blocks, counted. -/
def roundsIn (l : List (Block S Cl)) : Nat := (l.map fun b => b.rounds.length).sum

/-- One of the three chains' declared rounds, by the chain's number from 1. -/
def chainOf (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (c : Nat) : List
    Fmt.DeclaredRound :=
  if c == 1 then D.1 else if c == 2 then D.2.1 else D.2.2

/-- The round that is found for a message sends a root. -/
theorem sendRound_roots : ∀ (ds : List Fmt.DeclaredRound) (n i : Nat), sendRound ds n = some i →
    ∃ r, ds[i]? = some r ∧ 0 < r.entry.roots
  | [], _, _, h => by simp [sendRound] at h
  | r :: l, n, i, h => by
    unfold sendRound at h
    by_cases hn : n < r.entry.roots
    · rw [if_pos hn] at h
      obtain rfl : 0 = i := by simpa using h
      exact ⟨r, rfl, by omega⟩
    · rw [if_neg hn] at h
      cases hs : sendRound l (n - r.entry.roots) with
      | none => simp [hs] at h
      | some j =>
        rw [hs] at h
        obtain rfl : j + 1 = i := by simpa using h
        obtain ⟨r', h1, h2⟩ := sendRound_roots l _ j hs
        exact ⟨r', by simpa using h1, h2⟩

/-- **What a yes of `beforeAt` gives, at any block of the list.** -/
theorem beforeAt_at (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) :
    ∀ (pre : List (Block S Cl)) (from' : Nat) (b : Block S Cl) (post : List (Block S Cl)),
      beforeAt D O c from' (pre ++ b :: post) = true → ∀ m ∈ b.before,
        ∃ i, sendRound (chainOf D m.1) m.2 = some i ∧ 1 ≤ m.1 ∧ m.1 ≤ c + 1 ∧
          i ≤ (if m.1 == c + 1 then from' + roundsIn pre + b.rounds.findIdx drawsAny
            else (chainOf D m.1).length)
  | [], from', b, post, h, m, hm => by
    simp only [List.nil_append, beforeAt, Bool.and_eq_true, List.all_eq_true] at h
    have hm' := h.1 m hm
    unfold chainOf
    split at hm'
    · exact absurd hm' (by simp)
    · rename_i i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm'
      exact ⟨i, hs, hm'.1.1.1, hm'.1.1.2, by simpa [roundsIn] using hm'.1.2⟩
  | a :: pre, from', b, post, h, m, hm => by
    simp only [List.cons_append, beforeAt, Bool.and_eq_true] at h
    obtain ⟨i, h1, h2, h3, h4⟩ := beforeAt_at D O c pre (from' + a.rounds.length) b post h.2 m hm
    refine ⟨i, h1, h2, h3, ?_⟩
    have e : from' + a.rounds.length + roundsIn pre = from' + roundsIn (a :: pre) := by
      simp [roundsIn, Nat.add_assoc]
    rwa [e] at h4

theorem length_flatMap_rounds (l : List (Block S Cl)) : (l.flatMap (·.rounds)).length = roundsIn l
    := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [roundsIn, List.flatMap_cons] at ih ⊢

/-- In the chain's declared rounds, the round number `roundsIn pre` is the first round of the block
behind pre. -/
theorem flatMap_rounds_at (pre : List (Block S Cl)) (b : Block S Cl) (post : List (Block S Cl)) :
    ((pre ++ b :: post).flatMap (·.rounds))[roundsIn pre]? = (b.rounds ++ post.flatMap
        (·.rounds))[0]? := by
  rw [List.flatMap_append, List.flatMap_cons, ← length_flatMap_rounds pre,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]

end VerifiableInference.Desc

namespace VerifiableInference.Desc.First.K8

open VerifiableInference.OnPublicFiles

/-- Where the tests on the plan alone hold, the kind's one round draws. -/
theorem first_draw {S Cl : Type} (seat : Seat S) (p : Par) (h : (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk =
    true) :
    (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds.findIdx drawsAny = 0 := by
  have h' : (!p.ks.isEmpty && columns p != 0 && p.tau != 0 && !p.matsIn.isEmpty &&
      !p.readsIn.isEmpty && p.ms.length == p.ks.length &&
      p.asks.all fun a => a.2.1 != 0 && a.2.2 != 0) = true := h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
  have hc : columns p ≠ 0 := h'.1.1.1.1.1.2
  have ht : p.tau ≠ 0 := h'.1.1.1.1.2
  have hd : drawsAny (round p) = true := by
    have : columns p * p.tau ≠ 0 := Nat.mul_ne_zero hc ht
    simp [drawsAny, round, this]
  show [round p].findIdx drawsAny = 0
  simp [List.findIdx_cons, hd]

/-- **The kind's: every message that it names is sent strictly in front of the round of the draw.**
pre: the first chain's blocks in front of the kind's; the round of the draw is the chain's round
number `roundsIn pre`. -/
theorem before_draw {S Cl : Type} (seat : Seat S) (p : Par)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (pre post : List (Block S Cl))
    (hb : beforeAt D O 0 0 (pre ++ approximateRangeProofDrawKind seat p :: post) = true)
    (hp : (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk = true)
    (hD : D.1[roundsIn pre]? = some (round p)) (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    ∃ i, sendRound D.1 n = some i ∧ i < roundsIn pre := by
  have hm : ((1, n) : Nat × Nat) ∈ (approximateRangeProofDrawKind (Cl := Cl) seat p).before := by
    show (1, n) ∈ (p.matsIn ++ p.readsIn).map fun n => (1, n)
    exact List.mem_map.2 ⟨n, hn, rfl⟩
  obtain ⟨i, h1, _, _, h4⟩ := beforeAt_at D O 0 pre 0 (approximateRangeProofDrawKind seat p) post hb (1, n) hm
  rw [first_draw seat p hp] at h4
  have h1' : sendRound D.1 n = some i := by simpa [chainOf] using h1
  have h4' : i ≤ roundsIn pre := by simpa using h4
  refine ⟨i, h1', ?_⟩
  obtain ⟨r, hr, hpos⟩ := sendRound_roots D.1 n i h1'
  rcases Nat.lt_or_ge i (roundsIn pre) with hlt | hge
  · exact hlt
  · have e : i = roundsIn pre := Nat.le_antisymm h4' hge
    rw [e, hD] at hr
    obtain rfl : round p = r := by simpa using hr
    simp [round] at hpos

/-- What whoever lays a caller of the proved block at a place owes, to spend the test on the plan.
-/
structure CallerAt (p : Par) (c : TailCaller) where
  /-- the oracle messages off which the caller reads the symbols and the reads -/
  dep : c.Sg.O → Prop
  /-- meant: an oracle message's number in the first chain's order of sending, from 0. FREE DATA: no
  law here ties it to the message of the file that a stands for: a constant number out of the
  block's list, with `dep` := all, meets all three laws -/
  no : c.Sg.O → Nat
  sym_dep : ∀ m m' : c.Sg.Msg, (∀ a, dep a → m a = m' a) → c.sym m = c.sym m'
  tab_dep : ∀ m m' : c.Sg.Msg, (∀ a, dep a → m a = m' a) → c.tab m = c.tab m'
  named : ∀ a, dep a → no a ∈ p.matsIn ++ p.readsIn

/-- The NUMBER that the letters give to every message off which the caller reads the symbols or the
reads is the number of a message that is sent strictly in front of the round of the draw. NO MORE
THAN THAT: `CallerAt.no` is free data. -/
theorem caller_before_draw {S Cl : Type} (seat : Seat S) (p : Par) (c : TailCaller) (C : CallerAt p
    c)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (pre post : List (Block S Cl))
    (hb : beforeAt D O 0 0 (pre ++ approximateRangeProofDrawKind seat p :: post) = true)
    (hp : (approximateRangeProofDrawKind (Cl := Cl) seat p).planOk = true)
    (hD : D.1[roundsIn pre]? = some (round p)) (a : c.Sg.O) (ha : C.dep a) :
    ∃ i, sendRound D.1 (C.no a) = some i ∧ i < roundsIn pre :=
  before_draw seat p D O pre post hb hp hD (C.no a) (C.named a ha)

/-- **From the file's one test on the plan.** F: a file's description whose first chain's flat list
has the kind's block behind pre. If `F.planOk` says yes, every message that the block names is sent,
in the first chain's declared rounds, strictly in front of the round of the draw. -/
theorem file_before_draw {Xi : Type} (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par)
    (pre post : List (Block F.S₁ F.Cl)) (hflat : F.first.blocksInOrder = pre ++ approximateRangeProofDrawKind seat p :: post)
    (hF : F.planOk = true) (n : Nat) (hn : n ∈ p.matsIn ++ p.readsIn) :
    ∃ i, sendRound F.roundsDeclaredByBlocks.1 n = some i ∧ i < roundsIn pre := by
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hF
  have hbo : F.beforeOk = true := by tauto
  have hbl : blocksOk F.first.blocksInOrder = true := by tauto
  simp only [FileDescription.beforeOk, Bool.and_eq_true] at hbo
  have hb := hbo.1.1
  rw [hflat] at hb hbl
  have hp : (approximateRangeProofDrawKind (Cl := F.Cl) seat p).planOk = true := by
    simp only [blocksOk, List.all_eq_true, Bool.and_eq_true] at hbl
    exact (hbl (approximateRangeProofDrawKind seat p) (by simp)).1
  have hD : F.roundsDeclaredByBlocks.1[roundsIn pre]? = some (round p) := by
    show (F.first.blocksInOrder.flatMap (·.rounds))[roundsIn pre]? = _
    rw [hflat, flatMap_rounds_at]
    rfl
  exact before_draw seat p F.roundsDeclaredByBlocks _ pre post hb hp hD n hn

/-- The like for a caller of the proved block. -/
theorem file_caller_before_draw {Xi : Type} (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par) (c :
           TailCaller)
    (C : CallerAt p c) (pre post : List (Block F.S₁ F.Cl)) (hflat : F.first.blocksInOrder = pre ++ approximateRangeProofDrawKind seat
        p :: post)
    (hF : F.planOk = true) (a : c.Sg.O) (ha : C.dep a) :
    ∃ i, sendRound F.roundsDeclaredByBlocks.1 (C.no a) = some i ∧ i < roundsIn pre :=
  file_before_draw F seat p pre post hflat hF (C.no a) (C.named a ha)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.file_before_draw
#print axioms VerifiableInference.Desc.First.K8.file_caller_before_draw
#print axioms VerifiableInference.Desc.sendRound_roots
#print axioms VerifiableInference.Desc.beforeAt_at
#print axioms VerifiableInference.Desc.First.K8.first_draw
#print axioms VerifiableInference.Desc.First.K8.before_draw
#print axioms VerifiableInference.Desc.First.K8.caller_before_draw
