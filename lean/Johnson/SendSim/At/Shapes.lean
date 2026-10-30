-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Shapes.lean: what the honest sender sends in each of its two rounds has the shape
that K1's round declares, so it passes the framework's test Sending.fits at every round that agrees
with K1's in what play reads of it.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for every P, by unfolding and counting. The statements are only about lengths
and labels: no distribution and no coin's value is in them.
  fits_seed      For all rows Vr, what the sender sends in its first round (no item in the clear;
                 the tables treeTables P Vr) fits every round r with shapeOf r equal to shapeOf of
                 K1's first round with its oracle messages.
  fits_answer    A list of P.answers answers, sent with no table, fits every round r with shapeOf r
                 equal to shapeOf of K1's second round.
  length_answers   The list of answers that the library's function answers computes has the length
                 P.answers.

Limits. Nothing is said about the values that are sent.

How it fits. Johnson/SendSim/At/Shows.lean uses the three, with roundsOf_eq, to prove that play of
the sender's two rounds succeeds (play_send). That serves showsAt and tellsAt, so sendExactAt
(Johnson/SendSim/At/ExactAt.lean). shapeOf and roundsOf are defined in Johnson/SendSim/At/Sim.lean,
Sending.fits in Johnson/Desc/ProofFile/Honest/Frame.lean, answers in Johnson/Prover/Send/Core.lean.

The other names.
  items_seed     K1's first round declares no item but roots.
  items_answer   K1's second round declares, roots aside, P.answers answers.
  sum_answers    P.answers is the sum of the numbers of answers of P's oracle messages.
  tables_shape   the tables treeTables have, one by one, the log-length and the number of words that
                 K1's first list of oracle messages declares.
  roundsOf_eq    K1's two rounds with their oracle messages, written out; by rfl.
  filter_replicate_root, filter_replicate_answer, foldl_add_eq_sum, sum_filter_answers and
  range_map_shapeAt are tools on lists.
-/
import Johnson.SendSim.At.Sim

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt answers held)

theorem filter_replicate_root (n : ℕ) :
    (List.replicate n Fmt.Item.root).filter (· != .root) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using ih

theorem filter_replicate_answer (n : ℕ) :
    (List.replicate n Fmt.Item.answer).filter (· != .root) = List.replicate n .answer := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- K1's first round ("SEND seed") declares no item but roots. -/
theorem items_seed (P : K1.Par) :
    (({ entry := K1.seedEntry P } : Fmt.DeclaredRound).items).filter (· != .root) = [] := by
  have h : ({ entry := K1.seedEntry P } : Fmt.DeclaredRound).items =
      List.replicate P.trees.length .root := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.seedEntry]
  rw [h, filter_replicate_root]

/-- K1's second round ("SEND answer") declares, roots aside, exactly P.answers items, all of them
answers. -/
theorem items_answer (P : K1.Par) :
    (({ entry := K1.answerEntry P } : Fmt.DeclaredRound).items).filter (· != .root) =
      List.replicate P.answers .answer := by
  have h : ({ entry := K1.answerEntry P } : Fmt.DeclaredRound).items =
      List.replicate P.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.answerEntry]
  rw [h, filter_replicate_answer]

theorem foldl_add_eq_sum (l : List OracleShape) (a : ℕ) :
    l.foldl (fun a s => a + s.answers) a = a + (l.map (·.answers)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, Nat.add_assoc]

theorem sum_filter_answers (l : List OracleShape) :
    ((l.filter (·.answers != 0)).map (·.answers)).sum = (l.map (·.answers)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x.answers = 0
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem range_map_shapeAt (P : K1.Par) :
    (List.range P.sent.size).map (shapeAt P) = P.sent.toList.map (·.shape) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, shapeAt, Array.getElem_toList]
    have hi : i < P.sent.size := by simpa using h1
    simp [Array.getD, hi]

/-- P.answers is the sum, over P's oracle messages, of their numbers of answers. -/
theorem sum_answers (P : K1.Par) :
    P.answers = ((List.range P.sent.size).map fun k => (shapeAt P k).answers).sum := by
  unfold K1.Par.answers K1.Par.tuple
  rw [foldl_add_eq_sum, Nat.zero_add, sum_filter_answers, ← range_map_shapeAt, List.map_map]
  rfl

/-- The list that the library's function answers computes has the length P.answers, for every
statement, all words and all seeds. -/
theorem length_answers (P : K1.Par) (S' : Statement) (first : ℕ) (w' : OnBytes.Means.Words GE)
    (seeds : List (List E × E)) : (answers P S' first w' seeds).length = P.answers := by
  unfold answers
  rw [List.length_flatMap, sum_answers]
  simp only [List.length_map, List.length_range]
  have h : ∀ l : List ℕ, ((l.filter fun k => (shapeAt P k).answers != 0).map
      fun k => (shapeAt P k).answers).sum = (l.map fun k => (shapeAt P k).answers).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      by_cases hx : (shapeAt P x).answers = 0
      · simp [List.filter_cons, hx, ih]
      · simp [List.filter_cons, hx, ih]
  exact h _

/-- The tables treeTables P Vr have, one by one, the log-length and the number of words that K1's
first list of oracle messages declares. -/
theorem tables_shape (P : K1.Par) (Vr : ℕ → Rows) :
    (treeTables P Vr).map (fun t => (t.logLength, t.words)) =
      ((K1.oracles P).headD []).map fun o => (o.logLength, o.words) := by
  simp [treeTables, K1.oracles, List.map_map, Function.comp_def]

/-- roundsOf P written out: K1's two rounds, the first with K1's first list of oracle messages, the
second with none. By rfl. -/
theorem roundsOf_eq (P : K1.Par) :
    roundsOf P = [({ entry := K1.seedEntry P }, (K1.oracles P).headD []),
      ({ entry := K1.answerEntry P }, [])] := rfl

/-- If shapeOf r is shapeOf of K1's first round with its oracle messages, what the sender sends in
its first round (no item in the clear, the tables treeTables P Vr) passes Sending.fits at r. -/
theorem fits_seed (P : K1.Par) (Vr : ℕ → Rows)
    (r : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)
    (h : shapeOf r = shapeOf ({ entry := K1.seedEntry P }, (K1.oracles P).headD [])) :
    (⟨[], treeTables P Vr⟩ : Sending).fits r.1 r.2 = true := by
  have h1 : r.1.items.filter (· != .root) = [] := (congrArg Prod.fst h).trans (items_seed P)
  have h2 : (r.2.map fun o => (o.logLength, o.words)) =
      ((K1.oracles P).headD []).map fun o => (o.logLength, o.words) := congrArg Prod.snd h
  simp only [Sending.fits, h1, h2, tables_shape, List.map_nil, beq_self_eq_true, Bool.and_self]

/-- If shapeOf r is shapeOf of K1's second round and l has the length P.answers, the answers l, sent
with no table, pass Sending.fits at r. -/
theorem fits_answer (P : K1.Par) (l : List Fmt.Ext3) (hl : l.length = P.answers)
    (r : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)
    (h : shapeOf r = shapeOf ({ entry := K1.answerEntry P }, [])) :
    (⟨l.map fun a => .answer (toE a), []⟩ : Sending).fits r.1 r.2 = true := by
  have h1 : r.1.items.filter (· != .root) = List.replicate P.answers .answer :=
    (congrArg Prod.fst h).trans (items_answer P)
  have h2 : (r.2.map fun o => (o.logLength, o.words)) = [] := congrArg Prod.snd h
  have h3 : ((l.map fun a => Said.answer (toE a)).map fun v => itemOf v.got) =
      List.replicate P.answers .answer := by
    rw [← hl, List.map_map]
    exact List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hb
      rfl⟩
  simp only [Sending.fits, h1, h2, h3, List.map_nil, beq_self_eq_true, Bool.and_self]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.fits_seed
#print axioms OnBytes.SendSim.At.fits_answer
#print axioms OnBytes.SendSim.At.items_seed
#print axioms OnBytes.SendSim.At.items_answer
#print axioms OnBytes.SendSim.At.length_answers
#print axioms OnBytes.SendSim.At.tables_shape
