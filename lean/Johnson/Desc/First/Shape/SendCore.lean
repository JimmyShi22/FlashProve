-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/SendCore.lean: THE SENDING (the kind K1) ON THE ONE SHAPE OF STATEMENT,
BOOK AND ROOTS: one Bool and one update, and that they are enough: where the Bool accepts, K1's own
decision of the sending returns, at the count of rows owed as K1.owedOf reads it (0 rows owed is
none); and whatever it returns has the updated shape. General in the carried record: no chain's own
shape lies beneath. Nothing is evaluated.

What it is for. Every sending of a chain calls K1.decideSend (Johnson/Desc/K1/Own.lean), whose yes
the library has as an equivalence with the record behind as one written term (K1.decideSend_iff,
K1.behind, Johnson/Desc/K1/Law/Writes3.lean). The shape is Ground.Sh.CoreSh
(Johnson/Desc/Ground/Shape/Core.lean).

  1 `orcSent`, `orcSh_wr`, `map_outs`: a new message's shape hangs on its OracleShape and the codes
    alone, where the counts fit (K1.fitB): of its sample rows the number is its number of answers.
  2 **`sendCore`**, **`core_behind`**: the written record behind a sending, seen through the core.
    The book's half is Ground.Sh.recv_book, called.
  3 `idsAt`, **`send_core`**: from a return of K1.decideSend, at any rounds: the new messages'
    numbers; coreSh (coreOf x.2) = sendCore P (coreSh (coreOf d)); the chain's own values and the
    opened columns as they were.
  4 **`sendB`**, **`send_returns`**: no rows are owed, the record's codes are the plan's, the
    kind's own tests on the plan, statement and book in step, every sampled message's pad is found:
    then K1.decideSend, AT owed.filter (· != 0), returns on two rounds in which no seed's factor is
    0 and round 2 holds as many answers as the place counts. (At owed = some 0 the Bool accepts and
    the decision at some 0 itself refuses: the member hands in K1.owedOf, which reads 0 as none.)

Source. send_returns is the like, over the library alone, of send_yes_of in
Johnson/Prover/Send/Form.lean; its proof follows that one step for step. It has not been turned
into a call of it.

Limits. The two premises on the rounds are not paid here: that rounds which fit the kind's rounds
meet them is shown beside send_yes_of. No record is shown at which sendB accepts. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.Ground.Shape.Ground
import Johnson.Desc.K1.Law.Writes3
import Johnson.Desc.K1.Law.When
import Johnson.Desc.K1.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh OrcSh coreSh orcSh)

variable {L : Type}

/-! ## 1 The new messages -/

/-- A message behind a sending: of its sample rows the number. -/
def orcSent (codes : Codes) (s : OracleShape) : OrcSh :=
  if s.answers = 0 then ⟨s, false, 0, [], [], none, false⟩
  else ⟨s, true, s.answers, ((Send.pad codes s).getD []).map fun p => (p.part, p.index), [],
    Slice.freshLedger codes s, false⟩

theorem orcSh_wr (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (h : s.answers ≠ 0 → s.answers ≤ seeds.length ∧ s.answers ≤ ys.length) :
    orcSh (K1.wr codes seeds o s ys) = orcSent codes s := by
  unfold K1.wr orcSent
  split
  · rfl
  · rename_i h0
    show (⟨s, true, (K1.rowsOf codes seeds o s ys).size, _, [], _, false⟩ : OrcSh) = _
    rw [K1.rowsOf_size codes seeds o s ys (h h0).1 (h h0).2]

/-- All new messages, where the counts fit. -/
theorem map_outs (codes : Codes) (seeds : List (List E × E)) :
    ∀ (l : List OracleShape) (o : Nat) (ys : List E), K1.fitB codes seeds.length l ys = true →
      (K1.outs codes seeds o l ys).map orcSh = l.map (orcSent codes)
  | [], _, _, _ => rfl
  | s :: l, o, ys, h => by
    show orcSh (K1.wr codes seeds o s ys) ::
      (K1.outs codes seeds (o + 1) l (ys.drop s.answers)).map orcSh = orcSent codes s :: l.map _
    unfold K1.fitB at h
    by_cases h0 : s.answers = 0
    · rw [if_pos h0] at h
      rw [orcSh_wr _ _ _ _ _ (fun h1 => absurd h0 h1), h0, List.drop_zero,
        map_outs codes seeds l (o + 1) ys h]
    · rw [if_neg h0] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [orcSh_wr _ _ _ _ _ (fun _ => ⟨h.1.1.1, h.1.1.2⟩),
        map_outs codes seeds l (o + 1) _ h.2]

/-! ## 2 The record behind a sending, seen through the one shape of statement, book and roots -/

/-- **The sending's update on the core.** -/
def sendCore (P : K1.Par) (a : CoreSh) : CoreSh :=
  { st := { a.st with oracles := a.st.oracles ++ (K1.shapesOf P).map (orcSent P.codes) }
    book :=
      { trees := (List.range P.sent.size).foldl (fun t i =>
          Ground.Sh.modAt t
            (a.book.trees.length + ((layTrees P.codes P.sent).getD {}).tree.getD i 0) fun x =>
            { x with
              parts := x.parts ++ [a.st.oracles.length + i]
              oneList := x.oneList || (P.sent.getD i default).shape.answers == 0 })
          (Ground.Sh.treesSentS P.gp.firstTree ((layTrees P.codes P.sent).getD {}).shapes.toList
            a.roots a.book.trees)
        place := a.book.place ++ (List.range P.sent.size).map fun i =>
          (a.book.trees.length + ((layTrees P.codes P.sent).getD {}).tree.getD i 0,
            ((layTrees P.codes P.sent).getD {}).part.getD i 0) }
    roots := a.roots + ((layTrees P.codes P.sent).getD {}).shapes.size }

theorem core_behind (P : K1.Par) (d : DState L) (seeds : List (List E × E)) (ys : List E)
    (hf : K1.fitB P.codes seeds.length (K1.shapesOf P) ys = true) :
    coreSh (coreOf (K1.behind P d seeds ys)) = sendCore P (coreSh (coreOf d)) := by
  have h1 : Ground.Sh.stSh (K1.behind P d seeds ys).st =
      { Ground.Sh.stSh d.st with
        oracles := (Ground.Sh.stSh d.st).oracles ++ (K1.shapesOf P).map (orcSent P.codes) } := by
    show (⟨d.st.codes, ((d.st.oracles.toList ++ K1.outs P.codes seeds d.st.oracles.size
      (K1.shapesOf P) ys).toArray).toList.map orcSh, d.st.groups.toList.map Ground.Sh.grpSh⟩ :
        Ground.Sh.StSh) = _
    rw [List.toList_toArray, List.map_append, map_outs _ _ _ _ _ hf]
    rfl
  have h2 := Ground.Sh.recv_book P.gp.firstTree d.book d.st.oracles.size d.roots P.sent
    ((layTrees P.codes P.sent).getD {})
  show CoreSh.mk (Ground.Sh.stSh (K1.behind P d seeds ys).st)
    (Ground.Sh.bookSh (K1.behind P d seeds ys).book) (K1.behind P d seeds ys).roots = _
  rw [h1]
  show CoreSh.mk _ (Ground.Sh.bookSh
    { trees := Slice.partsLaid P.sent ((layTrees P.codes P.sent).getD {}) d.st.oracles.size
        d.book.trees.size (Slice.treesSent P.gp.firstTree
          ((layTrees P.codes P.sent).getD {}).shapes.toList d.roots d.book.trees)
      place := d.book.place ++ (Array.range P.sent.size).map fun i =>
        (d.book.trees.size + ((layTrees P.codes P.sent).getD {}).tree.getD i 0,
          ((layTrees P.codes P.sent).getD {}).part.getD i 0) }) _ = _
  rw [h2]
  unfold sendCore
  rw [show (coreSh (coreOf d)).st.oracles.length = d.st.oracles.size from
    Ground.Sh.orc_size d.st]
  rfl

/-! ## 3 What a sending's return is -/

/-- The new messages' numbers. n0: the number of messages in front. -/
def idsAt (P : K1.Par) (n0 : Nat) : Array Nat := (Array.range P.sent.size).map (· + n0)

/-- **A sending's return, seen through the core**: the numbers; the updated core; the chain's own
values and the opened columns as they were. -/
theorem send_core {P : K1.Par} {owed : Option Nat} {d : DState L} {rs : List Fmt.RoundView}
    {x : Array Nat × DState L} (h : K1.decideSend P owed d rs = .ok x) :
    x.1 = idsAt P d.st.oracles.size ∧ coreSh (coreOf x.2) = sendCore P (coreSh (coreOf d)) ∧
      x.2.loc = d.loc ∧ x.2.opened = d.opened := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨ids, d'⟩ := x
    obtain ⟨ha, rfl, rfl⟩ := (K1.decideSend_iff P owed d d' r₁ r₂ ids).1 h
    refine ⟨rfl, core_behind P d _ _ ?_, rfl, rfl⟩
    rw [show (K1.seedsOf P r₁).length = P.seeds from K1.cutSeeds_length _ _ _]
    exact ha.2.2.2.2
  | [], h => cases h
  | [_], h => cases h
  | _ :: _ :: _ :: _, h => cases h

/-! ## 4 The sending's Bool, and that it is enough -/

/-- **The sending's guards on the structure.** No rows are owed; the record's codes are the plan's;
the kind's own tests on the plan; statement and book are in step; the statement's page finds the
pad's places of every sampled message. -/
def sendB (P : K1.Par) (owed : Option Nat) (a : CoreSh) : Bool :=
  (owed.filter (· != 0)).isNone && (a.st.codes == P.codes) && K1.planOkOwn P &&
    (a.st.oracles.length == a.book.place.length) &&
    P.tuple.all fun s => (Own.padMade P.codes s).isSome

/-- **Where the Bool accepts, K1's own decision of the sending returns**, at the count as K1.owedOf
reads it (0 rows owed is none), on two rounds in which no seed's factor is 0 and round 2 holds as
many answers as the place counts. -/
theorem send_returns (P : K1.Par) (owed : Option Nat) (d : DState L) (r₁ r₂ : Fmt.RoundView)
    (hB : sendB P owed (coreSh (coreOf d)) = true)
    (hz : ∀ x ∈ K1.seedsOf P r₁, isZeroE x.2 = false)
    (hn : (K1.answersIn r₂).length = P.answers) :
    ∃ x, K1.decideSend P (owed.filter (· != 0)) d [r₁, r₂] = .ok x := by
  simp only [sendB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨h1, h2⟩, hp⟩, h4⟩, h5⟩ := hB
  have ho : owed.filter (· != 0) = none := Option.isNone_iff_eq_none.1 h1
  have hc : d.st.codes = P.codes := h2
  have hs : d.st.oracles.size = d.book.place.size := by
    have : (d.st.oracles.toList.map orcSh).length = d.book.place.toList.length := h4
    simpa using this
  refine ⟨_, (K1.decideSend_iff P _ d _ r₁ r₂ _).2 ⟨⟨ho, hc, hz, ?_, ?_⟩, rfl, rfl⟩⟩
  · simp only [K1.planOkOwn, K1.planOk, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨hsh, hlay⟩, _⟩, _⟩ := hp
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
    rw [hc]
    exact ⟨hsh, hlay, hs⟩
  · refine K1.fitB_true _ _ _ _ (fun x hx h0 => ⟨K1.le_seeds P x hx, ?_⟩)
      (by rw [hn, K1.answers_sum])
    rw [← Own.padMade_eq]
    refine h5 x ?_
    simp only [K1.Par.tuple, List.mem_filter]
    exact ⟨hx, by simpa using h0⟩

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.orcSh_wr
#print axioms VerifiableInference.Desc.First.Shape.map_outs
#print axioms VerifiableInference.Desc.First.Shape.core_behind
#print axioms VerifiableInference.Desc.First.Shape.send_core
#print axioms VerifiableInference.Desc.First.Shape.send_returns
