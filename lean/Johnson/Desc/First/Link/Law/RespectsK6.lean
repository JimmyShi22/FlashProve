-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RespectsK6.lean: THE THREE RUNS OF CLAIMS OF THE OUTPUT HEAD's OWN
SUB-PROTOCOL («norm», «policy», «logits») READ NOTHING OF WHAT A LATER COMMITMENT OF THE SAME
SEGMENT WRITES INTO THE VERIFIER's STATE: each is a member of `Respects`
(Johnson/Desc/K1/Law/RestDef.lean). Definitions and theorems, at the kind's own text
(Johnson/Desc/Kinds/HeadFrame.lean, HeadKind.lean) and at its seat in the verifier's state
(Johnson/Stored/HeadSeatAt.lean).

Why. The public item «the forms of a run are in» calls the run itself at the state. That the answer
is the same in front of and behind a later commitment is owed for every run that is open there. The
cut: a sub-protocol's files show once what its accepting step writes; a run's files show once that
its run reads none of that. This is the second half for these three runs.

What is said.
  `SeatRest L`: the five readers of a seat of the head's kind (the heard next token, the request's
    public part, the lookup's points, the reads' places, what was heard) do not turn when all that a
    later commitment writes is taken off the state; and laying the calls' key vectors leaves the
    state. `lettersAt_rest`: so neither do the letters that the runs are made of. `respects_runsBy`:
    **every run of `runsBy` at such a seat is a member of `Respects`.** `respects_k6`: so is every
    run that the kind states. `seatRest_at`: **the seat in the verifier's state is such a seat.**
    `respects_k6_at`: the three runs at that seat.

Limits. The runs as the kind states them: the guard that a seat lays around a sub-protocol's runs is
RestDef.lean's `respects_guarded`. The lookup's join, which stands between the first and the second
of the three in the link's order, is not here. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RestDef
import Johnson.Desc.Kinds.HeadKind
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (restOf hereRest forkRest treeRest RestAlike Respects ReadsRest
  respects_readRest lookHeard_rest)
open VerifiableInference.Desc.Kinds.Head (Seat Par Given Behind Places lettersAt given runsBy kind
  seatAt)

/-- **A seat of the head's kind whose readers read the rest alone.** -/
structure SeatRest (L : Seat S) : Prop where
  reply : ReadsRest L.reply
  request : ReadsRest L.request
  lookup : ReadsRest L.lookup
  reads : ReadsRest L.reads
  heard : ReadsRest L.heard
  keys : ∀ s fs, L.setKeyForms s fs = s

/-- The letters that the runs are made of read the rest alone. -/
theorem lettersAt_rest (p : Par) (L : Seat S) (h : SeatRest L) : ReadsRest (lettersAt p L) := by
  intro s
  unfold lettersAt given Kinds.Reply.token
  rw [h.lookup s, h.reply s, h.request s, h.heard s, h.reads s]

/-- What a list of named functions answers under a name. -/
theorem lookup_named {β : Type} (F : String → β) : ∀ (names : List String) (n : String) (r : β),
    (names.map fun x => (x, F x)).lookup n = some r → r = F n
  | [], _, _, h => nomatch h
  | x :: l, n, r, h => by
    rw [List.map_cons, List.lookup_cons] at h
    by_cases e : (n == x) = true
    · rw [e] at h
      obtain rfl : n = x := by simpa using e
      exact (Option.some.inj h).symm
    · have e' : (n == x) = false := by simpa using e
      rw [e'] at h
      exact lookup_named F l n r h

/-- **EVERY RUN OF runsBy AT SUCH A SEAT READS THE REST ALONE.** -/
theorem respects_runsBy (names : List String)
    (runs : Given → Behind → Places → List (String × List Kinds.Form))
    (keys : Given → Behind → Places → List Kinds.Form) (toCl : Kinds.Form → Claim) (p : Par)
    (L : Seat S)
    (h : SeatRest L) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (runsBy names runs keys toCl p L).lookup name = some run) : Respects run := by
  unfold runsBy at hrun
  obtain rfl := lookup_named _ names name run hrun
  have e : (fun (_ : Nat) (s : S) => (do
      let (g, b, x) ← lettersAt p L s
      let fs ← named "the run is there" ((runs g b x).lookup name)
      pure (fs.map toCl, if names.head? == some name then L.setKeyForms s (keys g b x) else s) :
        Except String (List Claim × S))) =
      fun _ s => ((do
        let (g, b, x) ← lettersAt p L s
        let fs ← named "the run is there" ((runs g b x).lookup name)
        pure (fs.map toCl) : Except String (List Claim))).map fun l => (l, s) := by
    funext _ s
    simp only [h.keys, ite_self]
    cases lettersAt p L s with
    | error _ => rfl
    | ok y =>
      obtain ⟨g, b, x⟩ := y
      show (named "the run is there" ((runs g b x).lookup name) >>= fun fs =>
        pure (fs.map toCl, s)) = Except.map (fun l => (l, s))
          (named "the run is there" ((runs g b x).lookup name) >>= fun fs => pure (fs.map toCl))
      cases named "the run is there" ((runs g b x).lookup name) <;> rfl
  rw [e]
  refine respects_readRest _ fun s => ?_
  rw [lettersAt_rest p L h s]

/-- Every run that the kind states. -/
theorem respects_k6 (toCl : Kinds.Form → Claim) (L : Seat S) (h : SeatRest L) (l piece : Nat)
    (p : Par) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind toCl L l piece p).claims.lookup name = some run) : Respects run := by
  unfold kind at hrun
  dsimp only at hrun
  exact respects_runsBy _ _ _ toCl p L h name run hrun

/-- **THE SEAT IN THE VERIFIER's STATE IS SUCH A SEAT.** -/
theorem seatRest_at (h : Model.Head.Shape) (iU3 : Nat) : SeatRest (seatAt h iU3) where
  reply _ := rfl
  request _ := rfl
  lookup s := by
    show (restOf s).lookHeard?.map _ = s.lookHeard?.map _
    rw [lookHeard_rest]
  reads s := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head o =>
      by_cases ho : o.opened = true
      · simp only [seatAt, restOf, hereRest, S.fork?, ho, if_true, forkRest, Array.getElem?_map]
        cases o.t with
        | none => rfl
        | some tt => cases o.F.trees[iU3]? <;> rfl
      · simp [seatAt, restOf, hereRest, S.fork?, ho]
    | _ => rfl
  heard s := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> rfl
  keys _ _ := rfl

/-- **THE THREE RUNS AT THAT SEAT.** -/
theorem respects_k6_at (toCl : Kinds.Form → Claim) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Par) (name : String) (run : Nat → S → Except String (List Claim × S))
    (hrun : (kind toCl (seatAt h iU3) l piece p).claims.lookup name = some run) : Respects run :=
  respects_k6 toCl _ (seatRest_at h iU3) l piece p name run hrun

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.respects_runsBy
#print axioms VerifiableInference.Desc.LinkJoin.seatRest_at
#print axioms VerifiableInference.Desc.LinkJoin.respects_k6_at
