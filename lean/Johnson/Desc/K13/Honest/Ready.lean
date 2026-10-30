--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Ready.lean: kind K13, the members' batching: WHAT THE JOINED SUB-PROTOCOL's
DECISION ASKS OF THE VERIFIER's STATE, AS ONE TEST WITH CODE. Definitions with code; statements with
their proofs.

Why. `atM3_accepts_code_gl` (Johnson/Desc/K13/Honest/Accepts.lean) says that the decision of the
joined sub-protocol accepts the honest rounds under nine premises on the state in front of its
place. A lemma under premises that no state meets is true and says nothing. Here the nine stand as
one test that can be run on a state, clause by clause, each clause under the name of the
sub-protocol's own test that asks it.
Main names:
  `atFinC s`: the chain's finish has run, and the members' places have not begun.
  `readyL P s`: the nine clauses, each with its name. `readyC`: all of them.
  `readyFails`: the names of those that fail. `readyFails_nil`: none fails exactly if all hold.
  `ready_iff`: **the test accepts exactly where the nine premises hold.**
  `honestRounds P s w x eps gs`: the honest rounds at the state, with code: `movesAtM3` at the
    state's pile and at the mask entries that the batching will take (`freshAt`,
    Johnson/Desc/K13/Law/Caller.lean).
  `atM3_accepts_ready`: **where the test accepts and all rows on the pile are true, the decision
    accepts the honest rounds, and the claim that it leaves is made of a true row.**

THE DECISION TESTS NO SENT VALUE (Johnson/Desc/K13/Honest/Accepts.lean says so of its statements):
where the test accepts, it accepts any elements in rounds of this form. Acceptance is no merit of
the honest rounds; what is said of the honest prover's values is that the row of the claim is true.

What is not claimed. THE DECISION ALONE IS TREATED (the field `decide`): the format's step in front
of it (each round against its declared entry; the columns) and the sub-protocol's test on the plan
are not. That the test accepts at any state is not shown in this file: a synthetic state stands in
Johnson/Desc/K13/Honest/ReadyToy.lean; the state of a real proof in no file. That the rows on the
pile are true: a premise, relative to the number nR of the matrix's rows, which is free here.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.Accepts
import Johnson.Desc.K13.Law.Caller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open OnBytes.Slice (GE ofE)
open VerifiableInference.Desc.K13.Law

/-- The chain's finish has run, and the members' places have not begun. -/
def atFinC (s : S) : Bool :=
  match s.here with
  | .fin _ => true
  | _ => false

/-- The test says what its name says. -/
theorem atFinC_iff (s : S) : atFinC s = true ↔ ∃ f, s.here = .fin f := by
  constructor
  · intro h
    cases hs : s.here with
    | fin a => exact ⟨a, rfl⟩
    | _ => simp [atFinC, hs] at h
  · rintro ⟨f, hf⟩
    simp [atFinC, hf]

/-- **What the decision asks of the state**, clause by clause, each under the name of the
sub-protocol's own test. -/
def readyL (P : Where) (s : S) : List (String × Bool) :=
  [("K13.comes-to-the-end-once", atFinC s),
   ("K13.reply-heard", !P.reply || s.out.reply.isSome),
   ("K13.pile-count", s.out.pending.length == P.rows),
   ("K13.pile-on-the-table", memberRowsFit s.st P.lin s.out.indexMasks s.out.pending),
   ("K13.nothing-owed", s.noneWaits),
   ("K13.pile-form", Batt.fits P.lin.kCol s.out.pending),
   ("K13.mask-entries",
     (takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol)).isSome),
   ("K13.shape-lawful", linOk s.st.codes P.lin),
   ("K13.message-W", (linMessageW P.lin).isSome)]

/-- All nine. -/
def readyC (P : Where) (s : S) : Bool := (readyL P s).all (·.2)

/-- The names of the clauses that fail. -/
def readyFails (P : Where) (s : S) : List String := ((readyL P s).filter (!·.2)).map (·.1)

/-- Of named clauses none fails exactly if all hold. -/
theorem fails_nil : ∀ l : List (String × Bool),
    (l.filter (!·.2)).map (·.1) = [] ↔ l.all (·.2) = true
  | [] => by simp
  | (n, true) :: l => by simp
  | (n, false) :: l => by simp

/-- No clause fails exactly if the test accepts. -/
theorem readyFails_nil (P : Where) (s : S) : readyFails P s = [] ↔ readyC P s = true :=
  fails_nil (readyL P s)

/-- **The test accepts exactly where the nine premises hold.** -/
theorem ready_iff (P : Where) (s : S) :
    readyC P s = true ↔ ∃ (f : First.FinOwn) (t : List ℕ × St) (msg : Array OracleNotice),
      s.here = .fin f ∧ (!P.reply || s.out.reply.isSome) = true ∧
      s.out.pending.length = P.rows ∧
      memberRowsFit s.st P.lin s.out.indexMasks s.out.pending = true ∧ s.noneWaits = true ∧
      Batt.fits P.lin.kCol s.out.pending = true ∧
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linOk s.st.codes P.lin = true ∧ linMessageW P.lin = some msg := by
  unfold readyC readyL
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists, atFinC_iff]
  constructor
  · rintro ⟨⟨f, h1⟩, h2, h3, h4, h5, h6, ⟨t, h7⟩, h8, ⟨msg, h9⟩⟩
    exact ⟨f, t, msg, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · rintro ⟨f, t, msg, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨⟨f, h1⟩, h2, h3, h4, h5, h6, ⟨t, h7⟩, h8, ⟨msg, h9⟩⟩

/-- Where the ground's taking returns, `freshAt` is what it hands out. -/
theorem freshAt_of_take {P : Where} {s : S} {t : List ℕ × St}
    (h : takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t) :
    freshAt P s = t.1.map fun i => ⟨s.out.indexMasks, i⟩ := by
  unfold freshAt
  rw [h]
  rfl

variable {nR : ℕ} {Cl : Type}

/-- **The honest rounds at the state.** w: the matrix and the mask entries. x, eps, gs: the sampled
elements. -/
def honestRounds (P : Where) (s : S) (w : Wit GE nR P.lin.kCol) (x eps : E) (gs : List E) :
    List Fmt.RoundView :=
  movesAtM3 ρg (fun a => E.ofTriple (ofE a)) w s.out.pending (freshAt P s) x eps gs

/-- **Where the test accepts and all rows on the pile are true, the decision accepts the honest
rounds**, and the claim that it leaves is made of a row that is true. The decision tests no sent
value: the weight lies in the row's truth. -/
theorem atM3_accepts_ready {P : Where} {s : S} (hr : readyC P s = true)
    (w : Wit GE nR P.lin.kCol) (hrows : ∀ r ∈ s.out.pending, Holds ρg w r) (x eps : E)
    (gs : List E) (hg : gs.length = P.lin.kCol) (cols : List (List (Nat × List UInt64))) :
    ∃ (st' : Statement) (msg : Array OracleNotice) (row : TensorRow),
      (atM3 (Cl := Cl) P).decide s (honestRounds P s w x eps gs) cols =
        .ok (withClaim s st' msg row) ∧ Holds ρg w row := by
  obtain ⟨f, t, msg, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := (ready_iff P s).1 hr
  obtain ⟨row, hd, hrow⟩ := atM3_accepts_code_gl (Cl := Cl) w h1 h2 h3 h4 h5 h6 h7 h8 h9 hrows x eps
    gs hg cols
  refine ⟨t.2.st, msg, row, ?_, hrow⟩
  unfold honestRounds
  rw [freshAt_of_take h7]
  exact hd

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.atFinC_iff
#print axioms VerifiableInference.Desc.K13.Honest.fails_nil
#print axioms VerifiableInference.Desc.K13.Honest.readyFails_nil
#print axioms VerifiableInference.Desc.K13.Honest.ready_iff
#print axioms VerifiableInference.Desc.K13.Honest.freshAt_of_take
#print axioms VerifiableInference.Desc.K13.Honest.atM3_accepts_ready
