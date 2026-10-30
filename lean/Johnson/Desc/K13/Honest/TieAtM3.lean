--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/TieAtM3.lean: kind K13, the members' batching, at the state of a proof
file's first chain: THE ROUNDS OF WHICH THE STATEMENT ON ACCEPTANCE SPEAKS AND THE ROUNDS OF THE
DISTRIBUTION ARE ONE AND THE SAME TERM. Statements with their proofs.

The family. A value s of the type of states that passes the tests below (not: a state that a run
reaches); a matrix and mask entries of which all rows on the pile are true. For each function v on
1 + 2 kCol numbers: the same matrix and mask entries, but for the values v at the entries that the
batching will take (`withTaken`, Johnson/Desc/K13/Honest/WithTaken.lean). Two tests with code on the
state: `readyC` (Johnson/Desc/K13/Honest/Ready.lean), under which both main statements stand;
`pileBelowC` (Johnson/Desc/K13/Honest/Fresh.lean), under which the first stands.

WHICH PROVER. Both statements are of THE PROVER THAT READS THE LIST OFF THE VERIFIER's STATE
(`honestRounds`): it reads there which mask entries will be taken (`freshAt`). The other is the
prover that is handed the list of its entries: `viewT_law` (BijLaw.lean) and `moves_law` (Tie.lean),
which have no state and no test on a state, serve that one. That the list which such a prover is
handed is `freshAt P s` where `readyC` accepts is shown in no file.

`readyC` IS A PREMISE ON WHICH `family_law` ITSELF HANGS, not one of acceptance alone. Of its nine
clauses the proof uses two: "K13.pile-form", for a column variable; "K13.mask-entries", for
2 kCol + 1 entries that differ. All nine read sizes, numbers, the ledger and where the chain stands:
no value, no sent scalar, no coin. WHERE "K13.mask-entries" FAILS NOTHING IS SAID: `freshAt` is then
the empty list, so this prover reads ONE mask entry, the default one, 2 kCol + 1 times; and
`maskWith mask [] v = mask`, so `withTaken w [] v` is w at every v: the rounds do not vary with v at
all.

THE DECISION TESTS NO SENT VALUE (Johnson/Desc/K13/Honest/Accepts.lean): where `readyC` accepts, it
accepts any elements in rounds of this form. ACCEPTANCE IS NO MERIT OF THE FAMILY. What ties the two
statements: the same term `honestRounds P s (withTaken w (freshAt P s) (onNat v)) x eps gs` stands
in both; and the row of the claim is true at that v.
Main names:
  `freshAt_nodup`, `freshAt_length`, `freshAt_off_pile`: the entries that will be taken differ from
    each other; there are 2 kCol + 1; no row on the pile names one.
  `family_accepts`: **at every v the rows on the pile are still true, the decision accepts the
    honest rounds, and the claim that it leaves is made of a row that is true at that v.**
  `family_law`: **over uniform v these very rounds have the distribution of the rounds of 2 kCol + 1
    uniform scalars.**

What is not claimed. What Johnson/Desc/K13/Honest/BijLaw.lean and Ready.lean do not claim.
`family_law` is the half of the sub-protocol that spends the entries, AND IS NOT TO BE QUOTED
WITHOUT THE SENDER's SENTENCE BESIDE IT: the state s is fixed while v varies, and a real state holds
the OOD answers of the message in which these entries lie, and columns of it are opened later: so
the family does not model a run in which that message was sent at v. THIS BEARS ON `family_accepts`
TOO: at a v other than the witness's own values the sample rows of that message in a real state are
in general not true of the witness; `Holds` speaks of rows on the matrix, so the statement does not
see them. It says: this decision, this state, the pile's rows and the one row handed on; not: an
honest run at v is accepted. THE MAP IS ONE TO ONE: with all that is held fixed, the scalars sent
fix every one of these entries, and so every other value that is computed from them: the row handed
on names all of them, and the later test computes on them. `family_law` has no premise on the number
of challenges: with fewer than kCol both sides are cut alike; it speaks of all 2 kCol + 1 scalars
where there are at least kCol. That the two tests accept at the state of a real proof. Nothing on
soundness, on zero knowledge or on hiding.

-/
import Johnson.Desc.K13.Honest.Ready
import Johnson.Desc.K13.Honest.Tie
import Johnson.Desc.K13.Honest.Fresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.First (S)
open OnBytes.Slice (GE ofE)
open VerifiableInference.Desc.K13.Law

/-- The entries that will be taken differ from each other. -/
theorem freshAt_nodup {P : Where} {s : S} (hr : readyC P s = true) : (freshAt P s).Nodup := by
  obtain ⟨_, t, _, _, _, _, _, _, _, h7, _, _⟩ := (ready_iff P s).1 hr
  rw [freshAt_of_take h7]
  exact taken_nodup h7

/-- There are 2 kCol + 1 of them. -/
theorem freshAt_length {P : Where} {s : S} (hr : readyC P s = true) :
    (freshAt P s).length = 2 * P.lin.kCol + 1 := by
  obtain ⟨_, t, _, _, _, _, _, _, _, h7, _, _⟩ := (ready_iff P s).1 hr
  rw [freshAt_of_take h7, List.length_map, takeMasks_length h7]
  show 1 + 2 * P.lin.kCol = 2 * P.lin.kCol + 1
  omega

/-- No row on the pile names one of them. -/
theorem freshAt_off_pile {P : Where} {s : S} (hr : readyC P s = true)
    (hb : pileBelowC s.st s.out.indexMasks s.out.pending = true) :
    ∀ r ∈ s.out.pending, ∀ m ∈ r.masks, m.1 ∉ freshAt P s := by
  obtain ⟨_, t, _, _, _, _, _, _, _, h7, _, _⟩ := (ready_iff P s).1 hr
  rw [freshAt_of_take h7]
  exact taken_off_pile (d := dOf s) hb h7

/-- The matrix has a column variable. -/
theorem one_le_kCol {P : Where} {s : S} (hr : readyC P s = true) : 1 ≤ P.lin.kCol := by
  obtain ⟨_, _, _, _, _, _, _, _, h6, _, _, _⟩ := (ready_iff P s).1 hr
  unfold Batt.fits at h6
  cases hp : s.out.pending with
  | nil =>
    rw [hp] at h6
    cases h6
  | cons r l =>
    rw [hp] at h6
    exact of_decide_eq_true (Bool.and_eq_true_iff.1 h6).1

variable {nR : ℕ} {Cl : Type}

/-- **At every v the decision accepts the honest rounds, with a true claim.** s IS FIXED WHILE v
VARIES; the decision tests no sent value; the sample rows in a real state are not treated: see the
head. -/
theorem family_accepts {P : Where} {s : S} (hr : readyC P s = true)
    (hb : pileBelowC s.st s.out.indexMasks s.out.pending = true) (w : Wit GE nR P.lin.kCol)
    (hrows : ∀ r ∈ s.out.pending, Holds ρg w r) (v : Fin (2 * P.lin.kCol + 1) → GE) (x eps : E)
    (gs : List E) (hg : gs.length = P.lin.kCol) (cols : List (List (Nat × List UInt64))) :
    (∀ r ∈ s.out.pending, Holds ρg (withTaken w (freshAt P s) (onNat v)) r) ∧
    ∃ (st' : Statement) (msg : Array OracleNotice) (row : TensorRow),
      (atM3 (Cl := Cl) P).decide s
          (honestRounds P s (withTaken w (freshAt P s) (onNat v)) x eps gs) cols =
        .ok (withClaim s st' msg row) ∧
      Holds ρg (withTaken w (freshAt P s) (onNat v)) row := by
  have h : ∀ r ∈ s.out.pending, Holds ρg (withTaken w (freshAt P s) (onNat v)) r := fun r hr' =>
    (holds_withTaken ρg w (freshAt P s) (onNat v) r (freshAt_off_pile hr hb r hr')).2 (hrows r hr')
  exact ⟨h, atM3_accepts_ready hr _ h x eps gs hg cols⟩

/-- **Over uniform v these rounds have the distribution of the rounds of uniform scalars.** s IS
FIXED WHILE v VARIES, and so are w's matrix and other entries, x, eps and gs. OF THE PROVER THAT
READS THE LIST OFF THE VERIFIER's STATE; `readyC` is a premise on which the distribution itself
hangs. THE SPENDER's HALF: see the head; not to be quoted without the sender's sentence. -/
theorem family_law {P : Where} {s : S} (hr : readyC P s = true) (w : Wit GE nR P.lin.kCol)
    (x eps : E) (gs : List E) :
    (Prob.unif (Fin (2 * P.lin.kCol + 1) → GE)).map
        (fun v => honestRounds P s (withTaken w (freshAt P s) (onNat v)) x eps gs) =
      (Prob.unif (Fin (2 * P.lin.kCol + 1) → GE)).map fun c =>
        roundsOfView (fun a => E.ofTriple (ofE a)) x eps gs (tellL (onNat c) P.lin.kCol) :=
  moves_law ρg (fun a => E.ofTriple (ofE a)) w s.out.pending (freshAt P s) (one_le_kCol hr)
    (freshAt_nodup hr) (freshAt_length hr) x eps gs

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.freshAt_nodup
#print axioms VerifiableInference.Desc.K13.Honest.freshAt_length
#print axioms VerifiableInference.Desc.K13.Honest.freshAt_off_pile
#print axioms VerifiableInference.Desc.K13.Honest.one_le_kCol
#print axioms VerifiableInference.Desc.K13.Honest.family_accepts
#print axioms VerifiableInference.Desc.K13.Honest.family_law
