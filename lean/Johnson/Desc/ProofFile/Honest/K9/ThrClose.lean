-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ThrClose.lean: `Plays` (Honest/Thread/Pays.lean) AND `BehindS`
(Honest/Thread/PaysS.lean) AT K9's TWO MEMBERS WITHOUT A ROUND, "the one equation" AND "the segment is shut", FROM
NAMED PREMISES. THE THREAD T AND THE LETTER Said ARE VARIABLES. A definition, statements and proofs; no goal is stated.
  `quiet_step`      at a block without a round, at challenges that its rounds can draw (so: none), the prover's side
      of the step, where it is there at all, plays nothing, reads no column and leaves the prover's run where it
      stands (its first lines are those of the frame's `plays_quiet`)
  `K9Ends T e z c Z l Lk p Q bE bS`   K9's structure of named premises there: `seat`: `SeatedClose`
      (Honest/K9/CloseKeeps.lean): no equation on a letter of T: it is paid under the library's one head by
      `close_at_head` · `bsE`, `bsS`: T.bs[e]? and T.bs[z]? are the description's own two blocks
  `SeatedClose.eqKeeps_yes`, `SeatedClose.shutKeeps_yes`   the two clauses from the frame's one form of a member's yes
      (`StepYes`) · `K9Ends.paysE`, `K9Ends.paysS`: from such a yes of whatever block stands at e, at z
  **`K9Ends.playsE`**, **`K9Ends.playsS`**   `Plays T e`, `Plays T z`: the frame's own `plays_quiet`
      (Honest/Thread/QuietLaw.lean), called
  **`K9Ends.formKeepsE`**, **`K9Ends.formKeepsS`**   behind each step of the member: T.Form ∧ T.keeps: from the
      structure and the named premises `FormBy` (Honest/K9/ThrBehind.lean) there, over K9's closed clause (`EqKeeps`,
      `ShutKeeps`): one call each of `formKeeps_of`
  **`K9Ends.behindE`**, **`K9Ends.behindS`**   `BehindS T Said e`, `BehindS T Said z` whole, from `BehindBy`: one call
      each of `behindS_by`
`formP` AND `rides` ARE LAWS, owed by whoever lays these two letters: from the pair in front and the clause, which is
an equation on the whole state. No member. `K9Ends` is spent also in Honest/K9/CloseYes.lean (`AcceptedS`);
`quiet_step` there alone; the theorems marked are called by no line. `K9Ends` binds e and z together, as `SeatedClose`
gives both blocks together: a theorem at e asks `bsS` for nothing.
WHAT IS NOT CLAIMED. Any premise at any thread (at the frame's thread at the library's head `rides` can be paid only
under a premise that the rider's own border is not the one behind the member: the frame's hb₀ : b₀ ≠ b + 1).
`Exchange` at either member. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.CloseKeeps
import Johnson.Desc.ProofFile.Honest.K9.ThrBehind
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- At a block without a round: the prover's side of the step plays nothing, stays where it stands, reads no column. -/
theorem quiet_step {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (blk : Block S' Cl) (hr : blk.rounds = [])
    (k : Coins Bk) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X)
    (cols : List Desc.OpenedColumn) (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m En ds y cols) :
    ds = [] ∧ y = ([], m) ∧ cols = [] := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  have hl0 : l = [] := by
    have e := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
    exact List.map_eq_nil_iff.1 e
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hl0
  subst hd0
  have e : (.ok ([], m) : Except Refusal (List Played × Mid W X)) = .ok y := hp
  obtain rfl := Except.ok.inj e
  rw [hr] at hc
  exact ⟨rfl, rfl, (Except.ok.inj hc).symm⟩

/-- **K9's named premises at its two members without a round.** e, z: their numbers in the thread's list. -/
structure K9Ends (T : Thread Bk S Claim V W X Pb) (e z : ℕ) (c : Chain S Claim) (Z : ProofFile.Pub) (l : ℕ)
    (Lk : Link S Claim) (p : Desc.K9.Where) (Q : Close.Par) (bE bS : Block S Claim) : Prop where
  seat : SeatedClose c Z l Lk p Q bE bS
  bsE : T.bs[e]? = some bE
  bsS : T.bs[z]? = some bS

variable {T : Thread Bk S Claim V W X Pb} {e z : ℕ} {c : Chain S Claim} {Z : ProofFile.Pub} {l : ℕ} {Lk : Link S Claim}
  {p : Desc.K9.Where} {Q : Close.Par} {bE bS : Block S Claim}

/-- **The payer in the frame's one form, at "the one equation".** -/
theorem SeatedClose.eqKeeps_yes (H : SeatedClose c Z l Lk p Q bE bS) (ft : ℕ) (s s' : S)
    (h : Johnson.Desc.First.Walk.Tied.StepYes ft bE s s') : EqKeeps s s' := by
  obtain ⟨R, cs, _, h⟩ := h
  exact H.eqKeeps ft s s' R cs _ h

/-- **The payer in the frame's one form, at "the segment is shut".** -/
theorem SeatedClose.shutKeeps_yes (H : SeatedClose c Z l Lk p Q bE bS) (ft : ℕ) (s s' : S)
    (h : Johnson.Desc.First.Walk.Tied.StepYes ft bS s s') : ShutKeeps s s' := by
  obtain ⟨R, cs, _, h⟩ := h
  exact H.shutKeeps ft s s' R cs _ h

/-- **`Plays` at "the one equation".** -/
theorem K9Ends.playsE (H : K9Ends T e z c Z l Lk p Q bE bS) : Plays T e :=
  plays_quiet T H.bsE H.seat.quiet.1 H.seat.quiet.2.1

/-- **`Plays` at "the segment is shut".** -/
theorem K9Ends.playsS (H : K9Ends T e z c Z l Lk p Q bE bS) : Plays T z :=
  plays_quiet T H.bsS H.seat.quiet.2.2.1 H.seat.quiet.2.2.2

variable {Said : ℕ → Coins Bk → Mid W X → Prop}

/-- The clause from a yes of whatever block stands at the number of "the one equation". -/
theorem K9Ends.paysE (H : K9Ends T e z c Z l Lk p Q bE bS) :
    ∀ blk, T.bs[e]? = some blk → ∀ s s', Johnson.Desc.First.Walk.Tied.StepYes T.ft blk s s' → EqKeeps s s' := by
  intro blk hblk s s' hy
  rw [H.bsE] at hblk
  cases hblk
  exact H.seat.eqKeeps_yes T.ft s s' hy

/-- The like at "the segment is shut". -/
theorem K9Ends.paysS (H : K9Ends T e z c Z l Lk p Q bE bS) :
    ∀ blk, T.bs[z]? = some blk → ∀ s s', Johnson.Desc.First.Walk.Tied.StepYes T.ft blk s s' → ShutKeeps s s' := by
  intro blk hblk s s' hy
  rw [H.bsS] at hblk
  cases hblk
  exact H.seat.shutKeeps_yes T.ft s s' hy

/-- The form behind and T.keeps, at "the one equation". -/
theorem K9Ends.formKeepsE (H : K9Ends T e z c Z l Lk p Q bE bS) (B : FormBy Said T e EqKeeps) :
    ∀ blk, T.bs[e]? = some blk → ∀ κ s m En ds y cols s', ThrS T Said e κ s m En →
      drawsFit blk.rounds ds = true → T.Stepped blk κ s m En ds y cols s' →
      T.Form (e + 1) κ s' y.2 ∧ T.keeps e s s' :=
  formKeeps_of B (fun _ _ K => K.mark) H.paysE

/-- The form behind and T.keeps, at "the segment is shut". -/
theorem K9Ends.formKeepsS (H : K9Ends T e z c Z l Lk p Q bE bS) (B : FormBy Said T z ShutKeeps) :
    ∀ blk, T.bs[z]? = some blk → ∀ κ s m En ds y cols s', ThrS T Said z κ s m En →
      drawsFit blk.rounds ds = true → T.Stepped blk κ s m En ds y cols s' →
      T.Form (z + 1) κ s' y.2 ∧ T.keeps z s s' :=
  formKeeps_of B (fun _ _ K => K.mark) H.paysS

/-- **`BehindS` at "the one equation".** -/
theorem K9Ends.behindE (H : K9Ends T e z c Z l Lk p Q bE bS) (B : BehindBy Said T e EqKeeps) : BehindS T Said e :=
  behindS_by B (fun _ _ K => K.mark) H.paysE

/-- **`BehindS` at "the segment is shut".** -/
theorem K9Ends.behindS (H : K9Ends T e z c Z l Lk p Q bE bS) (B : BehindBy Said T z ShutKeeps) : BehindS T Said z :=
  behindS_by B (fun _ _ K => K.mark) H.paysS

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.quiet_step
#print axioms ProofFile.Honest.K9.SeatedClose.eqKeeps_yes
#print axioms ProofFile.Honest.K9.SeatedClose.shutKeeps_yes
#print axioms ProofFile.Honest.K9.K9Ends.playsE
#print axioms ProofFile.Honest.K9.K9Ends.playsS
#print axioms ProofFile.Honest.K9.K9Ends.paysE
#print axioms ProofFile.Honest.K9.K9Ends.paysS
#print axioms ProofFile.Honest.K9.K9Ends.formKeepsE
#print axioms ProofFile.Honest.K9.K9Ends.formKeepsS
#print axioms ProofFile.Honest.K9.K9Ends.behindE
#print axioms ProofFile.Honest.K9.K9Ends.behindS
