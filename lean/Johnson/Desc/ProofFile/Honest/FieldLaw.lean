-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FieldLaw.lean: the one law that carries `FieldAt` (Field.lean) over a
place: where it holds before rounds that are played by `play`, and the columns that these rounds'
declared reads ask are filled from the tables then available, it holds after them at the state that
has taken these columns (`Mid.took`). So whoever proves `Good.plays` at a list with the field beside
its A and B need not prove the field's half for itself (FieldGood.lean).

  1  `FieldAt.step`   the law. Its proof follows the lines of `made_next` (Thread/MadeLaw.lean),
     which does the same for the thread's own columns
  2  `FieldFit`, `FieldFit.step`, `FieldFit.start`   the law's three side conditions as one
     definition; it carries itself over a place; where it starts

By what. `readsOf_append`, `fillCols_append`, `fillCols_mono` (Law/Cut.lean), `Env.Tight`,
`Env.add_tight` (Law/Along.lean), `play_heard` (Thread/PaysLaw.lean), `Env.add_keeps`
(Thread/MadeLaw.lean), `play_opened` (Gap.lean).

Limits.
  * The law has three side conditions: the available tables are tight; `skip` is at most the number
    of challenges heard; the declared rounds are as many as the challenges heard behind `skip`.
  * That `FieldAt` holds at a chain's start is not proved here, nor that a run's own start is a
    state whose field is `some base`.
  * In `FieldAt.step` `rounds` is any list: that it is the played steps' own declaration is the
    caller's (`plays_field`, FieldGood.lean).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Field
import Johnson.Desc.ProofFile.Honest.Gap
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (OpenedColumn)

variable {W Y : Type}

/-! ## 1 The law -/

section
variable {chain firstTree skip : Nat} {decls rounds : List Fmt.DeclaredRound} {base cols : List OpenedColumn}
  {m : Mid W Y} {E : Env} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {back : List Fmt.RoundView}
  {y : List Played × Mid W Y}

/-- **THE LAW: `FieldAt` is carried over rounds that are played.** -/
theorem FieldAt.step (hF : FieldAt chain firstTree decls base skip m E) (hT : E.Tight)
    (hs : skip ≤ m.st.heard.length) (hl : decls.length = (m.st.heard.drop skip).length)
    (hp : play ss ds back m = .ok y)
    (hc : fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree rounds ds) [] =
      .ok cols) :
    FieldAt chain firstTree (decls ++ rounds) base skip (y.2.took cols) (E.add y.1) := by
  obtain ⟨c₀, h0, hm⟩ := hF
  refine ⟨c₀ ++ cols, ?_, ?_⟩
  · have f₁ : fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree decls
        (m.st.heard.drop skip)) [] = .ok c₀ :=
      fillCols_mono (fun z pt hz => Env.add_keeps hT y.1 hz) _ _ _ h0
    show fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree (decls ++ rounds)
      (y.2.st.heard.drop skip)) [] = _
    rw [play_heard _ _ _ _ _ hp, List.drop_append_of_le_length hs,
      readsOf_append _ _ _ _ _ _ _ _ hl, fillCols_append, f₁]
    show (fillCols _ (([] : List OpenedColumn).drop _)).map _ = _
    rw [List.drop_nil, hc]
    rfl
  · show y.2.opened.map (· ++ cols) = _
    rw [play_opened _ _ _ _ _ hp, hm]
    show some ((base ++ c₀) ++ cols) = _
    rw [List.append_assoc]

/-! ## 2 Its side conditions -/

/-- The law's three side conditions. -/
def FieldFit (decls : List Fmt.DeclaredRound) (skip : Nat) (m : Mid W Y) (E : Env) : Prop :=
  skip ≤ m.st.heard.length ∧ decls.length = (m.st.heard.drop skip).length ∧ E.Tight

/-- They are carried over rounds that are played, where the declared rounds are as many as the
challenges. -/
theorem FieldFit.step (h : FieldFit decls skip m E) (hp : play ss ds back m = .ok y)
    (hr : rounds.length = ds.length) :
    FieldFit (decls ++ rounds) skip (y.2.took cols) (E.add y.1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (y.2.took cols).st.heard = m.st.heard ++ ds := play_heard _ _ _ _ _ hp
  refine ⟨?_, ?_, Env.add_tight h3 y.1⟩
  · rw [e, List.length_append]
    omega
  · rw [e, List.drop_append_of_le_length h1, List.length_append, List.length_append, h2, hr]

/-- They hold where nothing has been heard behind `skip`, at tables that are tight, with no declared
round. -/
theorem FieldFit.start (hh : m.st.heard.length = skip) (hT : E.Tight) : FieldFit [] skip m E := by
  refine ⟨Nat.le_of_eq hh.symm, ?_, hT⟩
  rw [List.length_drop, hh, Nat.sub_self]
  rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.FieldAt.step
#print axioms ProofFile.Honest.FieldFit.step
#print axioms ProofFile.Honest.FieldFit.start
#print axioms ProofFile.Honest.FieldFit
