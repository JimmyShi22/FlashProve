-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ExitBuild.lean: at the exit code 0 of verify-on-bytes the user's prompt, output and
further tokens build an instance at the sizes that `Flat.sizesAt` reads off the parameter file,
where it returns. For proofs only; the program does not import this file.

  `publicOf_head`: in the public part that the planner makes, the head's numbers lt and V are the
    parameter file's.
  `root_sizes`: under `Root F further D` (OnBytes/TieK/HeadRoot.lean): the window at which the
    program read the request is 2 ^ lt. It is drawn from the run: the head's routine tests the
    statement's positions against its own window (OnBytes/K/ReplyRoot.lean, `root_win`).
  `root_build`: so, for the sizes P that `Flat.sizesAt` (Johnson/Flat/Instance.lean) reads off the
    parameter file: `Flat.buildOf P` returns an instance at `promptOf`, `outputOf` and `auxOf` of
    the user's statement; its r, e and y are those that the program read, and its window is the
    request's tokens (`tokensOf`; that these are the program's own: `covered_of`,
    OnBytes/K/TokensCovered.lean).
  `build_zero`: at the exit code 0, at the options a and the files F of `main_zero_port`.
What is not claimed: nothing where `sizesAt` refuses: it refuses a parameter file whose own policy
is not the exact match, while a call that names -policy, or a call about the reply alone, can return
0 under such a file (OnBytes/K/ExitNarrow.lean [not in this library]). Nothing on what a yes says of that instance: no
verifier's part is shown to accept at i. Of the run only the routine's first test is used. No law
here says that the planner's window is 2 ^ lt without a run.


-/
import OnBytes.K.ReplyRoot
import Johnson.Top.TokensBuild
import OnBytes.Model.VerifyDerives

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- In the public part the head's lt and V are the parameter file's. -/
theorem publicOf_head {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) : X.hS.lt = X.P.h.lt ∧ X.hS.V = X.P.h.V := by
  unfold publicOf at h
  obtain ⟨⟨P, y⟩, _, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals (cases h; exact ⟨rfl, rfl⟩)

/-- What `planned` holds as the public part is what `publicOf` returns. -/
theorem planned_public {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) : publicOf pol KL layout = .ok p.X := by
  unfold planned at h
  obtain ⟨X, h0, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact h0

/-- The window at which the program read the request is 2 ^ lt. -/
theorem root_sizes {F : Files} {further : Params.TableName} {D : TieK.RootData}
    (R : TieK.Root F further D) :
    polScan F.pol = .ok D.p.X.P ∧ D.p.X.T = 2 ^ D.p.X.P.h.lt := by
  have hp := planned_public R.made.plan
  obtain ⟨e1, _⟩ := publicOf_head hp
  refine ⟨publicOf_scan hp, ?_⟩
  rw [← (root_win R).1, ← e1]
  rfl

/-- At the sizes that `sizesAt` reads off the parameter file. -/
theorem root_build {F : Files} {further : Params.TableName} {D : TieK.RootData}
    (R : TieK.Root F further D) (o : Options) {P : Inst.Model.Params}
    (hP : Flat.sizesAt F.pol = .ok P) :
    ∃ i : Flat.Instance' P,
      Flat.buildOf P (promptOf (stmOf F o), outputOf (stmOf F o)) (auxOf (stmOf F o)) = some i ∧
      i.r = D.so.r ∧ i.e = D.so.e ∧ i.y.val = D.so.y ∧
      ∀ t : Fin P.T, (i.prompt t).val = (tokensOf (stmOf F o)).getD t.val 0 := by
  obtain ⟨hs, hT⟩ := root_sizes R
  unfold Flat.sizesAt at hP
  obtain ⟨P0, h0, hP⟩ := exc_bind hP
  have e0 : P0 = D.p.X.P := Except.ok.inj (h0.symm.trans hs)
  subst e0
  split at hP
  · cases hP
    have hown : Head.stFromCall (words32 (stmOf F o).request) (words32 (stmOf F o).y)
        (Flat.sizesOf D.p.X.P.h).T = .ok D.so := by
      have h1 := R.made.own
      rw [hT] at h1
      exact h1
    have hcov : Head.coveredOf D.so (Flat.sizesOf D.p.X.P.h).T (Flat.sizesOf D.p.X.P.h).V =
        .ok D.cov := by
      have h2 := R.made.covered
      rw [hT] at h2
      exact h2
    exact build_of_files hown hcov
  · cases hP

/-- At the exit code 0. In words: the head of this file. -/
theorem build_zero {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∀ P : Inst.Model.Params, Flat.sizesAt F.pol = .ok P →
        ∃ i : Flat.Instance' P,
          Flat.buildOf P (promptOf (stmOf F a.options), outputOf (stmOf F a.options))
            (auxOf (stmOf F a.options)) = some i ∧
          i.r = rOf (stmOf F a.options) ∧ i.e = eOf (stmOf F a.options) ∧
          i.y.val = yOf (stmOf F a.options) ∧
          ∀ t : Fin P.T, (i.prompt t).val = (tokensOf (stmOf F a.options)).getD t.val 0 := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4, table,
    further, hp⟩ := main_zero_port h
  obtain ⟨D, R⟩ := TieK.head_root hp
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, h3, h4, ?_⟩
  intro P hP
  obtain ⟨i, b0, b1, b2, b3, b4⟩ := root_build R a.options hP
  have hown : Head.stFromCall (words32 (stmOf F a.options).request)
      (words32 (stmOf F a.options).y) D.p.X.T = .ok D.so := R.made.own
  obtain ⟨_, _, r1, r2, r3, _, _⟩ := read_of hown
  exact ⟨i, b0, b1.trans r1, b2.trans r2, b3.trans r3, b4⟩

end OnBytes.K
