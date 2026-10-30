-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontPlainB.lean: one function with values in Bool, `frontPlainB`
(below: the test), and the theorem `frontPlain_of_B`: where the test is true, the plain data of a
proximity test's first stage exist and meet what two other files ask of them. The test takes the
thin shape of the state before the proximity test (`ThinSh`,
Johnson/Desc/K12/Honest/Shape/TestCore.lean), which holds no field element. The clause `plain` of
`FrontAsks` (ShapeAll.lean in this folder) speaks of the state with the group's test begun (`batT`).
By `thin_batT`, that state's thin shape is what the batching's function on thin shapes (`batThin`)
returns. The library's plain data there have the shape that `gpOfS` computes. So the clause, and the
public clauses of a job made of a sending (`oneFitsB`, OneFitsB.lean in this folder), follow where
one evaluation gives true. General in the place p, the sending's public data P and the state t. A
definition with code, and two theorems with their proofs.

In the list: p is a place (`P12`, Johnson/Desc/K12/Frame.lean): the numbers of a place at which a
proximity test is. `stA p` (PlanB.lean in this folder) is its first stage (`Fmt.M1.Stage`), a stage
of zeros where it has none; C and Z are the stage's main code and mask code, and `l` is a code's
message length. P (`K1.Par`, Johnson/Desc/K1/Send.lean) is a sending's public data. A job
(`TestJob`, Test.lean in this folder) is what a caller supplies for its proximity test; the job made
of a sending is `jobOne`, and its public clauses are `OneFits` (both JobOne.lean in this folder). t
is a state of the type `T12` of the verifier's state inside a proximity test
(Johnson/Desc/K12/Join.lean). Its fields are a statement `st`, a book of trees `book` (`TreeBook`,
OnBytes/Iop/Ground.lean), a count `roots`, the number `g` of the group under test, what one part of
the proximity test passes to the next (`pass`), and `mask`: the number of the message that holds the
first fold's fresh table, where that has come earlier. `thinSh t` (TestCore.lean) is its thin shape:
the shape of `st`, `book` and `roots` (`coreSh`, Johnson/Desc/Ground/Shape/Core.lean), then `g`,
`mask`, and a part of `pass` (`thinPass`): of what a batching passes on, a claim's row with a
layout, the layout only. G is a group of `t.st`; its members are oracle messages. Its layout
(`GroupLayout`, Ground.lean) is `layoutOf t.st G` (Johnson/Desc/Means/Layout.lean). `layoutAt t`
(JobOne.lean) is the layout of group number `t.g`, an empty one where there is no such group.
`batT t G row` (Johnson/Prover/Link/FormFirst.lean) is t with the group's test begun: its statement
is `begun t.st t.g G` (OnBytes/Slice/BlkBegin.lean), and it passes on the row (`GroupRow`,
Ground.lean) with the layout of G. `{}` is the empty row. The plain data (`Plain`,
Johnson/Desc/K12/Law/FirstOk.lean) are what `gpOf` (FirstOk.lean) makes of a place, a state, a stage
and a layout: a statement, a book of trees, the layout `L`, the members and the fresh table, each as
a part of a tree (`Seat1`, FirstOk.lean), the trees' places and the declared openings. `gpL`
(FirstOk.lean) lists the library's clauses on the plain data, each a name with a Bool, and `ok` is
true where all are true. `PlainS`, `gpOfS` and `gpLS` (Johnson/Desc/K12/Honest/Shape/TestDoor.lean)
are `Plain`, `gpOf` and `gpL` on shapes: `PlainS` has the statement's codes in place of the
statement, and the book's shape in place of the book. `plainSh` (TestDoor.lean) maps `Plain` to
`PlainS`.

  `frontPlain_of_B`: under the three hypotheses below there are plain data Dp such that
    `oneFitsB p P (plainSh Dp)` is true, `Dp.L` is `layoutAt t`, and the four parts of the clause
    `plain` hold at every G that is group number `t.g` of `t.st`: `gpOf` returns Dp at p,
    `batT t G {}`, the first stage and the layout of G; `ok (gpL p (stA p) {} Dp)` is true;
    2 ^ `logEll` of that layout is `(stA p).C.l`; and 2 ^ `logEllZk` of it is `(stA p).Z.l`
  `frontPlainB p P a₀`: a definition: the test, on the place, the sending's public data and a thin
    shape. It is true where all of these hold, and false elsewhere: `batThin p a₀` returns a thin
    shape aB that passes on a layout L; `gpOfS p aB (stA p) L` returns D; all clauses of
    `gpLS p (stA p) 0 D` are true, where 0 is the empty row's number of kept forms; 2 ^ `L.logEll`
    is `(stA p).C.l`; 2 ^ `L.logEllZk` is `(stA p).Z.l`; `oneFitsB p P D` is true
  `thin_batT`: where `t.pass` is `.nothing`, `p.early` is true, G is group number `t.g` of `t.st`,
    and `batThin p (thinSh t)` returns aB: aB is `thinSh (batT t G row)`, whatever the row.
    FrontThin.lean in this folder has the same theorem, word for word, in the namespace
    `ProofFile.Honest.K12.Thin`

By what. `thin_batT` unfolds `batThin`. Where the beginning of a group's test on shapes
(`beginRunS`) returns, the description's `beginRunP` (Johnson/Desc/First/Base/Ground.lean) returns
(`beginRun_returns`), and what the first returns is read off what the second returns
(`beginRun_carries`; the three in Johnson/Desc/Ground/Shape/Ground.lean). `beginRunP` is then
unfolded at G, and `layoutOf_own` (Johnson/Prover/Link/FormBatLaws.lean) rewrites `Own.layoutOf` to
`layoutOf`. `frontPlain_of_B` unfolds the test. That there is a group number `t.g` follows from the
return of `batThin`, by `beginRun_returns`. `thin_batT` at the empty row gives that aB is the thin
shape of `batT t G {}`, so L is the layout of G. `gpOfS_eq` (TestDoor.lean) gives Dp with D =
`plainSh Dp`; `made_of` (Johnson/Desc/K12/Law/FirstOkLaw.lean) gives that `Dp.L` is that layout;
`gpLS_eq` (TestDoor.lean) carries the clauses over to `gpL`.

Hypotheses of `frontPlain_of_B`. hp: `t.pass` is `.nothing`, as it is before a batching. he:
`p.early` is true. h: `frontPlainB p P (thinSh t)` is true.

Limits.
- That the test is true is shown at no place here. FrontPlainAtKey.lean in this folder evaluates it
  at one written place, thin shape and sending (`frontPlain_KR`).
- Where the place counts the fresh table as come earlier (`p.early`). In Lean: `p.early = true` is a
  hypothesis of both theorems.
- Only the direction from the test to the clauses is proved: where the test is false, nothing is
  stated.
- t is a free parameter. It has the type of the verifier's state inside a proximity test; nothing
  here shows that it is the verifier's state.
- The four parts of the clause `plain` are stated at every G that is group number `t.g`: they are
  vacuous where there is no such group. The proof of `frontPlain_of_B` shows that there is one, but
  its statement does not say so.
- The theorem says that there are such data Dp. Dp holds a statement and a book of trees whole, and
  it is not stated to be a function of the thin shape.
- `oneFitsB` is all clauses of `OneFits` but `layout`. It asks that the sending has more than one
  message, not that it has two. It reads nothing of what rides (`OneSent.ride`, JobOne.lean). The
  clause "room" of `planL` (PlanB.lean) is not among the test's clauses.
- Nothing on values.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.OneFitsB
import Johnson.Desc.K12.Honest.Shape.TestCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open ProofFile.Honest.Sh (ThinSh thinSh batThin PlainS plainSh gpOfS gpOfS_eq gpLS gpLS_eq)

/-- **The thin shape of the state with the group's test begun is what `batThin` returns.** hp:
nothing is passed on. he: `p.early` is true. hG: G is the group under test. h: `batThin` returns aB
at the thin shape of t. At every row. -/
theorem thin_batT (p : P12) (t : T12) (G : Group) (row : GroupRow) (aB : ThinSh)
    (hp : t.pass = .nothing) (he : p.early = true) (hG : t.st.groups[t.g]? = some G)
    (h : batThin p (thinSh t) = some aB) : thinSh (batT t G row) = aB := by
  unfold batThin at h
  have e0 : (thinSh t).pass = .nothing := by
    show ProofFile.Honest.Sh.thinPass t.pass = _
    rw [hp]
    rfl
  rw [e0] at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 h
    have hy' : beginRunS (shD (H2K.Out.dT t [])) t.g = some y := hy
    obtain ⟨x, hx⟩ := beginRun_returns (H2K.Out.dT t []) t.g y hy'
    have c := beginRun_carries (H2K.Out.dT t []) x.2 t.g x.1 hx
    obtain rfl := Option.some.inj (hy'.symm.trans c)
    unfold VerifiableInference.Desc.Ground.beginRunP at hx
    split at hx
    · have hG' : (H2K.Out.dT t []).st.groups[t.g]? = some G := hG
      rw [hG'] at hx
      obtain rfl := Option.some.inj hx
      rw [he]
      show thinSh (batT t G row) = ⟨coreSh ⟨begun t.st t.g G, t.book, t.roots⟩, t.g,
        .claim (Own.layoutOf t.st G), t.mask⟩
      rw [layoutOf_own hG]
      rfl
    · cases hx
  · cases h

/-- The test, on the place p, a sending's public data P and a thin shape a₀. True where `batThin`
returns a thin shape that passes on a layout L, `gpOfS` returns D there, all clauses of `gpLS` at D
are true, the layout's two lengths are the first stage's, and `oneFitsB p P D` is true; false
elsewhere. -/
def frontPlainB (p : P12) (P : K1.Par) (a₀ : ThinSh) : Bool :=
  match batThin p a₀ with
  | some aB =>
    match aB.pass with
    | .claim L =>
      match gpOfS p aB (stA p) L with
      | some D =>
        ok (gpLS p (stA p) 0 D) && decide (2 ^ L.logEll = (stA p).C.l) &&
          decide (2 ^ L.logEllZk = (stA p).Z.l) && oneFitsB p P D
      | none => false
    | _ => false
  | none => false

/-- **Where the test is true at the state's thin shape, the plain data exist and meet the clauses.**
There are Dp at whose shape `oneFitsB` is true, whose layout is the state's, and which meet the four
parts of the clause `plain` of `FrontAsks` (ShapeAll.lean) at every G that is the group under test.
That there is such a G is shown in the proof and is not in the statement. -/
theorem frontPlain_of_B (p : P12) (P : K1.Par) (t : T12) (hp : t.pass = .nothing)
    (he : p.early = true) (h : frontPlainB p P (thinSh t) = true) :
    ∃ Dp : Plain, oneFitsB p P (plainSh Dp) = true ∧ Dp.L = layoutAt t ∧
      ∀ G, t.st.groups[t.g]? = some G →
        gpOf p (batT t G {}) (stA p) (layoutOf t.st G) = some Dp ∧
          ok (gpL p (stA p) {} Dp) = true ∧ 2 ^ (layoutOf t.st G).logEll = (stA p).C.l ∧
          2 ^ (layoutOf t.st G).logEllZk = (stA p).Z.l := by
  unfold frontPlainB at h
  split at h
  · rename_i aB hB
    split at h
    · rename_i L hL
      split at h
      · rename_i D hD
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        -- there is a group number `t.g`: `batThin` has returned
        have hGx : ∃ G, t.st.groups[t.g]? = some G := by
          cases hg : t.st.groups[t.g]? with
          | some G => exact ⟨G, rfl⟩
          | none =>
            exfalso
            unfold batThin at hB
            have e0 : (thinSh t).pass = .nothing := by
              show ProofFile.Honest.Sh.thinPass t.pass = _
              rw [hp]
              rfl
            rw [e0] at hB
            split at hB
            · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hB
              have hy' : beginRunS (shD (H2K.Out.dT t [])) t.g = some y := hy
              obtain ⟨x, hx⟩ := beginRun_returns (H2K.Out.dT t []) t.g y hy'
              unfold VerifiableInference.Desc.Ground.beginRunP at hx
              split at hx
              · have hg' : (H2K.Out.dT t []).st.groups[t.g]? = none := hg
                rw [hg'] at hx
                cases hx
              · cases hx
            · cases hB
        obtain ⟨G, hG⟩ := hGx
        have eT := thin_batT p t G {} aB hp he hG hB
        have eL : L = layoutOf t.st G := by
          have k : (thinSh (batT t G {})).pass = .claim (layoutOf t.st G) := rfl
          rw [eT, hL] at k
          injection k
        subst eL
        have k := gpOfS_eq p (batT t G {}) (stA p) (layoutOf t.st G)
        rw [eT, hD] at k
        obtain ⟨Dp, hDp, eD⟩ := Option.map_eq_some_iff.1 k.symm
        subst eD
        have hlay : Dp.L = layoutAt t := by
          rw [(made_of _ _ _ _ _ hDp).lay]
          unfold layoutAt
          rw [hG]
          rfl
        refine ⟨Dp, h4, hlay, fun G' hG' => ?_⟩
        obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
        refine ⟨hDp, ?_, h2, h3⟩
        rw [← gpLS_eq]
        exact h1
      · cases h
    · cases h
  · cases h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.thin_batT
#print axioms ProofFile.Honest.K12.frontPlain_of_B
#print axioms ProofFile.Honest.K12.frontPlainB
