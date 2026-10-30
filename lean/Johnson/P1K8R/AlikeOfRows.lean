-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/AlikeOfRows.lean: THE FIRST HALF OF THE FIELD "alike" OF `K8LeftT`
(Johnson/P1K8R/TightAt.lean), AT ONE STATE, FROM "ONE SHAPE, ONE RADIUS" AND NAMED PREMISES: every
place of the list of members that the smallness test's law reads off a state has a member of the
table's list with its shape, its radius and its seat. A joining of two lemmas: no new idea.
Why. The law lays the radius of each of the state's messages by `rad`, a function of the SHAPE alone
(`Named.listOf`); `K8Cond` lays `rad := P5J.At.rad3At Zp Z.lay`: the radius of the first sampled
entry of that shape in the first chain's rows of sendings. A member of the table's list bears the
rows' radius at its own sending and place. The two are one where one shape has one radius over these
rows: `P5T.radOneB`, a test with code; it stood on a list of tests to be evaluated (not named here).
  `listOf_radded`: each entry of `Named.listOf rad …` is (shape, rad shape): by its text.
  `alike_of_rows`: **the first half of "alike"**: by `P1Opts.some_at`
    (Johnson/Top/H0/Opts/SomeAtRows.lean) and `P5T.some_of_someB` (Johnson/P5J/Rad3Seat3At.lean).
THE PREMISES, NONE SHOWN HERE. hrows: the second reading of the three public files returns rows
(`P5J.rowsReadB` gives it) · h1: `radOneB` accepts · hSh: `P1Opts.RowsShaped`: the rows' shapes
are the plan's seats': a closed fact FOR WHICH NO TEST WITH CODE IS KNOWN TO US BY NAME · A: THE
STATE's SHARE: each place of the state's list has a seat of the plan with a sample, of its shape
and at its seat.
Limits. The second half of "alike" (`CellsIn`) is not treated. Nothing on soundness or on hiding.

-/
import Johnson.P1K8R.OwesAt
import Johnson.Top.H0.Opts.SomeAtRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound (Mem Alike)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open P5T (radOneB firstRows)

/-- Each entry of the list is (shape, rad shape). -/
theorem listOf_radded (rad : OracleShape → ℕ) (St : Statement) (book : TreeBook) (tl : HTailF2)
    (L : LinkCtx) : ∀ e ∈ Named.listOf rad St book tl L, e.2 = rad e.1 := by
  intro e he
  unfold Named.listOf at he
  obtain ⟨m, _, rfl⟩ := List.mem_map.1 he
  rfl

/-- **THE FIRST HALF OF "alike", AT ONE STATE.** -/
theorem alike_of_rows (Zp : ProofFile.Pub) (lay : ByteArray) {rows : List Johnson.G.SendRow}
    (hrows : P5T.rowsAt? Zp.pol lay Zp.KL = some rows)
    (h1 : radOneB ((firstRows rows).flatMap (·.sampled)) = true)
    (hSh : P1Opts.RowsShaped rows (P5J.At.pseats Zp)) (s : S) (tl : HTailF2) (L : LinkCtx)
    (A : ∀ i : Fin (lA (P5J.At.rad3At Zp lay) s tl L).length, ∃ p ∈ P5J.At.pseats Zp,
      p.smpd = true ∧ p.shape = ((lA (P5J.At.rad3At Zp lay) s tl L).get i).1 ∧
      p.seat = sA (P5J.At.rad3At Zp lay) s tl L i) :
    ∀ i, ∃ y ∈ P5J.At.ms Zp lay,
      Alike y ⟨⟨lA (P5J.At.rad3At Zp lay) s tl L, sA (P5J.At.rad3At Zp lay) s tl L⟩, i⟩ := by
  intro i
  have hL : ∀ e ∈ lA (P5J.At.rad3At Zp lay) s tl L, e.2 = P5J.At.rad3At Zp lay e.1 := by
    intro e he
    unfold lA at he
    exact listOf_radded _ _ _ _ _ e he
  have hs := P1Opts.some_at Zp lay hrows h1 hSh (lA (P5J.At.rad3At Zp lay) s tl L)
    (fun n => if h : n < (lA (P5J.At.rad3At Zp lay) s tl L).length then
      sA (P5J.At.rad3At Zp lay) s tl L ⟨n, h⟩ else (0, 0)) hL (fun j => by
      obtain ⟨p, hp, a1, a2, a3⟩ := A j
      refine ⟨p, hp, a1, a2, ?_⟩
      rw [a3]
      show _ = (if h : j.1 < (lA (P5J.At.rad3At Zp lay) s tl L).length then
        sA (P5J.At.rad3At Zp lay) s tl L ⟨j.1, h⟩ else (0, 0))
      rw [dif_pos j.isLt])
  obtain ⟨y, hy, e1, e2⟩ := P5T.some_of_someB _ _ _ hs i
  refine ⟨y, hy, e1, ?_⟩
  have e3 : y.1.seat y.2 = (if h : i.1 < (lA (P5J.At.rad3At Zp lay) s tl L).length then
      sA (P5J.At.rad3At Zp lay) s tl L ⟨i.1, h⟩ else (0, 0)) := e2
  rw [dif_pos i.isLt] at e3
  exact e3

end P1K8T

#print axioms P1K8T.listOf_radded
#print axioms P1K8T.alike_of_rows
