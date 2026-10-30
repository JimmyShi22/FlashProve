-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/Draws.lean: the yes of "LIN point", "LOC" and "LIN zeta" gives `PointLaid`,
`LocLaid` and `ZetaLaid` (Johnson/Desc/Key/Laid/DrawsDef.lean): of the functions, and of the first,
the fourth and the seventh of K14's eight blocks; and at these blocks, under the format's test
`roundsFit`, how many elements or locations the one round has drawn. Theorems; no definition.

OBJECT. The functions `linPoint`, `loc`, `linZeta` of Johnson/Desc/K14/Text.lean; and the members 0, 3
and 6 (from 0) of the list that `Desc.K14.blocks Q` returns, by their fields `decide` and `rounds`.
USER. Johnson/RunOne/KeyForward.lean (the promise's forward halves of the key file's rows 2.1, 2.4,
2.7), and through it the joining of the two halves of such a row.
LETTERS. p | Q, d d' rs gs: free. Tied: the eight are what `blocks Q` returns; `PointLaid` wants that
the shape splits.

CAUTION. Each statement has the form "a yes gives": true, and empty, of a block that never says yes.
NOTHING ON CHANCE: these are the facts that hold at every drawn point.

Main names.
  `newGroupP_eq`: the plain ground's newGroupP's yes, read back.
  `locX_kind`: a row (loc_x) is of the kind "generator" (by `locX_inv`,
    Johnson/Desc/K14/Law/MeansLoc.lean).
  `laid_point`, `laid_loc`, `laid_zeta`: of the functions.
  `point_at_blocks`, `loc_at_blocks`, `zeta_at_blocks`: of the blocks, with the counts.

Limits. Nothing on the blocks' tests on the plan. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Key.Laid.DrawsDef
import Johnson.Desc.Key.Laid.Rec
import Johnson.Desc.K14.Law.AtBlocks
import Johnson.Desc.K14.Law.MeansLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState Par)
open VerifiableInference.Desc (Block roundsFit noDigest)
open VerifiableInference.Desc.Ground (newGroupP addRowsP ok)
open _root_.Desc.K14 (St P14 blocks linPoint loc linZeta locX drawn)
open _root_.Desc.K14.Law (why_some linPoint_ok linZeta_inv linZeta_one loc_one)

namespace VerifiableInference.Desc.Key

/-- newGroupP's yes, whole. -/
theorem newGroupP_eq {L : Type} (d d' : DState L) (a b g : Nat)
    (h : newGroupP d a b = some (g, d')) :
    g = d.st.groups.size ∧
      d' = { d with st := { d.st with groups := d.st.groups.push { code := a, maskCode := b } } } := by
  unfold newGroupP at h
  split at h
  · have e := Option.some.inj h
    exact ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  · cases h

/-- **The yes of "LIN point" gives PointLaid**, where the shape splits. -/
theorem laid_point (p : Par) (d d' : St) (rs : List Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : linPoint p d rs = some d') : ∃ r, rs = [r] ∧ PointLaid p d d' r := by
  have hlin := linPoint_ok p d d' rs h
  unfold linPoint at h
  split at h
  · rename_i r
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    rw [if_pos hS] at h2
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
    obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
    have hord : Means.InOrder d.st → Means.InOrder d2.st :=
      fun hI => Means.newGroupP_keeps h3 (Means.newGroupP_keeps h1 hI)
    obtain ⟨e1, rfl⟩ := newGroupP_eq _ _ _ _ _ h1
    obtain ⟨e2, rfl⟩ := newGroupP_eq _ _ _ _ _ h3
    subst e1
    subst e2
    refine ⟨r, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, hlin, hord⟩
    simp
  · cases h

/-- A row (loc_x) is of the kind "generator". -/
theorem locX_kind (S : Params.FoldeqShape) (x : Nat) (w : Array E) (column : Array F)
    (u : FoldedRow) (row : OnBytes.Row) (h : locX S x w column u = some row) :
    row.kind = .generator := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := _root_.Desc.K14.Law.locX_inv S x w column u row h
  rfl

/-- What a mapM over Option returns has the list's length, and each member comes of a member. -/
theorem mapM_some {α β : Type} (f : α → Option β) : ∀ (l : List α) (out : List β),
    l.mapM f = some out → out.length = l.length ∧ ∀ y ∈ out, ∃ x ∈ l, f x = some y
  | [], out, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hy => by cases hy⟩
  | a :: l, out, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨i1, i2⟩ := mapM_some f l bs hbs
    refine ⟨by simp [i1], fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := i2 y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- **The yes of "LOC" gives LocLaid.** -/
theorem laid_loc (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : loc p d rs gs = some d') : ∃ r cols GU rows, rs = [r] ∧ gs = [cols] ∧ LocLaid p d d' r GU rows := by
  obtain ⟨r, cols, rfl, rfl⟩ := loc_one p d d' rs gs h
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, hm, ha⟩ := h
  -- the group is there: the ground's own first test
  obtain ⟨GU, hG⟩ : ∃ G, d.st.groups[d.loc.gU]? = some G := by
    have ha' := ha
    unfold addRowsP at ha'
    split at ha'
    · rename_i hok
      simp only [ok, VerifiableInference.Desc.Ground.rowsL, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true] at hok
      exact Option.isSome_iff_exists.1 hok.1
    · cases ha'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := addRowsP_eq _ _ _ _ _ ha hG
  obtain ⟨m1, m2⟩ := mapM_some _ _ _ hm
  refine ⟨r, cols, GU, rows, rfl, rfl, a1, a2, a3, a4, a5, a6, a7, hG, a8, a9, by simpa using m1, ?_,
    fun hI => Means.addRowsP_keeps ha hI⟩
  intro x hx
  obtain ⟨q, _, hq⟩ := m2 x hx
  simp only [Option.bind_eq_some_iff] at hq
  obtain ⟨_, _, hq⟩ := hq
  exact locX_kind _ _ _ _ _ _ hq

/-- **The yes of "LIN zeta" gives ZetaLaid.** -/
theorem laid_zeta (d d' : St) (rs : List Fmt.RoundView) (h : linZeta d rs = some d') :
    ∃ r, rs = [r] ∧ ZetaLaid d d' r := by
  obtain ⟨r, rfl⟩ := linZeta_one d d' rs h
  exact ⟨r, rfl, ⟨linZeta_inv d d' r h⟩⟩

/-- What `roundsFit` says at one declared round: one round, with the entry's counts. -/
theorem roundsFit_one (D : Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit [D] rs = true) :
    ∃ r, rs = [r] ∧ r.drawn.elems.length = D.entry.drawE ∧ r.drawn.poss.length = D.entry.poss := by
  rcases rs with _ | ⟨r, _ | ⟨r2, l⟩⟩
  · simp [roundsFit] at h
  · simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨r, rfl, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2⟩
  · simp [roundsFit] at h

theorem drawn_noDigest (r : Fmt.RoundView) : drawn (noDigest r) = drawn r := rfl

theorem drawn_length (r : Fmt.RoundView) : (drawn r).length = r.drawn.elems.length := by
  simp [drawn]

section
variable (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
include hb

/-- **The block "LIN point"**: under the format's test on its rounds its yes gives PointLaid, and the
point has the shape's number of coordinates. -/
theorem point_at_blocks (hS : Q.S.sharedSplitNeeded = true) :
    ∀ d rs gs d', roundsFit b1.rounds rs = true → b1.decide d (rs.map noDigest) gs = .ok d' →
      ∃ r, PointLaid Q.par d d' r ∧ (drawn r).length = Q.S.kCol := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' hf h
  obtain ⟨r0, rfl, he, _⟩ := roundsFit_one _ rs hf
  have k : linPoint Q.par d ([r0].map noDigest) = some d' := why_some h
  obtain ⟨r, er, P⟩ := laid_point Q.par d d' _ hS k
  obtain rfl : noDigest r0 = r := by simpa using er
  exact ⟨_, P, by rw [drawn_noDigest, drawn_length, he]; rfl⟩

/-- **The block "LOC"**: the like; as many rows as the shape has columns to fold. -/
theorem loc_at_blocks :
    ∀ d rs gs d', roundsFit b4.rounds rs = true → b4.decide d (rs.map noDigest) gs = .ok d' →
      ∃ r GU rows, LocLaid Q.par d d' r GU rows ∧ rows.length = Q.S.fold.columns := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' hf h
  obtain ⟨r0, rfl, _, hp⟩ := roundsFit_one _ rs hf
  have k : loc Q.par d ([r0].map noDigest) gs = some d' := why_some h
  obtain ⟨r, cols, GU, rows, er, _, P⟩ := laid_loc Q.par d d' _ gs k
  obtain rfl : noDigest r0 = r := by simpa using er
  refine ⟨_, GU, rows, P, ?_⟩
  rw [P.count]
  exact hp

/-- **The block "LIN zeta"**: the like. -/
theorem zeta_at_blocks :
    ∀ d rs gs d', roundsFit b7.rounds rs = true → b7.decide d (rs.map noDigest) gs = .ok d' →
      ∃ r, ZetaLaid d d' r ∧ (drawn r).length = Q.S.kRow := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  intro d rs gs d' hf h
  obtain ⟨r0, rfl, he, _⟩ := roundsFit_one _ rs hf
  have k : linZeta d ([r0].map noDigest) = some d' := why_some (l := []) h
  obtain ⟨r, er, P⟩ := laid_zeta d d' _ k
  obtain rfl : noDigest r0 = r := by simpa using er
  exact ⟨_, P, by rw [drawn_noDigest, drawn_length, he]; rfl⟩

end

end VerifiableInference.Desc.Key
