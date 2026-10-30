-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Fold/FoldView.lean: on a view, a run of the program's fold takes k + 1 rounds off the
view, and a run of its batching takes one; what these rounds hold, and what the fold returns.

The program's fold (`foldVerify`, OnBytes/Iop/Fold.lean), where the fresh mask came in an earlier
message, receives one element (the sum) and closes a round in which one element is drawn; then, k
times, it receives two elements and closes a round in which one element is drawn.
OnBytes/Slice/BlkFold.lean says what such a run computes if the rounds that are left begin with the
view of written rounds of one given form. Here nothing is asked of the rounds that are left: from
the run's success alone it is said which rounds of the view it has taken. The laws on single calls
are the library's (OnBytes/Iop/GroundLaws.lean) and those of OnBytes/Tie/Pv/Psc/PscView.lean and
OnBytes/Tie/Pv/Psc/Run/ViewRounds.lean. Statements and proofs.

Main names:
  `recvE_ate`: one element received is the next item of the first round that is not yet closed.
  `ate_close`: elements taken off a round, and the round closed: one round of the view, which holds
    these elements and no other item; no message is open behind it.
  `ate_closeOne`: the same where one element is drawn and returned.
  `RoundsHold rs qs gs`: the rounds rs hold, one by one, the pairs qs of elements and no other item,
    and each draws the one element of gs at its place.
  `claimAfter claim qs gs`: the running claim behind these rounds (`foldClaimRound`, round by
  round).
  `foldRounds_view`: the k rounds.
  `foldVerify_view`: the whole fold: the rounds not yet taken before the run are r₀, rs and those
    not yet taken behind it; r₀ holds the sum and draws eps; `RoundsHold rs qs gs` with k rounds;
    what is returned is
    `foldOutput` at eps, gs and the running claim; the program's three tests `foldShapeOk`,
    `foldMaskOk` (the oracle message named as the fresh mask has the mask's shape, is no member of
    the group and has no sample) and `foldRowOk` were true; no message is open behind the run.
  `batVerify_view`: the batching: one round, which holds no item and draws one element; no message
    is open behind the run.
Limits: one direction: from a run's success. On a view alone. If a message is open at c, r₀ is what
is left of that round. The fold whose mask's root is received in its own first message is not
treated. Nothing on what
`foldOutput` or `Bat.combine` compute. Nothing on soundness.

-/
import OnBytes.Iop.Fold
import OnBytes.Slice.BlkBat
import OnBytes.Tie.Pv.Psc.Run.ViewRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Fold
open OnBytes OnBytes.Slice OnBytes.Model.Road
open OnBytes.PscRun (Clean)

/-- One element received. -/
theorem recvE_ate {x : E} {c c' : Ctx} (hd : c.ch.dry = false) (h : Blk.recvE.Yields c x c') :
    Ate c.ch.pending [x] c'.ch.pending ∧ c'.ch.dry = false := by
  obtain ⟨r, rest, vs, e1, e2, e3, e4⟩ := Blk.recvE_inv x c c' hd h
  exact ⟨Or.inr ⟨r, rest, vs, e1, e2, e3⟩, e4.dry.trans hd⟩

/-- Elements taken off a round, and the round closed. -/
theorem ate_close {A : List Fmt.RoundView} {l : List E} {name : String} {kind : Fmt.Kind} {nz : Nat}
    {d : Fmt.Drawn} {c1 c' : Ctx} (hd : c1.ch.dry = false) (a3 : Ate A l c1.ch.pending)
    (h2 : (Blk.close name kind nz).Yields c1 d c') :
    ∃ r : Fmt.RoundView, A = r :: c'.ch.pending ∧ Holds r l ∧ d = r.drawn ∧ Clean c' := by
  obtain ⟨r1, t, _, b1, b2, b3, _, _, b5, b6⟩ :=
    OnBytes.PscRun.close_view name kind nz d c1 c' hd ((Blk.yields_iff _ _ _ _).1 h2)
  have b1' : c1.ch.pending = r1 :: t := b1
  have b4 : c'.ch.pending = t := by rw [pending_clean b5, b6]
  rcases a3 with ⟨e1, e2⟩ | ⟨r, t', gs, e1, e2, e3⟩
  · rw [e2] at b1'
    exact ⟨r1, by rw [b1', b4], by rw [Holds, b2, e1]; rfl, b3, b5⟩
  · rw [e3] at b1'
    obtain ⟨f1, f2⟩ := List.cons.inj b1'
    subst f1 f2
    have hg : gs = [] := b2
    exact ⟨r, by rw [e1, b4], by rw [Holds, e2, hg, List.append_nil], b3, b5⟩

/-- The same where one element is drawn and returned. -/
theorem ate_closeOne {A : List Fmt.RoundView} {l : List E} {name : String} {kind : Fmt.Kind} {nz : Nat}
    {g : E} {c1 c' : Ctx} (hd : c1.ch.dry = false) (a3 : Ate A l c1.ch.pending)
    (h2 : (Blk.closeOne name kind nz).Yields c1 g c') :
    ∃ r : Fmt.RoundView, A = r :: c'.ch.pending ∧ Holds r l ∧ r.drawn.elems = [g.triple] ∧ Clean c' := by
  obtain ⟨d, y, k1, k2, k3⟩ := closeOne_close h2
  obtain ⟨r, a, b, e, f⟩ := ate_close hd a3 k1
  refine ⟨r, a, b, ?_, f⟩
  rw [← e, k2, k3, E.triple_ofTriple]

/-- The rounds hold the pairs, one by one, and draw the elements, one by one. -/
def RoundsHold : List Fmt.RoundView → List (E × E) → List E → Prop
  | [], [], [] => True
  | r :: rs, q :: qs, g :: gs =>
      Holds r [q.1, q.2] ∧ r.drawn.elems = [g.triple] ∧ RoundsHold rs qs gs
  | _, _, _ => False

/-- The running claim behind the rounds. -/
def claimAfter (claim : E) (qs : List (E × E)) (gs : List E) : E :=
  (qs.zip gs).foldl (fun cl x => foldClaimRound cl x.1.1 x.1.2 x.2) claim

theorem claimAfter_cons (claim : E) (q : E × E) (qs : List (E × E)) (g : E) (gs : List E) :
    claimAfter claim (q :: qs) (g :: gs) = claimAfter (foldClaimRound claim q.1 q.2 g) qs gs := by
  unfold claimAfter
  rw [List.zip_cons_cons, List.foldl_cons]

/-- The k rounds of the fold. -/
theorem foldRounds_view : ∀ (k : Nat) (claim : E) (out : List E × E) (c c' : Ctx),
    c.ch.dry = false → (foldRounds k claim).Yields c out c' →
    ∃ (rs : List Fmt.RoundView) (qs : List (E × E)), c.ch.pending = rs ++ c'.ch.pending ∧
      RoundsHold rs qs out.1 ∧ out.1.length = k ∧ out.2 = claimAfter claim qs out.1 ∧
      c'.ch.dry = false ∧ (Clean c → Clean c')
  | 0, claim, out, c, c', hd, h => by
    unfold foldRounds at h
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
    exact ⟨[], [], rfl, trivial, rfl, rfl, hd, id⟩
  | k + 1, claim, out, c, c', hd, h => by
    unfold foldRounds at h
    obtain ⟨c0, x1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨c2, x2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
    obtain ⟨g, x3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
    obtain ⟨rest, x4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a4
    obtain ⟨t1, d1⟩ := recvE_ate hd h1
    obtain ⟨t2, d2⟩ := recvE_ate d1 h2
    obtain ⟨r, e1, e2, e3, e4⟩ := ate_closeOne d2 (t1.trans t2) h3
    obtain ⟨rs, qs, f1, f2, f3, f4, f5, f6⟩ := foldRounds_view k _ rest x3 _ e4.1 h4
    refine ⟨r :: rs, (c0, c2) :: qs, ?_, ⟨e2, e3, f2⟩, ?_, ?_, f5, fun _ => f6 e4⟩
    · rw [e1, f1]
      rfl
    · show (g :: rest.1).length = k + 1
      rw [List.length_cons, f3]
    · show rest.2 = claimAfter claim ((c0, c2) :: qs) (g :: rest.1)
      rw [claimAfter_cons]
      exact f4

/-- THE WHOLE FOLD, its mask sent earlier. -/
theorem foldVerify_view (F : FoldShape) (row : GroupRow) (o : Nat) (out : SingleRows) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (foldVerify F row (some o)).Yields c out c') :
    ∃ (c1 : Ctx) (r₀ : Fmt.RoundView) (rs : List Fmt.RoundView) (sum eps : E) (qs : List (E × E)) (gs : List E),
      foldShapeOk c.st F = true ∧ foldMaskOk c.st F o = true ∧ foldRowOk c1.st F row = true ∧
      (Blk.spendAsMask o).Yields c () c1 ∧ c.ch.pending = r₀ :: (rs ++ c'.ch.pending) ∧
      Holds r₀ [sum] ∧ r₀.drawn.elems = [eps.triple] ∧ RoundsHold rs qs gs ∧
      gs.length = F.layout.k ∧
      out = foldOutput c1.st F row o eps gs (claimAfter (maddE sum eps row.target) qs gs) ∧
      Clean c' := by
  unfold foldVerify at h
  obtain ⟨s1, x1, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨s2, x2, k3, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  -- the first message
  unfold foldStartVerify at k1
  obtain ⟨S0, y0, a0, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨hS0, hy0⟩ := (Blk.yields_statement _ _ _).1 a0
  rw [hS0, hy0] at a1
  obtain ⟨_, y1, a2, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨hShape, hy1⟩ := (Blk.yields_must _ _ _).1 a2
  rw [hy1] at a3
  obtain ⟨o', y2, a4, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨ho', hy2⟩ := (Blk.yields_pure _ _ _ _).1 a4
  rw [ho', hy2] at a5
  obtain ⟨S1, y3, a6, a7⟩ := (Blk.yields_bind _ _ _ _ _).1 a5
  obtain ⟨hS1, hy3⟩ := (Blk.yields_statement _ _ _).1 a6
  rw [hS1, hy3] at a7
  obtain ⟨_, y4, a8, a9⟩ := (Blk.yields_bind _ _ _ _ _).1 a7
  obtain ⟨hMask, hy4⟩ := (Blk.yields_must _ _ _).1 a8
  rw [hy4] at a9
  obtain ⟨_, c1, a10, a11⟩ := (Blk.yields_bind _ _ _ _ _).1 a9
  obtain ⟨sum, y6, a12, a13⟩ := (Blk.yields_bind _ _ _ _ _).1 a11
  obtain ⟨hs1, hy6⟩ := (Blk.yields_pure _ _ _ _).1 a13
  rw [hy6] at k3
  have hc1 := Blk.spendAsMask_inv o c c1 a10
  have p1 : c1.ch = c.ch := by rw [hc1]
  have d1 : c1.ch.dry = false := by rw [p1]; exact hd
  obtain ⟨t1, d2⟩ := recvE_ate d1 a12
  rw [p1] at t1
  have st6 : y6.st = c1.st := by
    obtain ⟨_, _, _, _, _, _, e4⟩ := Blk.recvE_inv sum c1 y6 d1 a12
    exact e4.st
  -- eps
  unfold foldEpsilon at k3
  obtain ⟨_, z1, b1, b2⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨-, hz1⟩ := (Blk.yields_must _ _ _).1 b1
  rw [hz1] at b2
  obtain ⟨eps, z2, b3, b4⟩ := (Blk.yields_bind _ _ _ _ _).1 b2
  obtain ⟨hs2, hz2⟩ := (Blk.yields_pure _ _ _ _).1 b4
  rw [hz2] at k4
  obtain ⟨r₀, e1, e2, e3, e4⟩ := ate_closeOne d2 t1 b3
  have st2 : z2.st = y6.st := by
    obtain ⟨d, _, q1, _, _⟩ := closeOne_close b3
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, q2, _⟩ := Blk.close_inv _ _ _ _ _ _ d2
        q1
    exact q2
  -- the rounds
  unfold foldRoundsVerify at k4
  obtain ⟨eps', w1, g1, g2⟩ := (Blk.yields_bind _ _ _ _ _).1 k4
  obtain ⟨he, hw1⟩ := (Blk.yields_get _ _ _ _).1 g1
  rw [hw1] at g2
  obtain ⟨_, w2, g3, g4⟩ := (Blk.yields_bind _ _ _ _ _).1 g2
  obtain ⟨-, hw2⟩ := (Blk.yields_must _ _ _).1 g3
  rw [hw2] at g4
  obtain ⟨S2, w3, g5, g6⟩ := (Blk.yields_bind _ _ _ _ _).1 g4
  obtain ⟨hS2, hw3⟩ := (Blk.yields_statement _ _ _).1 g5
  rw [hw3] at g6
  obtain ⟨_, w4, g7, g8⟩ := (Blk.yields_bind _ _ _ _ _).1 g6
  obtain ⟨hRow, hw4⟩ := (Blk.yields_testOnView _ _ _ e4.1).1 g7
  rw [hw4] at g8
  obtain ⟨r, w5, g9, g10⟩ := (Blk.yields_bind _ _ _ _ _).1 g8
  obtain ⟨hout, hw5⟩ := (Blk.yields_pure _ _ _ _).1 g10
  rw [← hw5] at g9
  obtain ⟨rs, qs, f1, f2, f3, f4, -, f6⟩ := foldRounds_view _ _ r _ _ e4.1 g9
  rw [hs2] at he hout f4
  rw [hs1] at hout f4
  have he' : eps = eps' := Option.some.inj he
  have hRow' : foldRowOk c1.st F row = true := by
    rw [hS2, st2, st6] at hRow
    exact hRow
  refine ⟨c1, r₀, rs, sum, eps, qs, r.1, hShape, hMask, hRow', a10, by rw [e1, f1], e2, e3, f2, f3,
    ?_, f6 e4⟩
  rw [hout, hS2, st2, st6, f4, ← he']

/-- The batching: one round; no message is open behind it. -/
theorem batVerify_view (g : Nat) (row : GroupRow) (lay : GroupLayout) (c c' : Ctx)
    (hd : c.ch.dry = false) (h : (batVerify g).Yields c (row, lay) c') :
    ∃ (r : Fmt.RoundView) (x : E), c.ch.pending = r :: c'.ch.pending ∧ r.vals = [] ∧
      r.drawn.elems = [x.triple] ∧ Clean c' := by
  unfold batVerify at h
  obtain ⟨input, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, _, _, _, _, _, _, e1⟩ := beginRun_inv _ _ _ _ h1
  obtain ⟨x, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  have p1 : c1.ch = c.ch := by rw [e1]
  have hd1 : c1.ch.dry = false := by rw [p1]; exact hd
  obtain ⟨r, k1, k2, k3, k4⟩ := ate_closeOne hd1 (Ate.nil c1.ch.pending) h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨_, _, _, e3⟩ := requireRows_inv _ _ _ k4.1 h3
  obtain ⟨S, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨_, e4⟩ := (Blk.yields_statement _ _ _).1 h4
  have hd4 : c4.ch.dry = false := by rw [e4, e3]; exact k4.1
  obtain ⟨row', c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  obtain ⟨_, e5⟩ := (Blk.yields_getOnView _ _ _ _ _ hd4).1 h5
  obtain ⟨_, e6⟩ := (Blk.yields_pure _ _ _ _).1 a5
  have ec : c' = { c2 with ch := { c2.ch with askedRows := true } } := by rw [e6, e5, e4, e3]
  have pc : c'.ch.pending = c2.ch.pending := by rw [ec]; rfl
  refine ⟨r, x, ?_, k2, k3, ?_⟩
  · rw [← p1, k1, pc]
  · rw [ec]
    exact ⟨k4.1, k4.2⟩

end OnBytes.Tie.Pv.Fold

#print axioms OnBytes.Tie.Pv.Fold.foldRounds_view
#print axioms OnBytes.Tie.Pv.Fold.foldVerify_view
#print axioms OnBytes.Tie.Pv.Fold.batVerify_view
