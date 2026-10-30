-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkFold.lean: what a run of the program's fold reads of a written transcript, in the
field.

The program's verifier of a fold (OnBytes/Iop/Fold.lean: `foldVerify`) takes the rounds of a view
one after the other, keeps a running claim and returns a new statement.
OnBytes/Slice/FoldPeel.lean gives the claim after a fold of the written protocol in the field: the
running claim `claimF` and the drawn point `ptF`, as functions of the written rounds. This file says
that a run of the program on the view of these rounds computes the same two.

`foldRounds_sem`. Let the rounds that are left for the run to take begin with the view of k written
rounds. If the program's k rounds succeed, the claim that they return is read as `claimF`, the
elements that they return are the point `ptF`, and the run has taken exactly these k rounds.
`foldVerify_sem`. The same for the whole block, where the fresh mask came in an earlier message:
the statement that it returns is `foldOutput` at a coefficient, elements and a claim with these
readings.

Main theorems: `readE_foldClaimRound`, `foldRounds_sem`, `foldVerify_sem`.
Not claimed. Nothing on the vectors of coefficients in the new statement. Nothing on the dry run.
Nothing on soundness.
-/
import OnBytes.Iop.Fold
import OnBytes.Slice.BlkRun
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.ProgField

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run

/-- One round of the program's running claim, in the field: the value at the drawn element of the
round polynomial that the message describes. -/
theorem readE_foldClaimRound (claim c0 c2 g : E) :
    readE (foldClaimRound claim c0 c2 g) =
      hev (hFill (HVar.plain GE 2) ((1 : Fin 3), (1 : GE)) (readE claim)
        (fun t : Fin 2 => if t.val = 0 then readE c0 else readE c2)) (readE g) := by
  have h := (toE_nextClaim_hev claim.triple (c0.triple, c2.triple) g.triple).symm.trans
    (toE_nextClaim claim.triple (c0.triple, c2.triple) g.triple)
  rw [readE_def claim, readE_def c0, readE_def c2, readE_def g, h]
  unfold foldClaimRound
  rw [readE_add, readE_mul, readE_add, readE_mul, readE_sub, readE_sub, readE_add,
    readE_def claim, readE_def c0, readE_def c2, readE_def g]
  ring

/-- The program's k rounds of a fold on the view of k written rounds: the claim and the elements
that they return are read as the running claim and the drawn point of the written rounds, and the
run has taken exactly these rounds. -/
theorem foldRounds_sem (dT : PQ.RD) : ∀ (k : ℕ) (claim : E)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate k dT))) (rest : List Fmt.RoundView) (c c' : Ctx)
    (gs : List E) (cl : E), c.ch.dry = false →
    c.ch.pending = PQ.rvSL (ckP .two) (List.replicate k dT) τ ++ rest →
    (foldRounds k claim).Yields c (gs, cl) c' →
    readE cl = claimF dT k (readE claim) τ ∧ readP k gs = ptF dT k τ ∧ gs.length = k ∧
      RanRounds k rest c c'
  | 0, claim, τ, rest, c, c', gs, cl, hd, hp, h => by
      obtain ⟨h1, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h
      cases h1
      exact ⟨rfl, funext fun i => i.elim0, rfl, ⟨hp, hd, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | k + 1, claim, (m, ch, τ), rest, c, c', gs, cl, hd, hp, h => by
      have h0 : (Blk.recvE >>= fun c0 => Blk.recvE >>= fun c2 =>
          Blk.closeOne "FOLD round" >>= fun g =>
          foldRounds k (foldClaimRound claim c0 c2 g) >>= fun r =>
          (pure (g :: r.1, r.2) : Blk (List E × E))).Yields c (gs, cl) c' := h
      obtain ⟨c0, x1, h1, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
      obtain ⟨c2, x2, h2, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
      obtain ⟨g, x3, h3, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
      obtain ⟨⟨gs', cl'⟩, x4, h4, h0⟩ := (Blk.yields_bind _ _ _ _ _).1 h0
      obtain ⟨h5, rfl⟩ := (Blk.yields_pure _ _ _ _).1 h0
      cases h5
      -- the round's two items and what it drew
      have hp' : c.ch.pending =
          ⟨PQ.PlainOf.gots dT.items (GPlain.old (b := dT.entry.work) m.2),
            (ckP .two).dr dT.entry dT.kind (GChal.old (b := dT.entry.work) ch)⟩ ::
            (PQ.rvSL (ckP .two) (List.replicate k dT) τ ++ rest) := hp
      obtain ⟨r1, t1, v1, a1, a2, a3, s1⟩ := Blk.recvE_inv c0 c x1 hd h1
      rw [hp'] at a1
      obtain ⟨rfl, rfl⟩ := List.cons.inj a1
      have hd1 : x1.ch.dry = false := s1.dry.trans hd
      obtain ⟨r2, t2, v2, b1, b2, b3, s2⟩ := Blk.recvE_inv c2 x1 x2 hd1 h2
      rw [a3] at b1
      obtain ⟨rfl, rfl⟩ := List.cons.inj b1
      have hd2 : x2.ch.dry = false := s2.dry.trans hd1
      obtain ⟨d, h3', hel⟩ := Blk.closeOne_inv _ _ _ g x2 x3 h3
      obtain ⟨e, es, r3, t3, e1, _, _, e4, e5, e6, _, _, _, e10, e11, _, e13, e14, e15, e16, e17,
    e18, e19, e20⟩ :=
        Blk.close_inv _ _ _ d x2 x3 hd2 h3'
      rw [b3] at e4
      obtain ⟨rfl, rfl⟩ := List.cons.inj e4
      have hv2 : v2 = [] := e5
      have hv1 : v1 = [.e c2.triple] := by
        have : v1 = .e c2.triple :: v2 := b2
        rw [this, hv2]
      have hgots : PQ.PlainOf.gots dT.items (GPlain.old (b := dT.entry.work) m.2) =
          [.e c0.triple, .e c2.triple] := by
        have : PQ.PlainOf.gots dT.items (GPlain.old (b := dT.entry.work) m.2) =
            .e c0.triple :: v1 := a2
        rw [this, hv1]
      have hs0 : sentAt dT m 0 = readE c0 := by
        unfold sentAt ansOf
        rw [hgots]
        rfl
      have hs1 : sentAt dT m 1 = readE c2 := by
        unfold sentAt ansOf
        rw [hgots]
        rfl
      have hg : gOne _ (valsOf dT ch) = readE g :=
        (gOne_of_els dT m ch (by rw [e6] at hel; exact hel)).trans (readE_def g).symm
      -- the other rounds
      obtain ⟨i1, i2, i3, i4⟩ := foldRounds_sem dT k _ τ rest x3 _ gs' cl' e16 e10 h4
      refine ⟨?_, ?_, congrArg (· + 1) i3, ?_⟩
      · rw [i1, readE_foldClaimRound, ← hs0, ← hs1, ← hg]
        rfl
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hg.symm
        · exact congrFun i2 j
      · refine ⟨i4.pending, i4.dry, i4.st.trans (e13.trans (s2.st.trans s1.st)),
          i4.book.trans (e14.trans (s2.book.trans s1.book)),
          i4.failed.trans (e15.trans (s2.failed.trans s1.failed)),
          i4.opened.trans (e17.trans (s2.opened.trans s1.opened)), ?_,
          i4.roots.trans (e18.trans (s2.roots.trans s1.roots)),
          i4.firstTree.trans (e19.trans (s2.firstTree.trans s1.firstTree)),
          i4.samples.trans (e20.trans (s2.samples.trans s1.samples))⟩
        have hen : c.ch.entries = e :: es := (s1.entries.symm.trans s2.entries.symm).trans e1
        rw [i4.entries, e11, hen]
        rfl

/-- The program's fold on the view of the written rounds of a fold, where the fresh mask came in
an earlier message. The run marks the mask as spent (c1), takes the fold's rounds and nothing else,
and returns `foldOutput` at a coefficient, elements and a claim that are read as the drawn
coefficient, the drawn point and the running claim of the written rounds. The program's three tests
`foldShapeOk`, `foldMaskOk` and `foldRowOk` were true. -/
theorem foldVerify_sem (F : FoldShape) (row : GroupRow) (o : ℕ) (dE dT : PQ.RD)
    (m : (wRound dE).Msg) (ch : (wRound dE).Chal)
    (τ : Tr (PQ.uL (ckP .two) (List.replicate F.layout.k dT))) (rest : List Fmt.RoundView)
    (c c' : Ctx) (out : SingleRows) (hd : c.ch.dry = false)
    (hp : c.ch.pending =
      PQ.rvSL (ckP .two) (dE :: List.replicate F.layout.k dT) (m, ch, τ) ++ rest)
    (h : (foldVerify F row (some o)).Yields c out c') :
    ∃ (c1 : Ctx) (eps claim : E) (gamma : List E),
      (Blk.spendAsMask o).Yields c () c1 ∧ foldShapeOk c.st F = true ∧
      foldMaskOk c.st F o = true ∧ foldRowOk c1.st F row = true ∧
      out = foldOutput c1.st F row o eps gamma claim ∧
      readE eps = gOne _ (valsOf dE ch) ∧ readP F.layout.k gamma = ptF dT F.layout.k τ ∧
      gamma.length = F.layout.k ∧
      readE claim = claimF dT F.layout.k
        (sentAt dE m 0 + readE row.target * gOne _ (valsOf dE ch)) τ ∧
      RanRounds (F.layout.k + 1) rest c1 c' := by
  unfold foldVerify at h
  obtain ⟨s1, x1, k1, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨s2, x2, k3, k4⟩ := (Blk.yields_bind _ _ _ _ _).1 k2
  -- the first message: two public conditions, the mark on the mask, the sum
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
  obtain ⟨sum, y5, a12, a13⟩ := (Blk.yields_bind _ _ _ _ _).1 a11
  obtain ⟨hs1, hy5⟩ := (Blk.yields_pure _ _ _ _).1 a13
  rw [← hy5] at a12
  rw [hs1] at k3
  have hc1 := Blk.spendAsMask_inv o c c1 a10
  have hch : c1.ch = c.ch := by rw [hc1]
  have hd1 : c1.ch.dry = false := by rw [hch]; exact hd
  have hp1 : c1.ch.pending =
      ⟨PQ.PlainOf.gots dE.items (GPlain.old (b := dE.entry.work) m.2),
        (ckP .two).dr dE.entry dE.kind (GChal.old (b := dE.entry.work) ch)⟩ ::
        (PQ.rvSL (ckP .two) (List.replicate F.layout.k dT) τ ++ rest) := by
    rw [hch]
    exact hp
  obtain ⟨r1, t1, v1, b1, b2, b3, sb⟩ := Blk.recvE_inv sum c1 x1 hd1 a12
  rw [hp1] at b1
  obtain ⟨rfl, rfl⟩ := List.cons.inj b1
  -- the coefficient
  unfold foldEpsilon at k3
  obtain ⟨_, z1, d1, d2⟩ := (Blk.yields_bind _ _ _ _ _).1 k3
  obtain ⟨_, hz1⟩ := (Blk.yields_must _ _ _).1 d1
  rw [hz1] at d2
  obtain ⟨eps, z2, d3, d4⟩ := (Blk.yields_bind _ _ _ _ _).1 d2
  obtain ⟨hs2, hz2⟩ := (Blk.yields_pure _ _ _ _).1 d4
  rw [← hz2] at d3
  rw [hs2] at k4
  obtain ⟨d, d5, hel⟩ := Blk.closeOne_inv _ _ _ eps x1 x2 d3
  obtain ⟨e, es, r3, t3, e1, _, _, e4, e5, e6, _, _, _, e10, e11, _, e13, e14, e15, e16, e17,
    e18, e19, e20⟩ :=
    Blk.close_inv _ _ _ d x1 x2 (sb.dry.trans hd1) d5
  rw [b3] at e4
  obtain ⟨rfl, rfl⟩ := List.cons.inj e4
  have hgots : PQ.PlainOf.gots dE.items (GPlain.old (b := dE.entry.work) m.2) =
      [.e sum.triple] := by
    have h1 : PQ.PlainOf.gots dE.items (GPlain.old (b := dE.entry.work) m.2) =
        .e sum.triple :: v1 := b2
    have h2 : v1 = [] := e5
    rw [h1, h2]
  have hs0 : sentAt dE m 0 = readE sum := by
    unfold sentAt ansOf
    rw [hgots]
    rfl
  have hg : gOne _ (valsOf dE ch) = readE eps :=
    (gOne_of_els dE m ch (by rw [e6] at hel; exact hel)).trans (readE_def eps).symm
  -- the rounds
  unfold foldRoundsVerify at k4
  obtain ⟨eps', w1, f1, f2⟩ := (Blk.yields_bind _ _ _ _ _).1 k4
  obtain ⟨f0, hw1⟩ := (Blk.yields_get _ _ _ _).1 f1
  have heps : eps' = eps := (Option.some.inj f0).symm
  rw [heps, hw1] at f2
  obtain ⟨_, w2, f3, f4⟩ := (Blk.yields_bind _ _ _ _ _).1 f2
  obtain ⟨_, hw2⟩ := (Blk.yields_must _ _ _).1 f3
  rw [hw2] at f4
  obtain ⟨S, w3, f5, f6⟩ := (Blk.yields_bind _ _ _ _ _).1 f4
  obtain ⟨hS, hw3⟩ := (Blk.yields_statement _ _ _).1 f5
  rw [hS, hw3] at f6
  obtain ⟨_, w4, f7, f8⟩ := (Blk.yields_bind _ _ _ _ _).1 f6
  obtain ⟨hRow, hw4⟩ := (Blk.yields_testOnView _ _ _ e16).1 f7
  rw [hw4] at f8
  obtain ⟨⟨gs, cl⟩, w5, f9, f10⟩ := (Blk.yields_bind _ _ _ _ _).1 f8
  obtain ⟨hout, hw5⟩ := (Blk.yields_pure _ _ _ _).1 f10
  rw [← hw5] at f9
  obtain ⟨i1, i2, i3, i4⟩ := foldRounds_sem dT _ _ τ rest x2 c' gs cl e16 e10 f9
  have hst : x2.st = c1.st := e13.trans sb.st
  rw [hst] at hRow hout
  refine ⟨c1, eps, cl, gs, a10, hShape, hMask, hRow, hout, hg.symm, i2, i3, ?_, ?_⟩
  · rw [i1, readE_maddE, hs0, hg, mul_comm (readE eps)]
  · refine ⟨i4.pending, i4.dry, i4.st.trans hst, i4.book.trans (e14.trans sb.book),
      i4.failed.trans (e15.trans sb.failed), i4.opened.trans (e17.trans sb.opened), ?_,
      i4.roots.trans (e18.trans sb.roots), i4.firstTree.trans (e19.trans sb.firstTree),
      i4.samples.trans (e20.trans sb.samples)⟩
    have hen : c1.ch.entries = e :: es := sb.entries.symm.trans e1
    rw [i4.entries, e11, hen]
    rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.readE_foldClaimRound
#print axioms OnBytes.Slice.foldRounds_sem
#print axioms OnBytes.Slice.foldVerify_sem
