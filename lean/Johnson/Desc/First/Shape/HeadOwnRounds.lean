-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/HeadOwnRounds.lean: WHAT A YES OF THE SUB-PROTOCOL "THE OUTPUT HEAD's OWN
ROUNDS" (the kind K6; Kinds.Head.blockAt, Johnson/Stored/HeadSeatAt.lean) LAYS, ON SHAPES. One law
at the bare block's decision; nothing is evaluated.
  `ztOf lt zx`: the number of coordinates of the lookup's point on the positions, of that of the
    whole point.
  **`k6_shapes`**: behind a yes: the state in front stands in the head's link, opened, with what the
    lookup returned laid (g); the state behind is the state in front but for three fields of the
    head's own part: the ledger F1, what was heard X, the squares' level's state Q; X.g1 is g; AND
    WHERE THE HEARING's STEP ON THE LEDGER's SHAPE RETURNS y (headS (ztOf h.lt g.zx.size),
    HearHead.lean): ledSh F1 = y.2, headHeardSh X = headHeardOfSh g.zx.size y.1 (HeardOfShape.lean),
    pscSh Q = pscOfSh y.1.norm.squares.psc false: the three fields' shapes are functions of the
    ledger's shape in front, the head's public sizes and the number of coordinates of the lookup's
    point.
By the library's decideBy_more (Johnson/Desc/Reads/HeardSizes.lean), Came.given_ok
(Johnson/Desc/Kinds/Law/FromGiven.lean), setHeard_form (Law/HeardBack.lean), and HearSh.head,
heardOf_sh, pscOf_sh.
Limits. THE WEAK FORM: under the step's own return (HearFrame.lean). The bare block: the guards of a
seat are not in it. No step on the chain's shape is laid here: HeadOwnStep.lean lays it, by
k6_shapes. "Returns" is another house's law. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.HeardOfShape
import Johnson.Desc.Reads.HeardSizes
import Johnson.Desc.Kinds.Law.FromGiven
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Kinds (Hear Hid Sum Point)
open VerifiableInference.Desc.Kinds.Head (blockAt seatAt sizesOf parOf)

/-- The number of coordinates of the lookup's point on the positions, of that of the whole point. -/
def ztOf (lt zx : Nat) : Nat := min zx zx - (zx - lt)

/-- **WHAT A YES OF THE OUTPUT HEAD's OWN ROUNDS LAYS, ON SHAPES.** The state behind is the state in
front but for three fields of the head's own part; and where the hearing's step on the ledger's
shape returns, it returns the shape of the ledger behind, and the shapes of the two other fields are
functions of its value. -/
theorem k6_shapes (h : Model.Head.Shape) (iU3 work l : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (o : HeadOwn) (g : Forest.Heard) (F1 : Fork) (X : Model.Head.Heard) (Q : Model.Psc),
      s.here = .head o ∧ o.opened = true ∧ o.lookHeard = some g ∧
      s' = { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } ∧
      X.g1 = g ∧
      ∀ y, @headS (sizesOf h) (ztOf h.lt g.zx.size) (ledSh o.F) = some y →
        ledSh F1 = y.2 ∧ headHeardSh X = @headHeardOfSh (sizesOf h) g.zx.size y.1 ∧
        pscSh Q = pscOfSh y.1.norm.squares.psc false := by
  have hd' : Kinds.Head.decideBy (fun _ => Kinds.Head.rounds) (fun _ => Kinds.Head.hear)
      (fun _ _ => Kinds.Head.forTheMerge) (parOf h work) (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨G, H, F1, left, s1, s2, hg, hh, e1, e2, rfl⟩ :=
      VerifiableInference.Reads.AtSeat.decideBy_more hd'
  obtain ⟨z, yt, hz, -, -, rfl⟩ := Kinds.Head.Law.Came.given_ok _ _ _ _ hg
  obtain ⟨o₁, g, ho₁, hlk, rfl⟩ := Kinds.Head.Law.setHeard_form h iU3 e2
  -- the ledger is laid: putFork?
  have e1' : s.putFork? F1 = .ok s1 := e1
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  have hun : s.putFork F1 = s1 := by
    unfold S.putFork? at e1'
    rw [if_pos hsome] at e1'
    exact ((S.unmarked_ok _ _).1 e1').1
  subst hun
  clear hd hd' e1 e1' e2 hg
  cases hs : s.here with
  | head o =>
    cases hop : o.opened with
    | false =>
      exfalso
      simp [S.fork?, hs, hop] at hsome
    | true =>
      have hp : s.putFork F1 = { s with here := .head { o with F := F1 } } := by
        simp only [S.putFork, hs, hop, if_true]
      rw [hp] at ho₁ ⊢
      obtain rfl : ({ o with F := F1 } : HeadOwn) = o₁ := Here.head.inj ho₁
      have hlk' : o.lookHeard = some g := hlk
      have hz' : z = (g.zx, fun c => g.zk.getD c #[]) := by
        have e : (seatAt h iU3).lookup s = some (g.zx, fun c => g.zk.getD c #[]) := by
          show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
          simp only [S.lookHeard?, hs, hop, if_true, hlk', Option.map_some]
        exact Option.some.inj (hz.symm.trans e)
      subst hz'
      have hled : (seatAt h iU3).ledger s = o.F := by
        show s.fork?.getD {} = o.F
        simp [S.fork?, hs, hop]
      rw [hled] at hh
      refine ⟨o, g, F1, _, _, rfl, hop, hlk', rfl, rfl, fun y hy => ?_⟩
      have hzt : (@Kinds.FinalNorm.zt
          (@Kinds.Head.fromLookup (parOf h work).sizes (parOf h work).floor g.zx
            fun c => g.zk.getD c #[]).norm).size = ztOf h.lt g.zx.size := by
        show (Kinds.Point.last g.zx h.lt).size = _
        unfold Kinds.Point.last ztOf
        rw [Array.size_extract]
      rw [← hzt] at hy
      obtain rfl := @HearSh.head (sizesOf h)
        (@Kinds.Head.fromLookup (parOf h work).sizes (parOf h work).floor g.zx
          fun c => g.zk.getD c #[]).norm o.F rs H F1 left y hh hy
      exact ⟨rfl, @heardOf_sh (sizesOf h) (Kinds.Head.requestOf _) ⟨_⟩ g H, pscOf_sh _ false⟩
  | between => simp [S.fork?, hs] at hsome
  | lay a =>
    exfalso
    simp [S.putFork, hs] at ho₁
  | att a =>
    exfalso
    simp [S.putFork, hs] at ho₁
  | fin a => simp [S.fork?, hs] at hsome
  | mem a => simp [S.fork?, hs] at hsome

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.k6_shapes
#print axioms VerifiableInference.Desc.First.Shape.ztOf
