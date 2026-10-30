-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerBases.lean: THEOREMS: THE THREE STATEMENTS OF LedgerBasesOwed.lean: the
bases of the shared row's pieces number 3 and 6, at every plan, with nothing evaluated.
  treesAlong      written rounds along declared rounds, as many as these, send the declared roots'
                  trees: round by round (RoundIs' last clause).
  entries_roots   no entry of the kind's own rounds declares a root (Round.entry sets none; the
                  format's Entry has roots := 0 where none is set).
  roots_plain     so a block whose declared rounds are made of these entries declares none.
  roots_send      a sending at parK1 Q piece part sent declares as many roots as the layout of sent
                  has trees (K1's seedEntry; treesMade_eq where Par.trees reads treesMade; nothing
                  where it reads layTrees outright: the proof tries both).
  roots           the second statement: block by block.
  bases           the third: along Tiled's equations.
What is not claimed. That a row is tiled or goes along the blocks: the caller's. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerBasesOwed
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

theorem treesAlong : TreesAlongOwed := by
  intro num rs
  induction rs with
  | nil =>
    intro ds _ hl
    cases ds with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons r rs ih =>
    intro ds h hl
    cases ds with
    | nil => simp at hl
    | cons d ds =>
      have h' : RoundIs num r d ∧ Along (RoundIs num) rs ds := h
      have hl' : ds.length = rs.length := by simpa using hl
      rw [nTrees_cons, ih ds h'.2 hl']
      unfold rootsOf
      rw [List.map_cons, List.sum_cons, h'.1.2.2.2.2.2]

/-- No entry of the kind's own rounds declares a root. -/
theorem entries_roots (Q : P14) : ∀ e ∈ entries Q, e.roots = 0 := by
  intro e he
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 he
  rfl

theorem roots_plain (Q : P14) (a k : ℕ) (f : Fmt.Entry → Fmt.DeclaredRound)
    (hf : ∀ e, (f e).entry = e) : rootsOf ((((entries Q).drop a).take k).map f) = 0 := by
  unfold rootsOf
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  rw [hf e]
  exact entries_roots Q e (List.mem_of_mem_drop (List.mem_of_mem_take he))

theorem roots_send (Q : P14) (piece : ℕ) (part : String) (sent : Array OracleNotice)
    (lay : TreeLay) (hl : layTrees Q.codes sent = some lay) :
    rootsOf (VerifiableInference.Desc.K1.rounds (parK1 Q piece part sent)) = lay.shapes.size := by
  have hs : (parK1 Q piece part sent).sent = sent := by
    simp [VerifiableInference.Desc.K1.Par.sent, parK1]
  have ht : (parK1 Q piece part sent).trees = lay.shapes.toList := by
    unfold VerifiableInference.Desc.K1.Par.trees
    first
      | rw [VerifiableInference.Desc.Own.treesMade_eq, hs]
      | rw [hs]
    show ((layTrees Q.codes sent).map (·.shapes.toList)).getD [] = _
    rw [hl]
    rfl
  show ((parK1 Q piece part sent).trees.length + (0 + 0) : ℕ) = _
  rw [ht, Array.length_toList]
  rfl

theorem roots : RootsOwed := by
  intro Q b1 b2 b3 b4 b5 b6 b7 b8 sentU layU layO hb hU hlU hlO
  unfold blocks at hb
  rw [hU] at hb
  have hb2 := Option.some.inj hb
  simp only [List.cons.injEq, and_true] at hb2
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb2
  refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
    (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
      (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)))))))
  all_goals try dsimp only
  · refine roots_plain Q 0 1 _ ?_
    intro _
    rfl
  · exact roots_send Q 2 _ sentU layU hlU
  · refine roots_plain Q 0 0 _ ?_
    intro _
    rfl
  · refine roots_plain Q 1 1 _ ?_
    intro _
    rfl
  · exact roots_send Q 5 _ (withOmega Q.S) layO hlO
  · refine roots_plain Q 0 0 _ ?_
    intro _
    rfl
  · refine roots_plain Q 2 1 _ ?_
    intro _
    rfl
  · refine roots_plain Q 3 _ _ ?_
    intro _
    rfl

theorem bases : BasesOwed := by
  intro Q b1 b2 b3 b4 b5 b6 b7 b8 sentU layU layO hb hU hlU hlO C Fr S Cl W num f pt x2 x3 x4 x5
    x6 rest hT hf hA
  have R := roots Q b1 b2 b3 b4 b5 b6 b7 b8 sentU layU layO hb hU hlU hlO
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at R
  obtain ⟨r1, r2, r3, r4, r5, -, -, -⟩ := R
  have t : ∀ y ∈ [(pt, b1), (x2, b2), (x3, b3), (x4, b4), (x5, b5)],
      y.1.trees = rootsOf y.2.rounds := fun y hy => treesAlong num _ _ (hA y hy).1 (hA y hy).2
  have t1 := t (pt, b1) (by simp)
  have t2 := t (x2, b2) (by simp)
  have t3 := t (x3, b3) (by simp)
  have t4 := t (x4, b4) (by simp)
  have t5 := t (x5, b5) (by simp)
  have f0 : f.trees = 0 := by
    unfold Piece.trees
    rw [hf]
    rfl
  obtain ⟨-, -, -, e0, -, -, -, e1, -, -, -, e2, -, -, -, e3, -, -, -, e4, -, -, -, e5, -⟩ := hT
  dsimp only at t1 t2 t3 t4 t5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Desc.K14.Law

#print axioms Desc.K14.Law.treesAlong
#print axioms Desc.K14.Law.roots
#print axioms Desc.K14.Law.bases
