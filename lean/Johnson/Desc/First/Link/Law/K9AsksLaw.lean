--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/K9AsksLaw.lean: WHAT AN ACCEPT OF THE CANDIDATE ROW `k9Entry`
(Johnson/Desc/First/Link/K9Asks.lean) GIVES, EACH PREMISE IN ITS SPENDER's OWN TYPE; AND WHAT A
REJECTION REJECTS. Theorems. A law file: no running text imports it.
THE TIES. The running file writes each test anew. Here each is tied to the text that it repeats:
  BY rfl (the text is copied to the letter): `lookOf_eq`, `looksOf_eq`, `oneRow_eq`, `unitAt_eq`,
  `tableAt_eq`, `sortsB_eq`, `fitsB_eq`, `allPieces_eq`.
  BY A THEOREM (the law side has a sentence, or "decide" of one): `hasRow_iff`, `noTwice_iff`,
  `apartL_iff`.
WHAT EACH CONJUNCT GIVES, AND WHO SPENDS IT.
  `sorts_gives`, `names_gives`: the fields `sorts` and `names` of `LinkPlanFits`
  (Law/HtinPaid.lean): for the field `htin`.
  `unit_gives`: the field `units` of `StaticOk` (Law/OkJoin.lean). Its proof is another hand's
  `unit_of_test` (Law/LooksTests.lean), line for line.
  `coef_gives`: `Fo.CoefOK`: the field `coef` of `StaticOk` and of `DigStatic`
  (Law/RestStatic.lean).
  `small_gives`, `ranges_gives`: the fields `small` and `apart` of `DigStatic`.
  `blocks_gives`, `vectors_gives`: the fields `blocks` and `apart` of `StaticOk`.
  `same_gives`: the equation on f9 of `SameDig` (the field `same` of `DigStatic`): as an equation
  of structures, by `forestView_inj` (Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean).
THE FIRST LAW.
  `static_of_seg`: **`StaticOk X.tl X.Fp`, WHOLE, from `segOk X = true`.**
  `k9Entry_gives`: **where the row accepts, at each number below 25 a built segment X stands, with
  `segOk X = true`, `sameB Z.p.X l X = true`, and the other pen's `rowsFitB`, `posPlanB` and
  `nuPosB` at true.**
THE SECOND LAW.
  `k9Entry_no`: **the row rejects just where at a number below 25 no built segment stands, or
  one of `segOk`, `sameB`, `rowsFitB`, `posPlanB`, `nuPosB` rejects the one that stands.**
  `vectors_of_apart`: what the running file's head says of `vectorsB`: behind `sortsB` and `unitB`,
  `vectorsB` rejects nothing that the law's own sentence accepts.
Limits. NOT HERE: the fields `pieces` and `inside` of `DigStatic`, and five of `SameDig`'s six
equations: row 11 asks them of the structure that it tests; that this is the built segment's is
owed. `smallB`'s clause on b is no law's premise. That the row accepts at any public files is no
theorem. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.K9Asks
import Johnson.Desc.First.Link.Law.CoefsFit
import Johnson.Desc.First.Link.Law.OkJoin
import Johnson.Desc.First.Link.Law.OkClauseTests
import Johnson.Desc.First.TailClaims.EquationsSheet
import Johnson.Desc.Ok.PlanWritten.XShapeLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes
import OnBytes.Tie.Pv.Lookup.Digits.PortDat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.LinkJoin (look Look oneRowLook unitLook tableAtB ApartAt StaticOk
  zOf_two)
open OnBytes.Tie.Pv.Tail.Port (uOf)

/-! ## 1 The ties -/

theorem lookOf_eq (X : HTree) : lookOf X = look X := rfl

theorem looksOf_eq (F : Fork) : looksOf F = F.trees.toList.map look := rfl

theorem oneRow_eq (sh : List Look) (t : ℕ) : oneRow sh t = oneRowLook sh t := rfl

theorem unitAt_eq (sh : List Look) (t : ℕ) : unitAt sh t = unitLook sh t := rfl

theorem tableAt_eq (sh : List Look) (tl : HTailF2) (t : ℕ) : tableAt sh tl t = tableAtB sh tl t :=
  rfl

theorem sortsB_eq (sh : List Look) (tl : HTailF2) : sortsB sh tl = LinkJoin.sortsB sh tl := rfl

theorem fitsB_eq (tl : HTailF2) : fitsB tl = First.TailClaims.Law.fitsB tl := rfl

theorem allPieces_eq (tl : HTailF2) : allPieces tl = Fo.allPieces tl := rfl

theorem hasRow_iff (F : Fork) (t e : ℕ) : hasRow F t e = true ↔ Fo.HasRow F t e := by
  unfold hasRow Fo.HasRow
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

theorem noTwice_iff : ∀ l : List (ℕ × ℕ), noTwice l = true ↔ l.Nodup
  | [] => by simp [noTwice]
  | a :: l => by
    rw [noTwice, Bool.and_eq_true, noTwice_iff l, List.nodup_cons]
    simp

theorem apartL_iff : ∀ l : List Piece, apartL l = true ↔
    l.Pairwise fun p p' => p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off
  | [] => by simp [apartL]
  | p :: l => by
    rw [apartL, Bool.and_eq_true, apartL_iff l, List.pairwise_cons]
    unfold apartFrom
    simp

/-! ## 2 What each conjunct gives -/

theorem sorts_gives {X : Stages.LinkH} (h : sortsB (looksOf X.Fp) X.tl = true) :
    LinkJoin.sortsB (X.Fp.trees.toList.map look) X.tl = true := h

theorem names_gives {X : Stages.LinkH} (h : namesB X = true) :
    X.Fp.trees.size ≤ X.arrayOf.size := of_decide_eq_true h

theorem unit_gives {sh : List Look} {tl : HTailF2} (h : unitB sh tl = true) (Fn : HFun) :
    unitLook sh (uOf tl Fn) = true := by
  unfold unitB at h
  obtain ⟨h0, hU⟩ := (Bool.and_eq_true _ _).mp h
  unfold uOf
  cases e : tl.ix.U.getD Fn.tree none with
  | none => exact h0
  | some t =>
    have hm : some t ∈ tl.ix.U.toList := by
      rw [Array.getD_eq_getD_getElem?] at e
      cases e' : tl.ix.U[Fn.tree]? with
      | none => rw [e'] at e; exact nomatch e
      | some y =>
        rw [e'] at e
        have ey : y = some t := e
        rw [ey] at e'
        exact Array.mem_toList_iff.2 (Array.mem_of_getElem? e')
    exact List.all_eq_true.1 hU _ hm

theorem coef_gives {tl : HTailF2} {F : Fork} (h : coefB tl F = true) : Fo.CoefOK tl F := by
  unfold coefB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h
  refine ⟨⟨(hasRow_iff _ _ _).1 a0, (hasRow_iff _ _ _).1 a1, (hasRow_iff _ _ _).1 a2⟩,
    eq_of_beq a3, fun mu hmu => ?_, (noTwice_iff _).1 a5, fun a ha => ?_⟩
  · exact ne_of_apply_ne id (by simpa using List.all_eq_true.1 a4 mu (List.mem_range.2 hmu))
  · have k := List.all_eq_true.1 a6 a ha
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range] at k
    obtain ⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩ := k
    refine ⟨(hasRow_iff _ _ _).1 k0, fun c => ?_, fun c => ?_, k3, fun mu hmu c => ?_⟩
    · rcases k1 with x | x
      · exact x c.1
      · exact x c.2
    · rcases k2 with x | x
      · exact x c.1
      · exact x c.2
    · rcases k4 mu hmu with x | x
      · exact x c.1
      · exact x c.2

theorem small_gives {tl : HTailF2} (h : smallB tl = true) :
    ∀ q < 2, (tl.zOf q).call.n ≤ 63 := fun q hq =>
  of_decide_eq_true ((Bool.and_eq_true _ _).mp (List.all_eq_true.1 h q (List.mem_range.2 hq))).1

theorem ranges_gives {tl : HTailF2} (h : rangesB tl = true) :
    ∀ q < 2, (OnBytes.DgP.piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off := fun q hq =>
  (apartL_iff _).1 (List.all_eq_true.1 h q (List.mem_range.2 hq))

theorem blocks_gives {tl : HTailF2} (h : blocksB tl = true) :
    tl.wants.map (·.1) = some tl.zzBlocks := eq_of_beq h

/-- What `tableAt` holds: the law's own sentence, and one clause beside. -/
theorem tableAt_iff (sh : List Look) (tl : HTailF2) (t : ℕ) :
    tableAt sh tl t = true ↔ ApartAt tl t ∧ oneRow sh t = true := by
  unfold tableAt ApartAt
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    beq_iff_eq, ne_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨n0, hn, e0⟩, r⟩, z⟩, b⟩, g⟩, p1⟩, p2⟩
    refine ⟨⟨n0, hn, e0, z, b, g, fun k p hp => ?_⟩, r⟩
    rcases zOf_two tl k with e | e
    · rw [e] at hp
      exact p1 p hp
    · rw [e] at hp
      exact p2 p hp
  · rintro ⟨⟨n0, hn, e0, z, b, g, pp⟩, r⟩
    exact ⟨⟨⟨⟨⟨⟨⟨n0, hn, e0⟩, r⟩, z⟩, b⟩, g⟩, fun p hp => pp 0 p hp⟩, fun p hp => pp 1 p hp⟩

theorem vectors_gives {sh : List Look} {tl : HTailF2} (h : vectorsB sh tl = true) (Fn : HFun)
    (hF : Fn.tree = 0 ∨ Fn.tree = 2) : ApartAt tl (uOf tl Fn) := by
  have k : tableAt sh tl ((tl.ix.U.getD Fn.tree none).getD 0) = true := by
    rcases hF with e | e <;> rw [e] <;> exact List.all_eq_true.1 h _ (by simp)
  exact ((tableAt_iff sh tl _).1 k).1

theorem same_gives {W : Verify.Public} {l : ℕ} {X : Stages.LinkH} (h : sameB W l X = true) :
    ∃ xt, K3Asks.digAt W l = some xt ∧ xt.2.f9 = X.tl.f9 := by
  unfold sameB at h
  cases e : K3Asks.digAt W l with
  | none =>
    rw [e] at h
    cases h
  | some xt =>
    rw [e] at h
    exact ⟨xt, rfl, PlanWritten.forestView_inj (eq_of_beq h)⟩

/-! ## 3 The first law -/

/-- **`StaticOk`, whole.** -/
theorem static_of_seg {X : Stages.LinkH} (h : segOk X = true) : StaticOk X.tl X.Fp := by
  unfold segOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hu⟩, _⟩, hc⟩, _⟩, _⟩, _⟩, hb⟩, hv⟩ := h
  exact ⟨blocks_gives hb, vectors_gives hv, unit_gives hu, coef_gives hc⟩

/-- **Where the row accepts.** -/
theorem k9Entry_gives {Z : ProofFile.Pub} (h : k9Entry Z = true) {l : ℕ} (hl : l < 25) :
    ∃ X, Z.p.built.links[l]? = some X ∧ segOk X = true ∧ sameB Z.p.X l X = true ∧
      rowsFitB (ProofFile.k9Stretches Z) Z l X = true ∧ posPlanB Z.p.X l X = true ∧
      nuPosB Z.p.X X = true := by
  have k := List.all_eq_true.1 h l (List.mem_range.2 hl)
  cases e : Z.p.built.links[l]? with
  | none =>
    rw [e] at k
    cases k
  | some X =>
    rw [e] at k
    simp only [Bool.and_eq_true] at k
    obtain ⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩ := k
    exact ⟨X, rfl, k1, k2, k3, k4, k5⟩

/-! ## 4 The second law -/

/-- **What a rejection rejects.** -/
theorem k9Entry_no (Z : ProofFile.Pub) : k9Entry Z = false ↔
    ∃ l, l < 25 ∧ ∀ X, Z.p.built.links[l]? = some X →
      (segOk X && sameB Z.p.X l X && rowsFitB (ProofFile.k9Stretches Z) Z l X &&
        posPlanB Z.p.X l X && nuPosB Z.p.X X) = false := by
  constructor
  · intro h
    by_contra hc
    have hy : k9Entry Z = true := by
      refine List.all_eq_true.2 fun l hl => ?_
      have hl' : l < 25 := List.mem_range.1 hl
      by_contra hn
      refine hc ⟨l, hl', fun X hX => ?_⟩
      rw [hX] at hn
      exact Bool.eq_false_iff.2 hn
    rw [hy] at h
    cases h
  · rintro ⟨l, hl, hX⟩
    refine Bool.eq_false_iff.2 fun hy => ?_
    obtain ⟨X, e, h1, h2, h3, h4, h5⟩ := k9Entry_gives hy hl
    have := hX X e
    rw [h1, h2, h3, h4, h5] at this
    cases this

/-- **Behind `sortsB` and `unitB`, `vectorsB` rejects nothing that the law's own sentence
accepts.** -/
theorem vectors_of_apart {sh : List Look} {tl : HTailF2} (hs : sortsB sh tl = true)
    (hu : unitB sh tl = true)
    (ha : ∀ n, n = 0 ∨ n = 2 → ApartAt tl ((tl.ix.U.getD n none).getD 0)) :
    vectorsB sh tl = true := by
  refine List.all_eq_true.2 fun n hn => ?_
  have hn' : n = 0 ∨ n = 2 := by simpa using hn
  have A := ha n hn'
  have hU : unitAt sh ((tl.ix.U.getD n none).getD 0) = true :=
    unit_gives hu { tree := n }
  have hlt : (tl.ix.U.getD n none).getD 0 < sh.length := by
    unfold unitAt at hU
    cases e : sh[(tl.ix.U.getD n none).getD 0]? with
    | none =>
      rw [e] at hU
      cases hU
    | some x => exact (List.getElem?_eq_some_iff.1 e).1
  have S := List.all_eq_true.1 hs _ (List.mem_range.2 hlt)
  obtain ⟨_, _, _, z, b, g, _⟩ := A
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at S
  rcases S with ((e | e) | ⟨mu, hmu, e⟩) | e
  · exact absurd e.symm z
  · exact absurd e.symm b
  · exact absurd e (g mu hmu)
  · exact e

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.lookOf_eq
#print axioms VerifiableInference.Desc.K9Asks.looksOf_eq
#print axioms VerifiableInference.Desc.K9Asks.oneRow_eq
#print axioms VerifiableInference.Desc.K9Asks.unitAt_eq
#print axioms VerifiableInference.Desc.K9Asks.tableAt_eq
#print axioms VerifiableInference.Desc.K9Asks.sortsB_eq
#print axioms VerifiableInference.Desc.K9Asks.fitsB_eq
#print axioms VerifiableInference.Desc.K9Asks.allPieces_eq
#print axioms VerifiableInference.Desc.K9Asks.hasRow_iff
#print axioms VerifiableInference.Desc.K9Asks.noTwice_iff
#print axioms VerifiableInference.Desc.K9Asks.apartL_iff
#print axioms VerifiableInference.Desc.K9Asks.sorts_gives
#print axioms VerifiableInference.Desc.K9Asks.names_gives
#print axioms VerifiableInference.Desc.K9Asks.unit_gives
#print axioms VerifiableInference.Desc.K9Asks.coef_gives
#print axioms VerifiableInference.Desc.K9Asks.small_gives
#print axioms VerifiableInference.Desc.K9Asks.ranges_gives
#print axioms VerifiableInference.Desc.K9Asks.blocks_gives
#print axioms VerifiableInference.Desc.K9Asks.tableAt_iff
#print axioms VerifiableInference.Desc.K9Asks.vectors_gives
#print axioms VerifiableInference.Desc.K9Asks.same_gives
#print axioms VerifiableInference.Desc.K9Asks.static_of_seg
#print axioms VerifiableInference.Desc.K9Asks.k9Entry_gives
#print axioms VerifiableInference.Desc.K9Asks.k9Entry_no
#print axioms VerifiableInference.Desc.K9Asks.vectors_of_apart
