-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/LinksInScope.lean: THE 25 LINKS' KINDS, NAMES, FLAGS AND GROUPS AS WRITTEN
LISTS, IN THE GOALS' SCOPE.

Two rows of the proof file's first chain's lots ask a written list of the 25 links as a hypothesis:
the smallness test's lot (kind and name of each link of the ground's list) and the frames' lot
(kind, the flag fv and the group of each link of the public part's built structure). Both lists are
proved here from the goals' scope, the reader, and the return of the public part (the first also
from the return of the ground): NO OPENING OF THE DESCRIPTION AND NO TEST AT THE ENTRY IS ASKED.

  zipped_is          a member of the list that is run IS a built link but for its routine: the whole
      equation (IM.zipped_kind, Johnson/IMR/Subs.lean, gives the kind; P1K2.zipped_back,
      Johnson/P1K2R/BuiltLinkAt.lean, kind · g · ns · Fp: neither the flag fv)
  list_of_25         a list of 25 from its entries
  kindsW_at · kindsW_len · viewsW_at · viewsW_len   closed facts on the two written lists
  kindsW_not · viewsW_not   two negative tests ON THE WRITTEN LISTS ALONE (they name no end): with
      each pair's two members swapped, or its two flags, it is another list
  **kinds_in_scope** (hS hR hZ hG)   G.built.toList.map (kind, name) = the written list: from the
      theorems IM.ground_gets and IM.ground_named (Johnson/IMR/PureJoin.lean)
  built_public       what the public part's built structure was made of: as in IM.ground_public's
      own proof, without the ground
  **views_in_scope** (hS hR hZ)   Z.p.built.links.toList.map (kind, fv, group; 0 at the head's) =
      the written list: from Meaning.scope_plans | links_alternate | links_named | built_at
      (Johnson/Goal/Meaning/PlanShapes.lean | PlanNames.lean), at one list of links for both, and
      Reads.AtSeat.public_older (Johnson/Desc/Reads/RunIsAtSecondHashFunction.lean)

The right sides are written out, as the terms to which P1K8L.k8KindsW and P1L20.Row.viewW unfold
(Johnson/AtFull/Desc/Lots/K8Row.lean | FramesRow.lean, which this file does not import); so is the
function in the second, as the term to which P1L20.Row.viewL unfolds. (That Lean closes these two
hypotheses at their own constants by the two ends: held by a loose trial file, in no tree.)

THE PREMISES, BY NAME: hS: the three public files are in the goals' scope · hR: they are read (it
follows from hS: IM.reads_of_scope; kept, since the laws in scope that are called ask it) · hZ: the
public part returns, at OnBytes.secondHashFunction; lay is a free letter, as in the laws called · hG: the ground
returns.
What is not claimed. That hS, hZ or hG can be met: no example is shown here. THE TWO ENDS MOVE A
DEBT TO THESE PREMISES: NOTHING IS PAID BY LEAN's KERNEL. Nothing on the links' other fields.
Nothing on soundness, completeness or hiding.

-/
import Johnson.IMR.PureJoin
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.PlanNames
import Johnson.Desc.Reads.RunIsAtSecondHashFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.LinksScope
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH LinksH SubPlanH listLinksH buildLinksH)
open OnBytes.L5.LinksOrder (zipped)

/-- **A member of the list that is run is a built link, but for its routine.** -/
theorem zipped_is {B : LinksH} {ls : Array LinkH} {k : ℕ} {l : LinkH}
    (h : (zipped B ls)[k]? = some l) :
    ∃ b y, B.links[k]? = some b ∧ ls[k]? = some y ∧ l = { b with run := y.run } := by
  unfold zipped at h
  rw [Array.getElem?_zipWith] at h
  cases hb : B.links[k]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases hl : ls[k]? with
    | none => rw [hl] at h; cases h
    | some y =>
      rw [hl] at h
      exact ⟨b, y, rfl, rfl, (Option.some.inj h).symm⟩

/-- A list of 25 from its entries. -/
theorem list_of_25 {α β : Type} (a : Array α) (f : α → β) (w : List β) (hs : a.size = 25)
    (hw : w.length = 25) (h : ∀ i < 25, ∃ x, a[i]? = some x ∧ w[i]? = some (f x)) :
    a.toList.map f = w := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, Array.getElem?_toList]
  by_cases hi : i < 25
  · obtain ⟨x, e, e'⟩ := h i hi
    rw [e, e']
    rfl
  · rw [Array.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rfl

/-! ## The two written lists: closed facts -/

theorem kindsW_len :
    (((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++
      [(2, "H")] : List (ℕ × String)).length = 25 := by decide +kernel

theorem kindsW_at : ∀ g < 12,
    (((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++
      [(2, "H")] : List (ℕ × String))[2 * g]? = some (0, "G" ++ toString g) ∧
    (((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++
      [(2, "H")] : List (ℕ × String))[2 * g + 1]? = some (1, "A" ++ toString g) := by
  decide +kernel

theorem kindsW_head :
    (((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++
      [(2, "H")] : List (ℕ × String))[24]? = some (2, "H") := by decide +kernel

/-- A negative test: with each pair's two members swapped it is another list. -/
theorem kindsW_not :
    (((List.range 12).flatMap fun g => [(1, "A" ++ toString g), (0, "G" ++ toString g)]) ++
      [(2, "H")] : List (ℕ × String)) ≠
    ((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++
      [(2, "H")] := by decide +kernel

theorem viewsW_len :
    ((List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)] :
      List (ℕ × Bool × ℕ)).length = 25 := by decide +kernel

theorem viewsW_at : ∀ g < 12,
    ((List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)] :
      List (ℕ × Bool × ℕ))[2 * g]? = some (0, true, g) ∧
    ((List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)] :
      List (ℕ × Bool × ℕ))[2 * g + 1]? = some (1, false, g) := by
  decide +kernel

theorem viewsW_head :
    ((List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)] :
      List (ℕ × Bool × ℕ))[24]? = some (2, true, 0) := by decide +kernel

/-- A negative test: with the two flags swapped it is another list. -/
theorem viewsW_not :
    ((List.range 12).flatMap (fun g => [(0, false, g), (1, true, g)]) ++ [(2, true, 0)] :
      List (ℕ × Bool × ℕ)) ≠
    (List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)] := by
  decide +kernel

/-- Below 25: the head's place, or a pair's first or second. -/
theorem split_25 {i : ℕ} (hi : i < 25) :
    i = 24 ∨ ∃ g, g < 12 ∧ (i = 2 * g ∨ i = 2 * g + 1) := by
  by_cases h : i = 24
  · exact Or.inl h
  · exact Or.inr ⟨i / 2, by omega, by omega⟩

/-! ## The ground's list -/

/-- **In the goals' scope, where the public part and the ground return: the 25 built links' kinds
and names, as ONE LIST.** -/
theorem kinds_in_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) :
    G.built.toList.map (fun X => (X.kind, X.name)) =
      ((List.range 12).flatMap fun g => [(0, "G" ++ toString g), (1, "A" ++ toString g)]) ++
        [(2, "H")] := by
  obtain ⟨hsz, -⟩ := IM.ground_gets hS hR hZ hG
  obtain ⟨hN, l24, e24, k24, n24⟩ := IM.ground_named hS hR hZ hG
  refine list_of_25 _ _ _ hsz kindsW_len fun i hi => ?_
  rcases split_25 hi with rfl | ⟨g, hg, rfl | rfl⟩
  · exact ⟨l24, e24, by rw [k24, n24.name]; exact kindsW_head⟩
  · obtain ⟨l, -, e, k, -, n, -⟩ := hN g hg
    exact ⟨l, e, by rw [k, n.name]; exact (kindsW_at g hg).1⟩
  · obtain ⟨-, l', -, -, -, -, e', k', -, n'⟩ := hN g hg
    exact ⟨l', e', by rw [k', n'.name]; exact (kindsW_at g hg).2⟩

/-! ## The public part's built structure -/

/-- **What the public part's built structure was made of**: one list of links, and the library's
function on it. No ground is asked. -/
theorem built_public {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ∃ (G A : Array SubPlanH) (H : SubPlanH) (l₀ : Array LinkH),
      listLinksH Z.p.X.NGr Z.p.X.p4 G A H = .ok l₀ ∧
      buildLinksH l₀ Z.p.X.NGr Z.p.X.p4 Z.p.X.layers.wsLay Z.first = .ok Z.p.built := by
  have hB := IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  exact ⟨_, _, _, l₀, h₀, hB⟩

/-- **In the goals' scope, where the public part returns (NO GROUND IS ASKED): the 25 links of the
public part's own built structure: kind, the flag fv, and the group (0 at the head's), as ONE
LIST.** -/
theorem views_in_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) :
    Z.p.built.links.toList.map
        (fun X : LinkH => (X.kind, X.fv, if X.kind == 2 then 0 else X.g)) =
      (List.range 12).flatMap (fun g => [(0, true, g), (1, false, g)]) ++ [(2, true, 0)] := by
  obtain ⟨G, A, H, l₀, h₀, hB⟩ := built_public hZ
  have hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X :=
    VerifiableInference.Reads.AtSeat.public_older hZ
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  rw [hq, hN] at h₀ hB
  obtain ⟨hsz, alt, l24, e24, I24⟩ := Meaning.links_alternate h₀ hB h₀
  obtain ⟨nam, m24, f24, N24⟩ := Meaning.links_named h₀ hB h₀
  have hs : Z.p.built.links.size = 25 := by
    have e := (Meaning.built_at hB).1
    unfold zipped at hsz
    rw [Array.size_zipWith, e] at hsz
    omega
  refine list_of_25 _ _ _ hs viewsW_len fun i hi => ?_
  rcases split_25 hi with rfl | ⟨g, hg, rfl | rfl⟩
  · obtain rfl : m24 = l24 := Option.some.inj (f24.symm.trans e24)
    obtain ⟨b, y, eb, -, rfl⟩ := zipped_is e24
    have k : b.kind = 2 := I24.kind
    have v : b.fv = true := N24.fv
    exact ⟨b, eb, by rw [k, v]; exact viewsW_head⟩
  · obtain ⟨s, a, l, l', -, -, e, I, -, -⟩ := alt g hg
    obtain ⟨m, m', f, N, -, -⟩ := nam g hg
    obtain rfl : m = l := Option.some.inj (f.symm.trans e)
    obtain ⟨b, y, eb, -, rfl⟩ := zipped_is e
    have k : b.kind = 0 := I.kind
    have q : b.g = g := I.g
    have v : b.fv = true := N.fv
    exact ⟨b, eb, by rw [k, v, q]; exact (viewsW_at g hg).1⟩
  · obtain ⟨s, a, l, l', -, -, -, -, e', I'⟩ := alt g hg
    obtain ⟨m, m', -, -, f', N'⟩ := nam g hg
    obtain rfl : m' = l' := Option.some.inj (f'.symm.trans e')
    obtain ⟨b, y, eb, -, rfl⟩ := zipped_is e'
    have k : b.kind = 1 := I'.kind
    have q : b.g = g := I'.g
    have v : b.fv = false := N'.fv
    exact ⟨b, eb, by rw [k, v, q]; exact (viewsW_at g hg).2⟩

end Johnson.AtFull.Lots.LinksScope

#print axioms Johnson.AtFull.Lots.LinksScope.zipped_is
#print axioms Johnson.AtFull.Lots.LinksScope.list_of_25
#print axioms Johnson.AtFull.Lots.LinksScope.kindsW_len
#print axioms Johnson.AtFull.Lots.LinksScope.kindsW_at
#print axioms Johnson.AtFull.Lots.LinksScope.kindsW_head
#print axioms Johnson.AtFull.Lots.LinksScope.kindsW_not
#print axioms Johnson.AtFull.Lots.LinksScope.viewsW_len
#print axioms Johnson.AtFull.Lots.LinksScope.viewsW_at
#print axioms Johnson.AtFull.Lots.LinksScope.viewsW_head
#print axioms Johnson.AtFull.Lots.LinksScope.viewsW_not
#print axioms Johnson.AtFull.Lots.LinksScope.split_25
#print axioms Johnson.AtFull.Lots.LinksScope.kinds_in_scope
#print axioms Johnson.AtFull.Lots.LinksScope.built_public
#print axioms Johnson.AtFull.Lots.LinksScope.views_in_scope
