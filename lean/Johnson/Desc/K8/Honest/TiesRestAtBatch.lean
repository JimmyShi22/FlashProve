-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TiesRestAtBatch.lean: THE SMALLNESS TEST: `TiesRest`
(Johnson/Desc/K8/Honest/TiesAtLink.lean: at each matrix's shape K1 = k and Kc = k; the shapes' rows
of cells add up to mz) AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF A
SEGMENT's BATCHING, IN THE GOALS' SCOPE. One of the seventeen sentences of `AllFront`
(Johnson/Desc/K8/Honest/LeftAtLink.lean). Definitions and lemmas; none of the library's goals.

  `WideN x`, `Wide T`   an entry of a sub-proof's list of arrays bears a shape with the two
                   equations, or none (the default shape has them too: 0 = 0); every entry does
  `wideN_none`, `wide_addN`, `wide_addP`, `wideN_getD`   the two routines that add an array keep
                   it: t2AddP lays ShP.of m k a, whose text has K1 := k and Kc := k
                   (OnBytes/Model/FormF.lean)
  **`addTreesF_wide`**   behind addTreesF (OnBytes/Model/Tail.lean): the two equations at every mu
                   below NM · there are NM shapes
  **`shapes_sum`**   there are NM shapes · each has its matrix's rows of cells · ColsFacts tl
                   (Johnson/Desc/K8/Honest/TiesLaidOf.lean: the matrices' first columns follow one
                   another from 0 to mz) ⊢ the shapes' rows of cells add up to mz
  `wide_fromAdd`   FromAdd tlc Fc (Johnson/Desc/K8/Honest/FromAddTrees.lean) ⊢ the same two
  `shapesView`, `planned_shapes`   the two fields NM and shp; they are planned fields
  **`tiesRest_at_batch`**   TiesRest tl at the state's own data
WRITTEN A FURTHER TIME: the walk of `addTreesF_wide` and its four small lemmas are those of the
library's `addTreesF_mS` (Johnson/Road/K4/Plan/ShapeRows.lean), cut for cut, with these two
equations in the place of that one. KIN, NOT CALLED: `shapes_at_batch`
(Johnson/P1K8R/SecondLaidAtBatch.lean) has "as many shapes as matrices" at the same states.
By: `built_fromAdd` · LinkJoin.planned_at_batch (Johnson/Desc/First/Link/Law/PlannedAtDraw.lean) ·
`sizes_at_batch` (Johnson/P1K8R/TiesAtBatch.lean) · `apart_at_batch` (ApartAtBatch.lean) ·
`colsFacts_of` (TiesLaidOf.lean).
Limits. IN SCOPE ALONE in the last: the full size's 25 segments; under an opening of the
description; the first chain; the family of states from the description's own first state. Nothing
says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.TiesAtLink
import Johnson.Desc.K8.Honest.FromAddTrees
import Johnson.Road.K4.Plan.ShapeRows
import Johnson.Desc.First.Link.Law.OkAtBatch
import Johnson.P1K8R.TiesAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The entry's shape, or the default shape where it bears none, has the two equations. -/
def WideN (x : N2) : Prop :=
  (x.p.getD {}).K1 = (x.p.getD {}).k ∧ (x.p.getD {}).Kc = (x.p.getD {}).k

/-- Every entry of the list has it. -/
def Wide (T : Tail2) : Prop := ∀ x ∈ T.nt, WideN x

/-- An entry without a shape has it. -/
theorem wideN_none (ec a : Nat) (foreign : Bool) :
    WideN { ec := ec, a := a, foreign := foreign } := by
  exact ⟨rfl, rfl⟩

/-- t2AddN lays no shape. -/
theorem wide_addN {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) (g : Wide T) : Wide T' := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨_, e3⟩ := Prod.mk.inj e2
    subst e3
    intro x hx
    rcases Array.mem_push.1 hx with h1 | rfl
    · exact g x h1
    · exact wideN_none ec a foreign

/-- t2AddP lays ShP.of. -/
theorem wide_addP {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : Wide T) : Wide T' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨_, e3⟩ := Prod.mk.inj e2
      subst e3
      intro x hx
      rcases Array.mem_push.1 hx with h1 | rfl
      · exact g x h1
      · exact ⟨rfl, rfl⟩

/-- What getD reads off such a list has it. -/
theorem wideN_getD {T : Tail2} (g : Wide T) (j : Nat) : WideN (T.nt.getD j {}) := by
  rw [Array.getD_eq_getD_getElem?]
  cases hj : T.nt[j]? with
  | none => exact ⟨rfl, rfl⟩
  | some x => exact g x (Array.mem_of_getElem? hj)

/-- **Behind addTreesF each matrix's shape has its number of columns as its places of a row and as
its array's columns, and there is a shape for each matrix.** -/
theorem addTreesF_wide {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    (∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).K1 = (tl'.shp.getD mu {}).k ∧
      (tl'.shp.getD mu {}).Kc = (tl'.shp.getD mu {}).k) ∧ tl'.shp.size = tl'.NM := by
  unfold addTreesF at h
  obtain ⟨h0, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  -- the list that is handed in is empty
  have G0 : Wide { T with link := true } := by
    intro x hx
    have hE : T.nt.isEmpty = true := by simpa using h0
    have hz : T.nt.size = 0 := Array.isEmpty_iff_size_eq_zero.1 hE
    obtain ⟨i, hi, _⟩ := Array.mem_iff_getElem.1 hx
    have hi' : i < T.nt.size := hi
    omega
  have K1 : Wide T1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => Wide s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨_, hs⟩ := ok_of_jp hs
        exact ⟨_, (Except.ok.inj hs).symm, wide_addN hP hI⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl G0 h1
  have K2 : Wide T2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun _ (s : MProd Fork Tail2) => Wide s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, wide_addP hP hI⟩)
    (List.range tl.pkMat.size) [] _ _ rfl K1 h2
  have K3 : Wide T3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun _ (s : MProd Fork Tail2) => Wide s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, wide_addP hP hI⟩)
    (List.range tl.pxMat.size) [] _ _ rfl K2 h3
  have KB : Wide TB := wide_addN hB (wide_addN hZ K3)
  have K4 : Wide T4 := forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => Wide s.2)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, wide_addP hP hI⟩)
    (List.range tl.ft.size) [] _ _ rfl KB h4
  refine ⟨fun mu hmu => ?_, by rw [← e1]; simp⟩
  have hNM : tl'.NM = tl.NM := by rw [← e1]
  have hm : mu < tl.NM := by rw [← hNM]; exact hmu
  have hs : tl'.shp.getD mu {} = (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {} := by
    rw [← e1]
    show ((Array.range tl.NM).map fun mu =>
      (T4.nt.getD (tl.gtTree.getD mu 0) {}).p.getD {}).getD mu {} = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hm]
    rfl
  have hg : WideN (T4.nt.getD (tl.gtTree.getD mu 0) {}) := wideN_getD K4 _
  unfold WideN at hg
  rw [← hs] at hg
  exact hg

/-- **The shapes' rows of cells add up to mz.** -/
theorem shapes_sum {tl : HTailF2} (hs : tl.shp.size = tl.NM)
    (hm : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).m = (tl.mats.getD mu {}).m)
    (C : ColsFacts tl) : tl.shp.foldl (fun n s => n + s.m) 0 = tl.mz := by
  have K := Array.foldl_induction (as := tl.shp)
    (motive := fun i n => n = if i < tl.NM then tl.off.getD i 0 else tl.mz)
    (init := 0) (f := fun n s => n + s.m)
    (by
      show (0 : Nat) = if 0 < tl.NM then tl.off.getD 0 0 else tl.mz
      by_cases h0 : 0 < tl.NM
      · rw [if_pos h0, C.first]
      · rw [if_neg h0, C.empty (by omega)])
    (fun i n ih => by
      have hi : i.1 < tl.NM := by
        rw [← hs]
        exact i.2
      have e : tl.shp.getD i.1 {} = tl.shp[i] := by simp [Array.getD, i.2]
      have ih0 : n = if i.1 < tl.NM then tl.off.getD i.1 0 else tl.mz := ih
      rw [if_pos hi] at ih0
      show n + tl.shp[i].m = if i.1 + 1 < tl.NM then tl.off.getD (i.1 + 1) 0 else tl.mz
      rw [ih0, ← e, hm i.1 hi]
      exact C.next i.1 hi)
  have K' : tl.shp.foldl (fun n s => n + s.m) 0 =
      if tl.shp.size < tl.NM then tl.off.getD tl.shp.size 0 else tl.mz := K
  have hn : ¬ tl.shp.size < tl.NM := by
    rw [hs]
    exact Nat.lt_irrefl _
  rw [if_neg hn] at K'
  exact K'

/-- At whatever one call of addTreesF has laid. -/
theorem wide_fromAdd {tlc : HTailF2} {Fc : Fork} (M : FromAdd tlc Fc) :
    (∀ mu, mu < tlc.NM → (tlc.shp.getD mu {}).K1 = (tlc.shp.getD mu {}).k ∧
      (tlc.shp.getD mu {}).Kc = (tlc.shp.getD mu {}).k) ∧ tlc.shp.size = tlc.NM := by
  obtain ⟨tl, tl', F, G, T, T', nU, aTX, hb, hbLine, ha, hr, -⟩ := M
  have cN : tlc.NM = tl'.NM := congrArg (·.NM) hr
  have cS : tlc.shp = tl'.shp := congrArg (·.shp) hr
  rw [cN, cS]
  exact addTreesF_wide ha

/-- The two fields that the sentences read. -/
def shapesView (tl : HTailF2) := (tl.NM, tl.shp)

/-- They are planned fields. -/
theorem planned_shapes : LinkJoin.Planned shapesView :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING.** -/
theorem tiesRest_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : TiesRest tl := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have g := LinkJoin.of_readTl
    (LinkJoin.planned_at_batch planned_shapes hS hR O hx e3 (z, s) h') tl ht
  simp only [shapesView, Prod.mk.injEq] at g
  obtain ⟨g1, g2⟩ := g
  obtain ⟨w1, w2⟩ := wide_fromAdd (built_fromAdd hS hR O hl e3)
  rw [← g1, ← g2] at w1 w2
  obtain ⟨t3, a3, -, hC⟩ := _root_.P1K8.apart_at_batch hS hR O hl h
  obtain rfl : tl = t3 := Option.some.inj (ht.symm.trans a3)
  obtain ⟨t4, a4, hZ⟩ := _root_.P1K8.sizes_at_batch hS hR O hl h
  obtain rfl : tl = t4 := Option.some.inj (ht.symm.trans a4)
  have hZ' := hZ
  unfold _root_.P1K8.sizesB at hZ'
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hZ'
  obtain ⟨h1, h2⟩ := hZ'
  have C : ColsFacts tl := colsFacts_of tl hC (fun mu hmu => (h1 mu hmu).2) fun h0 => by
    rcases h2 with h2 | h2
    · exact absurd h0 h2
    · exact h2
  exact ⟨fun mu hmu => (w1 mu hmu).1, fun mu hmu => (w1 mu hmu).2,
    shapes_sum w2 (fun mu hmu => (h1 mu hmu).1.1) C⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.wideN_none
#print axioms VerifiableInference.Desc.First.K8.Honest.wide_addN
#print axioms VerifiableInference.Desc.First.K8.Honest.wide_addP
#print axioms VerifiableInference.Desc.First.K8.Honest.wideN_getD
#print axioms VerifiableInference.Desc.First.K8.Honest.addTreesF_wide
#print axioms VerifiableInference.Desc.First.K8.Honest.shapes_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.wide_fromAdd
#print axioms VerifiableInference.Desc.First.K8.Honest.planned_shapes
#print axioms VerifiableInference.Desc.First.K8.Honest.tiesRest_at_batch
