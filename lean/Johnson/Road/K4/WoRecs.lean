-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WoRecs.lean: where the merge of the weight claims returns (`flatForkEnd`,
OnBytes/K/Kc/QuietLink.lean), what its own text has tested of the claims and what it has left of
them, in the shapes in which `woSays_iff_list` (Johnson/Road/K4/WoLed.lean) asks for them: one list
of pairs, a claim with its coefficient. Definitions, statements and proofs.

  `merge_rho`: the coefficients that `Fl.wsForkMerge` returns are the powers of the element that
    the tape's first round drew (`tapeEps`), one for each slot.
  `crOf cl x`: the claims cl, each with its power of x: the list on which the text maps.
  `FlatSpec lay cl sv t wo`, `flat_spec`: there is a claim; at most 4096; as many slots as claims;
    each claim's unit is a number of the layout; each claim passes `wsClaimShape`; wo.recs is the
    text's map over `crOf cl (tapeEps t)`.
  `crOf_length`, `crOf_mem`, `crOf_get`: the list's length, its members and its member number j.
  `crOf_fst`, `crOf_co`: member number a under a length n that is the list's by an equation: its
    claim is cl[a]; its coefficient reads as the a-th power of the reading of x.
  `ok_of_isOk`: a test without a value that has passed, as an equation with `.ok ()`.
  `FlatSpec.shape`: each member's claim passes `wsClaimShape`, as an equation with `.ok ()`.
  `FlatSpec.unit`: each member's claim has its unit in the layout, and the unit is `UnitOK`, if the
    layout is one that `wsLayOf` returns (`unitOK_of_layout`, Johnson/Road/FormsKeysWLay.lean).

Limits. One direction: from a return. Which claims cl are, and on which tape the merge stands, is
not said here. That the layout is one that `wsLayOf` returns is a premise. That `wsPending` returns
is not touched. Identities on data and tests that the text has made: nothing on what a claim is
worth, on a draw or on soundness.


-/
import OnBytes.K.Kc.QuietLink
import OnBytes.Desc.First.P1.BatchPoint
import OnBytes.Desc.First.P1.LevelLaw
import Johnson.Road.FormsKeysWLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading Fork WsLay WsUnit WsClaim WsForkOut WsMerged WsShape wsLayOf
  wsClaimShape wsRowPart wsEpsT powers)
open OnBytes.Desc.First.P1 (pure_some must_some batch_spec tapeEps powers_size powers_val)

/-- **Where `Fl.wsForkMerge` returns from the tape t, its coefficients are the powers of what t's
first round drew** (`tapeEps t`), as many as there are slots. -/
theorem merge_rho {lk : Nat} {sv : Array Nat} {F G : Fork} {t u : Tape} {om : WsMerged}
    {rho : Array E} (h : Fl.wsForkMerge lk sv F t = some ((om, rho), G, u)) :
    rho = powers (tapeEps t) sv.size := by
  unfold Fl.wsForkMerge at h
  obtain ⟨rho', F1, t1, c1, k1⟩ := OnBytes.Desc.First.P1.bind_some.mp h
  obtain ⟨_, _, x, e1, e2⟩ := batch_spec c1
  obtain ⟨p, F2, t2, _, k2⟩ := OnBytes.Desc.First.P1.bind_some.mp k1
  obtain ⟨z, F3, t3, _, k3⟩ := OnBytes.Desc.First.P1.bind_some.mp k2
  obtain ⟨rm, p1⟩ := z
  obtain ⟨z2, F4, t4, _, k4⟩ := OnBytes.Desc.First.P1.bind_some.mp k3
  obtain ⟨sFv, p2⟩ := z2
  obtain ⟨fvp, F5, t5, _, k5⟩ := OnBytes.Desc.First.P1.bind_some.mp k4
  obtain ⟨e, _, _⟩ := pure_some.mp k5
  have hx : tapeEps t = x := by
    rw [e1]
    rfl
  rw [hx, ← (Prod.mk.inj e).2, e2]

/-- The claims, each with its coefficient: the powers of x in their order, as many as claims. -/
def crOf (cl : Array WsClaim) (x : E) : List (WsClaim × E) := (cl.zip (powers x cl.size)).toList

/-- What the merge's text has tested of the claims, and what it has left of them. -/
structure FlatSpec (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (t : Tape)
    (wo : WsForkOut) : Prop where
  /-- there is a claim -/
  ne : cl.size ≠ 0
  /-- there are at most 4096 -/
  le : cl.size ≤ 4096
  /-- a slot for each -/
  sz : sv.size = cl.size
  /-- each claim's unit is a number of the layout -/
  ui : ∀ c ∈ cl, c.ui < lay.U.size
  /-- each claim passes `wsClaimShape` -/
  ok : ∀ c ∈ cl, (wsClaimShape lay c).isOk = true
  /-- what is left of each claim: the text's map over the claims with their coefficients -/
  recs : wo.recs = (crOf cl (tapeEps t)).map fun y =>
    wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))

/-- **Where `flatForkEnd` returns wo from the tape t: `FlatSpec` at t and wo.** -/
theorem flat_spec {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    FlatSpec lay cl sv t wo := by
  unfold flatForkEnd at h
  obtain ⟨_, A1, a1, c1, k1⟩ := OnBytes.Desc.First.P1.bind_some.mp h
  obtain ⟨q1, rfl, rfl⟩ := must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := OnBytes.Desc.First.P1.bind_some.mp k1
  obtain ⟨q2, rfl, rfl⟩ := must_some.mp c2
  obtain ⟨_, A3, a3, c3, k3⟩ := OnBytes.Desc.First.P1.bind_some.mp k2
  obtain ⟨q3, rfl, rfl⟩ := must_some.mp c3
  obtain ⟨z, F4, t4, c4, k4⟩ := OnBytes.Desc.First.P1.bind_some.mp k3
  obtain ⟨om, rho⟩ := z
  obtain ⟨e, _, _⟩ := pure_some.mp k4
  simp only [Bool.and_eq_true] at q1
  obtain ⟨⟨qa, qb⟩, qc⟩ := q1
  have hsz : sv.size = cl.size := eq_of_beq qc
  have hr : wo.recs = (cl.zip rho).toList.map fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm)) := by
    subst e
    rfl
  rw [merge_rho c4, hsz] at hr
  refine ⟨?_, of_decide_eq_true qb, hsz, ?_, ?_, hr⟩
  · intro h0
    rw [Array.isEmpty_iff_size_eq_zero.mpr h0] at qa
    simp at qa
  · intro c hc
    exact of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 q2 c hc)
  · intro c hc
    exact Array.all_eq_true_iff_forall_mem.1 q3 c hc

/-- The list has a member for each claim. -/
theorem crOf_length (cl : Array WsClaim) (x : E) : (crOf cl x).length = cl.size := by
  unfold crOf
  rw [Array.toList_zip, List.length_zip, Array.length_toList, Array.length_toList, powers_size,
    Nat.min_self]

/-- A member's claim is one of the claims. -/
theorem crOf_mem {cl : Array WsClaim} {x : E} {y : WsClaim × E} (h : y ∈ crOf cl x) :
    y.1 ∈ cl := by
  unfold crOf at h
  rw [Array.toList_zip] at h
  exact Array.mem_def.mpr (List.of_mem_zip h).1

/-- Member number j: claim number j with entry number j of the powers. -/
theorem crOf_get (cl : Array WsClaim) (x : E) (j : Fin (crOf cl x).length) :
    cl[j.val]? = some ((crOf cl x).get j).1 ∧
      ((crOf cl x).get j).2 = (powers x cl.size).getD j.val zeroE := by
  have e : (crOf cl x)[j.val]? = some ((crOf cl x).get j) := List.getElem?_eq_getElem j.2
  have e' : (cl.toList.zip (powers x cl.size).toList)[j.val]? = some ((crOf cl x).get j) := by
    rw [← Array.toList_zip]
    exact e
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 e'
  rw [Array.getElem?_toList] at h1
  refine ⟨h1, ?_⟩
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h2, Option.getD_some]

/-- Member number a, under a length that is the list's by an equation: its claim. -/
theorem crOf_fst (cl : Array WsClaim) (x : E) {n : Nat} (hn : (crOf cl x).length = n)
    (a : Fin n) : cl[a.val]? = some ((crOf cl x).get (a.cast hn.symm)).1 :=
  (crOf_get cl x (a.cast hn.symm)).1

/-- **Its coefficient reads as the a-th power of the reading of x**, in any reading ρ. -/
theorem crOf_co {K : Type} [Field K] (ρ : Reading K) (cl : Array WsClaim) (x : E) {n : Nat}
    (hn : (crOf cl x).length = n) (a : Fin n) :
    ρ.val x ^ (a : Nat) = ρ.val ((crOf cl x).get (a.cast hn.symm)).2 := by
  have h1 := crOf_length cl x
  have h2 := a.2
  have h3 : a.val < cl.size := by omega
  rw [(crOf_get cl x (a.cast hn.symm)).2]
  exact (powers_val ρ x cl.size a.val h3).symm

/-- A test without a value that has passed, as an equation. -/
theorem ok_of_isOk {x : Except String Unit} (h : x.isOk = true) : x = .ok () := by
  cases x with
  | error e => simp [Except.isOk, Except.toBool] at h
  | ok a => rfl

/-- **Each member's claim passes `wsClaimShape`**, whichever x the coefficients are powers of. -/
theorem FlatSpec.shape {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {t : Tape}
    {wo : WsForkOut} (S : FlatSpec lay cl sv t wo) (x : E) :
    ∀ y ∈ crOf cl x, wsClaimShape lay y.1 = .ok () :=
  fun y hy => ok_of_isOk (S.ok y.1 (crOf_mem hy))

/-- **Each member's claim has its unit, and the unit is as `UnitOK` asks**, in a layout that
`wsLayOf` returns; whichever x the coefficients are powers of. -/
theorem FlatSpec.unit {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {t : Tape}
    {wo : WsForkOut} (S : FlatSpec lay cl sv t wo) {s : WsShape} {p3 : Bool} {lk : Nat}
    (hl : wsLayOf s p3 lk = .ok lay) (x : E) :
    ∀ y ∈ crOf cl x, ∃ u, lay.U[y.1.ui]? = some u ∧ UnitOK lay.lk u := by
  intro y hy
  have hi : y.1.ui < lay.U.size := S.ui y.1 (crOf_mem hy)
  refine ⟨lay.U[y.1.ui]'hi, Array.getElem?_eq_getElem hi, ?_⟩
  rw [(unitOK_of_layout hl).1]
  exact ((unitOK_of_layout hl).2 _ (Array.getElem_mem hi)).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.merge_rho
#print axioms OnBytes.Road.K4.flat_spec
#print axioms OnBytes.Road.K4.crOf_length
#print axioms OnBytes.Road.K4.crOf_mem
#print axioms OnBytes.Road.K4.crOf_get
#print axioms OnBytes.Road.K4.crOf_fst
#print axioms OnBytes.Road.K4.crOf_co
#print axioms OnBytes.Road.K4.FlatSpec.shape
#print axioms OnBytes.Road.K4.FlatSpec.unit
