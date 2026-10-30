-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Levels.lean: a run of levels of a product tree, from its
return: for each level the row that it leaves, with its coefficients as `SumOut` tells them, and the
form from which it starts. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there stage, sumcheck, row, form, slot, ledger, hearing and
sample. In this file: f is the lookup's face, lo the ledger's count of slots in front of the lookup,
rs the rounds. `Pos` and `SumOut` are those of Honest/K3/Good/Step.lean. LINE is the round behind a
level, which samples xi.

What is shown.
  `Ok`, `ok_one`, `beta_ne`: every sampled element's words are below the prime; so the sample of Y,
    which the hearing holds against the word 0, reads as an element that is not 0.
  `sum_step`: the step `whole_step` of Step.lean, at `sumV`.
  `level_all`, `level_step`: one level with the round LINE behind it.
  `endOf`, `lineForm`, `startOf`: a stage's first end slot; the form behind a level; the form in
    front of level l.
  `RunOut`, `run_out`: the run: the rows in front are kept; the row of level l stands among the
    rows, with its coefficients, at the form in front of it; the form that is left is the one behind
    the last level.
Helpers: `ok_e1`, `lastD_mem`, `ok_take_drop`, `sumV_beta`, `mem_push_of`, `mem_push_self`.

Hypotheses that remain, in `run_out`.
  `hok`: every sampled element's words are below the prime (`Ok`).
  `P`, `hC`: the hearing stands in front of stage number i0; the form carried names slots between lo
    and the ledger's next slot alone.
Besides: which stages the levels are (the letters A and B, by their numbers in the row and their
calls), and the return of the run of levels.
In the theorems on the way. `h`: `Ok rs` (in `ok_one`, `beta_ne`, `ok_take_drop`; in `ok_e1` of one
round); the return of `level` (in `level_all`, `level_step`); a member of the rows (in
`mem_push_of`). `hz`: (in `beta_ne`) the hearing's test on the sample of Y has passed. `e`: (in
`sumV_beta`, `sum_step`) `sumV` returns. `hs`, `hk0`, `hd`, `he`, `hne`, `hp`: (in `sum_step`) as in
`whole_step` (Step.lean). `hA`, `hB`, `cA`, `cB`: (in `level_step`) A and B are the stages number n
and n + 1; A's call is the level's, B has none.

Users. Honest/K3/Good/Tie.lean imports this file.

Limits. A run of levels; the letters A and B say which stages they are.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE okE isZeroE)
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Call Ends Heard ownSlots)
open VerifiableInference.Desc.K3 (sumV)
open VerifiableInference.Desc.First.ProdV
    (LevelOut level turn Carried stepDown levelVars levelEnds endProd
  turn_spec run_succ_spec run_zero)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (In whole_names in_stepDown in_mono)

local notation "vRoundsOf" => VerifiableInference.Desc.K3.roundsOf
local notation "vRun" => VerifiableInference.Desc.First.ProdV.run
local notation "vLevelCall" => VerifiableInference.Desc.First.ProdV.levelCall

/-! ## Words below the prime -/

/-- Every sampled element's words are below the prime. -/
def Ok (rs : List Fmt.RoundView) : Prop := ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, okE (E.ofTriple x) = true

theorem ok_e1 {r : Fmt.RoundView} (h : ∀ x ∈ r.drawn.elems, okE (E.ofTriple x) = true) : okE (e1 r) = true
    := by
  unfold e1
  cases hx : r.drawn.elems with
  | nil => rfl
  | cons a t => exact h a (by rw [hx]; simp)

theorem ok_one {rs : List Fmt.RoundView} (h : Ok rs) (a : Nat) : okE (one rs a) = true := by
  unfold one
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hr : rs[a]? with
  | none => rfl
  | some r => exact ok_e1 (h r (List.mem_of_getElem? hr))

theorem lastD_mem (l : List E) (d : E) : l.getLastD d = d ∨ l.getLastD d ∈ l := by
  rw [List.getLastD_eq_getLast?]
  cases h : l.getLast? with
  | none => exact Or.inl rfl
  | some x => exact Or.inr (List.mem_of_getLast? h)

/-- Y's sample, held against the word 0, reads as an element that is not 0. -/
theorem beta_ne {rs : List Fmt.RoundView} (h : Ok rs) {a n : Nat}
    (hz : isZeroE ((seg rs a n).getLastD zeroE) = false) : vl ((seg rs a n).getLastD zeroE) ≠ 0 :=
    by
  refine vl_ne_zero ?_ hz
  rcases lastD_mem (seg rs a n) zeroE with h1 | h1
  · rw [h1]
    rfl
  · obtain ⟨l, _, e⟩ := mem_seg h1
    rw [e]
    exact ok_one h _

theorem ok_take_drop {rs : List Fmt.RoundView} (h : Ok rs) (a b : Nat) : Ok ((rs.drop a).take b) :=
  fun r hr => h r (List.mem_of_mem_drop (List.mem_of_mem_take hr))

variable {f : LFace} {lo : Nat} {rs : List Fmt.RoundView}

/-! ## A sumcheck with end values, as the hearing calls it -/

theorem sumV_beta {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G : Fork}
    {r rest : List Fmt.RoundView} {x : Heard × Aff} (e : sumV C k endTerm F r = some (x, G, rest)) :
    isZeroE (x.1.r.getLastD zeroE) = false := by
  unfold sumV at e
  split at e
  · exact nomatch e
  · split at e
    · rename_i h row G' hw
      split at e
      · exact nomatch e
      · rename_i hz
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨a1, _, _⟩ := e
        subst a1
        simpa using hz
    · exact nomatch e

/-- **A stage with end values, as `sumV` hears it.** -/
theorem sum_step {n : Nat} {s : Stage} {k0 k : Call} {C : Aff} {endTerm : List E → List E → E}
    {F G : Fork} {rest rest' : List Fmt.RoundView} {x : Heard × Aff}
    (hs : (stages f)[n]? = some s) (hk0 : s.call f = some k0)
    (hd : k.vs.map Var.d = k0.vs.map Var.d) (he : k.ends = k0.ends) (hne : k.ends.isSome = true)
    (hp : ∀ v ∈ k.vs, Pt v) (hok : Ok rs) (P : Pos f lo rs n F rest) (hC : In lo F.next C)
    (e : sumV C k endTerm F rest = some (x, G, rest')) :
    Pos f lo rs (n + 1) G rest' ∧ SumOut f lo rs s C x.2 x.1.sEnd ∧ In lo G.next x.2 ∧
      G.next = x.1.sEnd + k.endsN := by
  obtain ⟨a1, a2, _⟩ := sumV_spec e
  have hw := sumV_whole e
  have hz := sumV_beta e
  have hb : vl (x.1.r.getLastD zeroE) ≠ 0 := by
    obtain ⟨lead, vs, ends⟩ := k
    obtain ⟨e', rfl⟩ : ∃ e', ends = some e' := Option.isSome_iff_exists.1 hne
    obtain ⟨_, d2⟩ := whole_draws hw
    rw [d2] at hz ⊢
    rw [P.cut] at hz ⊢
    exact beta_ne (ok_take_drop hok _ _) hz
  obtain ⟨b1, b2, b3⟩ := whole_step hs hk0 hd he hne hp P hC hw a2 hb
  have hlo : lo ≤ F.next := by rw [P.next]; omega
  rw [a1]
  exact ⟨b1, b2, b3, (whole_names hw hC hlo).2.2⟩

/-! ## One level -/

theorem level_all {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {r rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F r = some (o, G, rest)) :
    ∃ (hd : Heard) (line : Fmt.RoundView),
      MaskedSum.whole C (vLevelCall m z order) endProd F (r.take (m + 3)) = some (hd, o.row, G) ∧
      r.drop (m + 3) = line :: rest ∧ o.xi = e1 line ∧ o.sL = hd.sEnd ∧ o.sR = hd.sEnd + 1 ∧
      isZeroE (hd.r.getLastD zeroE) = false := by
  unfold level at h
  split at h
  · cases h
  · split at h
    · rename_i hd row G' line rest' hw hdrop
      split at h
      · rename_i s xi hr
        split at h
        · cases h
        · rename_i hz
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2, h3⟩ := h
          subst h1 h2 h3
          have hx : [xi] = line.drawn.elems.map E.ofTriple := (MaskedSum.roundOf_spec hr).2.2.2
          exact ⟨hd, line, hw, hdrop, by simp [e1, ← hx], rfl, rfl, by simpa using hz⟩
      · cases h
    · cases h

/-- **One level with the round LINE behind it.** Here A is the level's stage, number n in the row,
and B the stage of LINE, number n + 1. -/
theorem level_step {n m : Nat} {A B : Stage} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rest rest' : List Fmt.RoundView} {o : LevelOut}
    (hA : (stages f)[n]? = some A) (hB : (stages f)[n + 1]? = some B)
    (cA : A.call f = some (K3.levelCall m)) (cB : B.call f = none) (hok : Ok rs)
    (P : Pos f lo rs n F rest) (hC : In lo F.next C)
    (h : level m z order C F rest = some (o, G, rest')) :
    Pos f lo rs (n + 2) G rest' ∧ SumOut f lo rs A C o.row o.sL ∧ o.sR = o.sL + 1 ∧
      o.xi = one rs (firstRound f B) ∧ In lo G.next o.row ∧ G.next = o.sL + 2 := by
  obtain ⟨hd, line, hw, hdrop, hxi, hL, hR, hz⟩ := level_all h
  obtain ⟨b1, _⟩ := whole_seg (lead := 0) (vs := levelVars m z order) (e := levelEnds) hw
  have hlen : (levelVars m z order).length = order.length := by simp [levelVars]
  obtain ⟨d1, d2, d3⟩ := drop_cons hdrop
  have hm : order.length = m := by
    rw [hlen, List.length_take] at b1
    omega
  have hro : vRoundsOf (vLevelCall m z order) = m + 3 := by
    show (levelVars m z order).length + 3 = m + 3
    rw [hlen, hm]
  have hw' : MaskedSum.whole C (vLevelCall m z order) endProd F
      (rest.take (vRoundsOf (vLevelCall m z order))) = some (hd, o.row, G) := by
    rw [hro]
    exact hw
  have hdd : (vLevelCall m z order).vs.map Var.d = (K3.levelCall m).vs.map Var.d := by
    show (levelVars m z order).map Var.d = (levelVars m #[] (List.range m)).map Var.d
    simp only [levelVars, List.map_map]
    show order.map (fun _ => 3) = (List.range m).map (fun _ => 3)
    rw [List.map_const', List.map_const', List.length_range, hm]
  have hp : ∀ v ∈ (vLevelCall m z order).vs, Pt v := by
    intro v hv
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hv
    exact ⟨_, 3, rfl⟩
  have hb : vl (hd.r.getLastD zeroE) ≠ 0 := by
    obtain ⟨_, e2⟩ := whole_draws (lead := 0) (vs := levelVars m z order) (e := levelEnds) hw
    rw [e2] at hz ⊢
    rw [P.cut] at hz ⊢
    exact beta_ne (ok_take_drop hok _ _) hz
  obtain ⟨p1, p2, p3⟩ := whole_step hA cA hdd rfl rfl hp P hC hw' (by rw [hro]; omega) hb
  have hlo : lo ≤ F.next := by rw [P.next]; omega
  have hn : G.next = hd.sEnd + 2 := (whole_names hw hC hlo).2.2
  have hrB : B.rounds f = 1 := by simp [Stage.rounds, cB]
  have hsB : B.slots f = 0 := by simp [Stage.slots, Stage.own, Stage.tail, cB]
  rw [hro] at p1
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, p3, ?_⟩
  · rw [p1.next, (slotsIn_at hB).2, hsB]
    rfl
  · have c := p1.cut
    rw [d1, ← List.drop_drop, c, List.drop_drop, off_succ hB, hrB]
  · rw [hL]
    exact p2
  · rw [hR, hL]
  · have c := p1.cut
    have x1 : one (rest.drop (m + 3)) 0 = one rest (m + 3 + 0) := one_drop rest (m + 3) 0
    have x2 : one (rs.drop (off f (n + 1))) 0 = one rs (off f (n + 1) + 0) := one_drop rs _ 0
    rw [c] at x1
    rw [hxi, ← one_of_get d3, off_at hB]
    exact x1.symm.trans x2
  · rw [hL]
    exact hn

/-! ## A run of levels -/

/-- A stage's first end slot. -/
def endOf (f : LFace) (lo : Nat) (s : Stage) : Nat := lo + firstSlot f s + s.own f

/-- The form behind a level: on its two end slots, under 1 - xi and xi. -/
def lineForm (sE : Nat) (xi : E) : Aff :=
  Aff.scale (Aff.slot sE) (subE oneE xi) + Aff.scale (Aff.slot (sE + 1)) xi

/-- The form in front of level number l of a run that starts from the form C0. -/
def startOf (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (A B : Nat → Stage) (C0 : Aff) : Nat → Aff
  | 0 => C0
  | l + 1 => lineForm (endOf f lo (A l)) (one rs (firstRound f (B l)))

/-- **What a run of N levels leaves.** -/
structure RunOut (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (A B : Nat → Stage) (N : Nat)
    (s c : Carried) : Prop where
  keep : ∀ y ∈ s.rows.toList, y ∈ c.rows.toList
  row : ∀ l, l < N → ∃ y ∈ c.rows.toList,
    SumOut f lo rs (A l) (startOf f lo rs A B s.form l) y (endOf f lo (A l))
  form : c.form = startOf f lo rs A B s.form N

theorem mem_push_of {rows : Array Aff} {y z : Aff} (h : y ∈ rows.toList) : y ∈ (rows.push z).toList
    := by
  rw [Array.toList_push]
  exact List.mem_append_left _ h

theorem mem_push_self (rows : Array Aff) (z : Aff) : z ∈ (rows.push z).toList := by
  rw [Array.toList_push]
  simp

/-- **A run of levels, from its return.** Level l has m0 + l variables; its stage A l has the number
i0 + 2 l in the row, the stage B l of the round LINE behind it the number i0 + 2 l + 1. -/
theorem run_out {i0 m0 : Nat} {A B : Nat → Stage} {orders : Nat → List Nat} {s : Carried} {F : Fork}
    {rest : List Fmt.RoundView} (hok : Ok rs) (P : Pos f lo rs i0 F rest) (hC : In lo F.next s.form) :
    ∀ (N : Nat), (∀ l, l < N → (stages f)[i0 + 2 * l]? = some (A l) ∧
        (stages f)[i0 + 2 * l + 1]? = some (B l) ∧ (A l).call f = some (K3.levelCall (m0 + l)) ∧
        (B l).call f = none) →
      ∀ {c : Carried} {G : Fork} {rest' : List Fmt.RoundView},
      vRun m0 N orders s F rest = some (c, G, rest') →
      Pos f lo rs (i0 + 2 * N) G rest' ∧ RunOut f lo rs A B N s c ∧ In lo G.next c.form ∧
        F.next ≤ G.next
  | 0, _, c, G, rest', h => by
    rw [run_zero] at h
    cases h
    exact ⟨P, ⟨fun _ hy => hy, fun l hl => absurd hl (Nat.not_lt_zero l), rfl⟩, hC, Nat.le_refl _⟩
  | N + 1, hst, c, G, rest', h => by
    obtain ⟨s1, F1, r1, h1, h2⟩ := run_succ_spec h
    obtain ⟨p1, q1, i1, n1⟩ := run_out hok P hC N (fun l hl => hst l (Nat.lt_succ_of_lt hl)) h1
    obtain ⟨o, hl, hc⟩ := turn_spec h2
    obtain ⟨a1, a2, a3, a4⟩ := hst N (Nat.lt_succ_self N)
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := level_step a1 a2 a3 a4 hok p1 i1 hl
    have hsE : o.sL = endOf f lo (A N) := b2.sEnd
    have hge : F1.next ≤ o.sL := by
      rw [hsE, p1.next, ← (slotsIn_at a1).1]
      unfold endOf
      omega
    have hlo : lo ≤ F1.next := by rw [p1.next]; omega
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, by omega⟩
    · have e : i0 + 2 * (N + 1) = i0 + 2 * N + 2 := by omega
      rw [e]
      exact b1
    · intro y hy
      rw [hc]
      exact mem_push_of (q1.keep y hy)
    · intro l hl'
      rw [hc]
      by_cases hlN : l < N
      · obtain ⟨y, hy, hS⟩ := q1.row l hlN
        exact ⟨y, mem_push_of hy, hS⟩
      · obtain rfl : l = N := by omega
        refine ⟨o.row, mem_push_self _ _, ?_⟩
        rw [← q1.form, ← hsE]
        exact b2
    · rw [hc]
      show (stepDown o).2 = lineForm (endOf f lo (A N)) (one rs (firstRound f (B N)))
      unfold stepDown lineForm
      rw [b3, hsE, b4]
    · rw [hc]
      exact in_stepDown o (by omega) (by omega) (by omega) (by omega)

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.ok_e1
#print axioms ProofFile.Honest.K3.Good.ok_one
#print axioms ProofFile.Honest.K3.Good.lastD_mem
#print axioms ProofFile.Honest.K3.Good.beta_ne
#print axioms ProofFile.Honest.K3.Good.ok_take_drop
#print axioms ProofFile.Honest.K3.Good.sumV_beta
#print axioms ProofFile.Honest.K3.Good.sum_step
#print axioms ProofFile.Honest.K3.Good.level_all
#print axioms ProofFile.Honest.K3.Good.level_step
#print axioms ProofFile.Honest.K3.Good.mem_push_of
#print axioms ProofFile.Honest.K3.Good.mem_push_self
#print axioms ProofFile.Honest.K3.Good.run_out
