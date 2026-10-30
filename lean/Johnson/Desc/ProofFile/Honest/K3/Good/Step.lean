-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Step.lean: one stage of the lookup's hearing, from its return:
where the hearing stands in front of a stage and behind it, by the stage's number in the row; which
sampled elements its structure holds, by the rounds' numbers; and the coefficients of the row that
it leaves. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there stage, sumcheck, row, form, slot, ledger, hearing and
sample. In this file: f is the lookup's face, lo the ledger's count of slots in front of the lookup,
rs the rounds. The row (of stages) is the list `stages f`; a stage's row is the linear form that its
sumcheck leaves.

What is shown.
  `many_head`, `elemsAt_many`, `value_many`, `value_one`: a spot's element, as the theorems on the
    hearing name it.
  `ne_of_fine`: what the test on a spot gives in the field.
  `whole_draws`, `open_draws`: a masked sumcheck's eps and challenges are the first samples of its
    rounds.
  `Pos`: where the hearing stands in front of stage number n: the ledger's count; the rounds left.
  `quiet_step`: a stage that sends nothing.
  `SumOut`, `whole_step`: a sumcheck with end values: where the hearing stands behind it; its first
    end slot; of its row's coefficients: those on the slots in front, and that none on its own slots
    is 0 where no challenge of its variables is; nothing on its end slots.
Helpers: `getD0_headD`, `vl_ne_zero`, `vl_ne_one`, `take_all_left`, `mem_seg`, `drawsV_same` (the
statement of `Law.drawsV_same`, Honest/K3/Law/GoesOn.lean, once more).

Hypotheses that remain, in `whole_step`.
  `hs`, `hk0`: s is stage number n of the row; k0 is its call, with points left as stand-ins.
  `hd`, `he`, `hne`, `hp`: k, the call in the run, has the degrees and the end values of k0; it has
    end values; each of its variables is summed at a point.
  `P`, `hC`: the hearing stands in front of stage n; the start form names slots between lo and the
    ledger's next slot alone.
  `hw`, `hlen`: the masked sumcheck returns on its own rounds; so many rounds are left.
  `hb`: the sample of Y reads as an element that is not 0.
In the others. `h`: (in `ne_of_fine`) the test on the spot accepts; (in `drawsV_same`) `drawsV`
returns; (in `take_all_left`, `mem_seg`) a length; a member. `h1`, `h2`: (in `vl_ne_zero`,
`vl_ne_one`) the element's words are below the prime; it is not the word 0, or not the word 1. `hh`:
(in `open_draws`) the open sumcheck's hearing returns. `hc`, `e`: (in `quiet_step`) the stage has no
call; `drawsV` returns.

Users. Honest/K3/Good/Levels.lean imports this file.

Limits. One stage. The walk over all stages stands in Honest/K3/Good/Walk.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Coef
import Johnson.Desc.ProofFile.Honest.K3.Parts.Index
import Johnson.Desc.ProofFile.Honest.K3.Law.LookHeard
import Johnson.Desc.ProofFile.Honest.K3.Law.StageStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE okE isZeroE)
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Call Ends Heard ownSlots)
open VerifiableInference.Desc.K3 (drawsV drawV sumV openV)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (In hear_names whole_names)

local notation "vRoundsOf" => VerifiableInference.Desc.K3.roundsOf

/-! ## A spot's element -/

theorem getD0_headD (l : List E) : l.getD 0 zeroE = l.headD zeroE := by cases l <;> rfl

theorem many_head (rs : List Fmt.RoundView) (a : Nat) : (many rs a).getD 0 zeroE = one rs a := by
  unfold many one
  rw [getD0_headD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rs[a]? with
  | none => rfl
  | some r => rfl

theorem elemsAt_many (rs : List Fmt.RoundView) (i : Nat) : elemsAt (rs.map (·.drawn)) i = many rs i := by
  unfold elemsAt many
  rw [List.getElem?_map, Option.map_map]
  rfl

/-- The element at a spot, of the rounds. -/
theorem value_many (f : LFace) (rs : List Fmt.RoundView) (p : Spot) :
    p.value f (rs.map (·.drawn)) = (many rs (firstRound f p.stage + p.round)).getD p.draw zeroE :=
      by
  unfold Spot.value
  rw [elemsAt_many]

theorem value_one (f : LFace) (rs : List Fmt.RoundView) (s : Stage) (r : Nat) (o : Bool) :
    (⟨s, r, 0, o⟩ : Spot).value f (rs.map (·.drawn)) = one rs (firstRound f s + r) := by
  rw [value_many]
  exact many_head _ _

/-- Words below the prime that are not all 0 read as an element that is not 0. -/
theorem vl_ne_zero {x : E} (h1 : okE x = true) (h2 : isZeroE x = false) : vl x ≠ 0 := by
  intro h0
  have hz : isZeroE x = true := (OnBytes.Slice.isZeroE_iff x h1).2 h0
  rw [hz] at h2
  exact nomatch h2

/-- Words below the prime that are not those of 1 read as an element that is not 1. -/
theorem vl_ne_one {x : E} (h1 : okE x = true) (h2 : x ≠ oneE) : vl x ≠ 1 := by
  intro h0
  exact h2 (OnBytes.Slice.readE_inj x oneE h1 rfl (h0.trans Reading.gl.one.symm))

/-- **What the test on a spot gives.** -/
theorem ne_of_fine {f : LFace} {ds : List Fmt.Drawn} {p : Spot} (h : p.fine f ds = true) :
    vl (p.value f ds) ≠ 0 ∧ (p.one = true → vl (p.value f ds) ≠ 1) := by
  unfold Spot.fine at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨vl_ne_zero h1 (by simpa using h2), fun ho => vl_ne_one h1 ?_⟩
  rw [ho] at h3
  simpa using h3

/-! ## A masked sumcheck's samples -/

theorem take_all_left (a b : List E) (n : Nat) (h : a.length = n) : (a ++ b).take n = a := by
  rw [← h]
  exact List.take_left

/-- With end values, on just its own rounds: eps is the first round's sample; the challenges, Y's
last, are the samples of the rounds behind it. -/
theorem whole_draws {C : Aff} {lead : Nat} {vs : List Var} {e : Ends}
    {endTerm : List E → List E → E} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} {row : Aff}
    (hw : MaskedSum.whole C ⟨lead, vs, some e⟩ endTerm F rs = some (h, row, G)) :
    h.eps = one rs 0 ∧ h.r = seg rs 1 (vs.length + 1) := by
  obtain ⟨_, G0, sh, _, hh, _, _⟩ := MaskedSum.whole_parts hw
  obtain ⟨_, T, R, _, hR, hrec, _⟩ := MaskedSum.hear_spec hh
  obtain ⟨r0, used, rv, front, a1, a2, _, a4, _⟩ := MaskedSum.readAll_spec hR
  have hl : used.length = vs.length + 1 := by simpa using (MaskedSum.VarsRead.length a4).1
  have hf := varsRead_firsts a4
  have he : [R.eps] = r0.drawn.elems.map E.ofTriple := a2.2.2.2
  subst a1
  constructor
  · rw [hrec]
    show R.eps = _
    simp [one, e1, ← he]
  · rw [hrec]
    show R.rounds.map (·.2) = _
    rw [hf]
    simp only [seg, List.map_cons, List.map_append, List.drop_succ_cons, List.drop_zero]
    rw [take_all_left _ _ _ (by simp [hl])]

/-- Without end values: the like. -/
theorem open_draws {C : Aff} {lead : Nat} {vs : List Var} {F G : Fork} {rs : List Fmt.RoundView}
    {h : Heard}
    (hh : MaskedSum.hear C ⟨lead, vs, none⟩ F rs = some (h, G)) :
    h.eps = one rs 0 ∧ h.r = seg rs 1 vs.length := by
  refine ⟨?_, (hear_none_seg hh).2.1⟩
  obtain ⟨_, T, R, _, hR, hrec, _⟩ := MaskedSum.hear_spec hh
  rw [hrec]
  show R.eps = _
  unfold MaskedSum.readAll at hR
  cases rs with
  | nil => cases hR
  | cons r rest =>
    simp only at hR
    split at hR
    · rename_i x mu eps l h1 h2 h3
      have e := Option.some.inj hR
      subst e
      unfold MaskedSum.firstRound at h1
      cases hf : MaskedSum.roundOf (lead + 1) 1 r with
      | none => simp [hf] at h1
      | some z =>
        simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨_, _, b3⟩ := h1
        have sf := MaskedSum.roundOf_spec hf
        have he : z.2 = r.drawn.elems.map E.ofTriple := sf.2.2.2
        show eps = _
        simp [one, e1, ← he, b3]
    · rename_i h3
      cases h3
    · cases hR

/-- An element of a stretch of first samples is one of them, by number. -/
theorem mem_seg {rs : List Fmt.RoundView} {a n : Nat} {x : E} (h : x ∈ seg rs a n) :
    ∃ l, l < n ∧ x = one rs (a + l) := by
  unfold seg at h
  obtain ⟨l, hl, e⟩ := List.mem_iff_getElem.1 h
  rw [List.length_take, List.length_drop] at hl
  refine ⟨l, by omega, ?_⟩
  rw [← e, List.getElem_take, List.getElem_drop]
  unfold one
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-! ## Where the hearing stands -/

/-- **Where the hearing stands in front of stage number n.** Here lo is the ledger's count in front
of the lookup, and rs are all the lookup's rounds. -/
structure Pos (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (n : Nat) (F : Fork) (rest : List Fmt.RoundView) :
    Prop where
  next : F.next = lo + slotsIn f n
  cut : rest = rs.drop (off f n)

variable {f : LFace} {lo : Nat} {rs : List Fmt.RoundView}

theorem drawsV_same {n : Nat} {F G : Fork} {r rest : List Fmt.RoundView} {x : Array E}
    (h : drawsV n F r = some (x, G, rest)) : G = F := by
  unfold drawsV at h
  cases r with
  | nil => exact nomatch h
  | cons r0 r' =>
    dsimp only at h
    split at h
    · obtain ⟨y, _, e⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at e
      exact e.2.1.symm
    · exact nomatch h

/-- **A stage that sends nothing**: its one round's samples, by the round's number. -/
theorem quiet_step {n k : Nat} {s : Stage} {F G : Fork} {rest rest' : List Fmt.RoundView} {x : Array E}
    (hs : (stages f)[n]? = some s) (hc : s.call f = none) (P : Pos f lo rs n F rest)
    (e : drawsV k F rest = some (x, G, rest')) :
    Pos f lo rs (n + 1) G rest' ∧ x.toList = many rs (firstRound f s) := by
  obtain ⟨a1, _, a3, _⟩ := drawsV_spec e
  have hr : s.rounds f = 1 := by simp [Stage.rounds, hc]
  have hsl : s.slots f = 0 := by simp [Stage.slots, Stage.own, Stage.tail, hc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [drawsV_same e, P.next, slotsIn_succ hs, hsl]
    rfl
  · rw [a1, P.cut, List.drop_drop, off_succ hs, hr]
  · rw [a3, P.cut, many_drop, off_at hs]
    rfl

/-! ## A sumcheck with end values -/

/-- What a stage with end values leaves. Here row is its row and sEnd its first end slot. -/
structure SumOut (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (s : Stage) (C row : Aff) (sEnd : Nat) :
    Prop where
  sEnd : sEnd = lo + firstSlot f s + s.own f
  /-- none of its own slots' coefficients is 0, where none of its variables' challenges is -/
  own : (∀ l, l < ((s.call f).map (·.vs.length)).getD 0 → vl (one rs (firstRound f s + 1 + l)) ≠ 0)
    →
    ∀ i, i < s.own f → sc row (lo + firstSlot f s + i) ≠ 0
  /-- on a slot in front: minus eps times the start form's coefficient -/
  front : ∀ j, j < lo + firstSlot f s → sc row j = - (vl (one rs (firstRound f s)) * sc C j)

/-- **A sumcheck with end values, from its return.** Here k0 is the stage's call, with points left
as stand-ins; k is the call in the run; `hb` says that the sample of Y reads as an element that is
not 0. -/
theorem whole_step {n : Nat} {s : Stage} {k0 k : Call} {C : Aff} {endTerm : List E → List E → E}
    {F G : Fork} {rest : List Fmt.RoundView} {h : Heard} {row : Aff}
    (hs : (stages f)[n]? = some s) (hk0 : s.call f = some k0)
    (hd : k.vs.map Var.d = k0.vs.map Var.d) (he : k.ends = k0.ends) (hne : k.ends.isSome = true)
    (hp : ∀ v ∈ k.vs, Pt v) (P : Pos f lo rs n F rest) (hC : In lo F.next C)
    (hw : MaskedSum.whole C k endTerm F (rest.take (vRoundsOf k)) = some (h, row, G))
    (hlen : vRoundsOf k ≤ rest.length) (hb : vl (h.r.getLastD zeroE) ≠ 0) :
    Pos f lo rs (n + 1) G (rest.drop (vRoundsOf k)) ∧ SumOut f lo rs s C row h.sEnd ∧
      In lo G.next row := by
  obtain ⟨lead, vs, ends⟩ := k
  obtain ⟨e, rfl⟩ : ∃ e, ends = some e := Option.isSome_iff_exists.1 hne
  obtain ⟨fs, _⟩ := slotsIn_at hs
  have hlo : lo ≤ F.next := by rw [P.next]; omega
  obtain ⟨w1, w2, w3⟩ := whole_names hw hC hlo
  obtain ⟨_, G1, _, _, hh, _, _⟩ := MaskedSum.whole_parts hw
  obtain ⟨_, _, n3, _, _⟩ := hear_names hh
  obtain ⟨d1, d2⟩ := whole_draws hw
  have hl0 : k0.lead = 0 := lead_zero s k0 hk0
  have hown : ownSlots (Call.all ⟨lead, vs, some e⟩) = s.own f := by
    rw [ownSlots_congr (all_map_d (k' := k0) hd he)]
    simp [Stage.own, hk0, ownRun, hl0]
  have htail : Call.endsN ⟨lead, vs, some e⟩ = s.tail f := by
    have he' : k0.ends = some e := he.symm
    simp [Stage.tail, hk0, he', Call.endsN]
  have hvl : vs.length = k0.vs.length := by
    have := congrArg List.length hd
    simpa using this
  have hro : vRoundsOf ⟨lead, vs, some e⟩ = s.rounds f := by
    have he' : k0.ends = some e := he.symm
    simp [Stage.rounds, hk0, VerifiableInference.Desc.K3.roundsOf, he', hvl]
  have hro' : vRoundsOf ⟨lead, vs, some e⟩ = vs.length + 3 := by simp
    [VerifiableInference.Desc.K3.roundsOf]
  have hF : F.next = lo + firstSlot f s := by rw [P.next, fs]
  have hone : ∀ a, a < vs.length + 3 →
      one (rest.take (vRoundsOf ⟨lead, vs, some e⟩)) a = one rs (firstRound f s + a) := by
    intro a ha
    rw [off_at hs, ← one_drop, ← P.cut]
    unfold one
    rw [List.map_take, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, w1⟩
  · rw [w3, n3, hown, htail, P.next, slotsIn_succ hs]
    unfold Stage.slots
    omega
  · rw [P.cut, List.drop_drop, off_succ hs, hro]
  · rw [n3, hown, hF]
  · intro hv i hi
    have hr : ∀ x ∈ h.r, vl x ≠ 0 := by
      intro x hx
      rw [d2] at hx
      obtain ⟨l, hl, ex⟩ := mem_seg hx
      by_cases hlv : l < vs.length
      · rw [ex, hone _ (by omega), ← Nat.add_assoc]
        refine hv l ?_
        simp [hk0, ← hvl, hlv]
      · have hl' : l = vs.length := by omega
        have hlast : h.r.getLastD zeroE = x := by
          rw [ex, d2, hl']
          unfold seg one
          have hlen' : vs.length + 3 ≤ ((rest.take (vRoundsOf ⟨lead, vs, some e⟩)).map e1).length :=
            by
            rw [List.length_map, List.length_take, hro']
            rw [hro'] at hlen
            omega
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take,
            List.length_drop,
            List.getElem?_take_of_lt (by omega), List.getElem?_drop, List.getD_eq_getElem?_getD]
          congr 2
          omega
        rw [← hlast]
        exact hb
    have := (whole_coef hw hC hp hr).1 (lo + firstSlot f s + i) (by omega) (by rw [hown]; omega)
    exact this
  · intro j hj
    obtain ⟨_, G1', sh, _, hh', _, hrow⟩ := MaskedSum.whole_parts hw
    rw [MaskedSum.row_spec hrow]
    have a := front_coef hh' hp (endTerm h.r sh) j (by omega)
    rw [a, d1, hone 0 (by omega)]
    rfl

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.getD0_headD
#print axioms ProofFile.Honest.K3.Good.many_head
#print axioms ProofFile.Honest.K3.Good.elemsAt_many
#print axioms ProofFile.Honest.K3.Good.value_many
#print axioms ProofFile.Honest.K3.Good.value_one
#print axioms ProofFile.Honest.K3.Good.vl_ne_zero
#print axioms ProofFile.Honest.K3.Good.vl_ne_one
#print axioms ProofFile.Honest.K3.Good.ne_of_fine
#print axioms ProofFile.Honest.K3.Good.take_all_left
#print axioms ProofFile.Honest.K3.Good.whole_draws
#print axioms ProofFile.Honest.K3.Good.open_draws
#print axioms ProofFile.Honest.K3.Good.mem_seg
#print axioms ProofFile.Honest.K3.Good.drawsV_same
#print axioms ProofFile.Honest.K3.Good.quiet_step
#print axioms ProofFile.Honest.K3.Good.whole_step
