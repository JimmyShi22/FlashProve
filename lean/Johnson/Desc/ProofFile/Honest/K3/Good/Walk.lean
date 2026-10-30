-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Walk.lean: the whole hearing of a lookup, from its return, at
any face: for every stage that is a sumcheck, the row that it leaves, with its coefficients as
`SumOut` tells them, and the form from which it starts. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md: see there stage, sumcheck, row, form, slot, ledger, hearing and
sample. In this file: f is the lookup's face, lo the ledger's count of slots in front of the lookup,
rs the rounds. `SumOut` (Honest/K3/Good/Step.lean) says what one sumcheck stage leaves; `Pos`
(there) where the hearing stands in front of a stage.

What is shown.
  `open_step`: a sumcheck without end values, whose row is made later: the coefficients of that row,
    at any end term.
  `rhoOf`, `tabStart`: the table side's first point; the form in front of the table side's level l.
  `HeardOut`, `heard_out`: the hearing, stage by stage; and which sampled element the eps of the
    leaves is.
Helpers: `drawV_draws`, `owe_all`, `slot_all`, `must_all`, `pos_zero`, `pos_of`. Each of the three
in the middle shares one clause, that on the ledger behind, with a lemma that stands elsewhere
(`owe_next`, Honest/K3/Shape/HeardWalk.lean; `slot_spec`, `must_spec`, Honest/K3/Law/GoesOn.lean),
and adds that the rounds are left as they were; the two of GoesOn.lean have a first clause of their
own.

Hypotheses that remain, in `heard_out`.
  `hokf`: the face passes the verifier's test on it (`Face.ok`).
  `hok`: every word of a sampled element is below the prime (`Ok`, Honest/K3/Good/Levels.lean).
  `h`: the hearing `messagesV` returns on the rounds.
In `open_step`: `hs`, `hk0`, `hd`, `hp`, `P`, `hC` as in `whole_step` (Step.lean); `he`: the call
has no end values; `hh`: the open sumcheck's hearing returns on its own rounds. In the helpers: `e`,
`h`: the routine returns; `P`, `h1`, `h2`: (in `pos_of`) the hearing stands there; the same count;
the same rounds.

Users. `goodGives` (Honest/K3/Good/Gives.lean) calls `heard_out`; so does
Honest/K3/Law/Thread/DigitsHeardLink.lean, for the field eps.

Limits. This file says what the rows are. That a slot is named with a coefficient that is not 0
follows from it in Gives.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open OnBytes (E zeroE oneE subE mulE okE isZeroE)
open OnBytes.Model (Fork Aff Reading orderDefault)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Call Ends Heard ownSlots rowAff)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3
    (HeardV Hr messagesV drawsV drawV sumV openV tieV partsV keysV leafVars
  bitsCall)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Forward (joinForm)
open ProofFile.Honest.K3.Parts (In in_ofConst in_slot in_mono in_joinForm hear_names atP_shift atP_alpha
    atP_join
  atP_tab atP_leaves atP_zero atP_bits jSplit jJoin jKey jTab)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {f : LFace} {lo : Nat} {rs : List Fmt.RoundView}

/-! ## A sumcheck without end values -/

/-- **A sumcheck without end values, from its return**: the coefficients of the row that is made of
its structure later, at any end term. -/
theorem open_step {n : Nat} {s : Stage} {k0 : Call} {vs : List Var} {C : Aff} {F G : Fork}
    {rest : List Fmt.RoundView} {h : Heard}
    (hs : (stages f)[n]? = some s) (hk0 : s.call f = some k0)
    (hd : vs.map Var.d = k0.vs.map Var.d) (he : k0.ends = none)
    (hp : ∀ v ∈ vs, Pt v) (P : Pos f lo rs n F rest) (hC : In lo F.next C)
    (hh : MaskedSum.hear C ⟨0, vs, none⟩ F (rest.take (vs.length + 1)) = some (h, G)) :
    Pos f lo rs (n + 1) G (rest.drop (vs.length + 1)) ∧
      ∀ S0, SumOut f lo rs s C (rowAff h S0 {}) h.sEnd := by
  obtain ⟨fs, _⟩ := slotsIn_at hs
  obtain ⟨_, _, n3, n4, _⟩ := hear_names hh
  obtain ⟨d1, d2⟩ := open_draws hh
  have hl0 : k0.lead = 0 := lead_zero s k0 hk0
  have hown : ownSlots (Call.all ⟨0, vs, none⟩) = s.own f := by
    rw [ownSlots_congr (all_map_d (k := ⟨0, vs, none⟩) (k' := k0) hd he.symm)]
    simp [Stage.own, hk0, ownRun, hl0]
  have htail : s.tail f = 0 := by simp [Stage.tail, hk0, he]
  have hvl : vs.length = k0.vs.length := by
    have := congrArg List.length hd
    simpa using this
  have hro : s.rounds f = vs.length + 1 := by
    simp [Stage.rounds, hk0, VerifiableInference.Desc.K3.roundsOf, he, hvl]
  have hF : F.next = lo + firstSlot f s := by rw [P.next, fs]
  have hone : ∀ a, a < vs.length + 1 →
      one (rest.take (vs.length + 1)) a = one rs (firstRound f s + a) := by
    intro a ha
    rw [off_at hs, ← one_drop, ← P.cut]
    unfold one
    rw [List.map_take, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]
  have n4' : G.next = h.sEnd + 0 := n4
  refine ⟨⟨?_, ?_⟩, fun S0 => ⟨?_, ?_, ?_⟩⟩
  · rw [n4', n3, hown, P.next, (slotsIn_at hs).2]
    unfold Stage.slots
    omega
  · rw [P.cut, List.drop_drop, off_succ hs, hro]
  · rw [n3, hown, hF]
  · intro hv i hi
    have hr : ∀ x ∈ h.r, vl x ≠ 0 := by
      intro x hx
      rw [d2] at hx
      obtain ⟨l, hl, ex⟩ := mem_seg hx
      rw [ex, hone _ (by omega), ← Nat.add_assoc]
      refine hv l ?_
      simp [hk0, ← hvl, hl]
    exact (record_coef hh hC hp hr S0).1 (lo + firstSlot f s + i) (by omega) (by rw [hown]; omega)
  · intro j hj
    rw [front_coef hh hp S0 j (by omega), d1, hone 0 (by omega)]
    rfl

/-! ## The whole hearing -/

/-- The table side's first point: what the round JOIN samples, read in reverse. -/
def rhoOf (f : LFace) (rs : List Fmt.RoundView) : Array E := (many rs (firstRound f .join)).toArray.reverse

/-- The form in front of the table side's level number l; at l := d: in front of the leaves. -/
def tabStart (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (sG : Array Nat) : Nat → Aff :=
  startOf f lo rs Stage.tab Stage.tabLine (joinForm f sG (rhoOf f rs))

/-- **What the hearing leaves**, stage by stage. Here lo is the ledger's count in front. -/
structure HeardOut (f : LFace) (lo : Nat) (rs : List Fmt.RoundView) (g : HeardV) : Prop where
  tie : ∀ t, t < f.planes - 1 → ∃ y ∈ g.rows.toList,
    SumOut f lo rs (.tie t) (tieStart f lo t) y (endOf f lo (.tie t))
  split : ∀ i, i < f.parts.length - 1 → ∃ y ∈ g.rows.toList,
    SumOut f lo rs (.split i) (splitStart f lo i) y (endOf f lo (.split i))
  key : ∀ i v m, f.parts[i]? = some v → m < v → ∃ y ∈ g.rows.toList,
    SumOut f lo rs (.key i m) (keyStart f lo rs i m) y (endOf f lo (.key i m))
  keys : ∀ i v, f.parts[i]? = some v → ∃ y ∈ g.keys, y.2 = keyStart f lo rs i v
  tab : ∃ sG : Array Nat, (∀ j, j < f.planes → sG.getD j 0 = planeSlot f lo j) ∧
    (∀ l, l < f.d → ∃ y ∈ g.rows.toList,
      SumOut f lo rs (.tab l) (tabStart f lo rs sG l) y (endOf f lo (.tab l))) ∧
    ∀ S0, SumOut f lo rs .leaves (tabStart f lo rs sG f.d) (rowAff g.leaves S0 {})
      (endOf f lo .leaves)
  bits : ∃ y ∈ g.rows.toList, SumOut f lo rs .bits (Aff.ofConst zeroE) y (endOf f lo .bits)
  sBit : g.sBit = endOf f lo .bits
  /-- the round JOIN samples mu elements -/
  rho : (many rs (firstRound f .join)).length = f.mu
  /-- the leaves' eps is the first element that the leaves' first round samples -/
  eps : g.leaves.eps = one rs (firstRound f .leaves)

theorem drawV_draws {F G : Fork} {r rest : List Fmt.RoundView} {x : E} (h : drawV F r = some (x, G, rest))
    :
    ∃ y, drawsV 1 F r = some (y, G, rest) := by
  unfold drawV at h
  split at h
  · rename_i y G' rest' e
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, a2, a3⟩ := h
      subst a2 a3
      exact ⟨y, e⟩
    · exact nomatch h
  · exact nomatch h

theorem owe_all {what : String} {F G : Fork} {r rest : List Fmt.RoundView} {a : Nat}
    (e : Hr.owe what F r = some (a, G, rest)) : G.next = F.next ∧ rest = r := by
  have e' : some ((F.owe what).1, (F.owe what).2, r) = some (a, G, rest) := e
  cases e'
  exact ⟨rfl, rfl⟩

theorem slot_all {F G : Fork} {r rest : List Fmt.RoundView} {a : Nat}
    (e : Hr.slot F r = some (a, G, rest)) : G = F ∧ rest = r := by
  have e' : some (F.next, F, r) = some (a, G, rest) := e
  cases e'
  exact ⟨rfl, rfl⟩

theorem must_all {b : Bool} {F G : Fork} {r rest : List Fmt.RoundView} {a : Unit}
    (e : Hr.must b F r = some (a, G, rest)) : G = F ∧ rest = r := by
  unfold Hr.must at e
  split at e
  · cases e
    exact ⟨rfl, rfl⟩
  · exact nomatch e

theorem pos_zero (f : LFace) (F : Fork) (rs : List Fmt.RoundView) : Pos f F.next rs 0 F rs :=
  ⟨by simp [slotsIn], by simp [off]⟩

theorem pos_of {n : Nat} {F F' : Fork} {r r' : List Fmt.RoundView} (P : Pos f lo rs n F r)
    (h1 : F'.next = F.next) (h2 : r' = r) : Pos f lo rs n F' r' :=
  ⟨by rw [h1]; exact P.next, by rw [h2]; exact P.cut⟩

/-- **The hearing, from its return.** -/
theorem heard_out {F G : Fork} {rest : List Fmt.RoundView} {g : HeardV} (hokf : f.ok = true) (hok : Ok rs)
    (h : messagesV f F rs = some (g, G, rest)) : HeardOut f F.next rs g := by
  have h2 : 2 ≤ f.planes := two_le_planes_of_ok f hokf
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1', h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2', h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3', h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4', h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5', h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6', h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7', h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8', h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9', h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10', h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11', h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12', h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13', h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14', h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15', h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16', h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17', h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18', h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  have hL : 1 ≤ f.parts.length := by
    simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at hokf
    have := hokf.1.1.1.1.2
    cases hp : f.parts with
    | nil => simp [hp] at this
    | cons a l => simp
  -- in front of the first stage
  obtain ⟨s1, s1'⟩ := slot_all e1'
  obtain ⟨w2, w2'⟩ := owe_all e2'
  obtain ⟨w3, w3'⟩ := owe_all e3'
  obtain ⟨w4, w4'⟩ := owe_all e4'
  have P4 : Pos f F.next rs 0 F4 r4 :=
    pos_of (pos_zero f F rs) (by rw [w4, w3, w2, s1]) (by rw [w4', w3', w2', s1'])
  -- the shift
  have P5 : Pos f F.next rs (oAlpha f) F5 r5 := by
    by_cases hsft : f.shifted = true
    · rw [if_pos hsft] at e5'
      obtain ⟨y, hy⟩ := drawV_draws e5'
      have := (quiet_step (atP_shift f hsft) rfl P4 hy).1
      have e : oAlpha f = 0 + 1 := by simp [oAlpha, hsft]
      rw [e]
      exact this
    · rw [if_neg hsft] at e5'
      obtain ⟨_, a2, a3⟩ := pure_spec e5'
      have e : oAlpha f = 0 := by simp [oAlpha, hsft]
      rw [e]
      exact pos_of P4 (by rw [a2]) a3
  -- alpha
  obtain ⟨y6, hy6⟩ := drawV_draws e6'
  have P6 : Pos f F.next rs (iTie f 0) F6 r6 := (quiet_step (atP_alpha f) rfl P5 hy6).1
  -- the tie
  obtain ⟨P7, T7, n7⟩ := tie_out h2 hok P6 e7'
  have hle := le_e0 f F.next
  -- the parts' steps
  obtain ⟨P8, k8, S8, R8, L8, I8, n8⟩ := parts_out hok (f.parts.length - 1) 0 rows (Aff.slot sZ) F7
    r7
    rows2 roots F8 r8 (by omega) P7 (by rw [T7.sZ]; rfl)
    (in_slot (by rw [T7.sZ]; exact hle) (by rw [T7.sZ, n7]; omega)) e8'
  -- JOIN
  obtain ⟨P9, hjo⟩ := quiet_step (atP_join f) rfl P8 e9'
  have f9 : F9 = F8 := Law.drawsV_same e9'
  have P9' : Pos f F.next rs (jKey f 0 0) F9 r9 := by
    have e : jKey f 0 0 = jJoin f + 1 := by simp [jKey]
    rw [e]
    exact P9
  -- the key trees
  obtain ⟨P10, k10, K10, KF10, n10⟩ := keys_out hok f.parts 0 roots rows2 F9 r9 rows3 keys F10 r10
    (by simp) (by rw [L8]; omega)
    (fun t ht => R8 t (by omega)) (fun C hC => by rw [f9]; exact I8 C hC) P9' e10'
  obtain ⟨m11, m11'⟩ := must_all e11'
  have P11 : Pos f F.next rs (jTab f 0) F11 r11 := by
    have e : jKey f (0 + f.parts.length) 0 = jTab f 0 := by simp [jKey, jTab]
    rw [← e]
    exact pos_of P10 (by rw [m11]) m11'
  -- the table side
  have hsG : ∀ j, j < f.planes → F.next ≤ sG.getD j 0 ∧ sG.getD j 0 < F11.next := by
    intro j hj
    rw [T7.sG j hj, m11]
    have hF : F7.next ≤ F10.next := by rw [f9] at n10; omega
    unfold planeSlot curOf
    split <;> omega
  have e12'' : vRun f.mu f.d orderDefault
      { rows := rows3, point := jo.reverse, form := joinForm f sG jo.reverse } F11 r11 =
      some (table, F12, r12) := e12'
  obtain ⟨P12, Q12, I12, n12⟩ := run_out (A := Stage.tab) (B := Stage.tabLine) (m0 := f.mu)
    (s := { rows := rows3, point := jo.reverse, form := joinForm f sG jo.reverse }) hok P11
    (in_joinForm f sG _ hsG) f.d
    (fun l hl => by
      obtain ⟨x1, x2⟩ := atP_tab f hl
      have e : jTab f l = jTab f 0 + 2 * l := by unfold jTab; omega
      rw [e] at x1 x2
      exact ⟨x1, x2, rfl, rfl⟩) e12''
  have hrho : jo.reverse = rhoOf f rs := by
    unfold rhoOf
    rw [← hjo]
  obtain ⟨m13, m13'⟩ := must_all e13'
  have P13 : Pos f F.next rs (jTab f f.d) F13 r13 := by
    have e : jTab f f.d = jTab f 0 + 2 * f.d := by unfold jTab; omega
    rw [e]
    exact pos_of P12 (by rw [m13]) m13'
  -- the leaves
  have hh14 := openV_hear e14'
  obtain ⟨c14, _, _, _⟩ := openV_spec e14'
  have hdL : (leafVars f table.point).map Var.d = (leafVars f #[]).map Var.d := by
    simp only [leafVars, List.map_map]
    rfl
  obtain ⟨P14, O14⟩ := open_step (k0 := { lead := 0, vs := leafVars f #[], ends := none })
    (atP_leaves f) rfl hdL rfl
    (fun v hv => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hv
      exact ⟨_, _, rfl⟩) P13 (by rw [m13]; exact I12) hh14
  rw [← c14] at P14
  -- ZERO
  obtain ⟨P15, _⟩ := quiet_step (atP_zero f) rfl P14 e15'
  obtain ⟨_, _, _, z15⟩ := drawsV_spec e15'
  -- the bits
  have hdB : (bitsCall ze.reverse.toList).vs.map Var.d =
      (bitsCall (List.replicate (f.mu + f.d) zeroE)).vs.map Var.d := by
    simp only [bitsCall, List.map_map]
    show ze.reverse.toList.map (fun _ => 3) = (List.replicate (f.mu + f.d) zeroE).map (fun _ => 3)
    rw [List.map_const', List.map_const', List.length_replicate]
    simp [z15]
  obtain ⟨_, O16, _, _⟩ := sum_step (k := bitsCall ze.reverse.toList) (atP_bits f) rfl hdB rfl rfl
    (fun v hv => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hv
      exact ⟨_, 3, rfl⟩) hok P15 (in_ofConst _ _ _) e16'
  -- all together
  have up : ∀ y ∈ table.rows.toList, y ∈ g.rows.toList := by
    intro y hy
    rw [hg]
    exact mem_push_of hy
  have up3 : ∀ y ∈ rows3.toList, y ∈ g.rows.toList := fun y hy => up y (Q12.keep y hy)
  have up2 : ∀ y ∈ rows2.toList, y ∈ g.rows.toList := fun y hy => up3 y (k10 y hy)
  have up1 : ∀ y ∈ rows.toList, y ∈ g.rows.toList := fun y hy => up2 y (k8 y hy)
  refine ⟨?_, ?_, ?_, ?_, ⟨sG, T7.sG, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨y, hy, hS⟩ := T7.row t ht
    exact ⟨y, up1 y hy, hS⟩
  · intro i hi
    obtain ⟨y, hy, hS⟩ := S8 i (Nat.zero_le i) hi
    exact ⟨y, up2 y hy, hS⟩
  · intro i v m hv hm
    obtain ⟨y, hy, hS⟩ := K10 i v m (Nat.zero_le i) hv hm
    exact ⟨y, up3 y hy, hS⟩
  · intro i v hv
    obtain ⟨y, hy, e⟩ := KF10 i v (Nat.zero_le i) hv
    refine ⟨y, ?_, e⟩
    rw [hg]
    exact hy
  · intro l hl
    obtain ⟨y, hy, hS⟩ := Q12.row l hl
    refine ⟨y, up y hy, ?_⟩
    unfold tabStart
    rw [← hrho]
    exact hS
  · intro S0
    have a := O14 S0
    have e : leaves.sEnd = endOf f F.next .leaves := a.sEnd
    rw [hg]
    show SumOut f F.next rs .leaves _ (rowAff leaves S0 {}) _
    unfold tabStart
    rw [← hrho, ← Q12.form, ← e]
    exact a
  · refine ⟨bits.2, ?_, ?_⟩
    · rw [hg]
      exact mem_push_self _ _
    · have e : bits.1.sEnd = endOf f F.next .bits := O16.sEnd
      rw [← e]
      exact O16
  · rw [hg]
    exact O16.sEnd
  · rw [← hjo]
    exact (drawsV_spec e9').2.2.2
  · rw [hg]
    show leaves.eps = one rs (firstRound f .leaves + 0)
    rw [(open_draws hh14).1, off_at (atP_leaves f), ← one_drop, ← P13.cut]
    unfold one
    rw [List.map_take, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega)]

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.open_step
#print axioms ProofFile.Honest.K3.Good.drawV_draws
#print axioms ProofFile.Honest.K3.Good.owe_all
#print axioms ProofFile.Honest.K3.Good.slot_all
#print axioms ProofFile.Honest.K3.Good.must_all
#print axioms ProofFile.Honest.K3.Good.pos_zero
#print axioms ProofFile.Honest.K3.Good.pos_of
#print axioms ProofFile.Honest.K3.Good.heard_out
