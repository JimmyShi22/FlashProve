-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LookHeard.lean: the honest side of the kind "lookup" (K3).
Conditional on `StageStep` and `LeavesStep` (Honest/K3/Law/Statements.lean: statements, not proved
in this file), on one part of keys, and on the course's rounds being cut by stage (`Cut`,
Honest/K3/Law/Walk.lean): the verifier's hearing returns on the course's rounds; what it heard is
the run's; the invariant holds behind the last stage; the leaves' own slots are free there; and, if
the stages' summands sum as they should, every row that was heard is worth 0 in every later world,
and the leaves' row, whenever it is made later, is worth what `LeavesStep` says. Theorems, with one
definition.

Terms. Honest/K3/GLOSSARY.md ("course", "hearing", "stage", "tie", "world, worth").

What is shown.
  `front_walk`: the shift, where there is one, and alpha.
  `tie_walk`: the tie: its first step and its fold.
  `join_walk`: JOIN.
  `keys_walk`, `tab_walk`: the two runs of levels (`run_walk`, Walk.lean, at their letters).
  `lookHeard_of_steps`: the assembly, over `messagesV_intro` (Honest/K3/Law/Forward.lean).

Hypotheses that remain. Three are assumed: `StageStep` (`SS`), `LeavesStep` (`LS`), `Cut` (`C`).
Besides: one part of keys (`hp`); `Fit` (`hF`); the invariant in front of the first stage (`I0`; in
the walks `I`: the invariant in front of the walk's first stage; `g0`: `RowsGood` of the rows so
  far).
  In the helpers: `h2`, `hj`, `hl`, `hm`: ranges of planes, steps and levels; `h`: a list's cut, a
    stage's number, two functions that agree, or (in `join_eq`) that the array holds the planes'
    slots.
  `StageStep`, `LeavesStep`. Shown in: `stageStep` and `leavesStep` (Honest/K3/Law/StageStep.lean),
    conditional on `HB`; `stageStepP` and `leavesStepP` (Honest/K3/Law/HBPaid.lean), without `HB`,
    resting on the theorems of Honest/SumLaw/.
  `Cut`. Shown in: `cut_of_rounds` (Honest/K3/Law/CutOf.lean), from `Fit R` and `R.rounds = some x`.

How the proof goes. Along the way each piece of `messagesV` is heard at the stage's call in the run
(`Course.call`), which is the stage's shape with the verifier's own variables at the points of
Honest/K3/Heard.lean (`walk_call_eq`, Walk.lean).

Users. This file is imported by Honest/K3/Good/Step.lean and Honest/K3/Law/LookHeardOne.lean.

Limits. One part of keys.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Walk
import Johnson.Desc.Part.MaskedSumFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE addE subE mulE isZeroE)
open OnBytes.Model (Reading Aff Fork eqTab orderDefault)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV noVar
  leafVars
  bitsCall)
open VerifiableInference.Desc.First.ProdV
  (layBack levelVars stepDown LevelOut level Carried levelEnds
  elementsAlone)
open ProofFile.Honest.K3.Forward

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run
local notation "vRoundsOf" => VerifiableInference.Desc.K3.roundsOf

variable {W : Type}

/-! ## Small helpers -/

/-- The three debts that the hearing lays first leave all that the invariant reads. -/
theorem inv_owed3 {R : Course W} {n : Nat} {F : Fork} (I : Inv R n F) : Inv R n (owed3 F) :=
  ⟨I.sized, I.next, I.room, I.free, I.filled, fun H mask entry hl =>
    I.ends H mask entry ⟨hl.next, hl.ns, hl.sized, hl.keep⟩⟩

theorem one_of_drop {x rest : List Fmt.RoundView} {a : Nat} {r : Fmt.RoundView} (h : x.drop a = r :: rest) :
    one x a = e1 r := one_of_get (drop_cons h).2.2

theorem many_of_drop {x rest : List Fmt.RoundView} {a : Nat} {r : Fmt.RoundView} (h : x.drop a = r :: rest) :
    many x a = r.drawn.elems.map E.ofTriple := by
  simp [many, (drop_cons h).2.2]

theorem getD_push (a : Array Nat) (y i : Nat) :
    (a.push y).getD i 0 = if i = a.size then y else a.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> simp

theorem foldl_congr' {α β : Type} (g g' : β → α → β) (l : List α) (b : β)
    (h : ∀ b a, g b a = g' b a) : l.foldl g b = l.foldl g' b := by
  have : g = g' := funext fun b => funext fun a => h b a
  rw [this]

/-- The slot whose hidden value the tie's step j + 1 takes apart. -/
def cur (R : Course W) : Nat → Nat
  | 0 => R.endSlot (.tie 0) + 1
  | n + 1 => R.endSlot (.tie (n + 1))

theorem form_tie (R : Course W) (j : Nat) : R.form (.tie (j + 1)) = Aff.slot (cur R j) := by
  cases j <;> rfl

theorem join_eq (R : Course W) (sG : Array Nat)
    (h : ∀ i, i < R.f.planes → sG.getD i 0 = R.planeSlot i) :
    joinForm R.f sG R.pts.rhoT = R.join := by
  unfold joinForm Course.join
  apply foldl_congr'
  intro c j
  by_cases hj : j < R.f.planes
  · simp only [if_pos hj, h j hj]
  · simp only [if_neg hj]

theorem tabPt_size (f : LFace) (b : Nat) (hd : List Fmt.Drawn) (l : Nat) :
    ((ptsOf f b hd).tabPt l).size = f.mu + l := by
  cases l with
  | zero => simp [ptsOf, drawsAt]
  | succ l =>
    show (behind _ _ _ _).size = _
    simp [behind, VerifiableInference.Desc.First.ProdV.layBack_size]
    omega

section Walk
variable (SS : StageStep) (LS : LeavesStep) {R : Course W} {x : List Fmt.RoundView} (v : Nat)
  (hp : R.f.parts = [v]) (hF : Fit R) (C : Cut R x)

/-! ## Rounds in front, at one part -/

include hp in
theorem off_alpha : off R.f (oAlpha R.f) = oAlpha R.f :=
  (off_at (at_alpha R.f v hp)).symm.trans (fr_alpha R.f v hp)

include hp in
theorem off_join : off R.f (iJoin R.f) = oJoin R.f :=
  (off_at (at_join R.f v hp)).symm.trans (fr_join R.f v hp)

include hp in
theorem off_iTab {l : Nat} (hl : l ≤ R.f.d) : off R.f (iTab R.f v l) = oTab R.f v + K R.f.mu l := by
  rcases Nat.lt_or_ge l R.f.d with h | h
  · exact (off_at (at_tab R.f v hp h)).symm.trans (fr_tab R.f v hp h)
  · have : l = R.f.d := by omega
    subst this
    exact (off_at (at_leaves R.f v hp)).symm.trans (fr_leaves R.f v hp)

include hp in
theorem off_iKey {m : Nat} (hm : m ≤ v) : off R.f (iKey R.f m) = oKey R.f + K 0 m := by
  rcases Nat.lt_or_ge m v with h | h
  · exact (off_at (at_key R.f v hp h)).symm.trans (fr_key R.f v hp h)
  · have : m = v := by omega
    subst this
    have e : iKey R.f m = iTab R.f m 0 := by simp [iTab]
    rw [e, off_iTab m hp (Nat.zero_le _)]
    rfl

include hp in
theorem off_zero : off R.f (iTab R.f v R.f.d + 1) = oZero R.f v :=
  (off_at (at_zero R.f v hp)).symm.trans (fr_zero R.f v hp)

include hp C in
theorem len_x : oEnd R.f v ≤ x.length := by
  rw [C.len, rounds_all R.f v hp]

/-! ## The calls, as the verifier's text writes them -/

include hp hF in
theorem call_tie0 (h2 : 2 ≤ R.f.planes) : R.call (.tie 0) = noVar 3 3 :=
  walk_call_eq R v hp hF (mem_at (at_tie R.f v hp (j := 0) (by omega))) (k := noVar 3 3) rfl

include hp hF in
theorem call_tieS {j : Nat} (hj : j + 1 < R.f.planes - 1) : R.call (.tie (j + 1)) = noVar 3 2 :=
  walk_call_eq R v hp hF (mem_at (at_tie R.f v hp hj)) (k := noVar 3 2) rfl

include hp hF in
theorem call_key {l : Nat} (hl : l < v) : R.call (.key 0 l) =
    ⟨0, levelVars l (R.pts.keyPt 0 l) (R.f.orders 0 l), some levelEnds⟩ :=
  walk_call_eq R v hp hF (mem_at (at_key R.f v hp hl)) (k := levelCall l) rfl

include hp hF in
theorem call_tab {l : Nat} (hl : l < R.f.d) : R.call (.tab l) =
    ⟨0, levelVars (R.f.mu + l) (R.pts.tabPt l) (orderDefault (R.f.mu + l)), some levelEnds⟩ :=
  walk_call_eq R v hp hF (mem_at (at_tab R.f v hp hl)) (k := levelCall (R.f.mu + l)) rfl

include hp hF in
theorem call_leaves : R.call .leaves =
    { lead := 0, vs := leafVars R.f (R.pts.tabPt R.f.d), ends := none } :=
  walk_call_eq R v hp hF (mem_at (at_leaves R.f v hp))
    (k := { lead := 0, vs := leafVars R.f #[], ends := none }) rfl

include hp hF in
theorem call_bits : R.call .bits = bitsCall R.pts.zeroPt.toList :=
  walk_call_eq R v hp hF (mem_at (at_bits R.f v hp))
    (k := bitsCall (List.replicate (R.f.mu + R.f.d) zeroE)) rfl

/-! ## The shift and alpha -/

include hp hF C in
theorem front_walk {F : Fork} (I : Inv R 0 F) :
    (if R.f.shifted then drawV else pure zeroE : Hr E) F x =
        some (R.pts.theta, F, x.drop (off R.f (oAlpha R.f))) ∧
      drawV F (x.drop (off R.f (oAlpha R.f))) =
        some (R.pts.alpha, F, x.drop (off R.f (iTie R.f 0))) ∧ Inv R (iTie R.f 0) F := by
  have hl := len_x v hp C
  have I1 : (if R.f.shifted then drawV else pure zeroE : Hr E) F x =
      some (R.pts.theta, F, x.drop (off R.f (oAlpha R.f))) ∧ Inv R (oAlpha R.f) F := by
    rw [pts_eq hF C, theta_all R.f v hp _ _ x hl]
    by_cases hs : R.f.shifted = true
    · obtain ⟨r, a, q, I'⟩ := quiet_step C (at_shift R.f v hp hs) rfl I
      have h0 : off R.f 0 = 0 := rfl
      have h1 : oAlpha R.f = 1 := by simp [oAlpha, hs]
      rw [h0, List.drop_zero] at a
      have a' : x.drop 0 = r :: x.drop (off R.f (0 + 1)) := by rw [List.drop_zero]; exact a
      simp only [if_pos hs, h1]
      rw [one_of_drop a']
      refine ⟨?_, I'⟩
      conv_lhs => rw [a]
      exact drawV_ret q F _
    · have h1 : oAlpha R.f = 0 := by simp [oAlpha, hs]
      have h0 : off R.f 0 = 0 := rfl
      simp only [if_neg hs, h1, h0, List.drop_zero]
      exact ⟨rfl, I⟩
  obtain ⟨e5, I5⟩ := I1
  obtain ⟨r, a, q, I'⟩ := quiet_step C (at_alpha R.f v hp) rfl I5
  refine ⟨e5, ?_, I'⟩
  have ha : R.pts.alpha = e1 r := by
    rw [pts_eq hF C, alpha_all R.f v hp _ _ x hl]
    rw [off_alpha v hp] at a
    exact one_of_drop a
  rw [ha, a]
  exact drawV_ret q F _

/-! ## The tie -/

include SS hp hF C in
theorem tie_walk {F : Fork} (I : Inv R (iTie R.f 0) F) :
    ∃ rows sG G, tieV R.f.planes R.factor F (x.drop (off R.f (iTie R.f 0))) =
        some ((rows, R.endSlot (.tie 0), sG), G, x.drop (off R.f (iJoin R.f))) ∧
      rows.size = R.f.planes - 1 ∧ (∀ i, i < R.f.planes → sG.getD i 0 = R.planeSlot i) ∧
      Inv R (iJoin R.f) G ∧ RowsGood R rows G ∧ Later F G := by
  have h2 : 2 ≤ R.f.planes := two_le_planes_of_ok R.f hF.ok
  obtain ⟨xs, h0, row0, G0, a, b, al, w, y, z, I1, lt0, zr0⟩ :=
    sum_step SS hF C (at_tie R.f v hp (j := 0) (by omega)) (show 0 < 3 by omega) I
  rw [call_tie0 v hp hF h2] at w
  rw [rounds_tie] at b
  have s1 := sumV_ret (k := noVar 3 3) w b al y (x.drop (off R.f (iTie R.f 0 + 1)))
  rw [← a] at s1
  -- The fold.
  let P : Nat → (Array Aff × Nat × Array Nat) → Fork → List Fmt.RoundView → Prop := fun j s F' rs =>
    Inv R (iTie R.f (j + 1)) F' ∧ rs = x.drop (off R.f (iTie R.f (j + 1))) ∧ s.2.1 = cur R j ∧
      s.1.size = j + 1 ∧ s.2.2.size = j + 1 ∧ (∀ i, i ≤ j → s.2.2.getD i 0 = R.planeSlot i) ∧
      RowsGood R s.1 F' ∧ Later F F'
  have hP0 : P 0 (#[row0], h0.sEnd + 1, #[h0.sEnd + 2]) G0 (x.drop (off R.f (iTie R.f 0 + 1))) := by
    refine ⟨I1, rfl, by show h0.sEnd + 1 = _; rw [z]; rfl, rfl, rfl, ?_,
      (rowsGood_empty R G0).push (mem_at (at_tie R.f v hp (j := 0) (by omega)))
        (show 0 < 3 by omega) zr0,
      lt0⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    show h0.sEnd + 2 = _
    rw [z]
    simp [Course.planeSlot]
  obtain ⟨s, G, rs', e2, I', hrs, hc, q1, q2, q3, gd, lt⟩ :=
    foldlM_ret (f := fun s (_ : Nat) => tieStep s) P (List.range (R.f.planes - 2)) 0 _ G0 _
      (by
        intro j hj s F rs hPj
        rw [List.length_range] at hj
        rw [Nat.zero_add] at hPj ⊢
        obtain ⟨I, hrs, hc, q1, q2, q3, gd, lt⟩ := hPj
        obtain ⟨xs, h, row, G, a, b, al, w, y, z, I', lt', zr⟩ :=
          sum_step SS hF C (at_tie R.f v hp (j := j + 1) (by omega)) (show 0 < 2 by omega) I
        rw [call_tieS v hp hF (by omega), form_tie, ← hc] at w
        rw [rounds_tie] at b
        have sv := sumV_ret (k := noVar 3 2) w b al y (x.drop (off R.f (iTie R.f (j + 1) + 1)))
        rw [← a, ← hrs] at sv
        refine ⟨(s.1.push row, h.sEnd, s.2.2.push (h.sEnd + 1)), G, _,
          (bind_ret sv).trans rfl, I', rfl, z, by simp [q1], by simp [q2], ?_,
          (gd.later lt').push (mem_at (at_tie R.f v hp (j := j + 1) (by omega)))
            (show 0 < 2 by omega) zr, lt.trans lt'⟩
        intro i hi
        show (s.2.2.push (h.sEnd + 1)).getD i 0 = _
        rw [getD_push, q2]
        by_cases hij : i = j + 1
        · subst hij
          rw [if_pos rfl, z]
          have h3 : j + 1 + 1 < R.f.planes := by omega
          simp [Course.planeSlot, h3]
        · rw [if_neg hij]
          exact q3 i (by omega)) hP0
  rw [Nat.zero_add, List.length_range] at I' hrs hc q1 q2 q3
  have hi : iTie R.f (R.f.planes - 2 + 1) = iJoin R.f := by
    unfold iTie iJoin
    omega
  rw [hi] at I' hrs
  have tv := tieV_ret (w := R.f.planes) (a := R.factor) s1 e2
  rw [hrs, z] at tv
  refine ⟨_, _, G, tv, by rw [q1]; omega, ?_, I', gd, lt⟩
  intro i hi
  rw [getD_push, q2]
  by_cases hij : i = R.f.planes - 2 + 1
  · rw [if_pos hij, hc]
    have h3 : ¬ (i + 1 < R.f.planes) := by omega
    have h4 : i ≠ 0 := by omega
    by_cases h5 : R.f.planes = 2
    · have h6 : R.f.planes - 2 = 0 := by omega
      rw [h6]
      simp [Course.planeSlot, h4, h5, cur]
    · obtain ⟨n, hn⟩ : ∃ n, R.f.planes - 2 = n + 1 := ⟨R.f.planes - 3, by omega⟩
      rw [hn]
      simp [Course.planeSlot, h3, h4, h5, cur, hn]
  · rw [if_neg hij]
    exact q3 i (by omega)

/-! ## JOIN -/

include hp hF C in
theorem join_walk {F : Fork} (I : Inv R (iJoin R.f) F) :
    ∃ jo, drawsV R.f.mu F (x.drop (off R.f (iJoin R.f))) =
        some (jo, F, x.drop (off R.f (iKey R.f 0))) ∧ jo.reverse = R.pts.rhoT ∧
      Inv R (iKey R.f 0) F := by
  obtain ⟨r, a, q, I'⟩ := quiet_step C (at_join R.f v hp) rfl I
  refine ⟨_, by rw [a]; exact drawsV_ret q F _, ?_, I'⟩
  rw [off_join v hp] at a
  have hm := many_of_drop a
  rw [pts_eq hF C, rhoT_all R.f v hp _ _ x (len_x v hp C) (by rw [hm]; simpa using q.elems), hm]

/-! ## The two runs of levels -/

include SS hp hF C in
theorem keys_walk (rows0 : Array Aff) {F : Fork} (I : Inv R (iKey R.f 0) F)
    (g0 : RowsGood R rows0 F) :
    ∃ c G, vRun 0 v (R.f.orders 0) { rows := rows0, point := #[], form := R.form (.key 0 0) } F
        (x.drop (off R.f (iKey R.f 0))) = some (c, G, x.drop (off R.f (iTab R.f v 0))) ∧
      c.point = R.pts.keyPt 0 v ∧ c.form = R.form (.key 0 v) ∧ c.rows.size = rows0.size + v ∧
      Inv R (iTab R.f v 0) G ∧ RowsGood R c.rows G ∧ Later F G := by
  have hix : ∀ l, iKey R.f 0 + 2 * l = iKey R.f l := fun l => by unfold iKey; omega
  have := run_walk SS hF C 0 (R.f.orders 0) (fun l => .key 0 l) (fun l => .keyLine 0 l)
    (iKey R.f 0) (fun l => R.pts.keyPt 0 l) (fun l => R.form (.key 0 l)) v
    (fun l hl => by rw [hix]; exact at_key R.f v hp hl)
    (fun l hl => by rw [hix]; exact at_keyLine R.f v hp hl)
    (fun l hl => by rw [Nat.zero_add]; exact call_key v hp hF hl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun l hl => by
      dsimp only
      rw [off_iKey v hp (Nat.zero_le _), lastPt_drop, pts_eq hF C,
        keyPt_all R.f v hp _ _ x (len_x v hp C) hl]
      rfl)
    (fun _ _ => show 0 < 2 by omega)
    (fun l _ => by rw [rounds_key]; omega)
    (fun _ _ => rfl) (fun _ _ => rfl) rows0 F I g0 v (Nat.le_refl _)
  rw [hix] at this
  exact this

include SS hp hF C in
theorem tab_walk (rows0 : Array Aff) {F : Fork} (I : Inv R (iTab R.f v 0) F)
    (g0 : RowsGood R rows0 F) :
    ∃ c G, vRun R.f.mu R.f.d orderDefault
        { rows := rows0, point := R.pts.rhoT, form := R.join } F
        (x.drop (off R.f (iTab R.f v 0))) = some (c, G, x.drop (off R.f (iTab R.f v R.f.d))) ∧
      c.point = R.pts.tabPt R.f.d ∧ c.form = R.tabForm R.f.d ∧
      c.rows.size = rows0.size + R.f.d ∧ Inv R (iTab R.f v R.f.d) G ∧ RowsGood R c.rows G ∧
      Later F G := by
  have hix : ∀ l, iTab R.f v 0 + 2 * l = iTab R.f v l := fun l => by unfold iTab; omega
  have hj : (many x (oJoin R.f)).length = R.f.mu := by
    obtain ⟨r, e, q⟩ := C.quiet .join (mem_at (at_join R.f v hp)) rfl
    obtain ⟨a, _, _⟩ := split_at C (at_join R.f v hp)
    rw [e, off_join v hp] at a
    rw [many_of_drop a]
    simpa using q.elems
  have := run_walk SS hF C R.f.mu orderDefault (fun l => .tab l) (fun l => .tabLine l)
    (iTab R.f v 0) (fun l => R.pts.tabPt l) (fun l => R.tabForm l) R.f.d
    (fun l hl => by rw [hix]; exact at_tab R.f v hp hl)
    (fun l hl => by rw [hix]; exact at_tabLine R.f v hp hl)
    (fun l hl => call_tab v hp hF hl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun l hl => by
      dsimp only
      rw [off_iTab v hp (Nat.zero_le _), lastPt_drop, pts_eq hF C,
        tabPt_all R.f v hp _ _ x (len_x v hp C) hj hl,
        tabPt_all R.f v hp _ _ x (len_x v hp C) hj (Nat.zero_le _)]
      rfl)
    (fun _ _ => show 0 < 2 by omega)
    (fun l _ => rounds_tab R.f l)
    (fun _ _ => rfl) (fun _ _ => rfl) rows0 F I g0 R.f.d (Nat.le_refl _)
  rw [hix] at this
  exact this

end Walk

/-! ## The assembly -/

theorem form_key0 (R : Course W) (v : Nat) (hp : R.f.parts = [v]) :
    R.form (.key 0 0) = Aff.slot (R.endSlot (.tie 0)) := by
  show R.root 0 = _
  simp [Course.root, hp]

theorem slotsIn_at {f : LFace} {n : Nat} {s : Stage} (h : (stages f)[n]? = some s) :
    firstSlot f s = slotsIn f n ∧ slotsIn f (n + 1) = slotsIn f n + s.slots f := by
  obtain ⟨hn, e⟩ := List.getElem?_eq_some_iff.1 h
  constructor
  · rw [← e]
    exact firstSlot_getElem f n hn
  · unfold slotsIn
    rw [take_succ_get h]
    simp

/-- **Conditional on `StageStep`, on `LeavesStep`, on one part of keys and on `Cut`: the verifier's
hearing returns on the course's rounds**, from a ledger at which the invariant holds in front of the
first stage; what it heard is the run's; the invariant holds behind the last stage; the leaves' own
slots are free there; the rows heard are `RowsGood`; the leaves' row, made later, is worth what
`LeavesStep` says. -/
theorem lookHeard_of_steps (SS : StageStep) (LS : LeavesStep) (R : Course W) (F : Fork)
    (x : List Fmt.RoundView) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R) (I0 : Inv R 0 F)
    (C : Cut R x) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      RowsGood R g.rows G ∧
      (∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
        ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
          Sized F' → Later G F' → MaskedSum.row g.leaves oneE {} F' = some (y, G') →
          Later G' H → MasksAre R mask →
          y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd g.leaves.eps * (1 - cf)) := by
  have h2 := two_le_planes_of_ok R.f hF.ok
  obtain ⟨e5, e6, I6⟩ := front_walk v hp hF C (inv_owed3 I0)
  obtain ⟨rows, sG, F7, e7, hrows, hsG, I7, g7, _⟩ := tie_walk SS v hp hF C I6
  obtain ⟨jo, e9, hjo, I9⟩ := join_walk v hp hF C I7
  obtain ⟨c, F10, e10, pc, fc, rc, I10, g10, _⟩ := keys_walk SS v hp hF C rows I9 g7
  obtain ⟨table, F12, e12, ptb, ftb, rtb, I12, g12, _⟩ := tab_walk SS v hp hF C c.rows I10 g10
  -- The leaves.
  obtain ⟨xs, lv, F14, a14, b14, al14, w14, r14, f14, I14, free14, lt14, last14⟩ :=
    leaves_step LS hF C (at_leaves R.f v hp) I12
  rw [call_leaves v hp hF] at w14
  rw [rounds_leaves] at b14
  have e14 := openV_ret w14 (by rw [b14]; simp [leafVars]) al14
    (x.drop (off R.f (iTab R.f v R.f.d + 1)))
  rw [← a14, ← ptb] at e14
  have hfl : R.form .leaves = table.form := ftb.symm
  rw [hfl] at e14
  -- ZERO
  obtain ⟨rz, az, qz, I15⟩ := quiet_step C (at_zero R.f v hp) rfl I14
  have e15 := drawsV_ret qz F14 (x.drop (off R.f (iTab R.f v R.f.d + 1 + 1)))
  rw [← az] at e15
  have hz : ((rz.drawn.elems.map E.ofTriple).toArray).reverse = R.pts.zeroPt := by
    rw [off_zero v hp] at az
    have hm := many_of_drop az
    rw [pts_eq hF C, zeroPt_all R.f v hp _ _ x (len_x v hp C) (by rw [hm]; simpa using qz.elems),
      hm]
  -- The bits.
  obtain ⟨xb, hb, rowb, F16, ab, bb, alb, wb, yb, zb, I16, lt16, zr16⟩ :=
    sum_step SS hF C (at_bits R.f v hp) (show 0 < 1 by omega) I15
  have wa := MaskedSum.whole_writesAbove I15.sized wb
  rw [call_bits v hp hF, ← hz] at wb
  have qe : rz.drawn.elems.length = R.f.mu + R.f.d := qz.elems
  have e16 := sumV_ret wb (by
    rw [bb, rounds_bits]
    simp [VerifiableInference.Desc.K3.roundsOf, bitsCall, qe]) alb yb
    (x.drop (off R.f (iTab R.f v R.f.d + 2 + 1)))
  rw [← ab] at e16
  have hlen : iTab R.f v R.f.d + 2 + 1 = (stages R.f).length := (stages_len R.f v hp).symm
  have hend : x.drop (off R.f (iTab R.f v R.f.d + 2 + 1)) = [] := by
    rw [hlen, off_len, ← C.len]
    exact List.drop_length
  rw [hend] at e16
  rw [form_key0 R v hp] at e10
  rw [← join_eq R sG hsG, ← hjo] at e12
  have hsz : table.point.size = R.f.mu + R.f.d := by
    rw [ptb]
    exact tabPt_size R.f R.a.base (R.t.heard ++ R.ds) R.f.d
  have hslots : F16.next = F.next + R.f.slots := by
    have n0 : slotsIn R.f 0 = 0 := rfl
    have n1 : slotsIn R.f (stages R.f).length = R.f.slots := by
      unfold slotsIn
      rw [List.take_length, slots_stages R.f h2]
    rw [I16.next, I0.next, hlen, n0, n1]
    omega
  have hlins : (table.rows.push rowb).size = R.f.lins := by
    simp only [Array.size_push, rtb, rc, hrows, VerifiableInference.Desc.K3.Face.lins, hp]
    simp
  have hm := messagesV_intro R.f v hp e5 e6 e7 e9 e10 e12 hsz e14 e15 e16 hslots hlins
  refine ⟨_, F16, hearV_intro R.f hF.ok hm, ⟨rfl, zb, hlins, ?_, ?_, f14, r14⟩, ?_, ?_,
    ((g12.later lt14).later lt16).push (mem_at (at_bits R.f v hp)) (show 0 < 1 by omega) zr16,
    fun cf hcf F' G' H y mask entry hS hl hr hl' hm' =>
      last14 cf hcf F' G' H y mask entry hS (lt16.trans hl) hr hl' hm'⟩
  · rw [hp]
    show [c.form] = [R.form (.key 0 v)]
    rw [fc]
  · obtain ⟨_, _, _, _, _, hrec, _⟩ := MaskedSum.hear_spec w14
    show lv.start = _
    rw [hrec]
  · rw [← hlen]
    exact I16
  · intro j j1 j2 hf
    obtain ⟨s1, s2⟩ := slotsIn_at (at_leaves R.f v hp)
    have hn : j < F14.next := by
      rw [I14.next, s2]
      rw [s1] at j2
      unfold Stage.slots
      omega
    exact free14 j (by rw [f14]; exact j1) (by rw [f14]; exact j2) ((wa.2 j hn).1 hf)

#print axioms ProofFile.Honest.K3.Law.inv_owed3
#print axioms ProofFile.Honest.K3.Law.one_of_drop
#print axioms ProofFile.Honest.K3.Law.many_of_drop
#print axioms ProofFile.Honest.K3.Law.getD_push
#print axioms ProofFile.Honest.K3.Law.foldl_congr'
#print axioms ProofFile.Honest.K3.Law.form_tie
#print axioms ProofFile.Honest.K3.Law.join_eq
#print axioms ProofFile.Honest.K3.Law.tabPt_size
#print axioms ProofFile.Honest.K3.Law.off_alpha
#print axioms ProofFile.Honest.K3.Law.off_join
#print axioms ProofFile.Honest.K3.Law.off_iTab
#print axioms ProofFile.Honest.K3.Law.off_iKey
#print axioms ProofFile.Honest.K3.Law.off_zero
#print axioms ProofFile.Honest.K3.Law.len_x
#print axioms ProofFile.Honest.K3.Law.call_tie0
#print axioms ProofFile.Honest.K3.Law.call_tieS
#print axioms ProofFile.Honest.K3.Law.call_key
#print axioms ProofFile.Honest.K3.Law.call_tab
#print axioms ProofFile.Honest.K3.Law.call_leaves
#print axioms ProofFile.Honest.K3.Law.call_bits
#print axioms ProofFile.Honest.K3.Law.front_walk
#print axioms ProofFile.Honest.K3.Law.tie_walk
#print axioms ProofFile.Honest.K3.Law.join_walk
#print axioms ProofFile.Honest.K3.Law.keys_walk
#print axioms ProofFile.Honest.K3.Law.tab_walk
#print axioms ProofFile.Honest.K3.Law.form_key0
#print axioms ProofFile.Honest.K3.Law.slotsIn_at
#print axioms ProofFile.Honest.K3.Law.lookHeard_of_steps

end ProofFile.Honest.K3.Law
