-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/RowsOnNew.lean: NO ROW THAT A CODE SWITCH BETWEEN TWO SEGMENTS LAYS
HAS, READ IN THE FIELD, A COEFFICIENT ON ANY MESSAGE BUT THE CARRYING ONE AND THE COPIES; SO WHAT
SUCH A ROW SAYS OF WORDS HANGS ON THE WORDS AT THESE MESSAGES ALONE. Under the public premises of
`SwitchRowsHold` (Inner/Statement.lean). One definition; statements with their proofs. No coin, no
round, no frame.

  `OnNew` with `OnNew.add`, `OnNew.sum`: a function of coefficients is 0 at every message that is
                    neither g nor a copy; sums
  `onNew_lift` with `onNew_stretch`, `onNew_addKept`: the three sorts of pieces
  `onNew_mask` a mask row's generator row
  `rowsOnNew` every made row
  `says_onNew` a row that is `OnNew` says of words m what it says of words m', where m and m' are
                    one at g and at each copy

WHY. `switchRowsHold` (Inner/Holds.lean) ends at `newWords`, which are 0 at every message but g and
the copies; Inner/Value.lean cuts a row's worth down to these BY THE WORDS' ZEROS, and says nothing
on the rows' coefficients. Words read off a chain's witness are not 0 elsewhere: whoever carries the
law's end to such words wants the rows' own zeros.

How. `rowsOnNew` goes as `padsUnread` (Inner/PadsProof.lean), case by case, in its binders: which
row is of which sort, and of which pieces it is the sum (`carried_pieces`, `main_pieces`,
`keptGen_pieces`); each piece by its text (`liftPiece`, `stretchPiece`: 0 off g) or by the library's
`addKept_other` (OnBytes/Slice/BlkCsKept.lean) and `mask_off` (Inner/GenRows.lean).

Kin, not called. ON THE ROWS: the soundness side's `OnlyAt` (Johnson/Top/H0/K2Hands/Support.lean):
inside the tables a row has no coefficient but at an entry of the typed new sending (`Named`): shown
of every made row in `only_at_rows` (Johnson/Top/H0/Tw/K2C/OnlyAtRows.lean) · `only_at_rows_light`,
`only_at_yes_light`, `only_at_yes_of_yes` (Johnson/Top/H0/Tw/K2C/OnlyAtLight.lean). WHY NOT CALLED:
each asks that side's typed letters: a signature of the new sending, its numberings, and records
over them (at the lightest: `CallerAt`, `FrontLight`, `Held`); each speaks inside the tables alone,
and ends at an entry of that signature, not at "g or a copy". Here: the public premises of
`SwitchRowsHold` alone; every part and index. ON THE WORDS: `says_agree_in`
(Johnson/Desc/Means/ItemsLen.lean): the same end, for a row that is `RowIn` a group, where the two
words are one at the group's members: the kind's own folders (Johnson/Desc/K2; Johnson/Top/H0's
Tw/K2, Tw/K2C, K2Hands, K2Hears, K2Caller) do not mention `RowIn` anywhere, so they hold no law that
would give it of a made row · three laws of the name `says_congr`
(Johnson/Desc/Third/Law/Row0Words.lean · Johnson/Desc/K12/Law/TupleWords.lean
· Johnson/Desc/First/Close/Law/FillRow.lean): these want the two words equal at every message that
the statement has. `says_onNew` wants them equal at g and the copies only, and pays for that with
its premise `OnNew` on the row.

Limits. Read in the field: nothing on the three words of a coefficient. Nothing on WHERE on g or a
copy a row has a coefficient: of the pads' places Inner/PadsProof.lean speaks. `says_onNew` asks the
two words to be one at g and the copies AT EVERY PART AND INDEX. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Inner.PadsProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE coefAt formAt stretchAt genMain genMask symAtB)
open OnBytes.Means (Words Says value onTable)
open Johnson.Prover.Send (Rows)
open H2K.Lift (genKept keptFrom keptForm)
open VerifiableInference.Desc.First.K2Hands (placeOf carriedOf formOn sampleRow)

/-- A function of coefficients is 0 at every message that is neither g nor a copy. -/
def OnNew (g : Nat) (anew : Array Nat) (κ : Nat → Part → Nat → GE) : Prop :=
  ∀ o, o ≠ g → o ∉ anew.toList → ∀ (p : Part) (J : Nat), κ o p J = 0

theorem OnNew.add {g : Nat} {anew : Array Nat} {κ₁ κ₂ : Nat → Part → Nat → GE}
    (h₁ : OnNew g anew κ₁) (h₂ : OnNew g anew κ₂) :
    OnNew g anew fun o p J => κ₁ o p J + κ₂ o p J := fun o hg ha p J => by
  show κ₁ o p J + κ₂ o p J = 0
  rw [h₁ o hg ha p J, h₂ o hg ha p J, add_zero]

theorem OnNew.sum {α : Type} {g : Nat} {anew : Array Nat} (κ : α → Nat → Part → Nat → GE)
    (l : List α) (h : ∀ x ∈ l, OnNew g anew (κ x)) :
    OnNew g anew fun o p J => (l.map fun x => κ x o p J).sum := fun o hg ha p J =>
  List.sum_eq_zero fun v hv => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    exact h x hx o hg ha p J

/-- **Coefficients on a stretch of the rest.** -/
theorem onNew_stretch (S : Statement) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (a n : Nat) (c : Nat → GE) : OnNew g anew (stretchPiece S T g a n c) := fun o hg _ p J => by
  have e : (g == o) = false := beq_false_of_ne fun k => hg k.symm
  unfold stretchPiece
  rw [e]
  simp

/-- **A form on the old main row's message, carried to g.** -/
theorem onNew_lift (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (c : Form) : OnNew g anew (liftPiece S old T g c) := fun o hg _ p J => by
  have e : (g == o) = false := beq_false_of_ne fun k => hg k.symm
  unfold liftPiece
  rw [e]
  simp

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows}

/-- **A form on a kept member's table, carried over.** -/
theorem onNew_addKept (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) (c : Form) : OnNew g anew (coefAt (Fr.addKept {} k c)) := by
  have I := frameIs hFr
  obtain ⟨s, o, _, ho, e1, e2, _, _, _, _, _⟩ := kept_at hFr a k hk
  have hform : Fr.addKept {} k c = switchAddKept {} (padPlaces S.codes s) o g .main
      (SwitchPlaces.make S.codes T) k.oldPadAt c := by
    unfold SwitchFrame.addKept
    rw [e2, e1, I.gIs, I.restPart, A.restMain, I.places]
  rw [hform]
  intro o' hg ha p J
  rw [OnBytes.Slice.addKept_other _ _ _ _ _ _ _ _ o' p
    (fun h => ha (by rw [h.1]; exact List.mem_of_getElem? ho)) (fun h => hg h.1),
    OnBytes.Slice.coefAt_empty]

/-- **A mask row's generator row.** -/
theorem onNew_mask (A : AtSwitch S old T g anew W V) {Fr : SwitchFrame}
    (hFr : switchFrame S old T g anew = some Fr)
    (hlog : (S.codes.mask.getD old.maskCode default).logN ≤ 32) (j : Nat) (hj : j < 2) (x : Nat)
    (t : E) : OnNew g anew (coefAt (genMask Fr x j t)) := by
  have I := frameIs hFr
  obtain ⟨xo, hxo, hxs⟩ := Option.map_eq_some_iff.1 A.seated.carrying
  have M := VerifiableInference.Desc.First.K2Hands.maskAt_of_check S old T g anew Fr hFr A.check
    xo hxo hxs (by rw [I.zk]; exact hlog) j hj
  intro o hg _ p J
  exact mask_off Fr j _ _ M x t o p J (by rw [I.gIs]; exact beq_false_of_ne fun k => hg k.symm)

/-- **No row that the switch lays has, read in the field, a coefficient on any message but the
carrying one and the copies.** -/
theorem rowsOnNew (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) (rows : List OnBytes.Row)
    (check : switchTargetCheck S old T = true) (restMain : T.rest.part = .main)
    (fits : OldFits S old) (keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (seated : SeatedAt S old T g anew) (lengths : S.codes.lengthsOk = true)
    (hlogC : (S.codes.base.getD old.code default).logN ≤ 32)
    (hlogZ : (S.codes.mask.getD old.maskCode default).logN ≤ 32)
    (hx : ∀ x ∈ pos.all.toList, x < 2 ^ (S.codes.base.getD old.code default).logN)
    (hrows : Own.swRows S old T g anew pos y = some rows) :
    ∀ r ∈ rows, OnNew g anew (coefAt r) := by
  intro r hr
  have A := atPublic check restMain fits keptPos seated lengths
  obtain ⟨Fr, carried, L⟩ := VerifiableInference.Desc.First.K2Hands.laid_of
    (show switchRows S old T g anew pos y = some rows from hrows)
  have hFr := L.frame
  have hm := A.target.masks
  rw [L.rows, List.cons_append, List.mem_cons, List.mem_append] at hr
  rcases hr with hr | hr | hr
  · obtain ⟨ks, hks, hc⟩ :=
      (VerifiableInference.Desc.First.K2Hands.switchCarried_iff Fr old carried).1 L.claim
    obtain ⟨_, hmem⟩ := Lists.mapM_mem _ _ _ hks
    rw [hr, hc, carried_pieces A hFr ks]
    refine OnNew.add (OnNew.add (OnNew.add (onNew_lift S old T g anew _) ?_)
      (onNew_stretch S T g anew _ _ _)) (onNew_stretch S T g anew _ _ _)
    refine OnNew.sum (fun x : KeptForm × KeptPlace => coefAt (Fr.addKept {} x.2 x.1.c)) _ ?_
    intro x hxm
    obtain ⟨_, a, hk⟩ := place_at x.1 x.2 (hmem x hxm)
    exact onNew_addKept A hFr a x.2 hk _
  · obtain ⟨k, hk, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨sample, _, rfl⟩ := List.mem_map.1 hr
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hk
    exact onNew_addKept A hFr a k ha (formOn sample)
  · obtain ⟨x, hxm, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨i, _, hlt, hget⟩ := listed_at pos x (L.listed x hxm)
    have hxin : x ∈ pos.all.toList := by
      rw [← hget, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
      exact Array.getElem_mem_toList hlt
    have hxlt := hx x hxin
    rw [H2K.Lift.switchGenerators_all, List.cons_append, List.mem_cons, List.mem_append] at hr
    rcases hr with hr | hr | hr
    · rw [hr, main_pieces A hFr hlogC x hxlt]
      exact OnNew.add (onNew_lift S old T g anew _) (onNew_stretch S T g anew _ _ _)
    · obtain ⟨a, k, b, hk, hb, hr⟩ := mem_keptFrom Fr x _ r Fr.kept 0 hr
      rw [hr]
      simp only [Nat.zero_add]
      rw [keptGen_pieces A hFr hlogC a k hk b hb x hxlt]
      exact OnNew.add (onNew_addKept A hFr a k hk _) (onNew_stretch S T g anew _ _ _)
    · obtain ⟨jj, hjj, hr⟩ := List.mem_map.1 hr
      have hj2 : jj < 2 := by
        have := List.mem_range.1 hjj
        omega
      rw [← hr]
      exact onNew_mask A hFr hlogZ jj hj2 x _

/-- **What such a row says hangs on the words at g and the copies alone.** -/
theorem says_onNew (St : Statement) (r : OnBytes.Row) (g₀ : Nat) (an : Array Nat)
    (m m' : Words GE) (h : OnNew g₀ an (coefAt r)) (hg : ∀ part i, m g₀ part i = m' g₀ part i)
    (ha : ∀ o ∈ an.toList, ∀ part i, m o part i = m' o part i) :
    Says rdE St r m ↔ Says rdE St r m' := by
  have key : ∀ o part, onTable rdE St r m o part = onTable rdE St r m' o part := by
    intro o part
    unfold onTable
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases e : o = g₀
    · rw [e, hg]
    · by_cases e' : o ∈ an.toList
      · rw [ha o e']
      · have z : rdE.val (r.coefficient o part i) = 0 := h o e e' part i
        rw [z, zero_mul, zero_mul]
  unfold Says value
  simp only [key]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.OnNew
#print axioms VerifiableInference.Desc.K2.Honest.OnNew.add
#print axioms VerifiableInference.Desc.K2.Honest.OnNew.sum
#print axioms VerifiableInference.Desc.K2.Honest.onNew_stretch
#print axioms VerifiableInference.Desc.K2.Honest.onNew_lift
#print axioms VerifiableInference.Desc.K2.Honest.onNew_addKept
#print axioms VerifiableInference.Desc.K2.Honest.onNew_mask
#print axioms VerifiableInference.Desc.K2.Honest.rowsOnNew
#print axioms VerifiableInference.Desc.K2.Honest.says_onNew
