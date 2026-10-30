-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Reads/StackEnts.lean: THE BATCHED SUMCHECK's TWO END FORMS AND ITS OWN CLAIM NAME
ENTRIES INSIDE THE FAMILIES OF TABLES, WHERE K4's HEAR RETURNS: THE TWO END FORMS OUTRIGHT; THE
CLAIM IF THE FORM IN WHICH THE LOOKUP's KEY SIDE ENDS DOES. The walk that
Johnson/Road/K4/Reads/Covered.lean names as owed (its premises hS, hA, hB). Statements and proofs.

  `ret_foldlM`: one rule more on what a plain function returns (`Ret`,
    Johnson/Road/K4/Reads/HearStarts.lean).
  `inTab_zipFold`, `inTab_startOf`, `joinStart_in`: the start form of the batched sumcheck: where
    K4's `joinStart` returns C, C is `InTab v`, IF the lookup's form H.fo.cEnd and the second token
    sumcheck's H.KT are.
  `ret_hearTerms_KT`: what `hearTerms` leaves as KT names no entry at all.
  `ret_plainRounds`: the rounds hand the start form on.
  `ret_hearStack`: so the batched sumcheck's own claim K.rowS is `InTab v`, under the same two.
  `hearStack_ends`: K.fin.Alin and K.fin.Blin are `InTab v`, with no premise.
  **`stack_covered`**: WHERE `hearFl` RETURNS o: o.K.rowS, o.K.fin.Alin, o.K.fin.Blin are
    `InTab o.v`, IF o.H.fo.cEnd IS.
  **`back_covered_hear`**: so every form of the run "back" is `InTab o.v`, under that one premise.
  `entsIn_noEnts`, `stack_covered_bare`, `back_covered_bare`: the same two, if o.H.fo.cEnd names no
    entry at all (its array of entries is empty).
  `stack_covered_left`, `back_covered_left`: the same two, with the premise at the record fo that
    the hearing was handed: fo.cEnd.ents = #[] (o.H.fo = fo: `own_fo`,
    Johnson/Road/K4/Slots/HearFills.lean).

ONE PREMISE STANDS WHERE THREE STOOD: on the form in which the lookup's key side ends, cEnd. K4's
text takes it into the start form as it is (OnBytes/Desc/First/K4/Hear.lean, `joinStart`'s last
line). It is a field of the record fo that HEAR IS HANDED (K3's): the first four theorems have it in
the letters o.H.fo, as `front_covered_heard` has its two (o.H.fo.rows, o.H.fo.leaves.start); by
`own_fo` that is fo. IT IS FOR THE LOOKUP's SIDE TO PAY, beside hK3 and hlv, AND IT HAS A PAYER: the
record of what K3 leaves has the field `cEndEnts : g.cEnd.ents = #[]`
(Johnson/Top/H/K3LeftStatement.lean), and `lkPadCEnd` (Johnson/Top/H/K3CEnd.lean) shows it of every
return of `lkPad` from a ledger with its sizes. THAT K4's fo IS SUCH A g IS NOT SAID HERE.

No new argument on the calls' factors and the panels: `ge_joinPart`
(Johnson/Road/K4/Reads/LineEnts.lean), `stackEnd_ents` and the lists' walk (PanelsEnts.lean). Also
used: `joinStart_startOf` (Johnson/Road/K4/JoinTie.lean), `hearStack_public`
(OnBytes/Desc/First/K4/StackPublic.lean), `hear_parts` (MergeClaims.lean), `entsIn_rowForm`
(RowsEnts.lean), `back_covered_heard` (Covered.lean).

Limits. One direction, from a return. As Covered.lean's: NOT SAID: that the families of v.tab fill,
or lie in, the part of the array that the reads' test covers; an index that strays to another
tensor, layer or limb of the same family is not caught. Nothing on soundness.
-/
import Johnson.Road.K4.Reads.LineEnts
import Johnson.Road.K4.Reads.PanelsEnts
import Johnson.Road.K4.Reads.Covered
import Johnson.Road.K4.JoinTie
import OnBytes.Desc.First.K4.MergeClaims
import OnBytes.Desc.First.K4.StackPublic
import Johnson.Road.K4.Slots.HearFills

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Reads

open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.Desc.First.K4.Slots (own_fo)
open OnBytes.Road (startOf)
open OnBytes.Road.K4 (joinStart_startOf)

variable {α β : Type} {v : Env}

/-! ### One rule more -/

/-- A fold of plain functions keeps what each step keeps. -/
theorem ret_foldlM {P : β → Prop} {f : β → α → Fl β} (hf : ∀ s x, P s → Ret (f s x) P) :
    ∀ (l : List α) (s : β), P s → Ret (l.foldlM f s) P
  | [], _, hs => by
    rw [List.foldlM_nil]
    exact Ret.pure hs
  | x :: l, s, hs => by
    rw [List.foldlM_cons]
    exact Ret.bind (hf s x hs) fun s' hs' => ret_foldlM hf l s' hs'

/-! ### The start form -/

/-- A sum of forms of a list, each under the weight of its number. -/
theorem inTab_zipFold (w : ℕ → E) : ∀ (l : List Aff) (k : ℕ) (a : Aff), (∀ f ∈ l, InTab v f) →
    InTab v a → InTab v ((l.zipIdx k).foldl (fun (a : Aff) x => a.addMul x.1 (w x.2)) a)
  | [], _, _, _, ha => ha
  | f :: l, k, a, h, ha => by
    rw [List.zipIdx_cons, List.foldl_cons]
    exact inTab_zipFold w l (k + 1) _ (fun g hg => h g (List.mem_cons_of_mem _ hg))
      (entsIn_addMul _ ha (h f List.mem_cons_self))

/-- The start form as a function of the calls' factors. -/
theorem inTab_startOf {H : Heard} (om : Array E) {parts : List Aff}
    (hp : ∀ f ∈ parts, InTab v f) (hc : InTab v H.fo.cEnd) (hK : InTab v H.KT) :
    InTab v (startOf H om parts) := by
  have c0 := inTab_zipFold (v := v) (fun i => H.fo.e.getD i zeroE) parts 0 aff0 hp inTab_aff0
  unfold startOf
  cases H.tT with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact entsIn_sub (entsIn_add c0 (entsIn_ofConst _)) hc
  | some tT =>
    simp only [Option.isSome_some, ↓reduceIte]
    exact entsIn_addMul _
      (entsIn_sub (entsIn_sub (entsIn_add c0 (entsIn_ofConst _)) (entsIn_slot _)) hc) hK

/-- **Where K4's `joinStart` returns, the start form names entries inside the families**, if the
lookup's form and the second token sumcheck's do. -/
theorem joinStart_in {H : Heard} {om : Array E} {C : Aff} {F F' : Fork} {t t' : Tape}
    (h : joinStart engFl v H om F t = some (C, F', t')) (hc : InTab v H.fo.cEnd)
    (hK : InTab v H.KT) : InTab v C := by
  obtain ⟨weighed, parts, laid, tT, _, hp, _, _, _, _, rfl, _, _⟩ := joinStart_startOf h
  exact inTab_startOf om
    (all_mapM (Pr := InTab v) (fun _ a ha => ge_joinPart _ _ _ _ _ a ha) _ parts hp) hc hK

/-! ### What the second token sumcheck leaves -/

/-- KT is a factor times that sumcheck's claim with nothing kept, and it began with a slot. -/
theorem ret_hearTerms_KT (P : Pub) (H : Heard) :
    Ret (hearTerms engFl P H) fun H' => ∀ Q : ℕ → ℕ → ℕ → Prop, EntsIn Q H'.KT := by
  unfold hearTerms
  refine Ret.bind (ret_tscIn _ _ _ _) fun tT ht => Ret.skip fun _ =>
    Ret.bind (ret_pscRow tT.p _ _) fun x hx => ?_
  obtain ⟨row, p⟩ := x
  refine Ret.pure fun Q => ?_
  show EntsIn Q (Aff.scale row _)
  rw [show row = _ from hx]
  exact entsIn_scale _ (entsIn_rowForm _ _ (ht Q) entsIn_empty)

/-! ### The batched sumcheck -/

theorem ret_plainRounds (st : Stack) :
    Ret (plainRounds engFl st) fun s' => s'.p.start = st.p.start := by
  unfold plainRounds
  refine Ret.bind (Φ := fun s : Array E × Psc => s.2.start = st.p.start) ?_ fun x hx => ?_
  · refine ret_foldlM (P := fun s : Array E × Psc => s.2.start = st.p.start)
      (fun s z hs => ?_) _ _ rfl
    refine Ret.bind (ret_roundIn _ _ _ _) fun x hx => ?_
    obtain ⟨r, q⟩ := x
    exact Ret.pure (hx.trans hs)
  · obtain ⟨r, p⟩ := x
    exact Ret.pure hx

/-- **The batched sumcheck's own claim** names entries inside the families, if the lookup's form and
the second token sumcheck's do. -/
theorem ret_hearStack (P : Pub) (H : Heard) (lamS NCLp : ℕ) (hc : InTab v H.fo.cEnd)
    (hK : InTab v H.KT) : Ret (hearStack engFl P v H lamS NCLp) fun K => InTab v K.rowS := by
  unfold hearStack
  refine Ret.skip fun om => Ret.skip fun tT => Ret.skip fun shownT => Ret.skip fun TS =>
    Ret.skip fun pans => ?_
  generalize placePanels pans.bl = pp
  obtain ⟨bl, places⟩ := pp
  refine Ret.skip fun _ => ?_
  refine Ret.bind (Φ := InTab v) (fun _ _ _ _ _ e => joinStart_in e hc hK) fun C hC => ?_
  refine Ret.bind (ret_pscBegin C) fun p hp => ?_
  refine Ret.bind (ret_plainRounds _) fun st hst => ?_
  refine Ret.skip fun _ => ?_
  refine Ret.bind (ret_pscEnds st.p 2 _) fun x hx => ?_
  obtain ⟨sA0, p2⟩ := x
  refine Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ => Ret.skip fun _ =>
    Ret.skip fun fin => ?_
  refine Ret.bind (ret_pscRow p2 _ _) fun x hx3 => ?_
  obtain ⟨rowS, p3⟩ := x
  refine Ret.pure ?_
  have e : p2.start = C := (hx.trans hst).trans hp
  show InTab v rowS
  rw [show rowS = _ from hx3]
  exact entsIn_rowForm _ _ (e ▸ hC) entsIn_empty

/-- **The two end forms** name entries inside the families, wherever `hearStack` returns. -/
theorem hearStack_ends {P : Pub} {H : Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    InTab v K.fin.Alin ∧ InTab v K.fin.Blin := by
  obtain ⟨_, shownT, TS, pans, _, _, _, _, _, _, _, _, _, _, _, _, q5, _, _, _, _, _, _, _, _, _,
    _, _, q16⟩ := hearStack_public h
  exact stackEnd_ents (placePanels_in
    (panelsT_in { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } TS
      (panelsA_in _ panIn_empty) pans q5)) q16

/-! ### HEAR -/

/-- **WHERE HEAR RETURNS: the batched sumcheck's claim and its two end forms**, if the form in which
the lookup's key side ends names entries inside the families. -/
theorem stack_covered {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, G, u))
    (hc : InTab o.v o.H.fo.cEnd) :
    InTab o.v o.K.rowS ∧ InTab o.v o.K.fin.Alin ∧ InTab o.v o.K.fin.Blin := by
  obtain ⟨_, _, _, _, H1, _, _, G1, G2, G3, _, _, u1, u2, u3, _, _, _, h2, h3, _⟩ :=
    hear_parts (show hear engFl P hp g fo F t = some (o, G, u) from hh)
  have hK : InTab o.v o.H.KT := ret_hearTerms_KT P H1 G1 u1 o.H G2 u2 h2 (inTab o.v)
  exact ⟨ret_hearStack P o.H _ _ hc hK G2 u2 o.K G3 u3 h3, hearStack_ends h3⟩

/-- **The run "back", behind HEAR**: one premise is left, on the lookup's own record. -/
theorem back_covered_hear {P : Pub} {hpl : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (hc : InTab o.v o.H.fo.cEnd)
    (h : formsBack o F = some (fs, G)) : ∀ f ∈ fs.toList, InTab o.v f := by
  obtain ⟨a, b, c⟩ := stack_covered hh hc
  exact back_covered_heard hh h a b c

/-! ### If the lookup's form names no entry -/

/-- A form whose array of entries is empty names no entry. -/
theorem entsIn_noEnts {Q : ℕ → ℕ → ℕ → Prop} {f : Aff} (h : f.ents = #[]) : EntsIn Q f :=
  fun y hy => by
    rw [h] at hy
    simp at hy

/-- `stack_covered`, if the form in which the lookup's key side ends names no entry. -/
theorem stack_covered_bare {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, G, u))
    (he : o.H.fo.cEnd.ents = #[]) :
    InTab o.v o.K.rowS ∧ InTab o.v o.K.fin.Alin ∧ InTab o.v o.K.fin.Blin :=
  stack_covered hh (entsIn_noEnts he)

/-- `back_covered_hear`, if the form in which the lookup's key side ends names no entry. -/
theorem back_covered_bare {P : Pub} {hpl : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (he : o.H.fo.cEnd.ents = #[])
    (h : formsBack o F = some (fs, G)) : ∀ f ∈ fs.toList, InTab o.v f :=
  back_covered_hear hh (entsIn_noEnts he) h

/-! ### The premise at the record that the hearing was handed -/

/-- `stack_covered`, if the form in which the key side of the lookup's record fo ends names no
entry. -/
theorem stack_covered_left {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, G, u))
    (he : fo.cEnd.ents = #[]) :
    InTab o.v o.K.rowS ∧ InTab o.v o.K.fin.Alin ∧ InTab o.v o.K.fin.Blin :=
  stack_covered_bare hh (by rw [own_fo hh]; exact he)

/-- `back_covered_hear`, if the form in which the key side of the lookup's record fo ends names no
entry. -/
theorem back_covered_left {P : Pub} {hpl : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hpl g fo F0 t = some (o, G0, u)) (he : fo.cEnd.ents = #[])
    (h : formsBack o F = some (fs, G)) : ∀ f ∈ fs.toList, InTab o.v f :=
  back_covered_bare hh (by rw [own_fo hh]; exact he) h

end OnBytes.Desc.First.K4.Reads

#print axioms OnBytes.Desc.First.K4.Reads.joinStart_in
#print axioms OnBytes.Desc.First.K4.Reads.ret_hearTerms_KT
#print axioms OnBytes.Desc.First.K4.Reads.ret_hearStack
#print axioms OnBytes.Desc.First.K4.Reads.hearStack_ends
#print axioms OnBytes.Desc.First.K4.Reads.stack_covered
#print axioms OnBytes.Desc.First.K4.Reads.back_covered_hear
#print axioms OnBytes.Desc.First.K4.Reads.stack_covered_bare
#print axioms OnBytes.Desc.First.K4.Reads.back_covered_bare
#print axioms OnBytes.Desc.First.K4.Reads.stack_covered_left
#print axioms OnBytes.Desc.First.K4.Reads.back_covered_left
