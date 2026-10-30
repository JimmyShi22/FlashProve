-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/DigitsBehind.lean: the honest side of the kind "lookup" (K3):
what stands behind the hearing's return, as the runs of claims of the smallness test ask it of the
structure that the lookup on the digits lays (Johnson/Desc/First/TailClaims/Equations.lean): the
structure is well made. Theorems; one class (`Owes`) with its instances, and a local tactic
("owes").

Terms. Honest/K3/GLOSSARY.md. In this file: the hearing is `hearV`, and `messagesV` is the reading
of the messages inside it (both Johnson/Desc/First/Look/Via/Rounds.lean). The list of owed claims is
the field owed of the ledger. The three debts are the three claims that the hearing appends to it;
their numbers in the list are the fields owedObjects, owedPlanes and owedJoin of what was heard. A
debt is not marked as added if `unpaid` (Johnson/Desc/First/Look/K3Runs.lean) accepts at its number.
`Longer` is defined in Honest/K3/Law/KeepsDefs.lean.

What is shown.
  `hideRun_owed`, `hear_owed`, `row_owed`, `whole_owed`, `level_owed`, `run_owed`: the parts' texts
    leave the ledger's list of owed claims as it is (helpers: `hide_owed`, `hideSteps_owed`,
    `turn_owed`, `fold_owed`).
  `Owes x`: a text that hears only lengthens that list, by claims that are not marked as added
    (`Longer`). The class is closed under the operations that compose such texts (pure, bind, if, a
    fold); the instances and theorems named owes_... say so, text by text.
  `owed_grows`: so the lookup's hearing only lengthens the list.
  `heard_counts`: of what was heard: as many rows as the face counts; the numbers of the three debts
    (helpers: `must_true`, `owe_spec`).
  `unpaid_behind`: the three debts are not marked as added behind the hearing (helper:
    `unpaid_of_longer`). `unpaid` accepts at a number beyond the list too: that the three stand in
    the list is not said by this theorem.
  `leaves_open`: the leaves' sumcheck as the program's structure: no row made; begun; it has a
    variable; a challenge for each variable. This is the test of `eqPscRow`
    (Johnson/Desc/First/TailClaims/Equations.lean), to the letter.
  `heardWellMade`: the four together, at the structure that `toHeard`
    (Johnson/Desc/First/Look/K3LookupGeneral.lean) makes.
All are general in the face but `heardWellMade`, which is stated at a shape's face.

Hypotheses that remain.
  The return of the text that each statement names: of `hearV` or `messagesV` in the theorems on the
    hearing (`h`, `hh`, `hr`, `hw`).
  `a`, `b`, `l`: (in `Longer.trans`, `unpaid_of_longer`) `Longer`; `hi`: the number lies from the
    earlier list's length on. `hx`, `hf`: (in `Owes.bind`, `owes_foldlM`) the texts that are joined
    are `Owes`.
  `hS`: (in `leaves_open`, `heardWellMade`) the ledger in front has its arrays at their size.
  `hg`: (in `heardWellMade`) `toHeard` returns.
  In `Longer.of_eq` `h` is no return: G.owed = F.owed. `hideSteps_owed` and `fold_owed` bear a
    hypothesis without a name in front of an arrow.

Users. `owed_grows` is called in Honest/K3/Law/Thread/K3Keeps.lean; `heard_counts` in
Honest/K3/Parts/KeyLeft.lean and Honest/K3/Shape/HeardTop.lean; `unpaid_behind` and `row_owed` in
KeyLeft.lean; `owe_spec` in Honest/K3/Parts/Packs.lean.

Limits. The runs `eqPlanesAdded` and `eqJoinAdded` (Johnson/Desc/First/TailClaims/Equations.lean)
mark the two debts and test nothing: "not yet marked" is asked in the words of
Johnson/Desc/First/Look/K3Runs.lean (`unpaid`). All is said at the ledger behind the hearing. The
runs of the smallness test stand at a later ledger: that no text between marks the two debts, or
fills the leaves' own slots, is a hypothesis for whoever walks the chain; it is not shown here.
Nothing is said on the calls' points and weights (`pointsHeld`, `forestHeld`, `callHeld`). Nothing
is said on what a claim is worth.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.KeepsDefs
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Digits
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Owed)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV faceOf
  toHeard toHeardG toPsc unpaid leafVars)
open VerifiableInference.Desc.First.ProdV (LevelOut level turn Carried)

local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

variable {α β γ : Type}

/-! ## The parts' texts leave the list of owed claims -/

theorem hide_owed {F G : Fork} {j : Nat} {s k : E} (h : F.hide j s k = some G) :
    G.owed = F.owed := by
  unfold Fork.hide at h
  split at h
  · cases h
    rfl
  · cases h

theorem hideSteps_owed (k : E) : ∀ (l : List E) (p q : Nat × Fork),
    l.foldlM (Fork.hideStep k) p = some q → q.2.owed = p.2.owed
  | [], p, q, h => by
    obtain rfl : p = q := Option.some.inj h
    rfl
  | y :: l, p, q, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨p1, hq, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨j, G⟩ := p
    obtain ⟨H, hh, e⟩ := Option.map_eq_some_iff.1 (show (G.hide j y k).map _ = some p1 from hq)
    rw [hideSteps_owed k l p1 q h2, ← e]
    exact hide_owed hh

theorem hideRun_owed {F G : Fork} {first : Nat} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : G.owed = F.owed := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hq : v.toList.foldlM (Fork.hideStep k) (first, F) with
  | none => simp [hq] at h
  | some x =>
    rw [hq] at h
    have e : x.2 = G := by simpa using h
    rw [← e]
    exact hideSteps_owed k v.toList (first, F) x hq

theorem hear_owed {C : Aff} {k : MaskedSum.Call} {F G : Fork} {rs : List Fmt.RoundView}
    {h : MaskedSum.Heard} (hh : MaskedSum.hear C k F rs = some (h, G)) : G.owed = F.owed := by
  obtain ⟨_, _, R, _, _, _, hG⟩ := MaskedSum.hear_spec hh
  have e := hideRun_owed hG
  exact e

theorem row_owed {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) : G.owed = F.owed :=
  hideRun_owed (MaskedSum.row_write hr)

theorem whole_owed {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard} {f : Aff}
    (hw : MaskedSum.whole C k endTerm F rs = some (h, f, G)) : G.owed = F.owed := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := MaskedSum.whole_parts hw
  exact (row_owed hr).trans (hear_owed hh)

theorem level_owed {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    G.owed = F.owed := by
  unfold level at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' line rest' hw _
      split at h
      · split at h
        · exact nomatch h
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj h)
          exact whole_owed hw
      · exact nomatch h
    · exact nomatch h

theorem turn_owed {order : List Nat} {s s' : Carried} {m : Nat} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : turn order s m F rs = some (s', G, rest)) : G.owed = F.owed := by
  unfold turn at h
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨o, G', rest'⟩ := x
  obtain rfl : G' = G := congrArg (·.2.1) e
  exact level_owed hx

theorem fold_owed (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat)
    (x y : Carried × Fork × List Fmt.RoundView),
    l.foldlM (fun (x : Carried × Fork × List Fmt.RoundView) i =>
      turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2) x = some y → y.2.1.owed = x.2.1.owed
  | [], x, y, h => by
    obtain rfl : x = y := Option.some.inj h
    rfl
  | i :: l, x, y, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨s', G, rest⟩ := z
    exact (fold_owed m0 orders l _ y h).trans (turn_owed hz)

theorem run_owed {m0 n : Nat} {orders : Nat → List Nat} {s s' : Carried} {F G : Fork}
    {rs rest : List Fmt.RoundView} (h : vRun m0 n orders s F rs = some (s', G, rest)) :
    G.owed = F.owed := fold_owed m0 orders _ (s, F, rs) (s', G, rest) h

/-! ## Texts that hear -/

theorem Longer.of_eq {F G : Fork} (h : G.owed = F.owed) : Longer F G :=
  ⟨[], by rw [h, List.append_nil], fun _ ho => by simp at ho⟩

theorem Longer.trans {F G H : Fork} (a : Longer F G) (b : Longer G H) : Longer F H := by
  obtain ⟨l, e, hl⟩ := a
  obtain ⟨l', e', hl'⟩ := b
  refine ⟨l ++ l', by rw [e', e, List.append_assoc], fun o ho => ?_⟩
  rcases List.mem_append.1 ho with h | h
  · exact hl o h
  · exact hl' o h

/-- Wherever x returns, it has only lengthened the list of owed claims, by claims not marked as
added. -/
class Owes (x : Hr α) : Prop where
  longer : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) → Longer F G

instance owes_pure (a : α) : Owes (pure a : Hr α) :=
  ⟨fun {F G rs rest b} e => by
    have e' : some (a, F, rs) = some (b, G, rest) := e
    exact Longer.of_eq (congrArg (fun y => y.2.1.owed) (Option.some.inj e')).symm⟩

theorem Owes.bind {x : Hr α} {f : α → Hr β} (hx : Owes x) (hf : ∀ a, Owes (f a)) :
    Owes (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some e
    exact (hx.longer h1).trans ((hf a).longer h2)⟩

instance owes_bind (x : Hr α) (f : α → Hr β) [Owes x] [∀ a, Owes (f a)] : Owes (x >>= f) :=
  Owes.bind inferInstance inferInstance

instance owes_ite (p : Prop) [Decidable p] (x y : Hr α) [Owes x] [Owes y] :
    Owes (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "owes" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Owes.bind ?_ ?_
    | intro _
    | split)

theorem owes_foldlM {f : β → γ → Hr β} (hf : ∀ s a, Owes (f s a)) :
    ∀ (l : List γ) (s : β), Owes (l.foldlM f s)
  | [], s => by
    show Owes (pure s : Hr β)
    infer_instance
  | a :: l, s => by
    show Owes (f s a >>= fun s' => l.foldlM f s')
    exact Owes.bind (hf s a) fun s' => owes_foldlM hf l s'

instance owes_must (b : Bool) : Owes (Hr.must b) :=
  ⟨fun {F G rs rest a} e => by
    unfold Hr.must at e
    split at e
    · exact Longer.of_eq (congrArg (fun y => y.2.1.owed) (Option.some.inj e)).symm
    · exact nomatch e⟩

instance owes_slot : Owes Hr.slot :=
  ⟨fun {F G rs rest a} e => by
    have e' : some (F.next, F, rs) = some (a, G, rest) := e
    exact Longer.of_eq (congrArg (fun y => y.2.1.owed) (Option.some.inj e')).symm⟩

instance owes_owe (what : String) : Owes (Hr.owe what) :=
  ⟨fun {F G rs rest a} e => by
    have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
    have e2 : (F.owe what).2 = G := congrArg (fun y => y.2.1) (Option.some.inj e')
    refine ⟨[{ what := what }], ?_, fun o ho => ?_⟩
    · rw [← e2]
      show (F.owed.push { what := what }).toList = _
      rw [Array.toList_push]
    · obtain rfl : o = { what := what } := by simpa using ho
      rfl⟩

instance owes_run (m0 n : Nat) (orders : Nat → List Nat) (s : Carried) :
    Owes (Hr.of (vRun m0 n orders s)) := ⟨fun e => Longer.of_eq (run_owed e)⟩

instance owes_drawsV (n : Nat) : Owes (drawsV n) :=
  ⟨fun {F G rs rest a} e => by
    unfold drawsV at e
    cases rs with
    | nil => exact nomatch e
    | cons r rs' =>
      dsimp only at e
      split at e
      · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
        exact Longer.of_eq (congrArg (fun y => y.2.1.owed) e).symm
      · exact nomatch e⟩

instance owes_drawV : Owes drawV :=
  ⟨fun {F G rs rest a} e => by
    unfold drawV at e
    split at e
    · rename_i x G' rest' hx
      split at e
      · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
        exact (owes_drawsV 1).longer hx
      · exact nomatch e
    · exact nomatch e⟩

instance owes_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    Owes (sumV C k endTerm) :=
  ⟨fun {F G rs rest a} e => by
    unfold sumV at e
    split at e
    · exact nomatch e
    · split at e
      · rename_i h row G' hw
        split at e
        · exact nomatch e
        · obtain rfl : G' = G := congrArg (·.2.1) (Option.some.inj e)
          exact Longer.of_eq (whole_owed hw)
      · exact nomatch e⟩

instance owes_openV (C : Aff) (vs : List MaskedSum.Var) : Owes (openV C vs) :=
  ⟨fun {F G rs rest a} e => by
    unfold openV at e
    split at e
    · exact nomatch e
    · obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨h, G'⟩ := x
      obtain rfl : G' = G := congrArg (·.2.1) e
      exact Longer.of_eq (hear_owed hx)⟩

instance owes_tieV (w : Nat) (a : E) : Owes (tieV w a) := by
  unfold tieV
  refine Owes.bind inferInstance fun x => ?_
  refine Owes.bind (owes_foldlM (fun s _ => by owes) _ _) fun _ => ?_
  infer_instance

theorem owes_partsV : ∀ (n : Nat) (rows : Array Aff) (C : Aff), Owes (partsV n rows C)
  | 0, rows, C => by
    unfold partsV
    infer_instance
  | n + 1, rows, C => by
    unfold partsV
    refine Owes.bind inferInstance fun w => ?_
    refine Owes.bind (owes_partsV n _ _) fun _ => ?_
    infer_instance

instance (n : Nat) (rows : Array Aff) (C : Aff) : Owes (partsV n rows C) := owes_partsV n rows C

theorem owes_keysV (f : LFace) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff),
    Owes (keysV f xs Cs rows)
  | [], _, rows => by
    unfold keysV
    infer_instance
  | _ :: _, [], rows => by
    unfold keysV
    infer_instance
  | x :: xs, C :: Cs, rows => by
    unfold keysV
    refine Owes.bind inferInstance fun k => ?_
    refine Owes.bind (owes_keysV f xs Cs _) fun _ => ?_
    infer_instance

instance (f : LFace) (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff) :
    Owes (keysV f xs Cs rows) := owes_keysV f xs Cs rows

instance owes_messagesV (f : LFace) : Owes (messagesV f) := by
  unfold messagesV
  owes

/-- **The lookup's hearing only lengthens the list of owed claims**, by claims not marked as added.
-/
theorem owed_grows {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) : Longer F G :=
  (owes_messagesV f).longer (hearV_messages h).2

/-! ## What was heard: the rows' number; the debts' numbers -/

theorem must_true {b : Bool} {F G : Fork} {rs rest : List Fmt.RoundView} {u : Unit}
    (h : Hr.must b F rs = some (u, G, rest)) : b = true := by
  unfold Hr.must at h
  split at h
  · assumption
  · exact nomatch h

theorem owe_spec {what : String} {F G : Fork} {rs rest : List Fmt.RoundView} {n : Nat}
    (h : Hr.owe what F rs = some (n, G, rest)) : n = F.owed.size ∧ G.owed.size = F.owed.size + 1 :=
      by
  have h' : some ((F.owe what).1, (F.owe what).2, rs) = some (n, G, rest) := h
  cases h'
  exact ⟨rfl, by show (F.owed.push _).size = _; simp⟩

/-- **Of what was heard**: as many rows as the face counts; the three debts have the next three
numbers of the ledger's list. -/
theorem heard_counts {f : LFace} {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV}
    (h : messagesV f F rs = some (g, G, rest)) :
    g.rows.size = f.lins ∧ g.owedObjects = F.owed.size ∧ g.owedPlanes = F.owed.size + 1 ∧
      g.owedJoin = F.owed.size + 2 := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  have hF1 : F1 = F := by
    have e' : some (F.next, F, rs) = some (slot0, F1, r1) := e1
    cases e'
    rfl
  obtain ⟨a1, b1⟩ := owe_spec e2
  obtain ⟨a2, b2⟩ := owe_spec e3
  obtain ⟨a3, _⟩ := owe_spec e4
  have hm := must_true e18
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hm
  subst hg
  rw [hF1] at a1 b1
  exact ⟨hm.2, a1, by rw [a2, b1], by rw [a3, b2, b1]⟩

/-- A number at or behind the end of the list of F names no claim that is marked as added in a
longer list. -/
theorem unpaid_of_longer {F G : Fork} (l : Longer F G) {i : Nat} (hi : F.owed.size ≤ i) :
    unpaid G i = true := by
  obtain ⟨l, e, hl⟩ := l
  unfold unpaid
  have e1 : G.owed[i]? = l[i - F.owed.size]? := by
    rw [← Array.getElem?_toList, e, List.getElem?_append_right (by simpa using hi)]
    simp
  rw [e1]
  cases hq : l[i - F.owed.size]? with
  | none => rfl
  | some o =>
    have := hl o (List.mem_of_getElem? hq)
    simp [this]

/-- **Behind the hearing the three debts are not marked as added.** -/
theorem unpaid_behind {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (h : hearV f F rs = some (g, G)) :
    unpaid G g.owedObjects = true ∧ unpaid G g.owedPlanes = true ∧ unpaid G g.owedJoin = true := by
  obtain ⟨_, a, b, c⟩ := heard_counts (hearV_messages h).2
  have l := owed_grows h
  exact ⟨unpaid_of_longer l (by omega), unpaid_of_longer l (by omega),
    unpaid_of_longer l (by omega)⟩

/-! ## The leaves' sumcheck, as the program's structure -/

/-- **The leaves' sumcheck is open**: the test of `eqPscRow` (and of `leavesRowOwn`), to the letter.
-/
theorem leaves_open {f : LFace} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (h : hearV f F rs = some (g, G)) :
    (!(toPsc g.leaves).rowMade && (toPsc g.leaves).started && !(toPsc g.leaves).vars.isEmpty &&
      (toPsc g.leaves).r.size == (toPsc g.leaves).vars.size) = true := by
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, _⟩ := leaves_heard f hS (hearV_messages h).2
  obtain ⟨hs, T, R, _, hR, he, _⟩ := MaskedSum.hear_spec h0
  have hlen : R.rounds.length = (leafVars f z).length := MaskedSum.readAll_none_len hR
  have hne : (leafVars f z).isEmpty = false := by
    simp only [MaskedSum.shapeOk, Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hv : g.leaves.vars = leafVars f z := by rw [he]; rfl
  have hrl : g.leaves.r.length = (leafVars f z).length := by rw [he]; simp [hlen]
  cases hq : leafVars f z with
  | nil => simp [hq] at hne
  | cons v vs' => simp [toPsc, hv, hrl, hq]

/-! ## The four together -/

/-- **The structure that the lookup lays is well made**, in the words of the tests that read it: the
count of the lookup's own claims in `eqAll`; the test of `eqPscRow`; the two debts that the runs of
the smallness test mark are not yet marked. -/
theorem heardWellMade (h : Shape) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {g' : OnBytes.Model.Forest.Heard} (hS : Sized F) (hh : hearV (faceOf h) F rs = some (g, G))
    (hg : toHeard h (toHeardG g) = some g') :
    (g'.rows.size == 31 + h.v + h.d + 1) = true ∧
      (!g'.leaves.rowMade && g'.leaves.started && !g'.leaves.vars.isEmpty &&
        g'.leaves.r.size == g'.leaves.vars.size) = true ∧
      unpaid G g'.owedPlanes = true ∧ unpaid G g'.owedJoin = true := by
  obtain ⟨pt, form, hk, hs⟩ := keys_of_hearV h hh
  have hf : g'.rows = g.rows ∧ g'.leaves = toPsc g.leaves ∧ g'.owedPlanes = g.owedPlanes ∧
      g'.owedJoin = g.owedJoin := by
    unfold toHeard at hg
    split at hg
    · simp only at hg
      split at hg
      · cases hg
        exact ⟨rfl, rfl, rfl, rfl⟩
      · cases hg
    · cases hg
  obtain ⟨f1, f2, f3, f4⟩ := hf
  obtain ⟨c1, _, _, _⟩ := heard_counts (hearV_messages hh).2
  obtain ⟨_, u2, u3⟩ := unpaid_behind hh
  refine ⟨?_, ?_, by rw [f3]; exact u2, by rw [f4]; exact u3⟩
  · rw [f1, c1, beq_iff_eq]
    simp [VerifiableInference.Desc.K3.Face.lins, faceOf]
  · rw [f2]
    exact leaves_open hS hh

#print axioms ProofFile.Honest.K3.Law.Digits.hide_owed
#print axioms ProofFile.Honest.K3.Law.Digits.hideSteps_owed
#print axioms ProofFile.Honest.K3.Law.Digits.hideRun_owed
#print axioms ProofFile.Honest.K3.Law.Digits.hear_owed
#print axioms ProofFile.Honest.K3.Law.Digits.row_owed
#print axioms ProofFile.Honest.K3.Law.Digits.whole_owed
#print axioms ProofFile.Honest.K3.Law.Digits.level_owed
#print axioms ProofFile.Honest.K3.Law.Digits.turn_owed
#print axioms ProofFile.Honest.K3.Law.Digits.fold_owed
#print axioms ProofFile.Honest.K3.Law.Digits.run_owed
#print axioms ProofFile.Honest.K3.Law.Digits.Longer.of_eq
#print axioms ProofFile.Honest.K3.Law.Digits.Longer.trans
#print axioms ProofFile.Honest.K3.Law.Digits.Owes.bind
#print axioms ProofFile.Honest.K3.Law.Digits.owes_foldlM
#print axioms ProofFile.Honest.K3.Law.Digits.owes_partsV
#print axioms ProofFile.Honest.K3.Law.Digits.owes_keysV
#print axioms ProofFile.Honest.K3.Law.Digits.owed_grows
#print axioms ProofFile.Honest.K3.Law.Digits.must_true
#print axioms ProofFile.Honest.K3.Law.Digits.owe_spec
#print axioms ProofFile.Honest.K3.Law.Digits.heard_counts
#print axioms ProofFile.Honest.K3.Law.Digits.unpaid_of_longer
#print axioms ProofFile.Honest.K3.Law.Digits.unpaid_behind
#print axioms ProofFile.Honest.K3.Law.Digits.leaves_open
#print axioms ProofFile.Honest.K3.Law.Digits.heardWellMade

end ProofFile.Honest.K3.Law.Digits
