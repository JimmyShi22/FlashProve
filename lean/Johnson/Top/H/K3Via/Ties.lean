-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/Ties.lean: the kind "lookup" (K3): what it means that a text on a view's rounds
and a flat text on a tape go together, and the simple pieces. Definitions and theorems.

`Ties R es x y`: x hears rounds (`Hr`, Johnson/Desc/First/Look/Via/Rounds.lean), y is a flat
function (`Fl`, OnBytes/K/Kc/Flat.lean), es are entries of the plan. It says: if every entry of es
passes the tests of the strict reading that read the entry alone (`staticT`,
Johnson/Desc/First/Look/Via/Static.lean), then wherever x says yes, the rounds that it has taken are
such that the strict maker (`tapeT {}`, Johnson/Desc/First/Tape/Tape.lean) makes a tape of them at
es, and y says yes on that tape (with anything behind it), takes just that tape, leaves the same
ledger, and its value stands in R to x's. So the strict tape is made, not assumed: the hearing's own
tests give the strict reading's clauses on the view; `staticT` is what is left of them, and reads no
view.
It is closed under pure, bind, if and a fold over a list (`Ties.pure`, `Ties.bind`, `Ties.ite`,
`Ties.fold`); the entries are laid one list behind the other.
The pieces here: the slot, a debt, a public test, a round of draws against `Fl.point`, one draw
against `Fl.answer`.

Limits. One way: from the yes of the text on rounds to the flat text's yes. A tie: it has no error
term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.Via.Rounds
import Johnson.Desc.First.Look.Via.Static
import Johnson.Top.H.P1Tie.Tie3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Tape (tapeT roundT elemsOf kindAsked)
open VerifiableInference.Desc.K3Cut (bindM mustM)
open First.ProdV (elementsAlone)

/-! ## The strict maker -/

/-- The strict reading returns. -/
theorem roundT_mk {r : Fmt.RoundView} {e : Fmt.Entry} {sent : List E} (h0 : staticT e = true)
    (h1 : MaskedSum.scalars r.vals = some sent) (h2 : r.drawn.elems.length = e.drawE)
    (h3 : r.drawn.poss.isEmpty = true) (h4 : r.drawn.trits.isEmpty = true)
      (h5 : e.msg = 24 * sent.length)
    (h6 : ((r.drawn.elems.drop (e.drawE - e.drawNZ)).all fun x => !isZeroE (E.ofTriple x)) = true) :
    roundT {} r e = some { name := some e.name, nz := e.drawNZ, rows := e.rows, sent := sent,
                           drawn := r.drawn.elems.map E.ofTriple } := by
  unfold staticT at h0
  simp only [Bool.and_eq_true] at h0
  obtain ⟨⟨⟨⟨a1, a2⟩, a3, a4⟩, a5⟩, ⟨a6, a7⟩, a8⟩ := h0
  unfold roundT
  rw [MaskedSum.elemsOf_eq, h1]
  have hc : (r.drawn.elems.length == e.drawE &&
        (r.drawn.poss.isEmpty && e.poss == 0) &&
        (r.drawn.trits.isEmpty && e.trits == 0) &&
        ((e.rows == 0 && e.name != Model.RoundName.batSigma.name) ||
          ({} : First.Tape.TapeRule).rows e) &&
        Params.kindOf e.name == some (({} : First.Tape.TapeRule).kind e.name) &&
        (e.msg == 24 * sent.length && e.roots == 0 && e.answers == 0 && e.count == 1) &&
        ((r.drawn.elems.drop (e.drawE - e.drawNZ)).all fun x => !isZeroE (E.ofTriple x))) =
          true := by
    have b1 : (r.drawn.elems.length == e.drawE) = true := by rw [h2]; exact beq_self_eq_true _
    have b5 : (e.msg == 24 * sent.length) = true := by rw [h5]; exact beq_self_eq_true _
    have a5' : (Params.kindOf e.name == some (({} : First.Tape.TapeRule).kind e.name)) = true := a5
    rw [b1, h3, h4, a1, a2, a3, a4, a5', b5, a6, a7, a8, h6]
    rfl
  show (if _ then _ else none) = _
  rw [if_pos hc]

theorem tapeT_cons_mk {rule : First.Tape.TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {x : FlatRound}
    {rs : List Fmt.RoundView}
    {es : List Fmt.Entry} {t : Tape} (h1 : roundT rule r e = some x)
      (h2 : tapeT rule rs es = some t) :
    tapeT rule (r :: rs) (e :: es) = some (x :: t) := by
  simp only [tapeT, h1, h2]

theorem tapeT_one {rule : First.Tape.TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {x : FlatRound}
    (h1 : roundT rule r e = some x) : tapeT rule [r] [e] = some [x] := tapeT_cons_mk h1 rfl

theorem tapeT_cons_some {rule : First.Tape.TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {rs : List Fmt.RoundView}
    {es : List Fmt.Entry} {t : Tape} (h : tapeT rule (r :: rs) (e :: es) = some t) :
    ∃ x t', roundT rule r e = some x ∧ tapeT rule rs es = some t' ∧ t = x :: t' := by
  simp only [tapeT] at h
  cases hx : roundT rule r e with
  | none => simp [hx] at h
  | some x =>
    cases ht : tapeT rule rs es with
    | none => simp [hx, ht] at h
    | some t' =>
      simp only [hx, ht, Option.some.injEq] at h
      exact ⟨x, t', rfl, rfl, h.symm⟩

/-- Rounds after rounds, at entries after entries. -/
theorem tapeT_append {rule : First.Tape.TapeRule} :
    ∀ (a : List Fmt.RoundView) (ea : List Fmt.Entry) (ta : Tape)
    (b : List Fmt.RoundView) (eb : List Fmt.Entry) (tb : Tape), tapeT rule a ea = some ta →
      tapeT rule b eb = some tb →
    tapeT rule (a ++ b) (ea ++ eb) = some (ta ++ tb)
  | [], [], ta, b, eb, tb, h1, h2 => by
    have e : some ([] : Tape) = some ta := h1
    cases e
    exact h2
  | r :: a, e :: ea, ta, b, eb, tb, h1, h2 => by
    obtain ⟨x, t', k1, k2, k3⟩ := tapeT_cons_some h1
    subst k3
    exact tapeT_cons_mk k1 (tapeT_append a ea t' b eb tb k2 h2)
  | [], _ :: _, ta, b, eb, tb, h1, h2 => by
    have e : (none : Option Tape) = some ta := h1
    cases e
  | _ :: _, [], ta, b, eb, tb, h1, h2 => by
    have e : (none : Option Tape) = some ta := h1
    cases e

/-! ## A text that hears: where it returns -/

namespace Hr
variable {α β : Type}

theorem bindS {x : Hr α} {f : α → Hr β} {F : Fork} {rs : List Fmt.RoundView} {r : β × Fork × List Fmt.RoundView}
    (h : (x >>= f) F rs = some r) : ∃ a G rest, x F rs = some (a, G, rest) ∧ f a G rest =
      some r := by
  have h' : Hr.andThen x f F rs = some r := h
  unfold Hr.andThen at h'
  cases hx : x F rs with
  | none =>
    rw [hx] at h'
    have h2 : (none : Option (β × Fork × List Fmt.RoundView)) = some r := h'
    cases h2
  | some y =>
    obtain ⟨a, G, rest⟩ := y
    rw [hx] at h'
    exact ⟨a, G, rest, rfl, h'⟩

theorem pureS {a b : α} {F G : Fork} {rs rest : List Fmt.RoundView}
    (h : (pure a : Hr α) F rs = some (b, G, rest)) :
    b = a ∧ G = F ∧ rest = rs := by
  have e : some (a, F, rs) = some (b, G, rest) := h
  cases e
  exact ⟨rfl, rfl, rfl⟩

theorem mustS {b : Bool} {x : Unit} {F G : Fork} {rs rest : List Fmt.RoundView}
    (h : Hr.must b F rs = some (x, G, rest)) :
    b = true ∧ G = F ∧ rest = rs := by
  cases b with
  | false =>
    have e : (none : Option (Unit × Fork × List Fmt.RoundView)) = some (x, G, rest) := h
    cases e
  | true =>
    have e : some ((), F, rs) = some (x, G, rest) := h
    cases e
    exact ⟨rfl, rfl, rfl⟩

end Hr

/-! ## Going together -/

/-- **x on a view's rounds and y on the strict tape of these rounds go together**, at the entries
es. -/
def Ties {α β : Type} (R : α → β → Prop) (es : List Fmt.Entry) (x : Hr α) (y : Fl β) : Prop :=
  es.all staticT = true → ∀ (F G : Fork) (rs rest : List Fmt.RoundView) (a : α), x F rs =
    some (a, G, rest) →
    ∃ (used : List Fmt.RoundView) (t : Tape) (b : β), rs = used ++ rest ∧ tapeT {} used es = some t ∧
      R a b ∧
      ∀ u : Tape, y F (t ++ u) = some (b, G, u)

namespace Ties
variable {α β γ δ : Type}

theorem pure {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Ties R [] (Pure.pure a : Hr α) (Pure.pure b : Fl β) := by
  intro _ F G rs rest a' e
  obtain ⟨rfl, rfl, rfl⟩ := Hr.pureS e
  exact ⟨[], [], b, rfl, rfl, h, fun _ => rfl⟩

theorem bind {R : α → β → Prop} {S : γ → δ → Prop} {es1 es2 : List Fmt.Entry} {x : Hr α} {y : Fl β}
    {f : α → Hr γ}
    {g : β → Fl δ} (h1 : Ties R es1 x y) (h2 : ∀ a b, R a b → Ties S es2 (f a) (g b)) :
    Ties S (es1 ++ es2) (x >>= f) (y >>= g) := by
  intro hs F G rs rest c hc
  rw [List.all_append, Bool.and_eq_true] at hs
  obtain ⟨a, F1, r1, e1, e2⟩ := Hr.bindS hc
  obtain ⟨u1, t1, b, q1, q2, q3, q4⟩ := h1 hs.1 F F1 rs r1 a e1
  obtain ⟨u2, t2, d, p1, p2, p3, p4⟩ := h2 a b q3 hs.2 F1 G r1 rest c e2
  refine
    ⟨u1 ++ u2, t1 ++ t2, d, by rw [q1, p1,
      List.append_assoc], tapeT_append _ _ _ _ _ _ q2 p2, p3, fun u => ?_⟩
  rw [List.append_assoc]
  exact bindM (q4 (t2 ++ u)) (p4 u)

/-- The relation may be widened. -/
theorem mono {R S : α → β → Prop} {es : List Fmt.Entry} {x : Hr α} {y : Fl β} (h : Ties R es x y)
    (hrs : ∀ a b, R a b → S a b) : Ties S es x y := by
  intro hs F G rs rest a e
  obtain ⟨u, t, b, q1, q2, q3, q4⟩ := h hs F G rs rest a e
  exact ⟨u, t, b, q1, q2, hrs a b q3, q4⟩

theorem ite {R : α → β → Prop} {e1 e2 : List Fmt.Entry} {x1 x2 : Hr α} {y1 y2 : Fl β} (c : Bool)
    (h1 : Ties R e1 x1 y1) (h2 : Ties R e2 x2 y2) :
    Ties R (if c then e1 else e2) (if c then x1 else x2) (if c then y1 else y2) := by
  cases c with
  | true => exact h1
  | false => exact h2

theorem fold {σ τ ι : Type} {R : σ → τ → Prop} (kf : ι → List Fmt.Entry) (f : σ → ι → Hr σ)
    (g : τ → ι → Fl τ)
    (hstep : ∀ i a b, R a b → Ties R (kf i) (f a i) (g b i)) :
    ∀ (l : List ι) (a : σ) (b : τ), R a b → Ties R (l.flatMap kf) (l.foldlM f a) (l.foldlM g b)
  | [], a, b, h => by
    rw [List.foldlM_nil, List.foldlM_nil]
    exact Ties.pure h
  | i :: l, a, b, h => by
    rw [List.foldlM_cons, List.foldlM_cons, List.flatMap_cons]
    exact Ties.bind (hstep i a b h) (fun a' b' h' => fold kf f g hstep l a' b' h')

end Ties

/-! ## The simple pieces -/

theorem ties_slot : Ties (fun a b => b = a) [] Hr.slot Fl.slot := by
  intro _ F G rs rest a e
  have e' : some (F.next, F, rs) = some (a, G, rest) := e
  cases e'
  exact ⟨[], [], F.next, rfl, rfl, rfl, fun _ => rfl⟩

theorem ties_owe (what : String) : Ties (fun a b => b = a) [] (Hr.owe what) (Fl.owe what) := by
  intro _ F G rs rest a e
  have e' : some ((F.owe what).1, (F.owe what).2, rs) = some (a, G, rest) := e
  cases e'
  exact ⟨[], [], (F.owe what).1, rfl, rfl, rfl, fun _ => rfl⟩

theorem ties_must (b : Bool) : Ties (fun _ _ => True) [] (Hr.must b) (Fl.must b) := by
  intro _ F G rs rest a e
  obtain ⟨rfl, rfl, rfl⟩ := Hr.mustS e
  exact ⟨[], [], (), rfl, rfl, trivial, fun _ => rfl⟩

/-- No draw is asked to be other than 0: the strict reading's seventh clause is idle. -/
theorem nz_none (l : List (UInt64 × UInt64 × UInt64)) (n : Nat) (h : l.length = n) :
    ((l.drop (n - 0)).all fun x => !isZeroE (E.ofTriple x)) = true := by
  subst h
  simp

theorem alone_one {r : Fmt.RoundView} (h : elementsAlone [r] = true) :
    r.drawn.poss.isEmpty = true ∧ r.drawn.trits.isEmpty = true := by
  have h' : ((r.drawn.poss.isEmpty && r.drawn.trits.isEmpty) && true) = true := h
  rw [Bool.and_true, Bool.and_eq_true] at h'
  exact h'

/-- Where a round of draws is heard. -/
theorem draws_some {n : Nat} {F G : Fork} {rs rest : List Fmt.RoundView} {a : Array E}
    (h : drawsV n F rs = some (a, G, rest)) :
    ∃ r, rs = r :: rest ∧ G = F ∧ a = (r.drawn.elems.map E.ofTriple).toArray ∧
      r.drawn.elems.length = n ∧
      MaskedSum.scalars r.vals = some [] ∧ r.drawn.poss.isEmpty = true ∧ r.drawn.trits.isEmpty =
        true := by
  cases rs with
  | nil =>
    have e : (none : Option (Array E × Fork × List Fmt.RoundView)) = some (a, G, rest) := h
    cases e
  | cons r rs' =>
    have h' : (if elementsAlone [r] then (MaskedSum.roundOf 0 n r).map
      (fun x => (x.2.toArray, F, rs')) else none) =
        some (a, G, rest) := h
    split at h'
    · rename_i hc
      cases hr : MaskedSum.roundOf 0 n r with
      | none =>
        rw [hr] at h'
        have e : (none : Option (Array E × Fork × List Fmt.RoundView)) = some (a, G, rest) := h'
        cases e
      | some sd =>
        obtain ⟨s, d⟩ := sd
        rw [hr] at h'
        have e : some (d.toArray, F, rs') = some (a, G, rest) := h'
        cases e
        obtain ⟨a1, a2, a3, a4⟩ := MaskedSum.roundOf_some hr
        have s0 : s = [] := List.eq_nil_of_length_eq_zero a2
        subst s0 a4
        obtain ⟨c1, c2⟩ := alone_one hc
        exact ⟨r, rfl, rfl, rfl, a3, a1, c1, c2⟩
    · cases h'

theorem static_one {e : Fmt.Entry} (h : [e].all staticT = true) : staticT e = true := by
  have h' : (staticT e && true) = true := h
  rw [Bool.and_true] at h'
  exact h'

theorem closeN_mk (name : String) (nz w : Nat) (d : List E) (t : Tape) :
    closeN name nz d.length (⟨some name, nz, w, [], d⟩ :: t) = some (d, t) := by
  simp [closeN]

/-- The strict tape's round of a round of draws. -/
theorem draw_round {name : String} {n : Nat} {r : Fmt.RoundView} (h0 : staticT (drawEntry name n) = true)
    (h1 : MaskedSum.scalars r.vals = some []) (h2 : r.drawn.elems.length = n)
      (h3 : r.drawn.poss.isEmpty = true)
    (h4 : r.drawn.trits.isEmpty = true) :
    roundT {} r (drawEntry name n) = some ⟨some name, 0, 0, [], r.drawn.elems.map E.ofTriple⟩ :=
  roundT_mk h0 h1 h2 h3 h4 rfl (nz_none _ n h2)

/-- **A round of draws.** -/
theorem ties_draws (rn : Model.RoundName) (n : Nat) :
    Ties (fun a b => b = a) [drawEntry rn.name n] (drawsV n) (Fl.point rn n) := by
  intro hs F G rs rest a h
  obtain ⟨r, rfl, rfl, rfl, a3, a1, c1, c2⟩ := draws_some h
  refine ⟨[r], _, _, rfl, tapeT_one (draw_round (static_one hs) a1 a3 c1 c2), rfl, fun u => ?_⟩
  have hl : (r.drawn.elems.map E.ofTriple).length = n := by rw [List.length_map]; exact a3
  have hp : Fl.pointOn rn.name n (⟨some rn.name, 0, 0, [], r.drawn.elems.map E.ofTriple⟩ :: u) =
      some ((r.drawn.elems.map E.ofTriple).toArray, u) := by
    unfold Fl.pointOn
    rw [← hl, closeN_mk]
    rfl
  exact MaskedSum.onTapeM hp G

/-- **One draw.** -/
theorem ties_draw (rn : Model.RoundName) :
    Ties (fun a b => b = a) [drawEntry rn.name 1] drawV (Fl.answer rn) := by
  intro hs F G rs rest a h
  cases hd : drawsV 1 F rs with
  | none =>
    have h' : (match drawsV 1 F rs with
      | some (x, G, rest) => if x.size == 1 then some (x.getD 0 zeroE, G, rest) else none
      | none => none) = some (a, G, rest) := h
    rw [hd] at h'
    have e : (none : Option (E × Fork × List Fmt.RoundView)) = some (a, G, rest) := h'
    cases e
  | some y =>
    obtain ⟨x, G', rest'⟩ := y
    have h' : (match drawsV 1 F rs with
      | some (x, G, rest) => if x.size == 1 then some (x.getD 0 zeroE, G, rest) else none
      | none => none) = some (a, G, rest) := h
    rw [hd] at h'
    obtain ⟨r, rfl, rfl, rfl, a3, a1, c1, c2⟩ := draws_some hd
    obtain ⟨g, eg⟩ := MaskedSum.one_of_length (r.drawn.elems.map E.ofTriple)
      (by rw [List.length_map]; exact a3)
    rw [eg] at h'
    have e : some (g, G', rest') = some (a, G, rest) := h'
    cases e
    refine ⟨[r], _, _, rfl, tapeT_one (draw_round (static_one hs) a1 a3 c1 c2), rfl, fun u => ?_⟩
    rw [eg]
    exact MaskedSum.onTapeM (MaskedSum.closeOne_mk rn.name 0 0 a u) G

end VerifiableInference.Desc.K3
