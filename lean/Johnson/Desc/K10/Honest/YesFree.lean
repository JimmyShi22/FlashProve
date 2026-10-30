-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/YesFree.lean: THE YES OF THE CLOSING OF A SEGMENT HANGS ON NO VALUE THAT IS
SENT, AND ON NO CHALLENGE BUT THE ONE THAT "BAT" DRAWS. A theorem on the verifier's own text
(`closeFrame`, Johnson/Desc/First/Close/Closing.lean; the kind's block, Close/Kind.lean). It names no
frame of an honest side.

What is said. Take two lists of rounds OF EQUAL LENGTH that both have the shape of the kind's rounds:
in "BAT" nothing is shown, in "FOLD epsilon" one element, in each "FOLD round" two; each round drew
one element, no position and no matrix entry (of the sealed digest nothing is asked). Let "BAT" have
drawn the same element in both. Then the text says yes at
the one list just if it says yes at the other, at every record in front.

  `Shaped n r`      the round shows n elements and drew one element, no position, no matrix entry
  `ShapedAll rs`    a list of rounds: "BAT", "FOLD epsilon", then any number of rounds of two elements
  `batDraw rs`      what the first round drew
  `closeFrame_free`, `kind_free`   the theorem: of `closeFrame`; of the kind's block's decision

By: `closeFrame_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean): the text says yes just if a
proposition with a conjunct for each guard holds; that proposition is opened here.

Limits. THE CHALLENGE OF "BAT" IS HELD FIXED: that the yes does not hang on it either (the batching
returns, and the batched row passes the fold's test on its sizes, at every element) is not shown
here: Johnson/Desc/K10/Honest/RowFits.lean, Base.lean. `kind_free` is of the block's decision
(`Block.decide`), not of its step (Johnson/Desc/K10/Honest/Step.lean). Nothing here says that the text
says yes at any record. Nothing on what is handed on. Nothing on soundness, completeness or hiding of
the protocol.

-/
import Johnson.Desc.First.Close.Law.CloseMeans
import Johnson.Desc.First.Close.Law.KindDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- The round shows n elements of the extension field, and drew one element, no position and no
matrix entry. Of the sealed digest nothing is asked. -/
def Shaped (n : Nat) (r : Fmt.RoundView) : Prop :=
  (∃ xs : List Fmt.Ext, r.vals = xs.map Fmt.ItemValue.e ∧ xs.length = n) ∧ (∃ t, r.drawn.elems = [t]) ∧
    r.drawn.poss = [] ∧ r.drawn.trits = []

/-- "BAT", "FOLD epsilon", then rounds "FOLD round". -/
def ShapedAll : List Fmt.RoundView → Prop
  | rB :: rE :: rR => Shaped 0 rB ∧ Shaped 1 rE ∧ ∀ r ∈ rR, Shaped 2 r
  | _ => False

/-- What the first round drew. -/
def batDraw (rs : List Fmt.RoundView) : List Fmt.Ext := (rs.head?.map (·.drawn.elems)).getD []

theorem elemsOf_map (xs : List Fmt.Ext) :
    First.Close.elemsOf (xs.map Fmt.ItemValue.e) = some (xs.map E.ofTriple) := by
  unfold First.Close.elemsOf
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- A round's guards pass at every other round of the same shape. -/
theorem heard_swap {name : String} {items roots : Nat} {e : Fmt.Entry} {r r' : Fmt.RoundView}
    {xs : List E} {x : E} (h : HeardMeans name items e r roots xs x) (hs : Shaped items r') :
    ∃ xs' x', HeardMeans name items e r' roots xs' x' ∧ xs'.length = items ∧
      (r'.drawn.elems = r.drawn.elems → x' = x) := by
  obtain ⟨h1, h2, h3, _, ⟨d1, _, _⟩, _, t, ht, hx⟩ := h
  obtain ⟨⟨ys, hv, hl⟩, ⟨t', ht'⟩, hp, hq⟩ := hs
  refine ⟨ys.map E.ofTriple, E.ofTriple t', ⟨h1, h2, h3, ?_, ⟨?_, ?_, ?_⟩, ?_, t', ht', rfl⟩, ?_, ?_⟩
  · rw [hv, List.length_map, hl]
  · rw [ht', ← d1, ht]; rfl
  · rw [hp, h3.2.2.2.2.1]; rfl
  · rw [hq, h3.2.2.2.2.2]; rfl
  · rw [hv, elemsOf_map]
  · rw [List.length_map, hl]
  · intro he
    rw [ht', ht] at he
    rw [hx, List.cons.inj he |>.1]

/-- The rounds "FOLD round". -/
theorem rounds_swap : ∀ (es : List Fmt.Entry) (rs rs' : List Fmt.RoundView) (claim claim' : E)
    (gs : List E) (cl : E), RoundsMeans es rs claim gs cl → rs'.length = rs.length →
    (∀ r ∈ rs', Shaped 2 r) → ∃ gs' cl', RoundsMeans es rs' claim' gs' cl'
  | [], [], [], _, claim', _, _, _, _, _ => ⟨[], claim', rfl, rfl⟩
  | [], [], _ :: _, _, _, _, _, _, hl, _ => by simp at hl
  | e :: es, r :: rs, [], _, _, _, _, _, hl, _ => by simp at hl
  | e :: es, r :: rs, r' :: rs', claim, claim', gs, cl, h, hl, hs => by
    obtain ⟨c0, c2, g, gs₁, hh, hr, _⟩ := h
    obtain ⟨xs', g', hh', hlen, _⟩ := heard_swap hh (hs r' (List.mem_cons_self ..))
    obtain ⟨a, b, rfl⟩ : ∃ a b, xs' = [a, b] := List.length_eq_two.1 hlen
    obtain ⟨gs₂, cl₂, h₂⟩ := rounds_swap es rs rs' _ (foldClaimRound claim' a b g') gs₁ cl hr
      (Nat.succ.inj hl) fun q hq => hs q (List.mem_cons_of_mem _ hq)
    exact ⟨g' :: gs₂, cl₂, a, b, g', gs₂, hh', h₂, rfl⟩
  | [], _ :: _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, h, _, _ => h.elim

/-- One direction. -/
theorem closeFrame_free_of (owed : Option Nat) (f : ReqFrame) (S : Statement)
    (es : List Fmt.Entry) (rs rs' : List Fmt.RoundView) (hl : rs'.length = rs.length)
    (hs : ShapedAll rs') (hb : batDraw rs' = batDraw rs) (y : ReqFrame × Statement)
    (h : closeFrame owed f S es rs = .ok y) : ∃ y', closeFrame owed f S es rs' = .ok y' := by
  obtain ⟨k1, L, k2, G, k3, k4, rows, hc, _⟩ := (closeFrame_iff owed f S es rs y.1 y.2).1 h
  obtain ⟨eB, es₁, rB, rs₁, e1, rfl, m, hm, row, Ly, S1, hbat, hkh, hfold⟩ := hc
  obtain ⟨b1, input, d, b2, xs, x, b3, b4, b5, b6, b7⟩ := hbat
  obtain ⟨eE, eR, rE, rR, rfl, rfl, ⟨s1, s2⟩, f2, f3, f4, f5, d2, f6, sum, eps, f7, f8, gamma,
    claim, f9, _, hS'⟩ := hfold
  match rs', hl, hs, hb with
  | rB' :: rE' :: rR', hl, ⟨t1, t2, t3⟩, hb =>
    obtain ⟨xs', x', u1, _, u3⟩ := heard_swap b3 t1
    have hx : x' = x := u3 (by simpa [batDraw] using hb)
    subst hx
    obtain ⟨ys, eps', v1, vl, _⟩ := heard_swap f7 t2
    obtain ⟨sum', rfl⟩ : ∃ a, ys = [a] := List.length_eq_one_iff.1 vl
    have hlen : rR'.length = rR.length := by simpa using hl
    obtain ⟨gamma', claim', w⟩ := rounds_swap eR rR rR' _ (maddE sum' eps' row.target) gamma claim
      f9 hlen t3
    exact ⟨(_, _), (closeFrame_iff owed f S _ _ _ _).2 ⟨k1, L, k2, G, k3, k4, _,
      ⟨eB, _, rB', _, e1, rfl, m, hm, row, Ly, S1, ⟨b1, input, d, b2, xs', x', u1, b4, b5, b6, b7⟩,
        hkh, eE, eR, rE', rR', rfl, rfl, ⟨s1, hlen.trans s2⟩, f2, f3, f4, f5, d2, f6, sum', eps',
        v1, f8, gamma', claim', w, rfl, rfl⟩, rfl⟩⟩

/-- **THE YES OF `closeFrame` IS THE SAME AT ALL LISTS OF ONE LENGTH OF ROUNDS OF THE KIND's SHAPE IN
WHICH "BAT" DREW THE SAME ELEMENT.** -/
theorem closeFrame_free (owed : Option Nat) (f : ReqFrame) (S : Statement) (es : List Fmt.Entry)
    (rs rs' : List Fmt.RoundView) (hl : rs'.length = rs.length) (hs : ShapedAll rs) (hs' : ShapedAll rs')
    (hb : batDraw rs' = batDraw rs) :
    (∃ y, closeFrame owed f S es rs = .ok y) ↔ ∃ y', closeFrame owed f S es rs' = .ok y' :=
  ⟨fun ⟨y, h⟩ => closeFrame_free_of owed f S es rs rs' hl hs' hb y h,
    fun ⟨y, h⟩ => closeFrame_free_of owed f S es rs' rs hl.symm hs hb.symm y h⟩

/-- **The same of the kind's block's decision.** -/
theorem kind_free {Cl : Type} (P : Par) (s : Rec) (rs rs' : List Fmt.RoundView)
    (gs gs' : List (List (Nat × List UInt64))) (hl : rs'.length = rs.length) (hs : ShapedAll rs)
    (hs' : ShapedAll rs') (hb : batDraw rs' = batDraw rs) :
    (∃ t, ((kind (Cl := Cl)) P).decide s rs gs = .ok t) ↔
      ∃ t', ((kind (Cl := Cl)) P).decide s rs' gs' = .ok t' := by
  have key := closeFrame_free s.owed s.frame s.st (entries P) rs rs' hl hs hs' hb
  constructor
  · rintro ⟨t, h⟩
    obtain ⟨x, hx, _⟩ := (kind_decide_iff P s t rs gs).1 h
    obtain ⟨y, hy⟩ := key.1 ⟨x, hx⟩
    exact ⟨_, (kind_decide_iff P s _ rs' gs').2 ⟨y, hy, rfl⟩⟩
  · rintro ⟨t, h⟩
    obtain ⟨x, hx, _⟩ := (kind_decide_iff P s t rs' gs').1 h
    obtain ⟨y, hy⟩ := key.2 ⟨x, hx⟩
    exact ⟨_, (kind_decide_iff P s _ rs gs).2 ⟨y, hy, rfl⟩⟩

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.heard_swap
#print axioms ProofFile.Honest.K10.YesFree.rounds_swap
#print axioms ProofFile.Honest.K10.YesFree.closeFrame_free
#print axioms ProofFile.Honest.K10.YesFree.kind_free
