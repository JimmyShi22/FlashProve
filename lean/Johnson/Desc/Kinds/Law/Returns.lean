-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Returns.lean.
WHAT IT DOES NOT SHOW. That any form is worth 0; that the rounds are an honest prover's; that the
ledger which the verifier makes has the room that is asked here (Fresh is a premise). Nothing on
soundness, on probabilities or on hiding.
WHAT IT IS. THE PARTS OF A HEARING (HeadParts.lean) RETURN. All lemmas on these parts that lay so
far go FROM a return (Law/Sum2b.lean: heardBy_spec, sumcheck_spec; Law/Cut.lean). Here is the other
direction, part by part, on rounds as the view shows them (Part/MaskedSumHonest.lean: rvOf).
  Fresh F n          n more numbers are there, and every number from the next on is free.
  round_returns, drawPoint_returns, hide_returns, sendThenBatch_returns, hiddenFrom_returns
  own_length         the hiding polynomial has as many coefficients as the call has own numbers.
  heardBy_returns    at rounds t that the part's reader takes (readAll, leadScalars), a start form
                     with a public part behind the lead's laying, and a Fresh ledger: heardBy
                     returns on t ++ rest and leaves rest; the ledger behind is Fresh with what is
                     left; every field of what the part's hearing handed back.
  sumcheck_returns, level_returns   the same for the two callers; a sumcheck's start form is the one
                     slot of its claimed sum, whose public part is there: no premise on it is left.
The part's own half is Part/MaskedSumReturns.lean (hideRun_returns, hear_returns, rowLaid_returns).
own_length's lines stand inside Law/LevelLaw.lean (coreL).

-/
import Mathlib
import Johnson.Desc.Part.MaskedSumReturns
import Johnson.Desc.Kinds.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE subE)
open OnBytes.Model (Aff Fork)
open Came (bind_eq)
open Part.MaskedSum (Var Call Ends Sent VarsRead readAll leadScalars ownSlots hidingAt rowLaid
  challenges FreeIn Marked rvOf roundOf_of hideRun_returns hear_returns rowLaid_returns
  shown_returns)

/-- n more numbers are there, and every number from the next on is free. -/
def Fresh (F : Fork) (n : Nat) : Prop := F.next + n ≤ F.ns ∧ FreeIn F F.next F.ns

theorem Fresh.less {F : Fork} {n m : Nat} (h : Fresh F n) (hm : m ≤ n) : Fresh F m :=
  ⟨by have := h.1; omega, h.2⟩

/-! ## The small parts -/

theorem round_returns (s dr : List E) (F : Fork) (rest : List Fmt.RoundView) :
    Hear.round s.length dr.length F (rvOf s dr :: rest) = some ((s, dr), F, rest) := by
  unfold Hear.round
  simp only [roundOf_of, Option.map_some]

theorem drawPoint_returns (pts : List E) (F : Fork) (rest : List Fmt.RoundView) :
    drawPoint pts.length F (rvOf [] pts :: rest) = some (pts.toArray, F, rest) := by
  unfold drawPoint
  rw [bind_eq (show Hear.round 0 pts.length F (rvOf [] pts :: rest) = some (([], pts), F, rest)
    from round_returns [] pts F rest)]
  rfl

/-- The hidden scalars that a laying of v hands back. -/
def hidOf (first : Nat) (v : List E) : Array Hid :=
  v.toArray.mapIdx fun j x => { var := Aff.slot (first + j), shown := x }

theorem hide_returns (v : List E) {F : Fork} {m : Nat} (h : Fresh F (v.length + m))
    (rs : List Fmt.RoundView) :
    ∃ G, hide v F rs = some (hidOf F.next v, G, rs) ∧ G.next = F.next + v.length ∧ G.ns = F.ns ∧
      Fresh G m ∧ ∀ i z, G.gotF.getD i z =
        if F.next ≤ i ∧ i < F.next + v.length then true else F.gotF.getD i z := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨G, hG, g1, g2, g3, g4⟩ := hideRun_returns
    ({ F with next := F.next + v.length } : Fork) F.next v.toArray oneE
    (by rw [List.size_toArray]; exact FreeIn.sub h2 (le_refl _) (by omega))
  rw [List.size_toArray] at g4
  refine ⟨G, ?_, g2, g1, ⟨?_, ?_, g3, fun j a b => ?_⟩, g4⟩
  · unfold hide
    rw [hG]
    rfl
  · rw [g2, g1]
    show F.next + v.length + m ≤ F.ns
    omega
  · exact le_refl _
  · rw [g2] at a
    have a' : F.next + v.length ≤ j := a
    rw [g4, if_neg (by omega)]
    exact h2.2.2 j (by omega) (by rw [g1] at b; exact b)

theorem sendThenBatch_returns (v : List E) (g : E) (rows : Nat) {F : Fork} {m : Nat}
    (h : Fresh F (v.length + m)) (rest : List Fmt.RoundView) :
    ∃ G, sendThenBatch v.length rows F (rvOf v [g] :: rest) = some ((hidOf F.next v, g), G, rest) ∧
      G.next = F.next + v.length ∧ G.ns = F.ns ∧ Fresh G m ∧ ∀ i z, G.gotF.getD i z =
        if F.next ≤ i ∧ i < F.next + v.length then true else F.gotF.getD i z := by
  obtain ⟨G, hG, g1, g2, g3, g4⟩ := hide_returns v h rest
  refine ⟨G, ?_, g1, g2, g3, g4⟩
  unfold sendThenBatch
  rw [bind_eq (show Hear.round v.length 1 F (rvOf v [g] :: rest) = some ((v, [g]), F, rest)
    from round_returns v [g] F rest)]
  dsimp only
  rw [bind_eq hG]
  rfl

theorem mapM_returns {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ a ∈ l, ∃ b, f a = some b) →
    ∃ r, l.mapM f = some r
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a (by simp)
    obtain ⟨r, hr⟩ := mapM_returns f l fun x hx => h x (by simp [hx])
    exact ⟨b :: r, by simp [List.mapM_cons, hb, hr]⟩

theorem hiddenFrom_returns (first n : Nat) (F : Fork) (rs : List Fmt.RoundView) (hn : first + n ≤ F.ns)
    (hg : ∀ j, j < n → F.gotF.getD (first + j) false = true) :
    ∃ es, hiddenFrom first n F rs = some (es, F, rs) := by
  obtain ⟨r, hr⟩ := mapM_returns (fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) (List.range n) fun j hj => by
    have hj' : j < n := List.mem_range.mp hj
    dsimp only
    rw [shown_returns (by omega) (hg j hj')]
    exact ⟨_, rfl⟩
  refine ⟨r.toArray, ?_⟩
  unfold hiddenFrom
  rw [hr]
  rfl

/-! ## The masked sumcheck as HeadParts.lean hears it -/

/-- The hiding polynomial has as many coefficients as the call has own numbers. -/
theorem own_length (lead : Nat) (z : Point) (ends : Nat) {t : List Fmt.RoundView}
    {R : Part.MaskedSum.Read} (hR : readAll (callOf lead z ends) t = some R) :
    (hidingAt ((callOf lead z ends).all.zip (R.rounds.map (·.2)))).1.length =
      ownSlots (callOf lead z ends).all := by
  obtain ⟨_, _, _, _, _, _, _, hvr, _⟩ := Part.MaskedSum.readAll_spec
    (show readAll ⟨lead, z.toList.map (.point · 3), some ⟨2, ends⟩⟩ t = some R from hR)
  have hlenR : R.rounds.length = (callOf lead z ends).all.length := hvr.length.2
  have hz : ((callOf lead z ends).all.zip (R.rounds.map (·.2))).map (·.1) =
      (callOf lead z ends).all := List.map_fst_zip (by rw [List.length_map, hlenR])
  have hd : ∀ v ∈ (callOf lead z ends).all, v.d = 3 := by
    intro v hv
    have hm : v ∈ z.toList.map (Var.point · 3) ++ [Var.point zeroE 3] := hv
    rcases List.mem_append.mp hm with h | h
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
      rfl
    · rw [List.mem_singleton] at h
      rw [h]
      rfl
  rw [hidingAt_length _ ?_ ?_, hz]
  · intro e
    have := congrArg (List.map (·.1)) e
    rw [hz] at this
    exact absurd this (by
      show z.toList.map (Var.point · 3) ++ [Var.point zeroE 3] ≠ []
      simp)
  · intro x hx
    have : x.1 ∈ (callOf lead z ends).all := by
      rw [← hz]
      exact List.mem_map_of_mem hx
    rw [hd _ this]
    omega

theorem shape_callOf (lead : Nat) (z : Point) {ends : Nat} (he : 1 ≤ ends) :
    Part.MaskedSum.shapeOk (callOf lead z ends) = true := by
  simp only [callOf, Part.MaskedSum.shapeOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq]
  refine ⟨fun v hv => ?_, by omega, he⟩
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
  exact ⟨by show 2 ≤ 3; omega, by show 3 ≤ 65; omega⟩

/-- What the part's hearing hands back, of what was read. -/
def heardRec (C : Form) (T : E) (R : Part.MaskedSum.Read) (k : Call) (first : Nat) :
    Part.MaskedSum.Heard :=
  { start := C, target := T, eps := R.eps,
    claim := Part.MaskedSum.after k.all R.rounds (addE R.mu (mulE R.eps T)), first := first,
    vars := k.all, r := R.rounds.map (·.2), sEnd := first + ownSlots k.all }

/-- **heardBy RETURNS.** own: the call's own numbers. m: the numbers that are left free. -/
theorem heardBy_returns (lead : Nat) (C : Array Hid → Form) (z : Point) {ends : Nat}
    (he : 1 ≤ ends) {F : Fork} {m : Nat} {t : List Fmt.RoundView} {ld : List E}
    {R : Part.MaskedSum.Read} (hlen : t.length = z.size + 3)
    (hld : leadScalars (callOf lead z ends) t = some ld)
    (hR : readAll (callOf lead z ends) t = some R) (hv : R.values.length = ends)
    (hF : Fresh F (ld.length + (ownSlots (callOf lead z ends).all + ends + m)))
    (hT : ∀ Fa, hide ld F [] = some (hidOf F.next ld, Fa, []) →
      ∃ T, Fa.publicPart (C (hidOf F.next ld)) = some T)
    (rest : List Fmt.RoundView) :
    ∃ (T : E) (es : Array Hid) (Fa F1 : Fork),
      hide ld F [] = some (hidOf F.next ld, Fa, []) ∧
      Fa.publicPart (C (hidOf F.next ld)) = some T ∧
      heardBy lead C z ends F (t ++ rest) = some ((hidOf F.next ld,
        { r := (challenges (callOf lead z ends)
            (heardRec (C (hidOf F.next ld)) T R (callOf lead z ends) (F.next + ld.length))).toArray,
          ends := es,
          psc := some
            (heardRec (C (hidOf F.next ld)) T R (callOf lead z ends) (F.next + ld.length)) }),
        F1, rest) ∧
      F1.next = F.next + ld.length + ownSlots (callOf lead z ends).all + ends ∧ F1.ns = F.ns ∧
      Fresh F1 m := by
  obtain ⟨Fa, a0, a1, a2, a3, a4⟩ := hide_returns ld hF []
  obtain ⟨T, hTa⟩ := hT Fa a0
  have a0' := (hide_returns ld hF rest)
  obtain ⟨Fa', b0, _⟩ := a0'
  have hFa : Fa' = Fa := by
    obtain ⟨_, e⟩ := hide_some b0
    rw [a0] at e
    simp only [Option.some.injEq, Prod.mk.injEq, and_true, true_and] at e
    exact e.symm
  subst hFa
  -- the part's hearing
  obtain ⟨G, hG, g1, g2, g3, g4⟩ := hear_returns (C (hidOf F.next ld)) (callOf lead z ends)
    (shape_callOf lead z he) Fa' T hTa t R hR
    (FreeIn.sub a3.2 (by omega) (by have := a3.1; rw [hv]; omega))
  rw [hv] at g2 g4
  -- the row's writing
  have hown := own_length lead z ends hR
  obtain ⟨F1, hF1, f1, f2, f3, f4⟩ := rowLaid_returns
    (heardRec (C (hidOf F.next ld)) T R (callOf lead z ends) Fa'.next) G
    ⟨by
      show Fa'.next + (hidingAt ((callOf lead z ends).all.zip (R.rounds.map (·.2)))).1.length ≤ G.ns
      rw [hown, g1]
      have := a3.1
      omega, g3, fun j j1 j2 => by
      have j1' : Fa'.next ≤ j := j1
      have j2' : j < Fa'.next +
          (hidingAt ((callOf lead z ends).all.zip (R.rounds.map (·.2)))).1.length := j2
      rw [hown] at j2'
      rw [g4, if_neg (by omega)]
      exact a3.2.2.2 j j1' (by have := a3.1; omega)⟩
  have f4' : ∀ i z', F1.gotF.getD i z' =
      if Fa'.next ≤ i ∧ i < Fa'.next + ownSlots (callOf lead z ends).all then true
      else G.gotF.getD i z' := by
    intro i z'
    have h0 : F1.gotF.getD i z' = if Fa'.next ≤ i ∧ i < Fa'.next +
        (hidingAt ((callOf lead z ends).all.zip (R.rounds.map (·.2)))).1.length then true
        else G.gotF.getD i z' := f4 i z'
    rw [hown] at h0
    exact h0
  -- the end values
  obtain ⟨es, hes⟩ := hiddenFrom_returns (Fa'.next + ownSlots (callOf lead z ends).all) ends F1 rest
    (by rw [f1, g1]; have := a3.1; omega) fun j hj => by
      rw [f4', if_neg (by omega), g4, if_pos (by omega)]
  refine ⟨T, es, Fa', F1, a0, hTa, ?_, ?_, by rw [f1, g1, a2], ?_, ?_, f3, fun j j1 j2 => ?_⟩
  · unfold heardBy
    have hst : Hear.stretch (z.size + 3) F (t ++ rest) = some (t, F, rest) := by
      unfold Hear.stretch
      rw [if_neg (by rw [List.length_append]; omega), ← hlen, List.take_left, List.drop_left]
    rw [bind_eq hst]
    have hn1 : Hear.need (leadScalars (callOf lead z ends) t) F rest = some (ld, F, rest) := by
      unfold Hear.need
      rw [hld]
      rfl
    rw [bind_eq (show Hear.need (leadScalars
      { lead := lead, vs := z.toList.map (.point · 3), ends := some ⟨2, ends⟩ } t) F rest =
        some (ld, F, rest) from hn1), bind_eq b0,
      bind_eq (show Hear.ledger Fa' rest = some (Fa', Fa', rest) from rfl)]
    have hn2 : Hear.need (Part.MaskedSum.hear (C (hidOf F.next ld))
        { lead := lead, vs := z.toList.map (.point · 3), ends := some ⟨2, ends⟩ } Fa' t) Fa' rest =
        some ((heardRec (C (hidOf F.next ld)) T R (callOf lead z ends) Fa'.next, G), Fa',
          rest) := by
      unfold Hear.need
      rw [show Part.MaskedSum.hear (C (hidOf F.next ld))
        { lead := lead, vs := z.toList.map (.point · 3), ends := some ⟨2, ends⟩ } Fa' t = _ from hG]
      rfl
    rw [bind_eq hn2]
    dsimp only
    have hn3 : Hear.need (rowLaid (heardRec (C (hidOf F.next ld)) T R (callOf lead z ends) Fa'.next)
        G) Fa' rest = some (F1, Fa', rest) := by
      unfold Hear.need
      rw [hF1]
      rfl
    rw [bind_eq hn3, bind_eq (show Hear.lay F1 Fa' rest = some ((), F1, rest) from rfl),
      bind_eq (show hiddenFrom
        (heardRec (C (hidOf F.next ld)) T R (callOf lead z ends) Fa'.next).sEnd ends F1 rest =
          some (es, F1, rest) from hes), a1]
    rfl
  · rw [f2, g2, a1]
  · rw [f2, g2, f1, g1, a1, a2]
    have := hF.1
    omega
  · exact le_refl _
  · rw [f2, g2] at j1
    rw [f4', if_neg (by omega), g4, if_neg (by omega)]
    exact a3.2.2.2 j (by omega) (by rw [f1, g1] at j2; exact j2)

end VerifiableInference.Desc.Kinds.Head.Law
