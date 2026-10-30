-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Takes.lean: HOW MANY NUMBERS OF THE LEDGER THE OUTPUT HEAD's HEARING TAKES, AND WHERE IT WRITES.
Takes F G t: the next number has moved on by just t; G is F but for what lies under the t numbers from
F's next on (no mark, shown value or factor turns below F's next, nor from G's next on); and each of
these t numbers is filled in G. Closed under "one behind the other", where the counts add.
  takes_hide · takes_heardBy · takes_sumcheck · takes_level · takes_send   the parts of HeadParts.lean's hearings: a
        masked sumcheck in n variables with m end values and a lead of l takes l + (2 n + 3) + m.
  hear_takes   WHERE Head.lean's hear RETURNS, from a ledger with a place for each number:
        Takes F G (41 + 4 lt + 4 |zt| + 4 lPd): AT |zt| = lt: 41 + 8 lt + 4 lPd: numbers of the plan alone.
WHAT IT IS NOT. Nothing on soundness. Not in the words of OnBytes/Tie/Pv/Psc/PscRoom.lean (LedgerRoom, WritesAbove:
not imported). |zt| = lt is not shown here: zt is a letter that comes in from the lookup's point.
INSIDE a sumcheck the row's laying writes below the hearing's own next number: between two ledgers of
this proof's own; against the ledger that the hearing is handed nothing is written below its next.
THIS FILE IMPORTS NO Block.lean, State.lean OR Tape.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.KeepsHear
import Johnson.Desc.Kinds.Law.Decode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Sized hideRun_ok)
open Norm (lt lPd)
open Part.MaskedSum (ownSlots hidingAt)

/-- G is F but for the next number and for what lies under the numbers from lo up to hi. -/
structure Touch (F G : Fork) (lo hi : Nat) : Prop where
  sized : Sized G
  ns : G.ns = F.ns
  out : ∀ j, (j < lo ∨ hi ≤ j) → G.vp.getD j zeroE = F.vp.getD j zeroE ∧
    G.mf.getD j zeroE = F.mf.getD j zeroE ∧ (OnBytes.PscRun.Filled G j ↔ OnBytes.PscRun.Filled F j)

theorem Touch.refl {F : Fork} (h : Sized F) (lo hi : Nat) : Touch F F lo hi :=
  ⟨h, rfl, fun _ _ => ⟨rfl, rfl, Iff.rfl⟩⟩

theorem Touch.trans {F G H : Fork} {lo hi : Nat} (a : Touch F G lo hi) (b : Touch G H lo hi) :
    Touch F H lo hi :=
  ⟨b.sized, b.ns.trans a.ns, fun j hj => by
    obtain ⟨a1, a2, a3⟩ := a.out j hj
    obtain ⟨b1, b2, b3⟩ := b.out j hj
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3⟩⟩

theorem Touch.mono {F G : Fork} {lo hi lo' hi' : Nat} (a : Touch F G lo hi) (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') : Touch F G lo' hi' :=
  ⟨a.sized, a.ns, fun j hj => a.out j (by omega)⟩

theorem touch_next {F : Fork} (h : Sized F) (n lo hi : Nat) : Touch F { F with next := n } lo hi :=
  ⟨h, rfl, fun _ _ => ⟨rfl, rfl, Iff.rfl⟩⟩

/-- A run of layings: where it writes, what it fills, and that it keeps the next number. -/
theorem touch_hideRun {F G : Fork} {first : Nat} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) :
    Touch F G first (first + v.size) ∧ G.next = F.next ∧
      ∀ j, first ≤ j → j < first + v.size → OnBytes.PscRun.Filled G j := by
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok F G first v f hF h
  refine ⟨⟨a2, a1.ns, fun j hj => a4 j hj⟩, a1.next, fun j h1 h2 => ?_⟩
  have e : first + (j - first) = j := by omega
  have := (a3 (j - first) (by omega)).2.2.1
  rwa [e] at this

/-- **The hearing has taken just t numbers.** -/
structure Takes (F G : Fork) (t : Nat) : Prop where
  next : G.next = F.next + t
  touch : Touch F G F.next (F.next + t)
  full : ∀ j, F.next ≤ j → j < F.next + t → OnBytes.PscRun.Filled G j

theorem Takes.refl {F : Fork} (h : Sized F) : Takes F F 0 :=
  ⟨rfl, Touch.refl h _ _, fun j h1 h2 => by omega⟩

theorem Takes.trans {F G H : Fork} {a b : Nat} (x : Takes F G a) (y : Takes G H b) :
    Takes F H (a + b) := by
  have hn := x.next
  refine ⟨by rw [y.next, hn]; omega, ?_, fun j h1 h2 => ?_⟩
  · exact (x.touch.mono (Nat.le_refl _) (by omega)).trans (y.touch.mono (by omega) (by omega))
  · by_cases hj : j < G.next
    · exact ((y.touch.out j (Or.inl hj)).2.2).2 (x.full j h1 (by omega))
    · exact y.full j (by omega) (by omega)

theorem Takes.cast {F G : Fork} {a b : Nat} (x : Takes F G a) (h : a = b) : Takes F G b := h ▸ x

/-- It writes above: the next number is not lowered, and no mark turns below the next number in front.
(After the text of WritesAbove, OnBytes/Tie/Pv/Psc/PscRoom.lean, which is not
imported.) -/
theorem Takes.writesAbove {F G : Fork} {t : Nat} (x : Takes F G t) :
    F.next ≤ G.next ∧ ∀ j, j < F.next → (OnBytes.PscRun.Filled G j ↔ OnBytes.PscRun.Filled F j) :=
  ⟨by rw [x.next]; omega, fun j hj => (x.touch.out j (Or.inl hj)).2.2⟩

/-- From room for u ≥ t numbers and m more it gives back room for m. (Room: the three fields of
LedgerRoom: the sizes; next + n within the numbers; nothing filled from next on.) -/
theorem Takes.room {F G : Fork} {t u m : Nat} (x : Takes F G t) (htu : t ≤ u)
    (fits : F.next + (u + m) ≤ F.ns) (free : ∀ j, F.next ≤ j → ¬ OnBytes.PscRun.Filled F j) :
    Sized G ∧ G.next + m ≤ G.ns ∧ ∀ j, G.next ≤ j → ¬ OnBytes.PscRun.Filled G j := by
  have hn := x.next
  refine ⟨x.touch.sized, by rw [hn, x.touch.ns]; omega, fun j hj hf => ?_⟩
  exact free j (by omega) (((x.touch.out j (Or.inr (by omega))).2.2).1 hf)

/-! ## The parts -/

theorem takes_hide {v : List E} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid} (hF : Sized F)
    (h : hide v F rs = some (c, G, left)) : Takes F G v.length := by
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray oneE with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    obtain ⟨t1, t2, t3⟩ := touch_hideRun
      (show Sized { F with next := F.next + v.length } from hF) hr
    have hs : v.toArray.size = v.length := by simp
    rw [hs] at t1 t3
    exact ⟨t2, (touch_next hF _ _ _).trans t1, t3⟩

theorem takes_round {n k : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {x : List E × List E}
    (h : Hear.round n k F rs = some (x, G, left)) :
    F = G ∧ x.1.length = n ∧ x.2.length = k := by
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some w =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, _⟩ := h
      obtain ⟨s, d⟩ := w
      obtain ⟨_, e2, e3, e4⟩ := Part.MaskedSum.roundOf_spec hr
      exact ⟨rfl, e2, by rw [e4, List.length_map]; exact e3⟩

theorem takes_send {n rows : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {x : Array Hid × E}
    (hF : Sized F) (h : sendThenBatch n rows F rs = some (x, G, left)) : Takes F G n := by
  unfold sendThenBatch at h
  obtain ⟨⟨v, gs⟩, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨rfl, hv, _⟩ := takes_round h1
  dsimp only at k1 hv
  obtain ⟨W', G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, _⟩ := need_some h3
  obtain ⟨_, rfl, _⟩ := pure_some k3
  exact (takes_hide hF h2).cast hv

theorem lead_length {k : Part.MaskedSum.Call} {rs : List Fmt.RoundView} {ld : List E}
    (h : Part.MaskedSum.leadScalars k rs = some ld) : ld.length = k.lead := by
  unfold Part.MaskedSum.leadScalars at h
  cases rs with
  | nil => cases h
  | cons r l =>
    have h' : (Part.MaskedSum.firstRound k r).map (·.1) = some ld := h
    unfold Part.MaskedSum.firstRound at h'
    cases hr : Part.MaskedSum.roundOf (k.lead + 1) 1 r with
    | none => rw [hr] at h'; cases h'
    | some x =>
      obtain ⟨v, g⟩ := x
      rw [hr] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      have hl := (Part.MaskedSum.roundOf_spec hr).2.1
      simp [hl]

/-- A sumcheck of HeadParts.lean in n variables has 2 n + 3 numbers of its own. -/
theorem own_callOf (lead : Nat) (z : Point) (e : Nat) :
    ownSlots (callOf lead z e).all = 2 * z.size + 3 := by
  rw [Part.MaskedSum.ownSlots_eq]
  simp only [callOf, Part.MaskedSum.Call.all, List.map_append, List.map_map, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  have h : (List.map ((fun v : Part.MaskedSum.Var => v.d - 1) ∘ fun x => Part.MaskedSum.Var.point x 3)
      z.toList).sum = 2 * z.size := by
    have : ((fun v : Part.MaskedSum.Var => v.d - 1) ∘ fun x : E => Part.MaskedSum.Var.point x 3)
        = fun _ => 2 := rfl
    rw [this]
    simp [Nat.mul_comm]
  rw [h]
  show 1 + (2 * z.size + (2 + 0)) = _
  omega

theorem takes_heardBy {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F0 F1 : Fork}
    {t left : List Fmt.RoundView} {x : Array Hid × Sum} (hF : Sized F0)
    (h : heardBy lead C z ends F0 t = some (x, F1, left)) :
    Takes F0 F1 (lead + ((2 * z.size + 3) + ends)) := by
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hFx : F0 = Fx := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact h1.2.1
  subst hFx
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨e2, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  have T1 : Takes F0 Fa lead := (takes_hide hF h3).cast (lead_length e2)
  have sa : Sized Fa := T1.touch.sized
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec e5
  obtain ⟨r0, used, rv, front, _, _, _, hvr, hsv⟩ := Part.MaskedSum.readAll_spec hread
  have hval : R.values.length = ends := hsv.2.1
  have hlenR : R.rounds.length = (callOf lead z ends).all.length := hvr.length.2
  have hown : ownSlots (callOf lead z ends).all = 2 * z.size + 3 := own_callOf lead z ends
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  -- the end values
  have hrun2' : ({ Fa with next := Fa.next + (2 * z.size + 3) + ends } : Fork).hideRun
      (Fa.next + (2 * z.size + 3)) R.values.toArray ((R.rounds.map (·.2)).getLastD zeroE)
      = some G := by
    have e := hrun2
    have hown' : ownSlots (Part.MaskedSum.Call.all
        (⟨lead, z.toList.map (Part.MaskedSum.Var.point · 3), some ⟨2, ends⟩⟩ :
          Part.MaskedSum.Call)) = 2 * z.size + 3 := hown
    rw [hown', hval] at e
    exact e
  obtain ⟨t1, n1, f1⟩ := touch_hideRun
    (show Sized { Fa with next := Fa.next + (2 * z.size + 3) + ends } from sa) hrun2'
  have n1' : G.next = Fa.next + (2 * z.size + 3) + ends := n1
  have hs1 : R.values.toArray.size = ends := by simpa using hval
  rw [hs1] at t1 f1
  -- the row's laying
  have hlen : (hidingAt (hd.vars.zip hd.r)).1.length = 2 * z.size + 3 := by
    rw [hhd]
    show (hidingAt ((callOf lead z ends).all.zip (R.rounds.map (·.2)))).1.length = _
    have hz : ((callOf lead z ends).all.zip (R.rounds.map (·.2))).map (·.1)
        = (callOf lead z ends).all := List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz, hown]
    · intro hnil
      have := congrArg (List.map (·.1)) hnil
      rw [hz] at this
      simp [callOf, Part.MaskedSum.Call.all] at this
    · intro y hy
      have hy' : y.1 ∈ (callOf lead z ends).all := by
        rw [← hz]; exact List.mem_map_of_mem hy
      simp only [callOf, Part.MaskedSum.Call.all, List.mem_append, List.mem_map, List.mem_cons,
        List.not_mem_nil, or_false] at hy'
      rcases hy' with ⟨w, _, hw⟩ | hw
      · rw [← hw]
        show 1 ≤ 3
        omega
      · rw [hw]
        show 1 ≤ 2 + 1
        omega
  have hfirst : hd.first = Fa.next := by rw [hhd]
  have e6' : G.hideRun Fa.next (Array.replicate (2 * z.size + 3) zeroE)
      (OnBytes.subE zeroE oneE) = some Fr := by
    have := e6
    unfold Part.MaskedSum.rowLaid at this
    rw [hlen, hfirst] at this
    exact this
  obtain ⟨t2, n2, f2⟩ := touch_hideRun t1.sized e6'
  have hs2 : (Array.replicate (2 * z.size + 3) zeroE).size = 2 * z.size + 3 := Array.size_replicate
  rw [hs2] at t2 f2
  have T2 : Takes Fa Fr ((2 * z.size + 3) + ends) := by
    refine ⟨by rw [n2, n1']; omega, ?_, fun j h1 h2 => ?_⟩
    · exact ((touch_next sa _ _ _).trans (t1.mono (by omega) (by omega))).trans
        (t2.mono (Nat.le_refl _) (by omega))
    · by_cases hj : j < Fa.next + (2 * z.size + 3)
      · exact f2 j h1 hj
      · exact ((t2.out j (Or.inr (by omega))).2.2).2 (f1 j (by omega) (by omega))
  exact T1.trans T2

theorem takes_sumcheck {z : Point} {n : Nat} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (hF : Sized F0) (h : sumcheck z n F0 t = some (s, F1, left)) :
    Takes F0 F1 (1 + ((2 * z.size + 3) + n)) := by
  unfold sumcheck at h
  obtain ⟨⟨c, s0⟩, G1, l1, h1, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨_, rfl, _⟩ := pure_some k1
  exact takes_heardBy hF h1

theorem takes_level {z : Point} {start : Form} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (hF : Sized F0) (h : level z start F0 t = some (s, F1, left)) :
    Takes F0 F1 (0 + ((2 * z.size + 3) + 2)) := by
  unfold level at h
  obtain ⟨⟨c, s0⟩, G1, l1, h1, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨⟨a, g⟩, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨rfl, _, _⟩ := takes_round h2
  dsimp only at k2
  obtain ⟨x, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, _⟩ := need_some h3
  obtain ⟨_, rfl, _⟩ := pure_some k3
  exact takes_heardBy hF h1

/-! ## The whole hearing -/

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **The head's hearing takes 41 + 4 lt + 4 |zt| + 4 lPd numbers**, writes nowhere else, and fills
each. -/
theorem hear_takes {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hF : Sized F)
    (h : hear F rs = some (H, G, left)) :
    Takes F G (41 + 4 * lt + 4 * (FinalNorm.zt).size + 4 * lPd) := by
  unfold hear at h
  obtain ⟨n, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨f, F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨lg, F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, _⟩ := pure_some k3
  unfold Norm.hear at h1
  obtain ⟨pV, Fa, la, a1, a2⟩ := bind_some h1
  unfold Norm.hearPoint drawPoint at a1
  obtain ⟨⟨v0, g0⟩, Fa', la', a3, a4⟩ := bind_some a1
  obtain ⟨rfl, _, hg0⟩ := takes_round a3
  obtain ⟨rfl, rfl, _⟩ := pure_some a4
  unfold Norm.hearRest at a2
  obtain ⟨⟨W, gam⟩, Fb, lb, b1, b2⟩ := bind_some a2
  dsimp only at b2
  have Tb := takes_send hF b1
  obtain ⟨rhoI, Fc, lc, c1, c2⟩ := bind_some b2
  have c1' : (pure #[] : Hear Point) Fb lb = some (rhoI, Fc, lc) := c1
  obtain ⟨rfl, rfl, _⟩ := pure_some c1'
  obtain ⟨sq, Fd, ld, d1, d2⟩ := bind_some c2
  have Td := takes_level Tb.touch.sized d1
  obtain ⟨⟨P, om⟩, Fe, le, e1, e2⟩ := bind_some d2
  dsimp only at e2
  have Te := takes_send Td.touch.sized e1
  obtain ⟨pr, Ff, lf, f1, f2⟩ := bind_some e2
  have Tf := takes_sumcheck Te.touch.sized f1
  obtain ⟨_, rfl, _⟩ := pure_some f2
  unfold FinalNorm.hear at h2
  obtain ⟨nm, Fg, lg', g1, g2⟩ := bind_some h2
  obtain ⟨_, rfl, _⟩ := pure_some g2
  have Tg := takes_sumcheck Tf.touch.sized g1
  have Th := takes_sumcheck Tg.touch.sized h3
  have hp : (g0.toArray).size = lt := by simpa using hg0
  have s1 : ((#[] : Point) ++ halves lPd ++ g0.toArray).size = lPd + lt := by
    simp [halves, hp]
  have s2 : (FinalNorm.zt ++ halves lPd).size = (FinalNorm.zt).size + lPd := by
    simp [halves]
  have all := ((((Tb.trans Td).trans Te).trans Tf).trans Tg).trans Th
  rw [s1, s2, hp] at all
  refine all.cast ?_
  show 9 * 1 + (0 + (2 * (lPd + lt) + 3 + 2)) + 7 * 1 + (1 + (2 * lt + 3 + 4 * 1))
      + (1 + (2 * (FinalNorm.zt).size + 3 + 2)) + (1 + (2 * ((FinalNorm.zt).size + lPd) + 3 + 2)) = _
  omega

/-- At a point on the positions of the plan's length: a count off the plan alone. -/
theorem hear_takes_plan {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hF : Sized F)
    (hzt : (FinalNorm.zt).size = lt) (h : hear F rs = some (H, G, left)) :
    Takes F G (41 + 8 * lt + 4 * lPd) :=
  (hear_takes hF h).cast (by rw [hzt]; omega)

end Classes

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_takes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_takes_plan
