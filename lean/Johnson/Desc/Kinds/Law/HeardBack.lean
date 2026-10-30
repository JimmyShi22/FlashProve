-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file stands over Johnson/Desc/Block.lean and Johnson/Desc/First/State.lean,
and over the seats that go with them (Johnson/Stored/HeadSeatAt.lean, ReplySeatAt.lean).


Johnson/Desc/Kinds/Law/HeardBack.lean: THE REAL SEAT READS BACK WHAT THE HEARING LAID. The output head's
block lays three things behind its hearing (HeadFrame.lean: decideBy): the ledger, what was heard, the
claim on the weights. At the first chain's record (Johnson/Stored/HeadSeatAt.lean: seatAt) what was heard
is not kept as it is: it is laid as `verify-on-bytes`'s record (HeadSeat.lean: heardOf) and read back out
of that record, the ledger and one further field (allOf).
WHAT IT IS NOT. Nothing on soundness. NOT «whatever is laid comes back»: that is false at seatAt (allOf
lays rhoI := #[], the level's claimed sum := {}, a sumcheck's down := 0, and a hidden scalar comes back
only as the variable of its number with what the ledger shows under it).
WHAT IS SHOWN. SeatBackHeard p L s: for the ledger F and the H THAT Head.lean's hear RETURNED at the
record's own ledger, at letters that given returned, from a ledger that is WellLaid and rounds that are
Canonical: behind the three layings the seat reads back F, some H TO THE LETTER, the same letters and
the same points of the lookup. seatBack_at: it holds at seatAt, at every record.
WHAT EACH PREMISE IS SPENT ON. Canonical: the two batching elements come back as powE x 1, which is x
just for words below the prime. WellLaid: a shown scalar is kept only where the ledger has a place.
The hearing's return: all else (one norm, so rhoI = #[]; each hidden scalar is a number's variable;
runs of numbers; every variable of a sumcheck is summed at a point with three coefficients, at which
varOf after weightOf is the identity; the head's sumcheck has at most lt + lPd challenges).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.KeepsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE mulE powE oneE zeroE)
open OnBytes.Model (Aff Fork Reading)
open OnBytes.PscRun (Later Sized Filled shown_later shown_iff hideRun_ok hideRun_keeps)
open VerifiableInference.Desc.First (S)
open Norm (lt lPd)

/-! ## 0. Small facts -/

theorem sized_of_wellLaid {F : Fork} (h : WellLaid F) : Sized F := ⟨h.2.1, h.2.2, h.1⟩

theorem okE_mulE1 (a b : E) : okE (mulE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.mulE
  simp [Fmt.Fld.ok_add]

/-- The first power of an element whose words are below the prime is the element. -/
theorem powE_one {x : E} (hx : okE x = true) : powE x 1 = x := by
  have e : powE x 1 = mulE oneE x := by
    simp [powE, OnBytes.powLoopE]
  rw [e]
  refine eq_of_rd (okE_mulE1 _ _) hx ?_
  show Reading.gl.val (mulE oneE x) = Reading.gl.val x
  rw [Reading.gl.mul, Reading.gl.one, one_mul]

theorem powersOf_one {x : E} (hx : okE x = true) (n : Nat) (hn : 1 < n) :
    (powersOf x n)[1]? = some x := by
  unfold powersOf
  simp [hn, powE_one hx]

theorem map_fix {α : Type} {f : α → α} : ∀ l : List α, (∀ v, v ∈ l → f v = v) → l.map f = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, h a (by simp), map_fix l fun v hv => h v (by simp [hv])]

theorem two_eta (a : Array Hid) (h : a.size = 2) : #[a.getD 0 {}, a.getD 1 {}] = a := by
  apply Array.ext
  · simp [h]
  · intro i h1 h2
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp [Array.getD_eq_getD_getElem?, h]

/-! ## 1. mapM in Option -/

theorem mapM_mono {α β : Type} {f g : α → Option β} (hfg : ∀ a b, f a = some b → g a = some b) :
    ∀ (l : List α) (bs : List β), l.mapM f = some bs → l.mapM g = some bs
  | [], bs, h => by simpa using h
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h ⊢
    cases ha : f a with
    | none => rw [ha] at h; simp at h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; simp at h
      | some t =>
        rw [ha, hl] at h
        rw [hfg a b ha, mapM_mono hfg l t hl]
        exact h

theorem mapM_spec {α β : Type} {f : α → Option β} :
    ∀ (l : List α) (bs : List β), l.mapM f = some bs →
      bs.length = l.length ∧ ∀ i : Nat, (l[i]?).bind f = bs[i]?
  | [], bs, h => by
    have hb : bs = [] := by simpa using h.symm
    subst hb
    exact ⟨rfl, fun i => by simp⟩
  | a :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; simp at h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; simp at h
      | some t =>
        rw [ha, hl] at h
        have hb : b :: t = bs := by simpa using h
        subst hb
        obtain ⟨e1, e2⟩ := mapM_spec l t hl
        refine ⟨by simp [e1], fun i => ?_⟩
        cases i with
        | zero => simp [ha]
        | succ i => simpa using e2 i

theorem mapM_all {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ (l : List α), (∀ a, a ∈ l → f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons, h a (by simp), mapM_all l fun x hx => h x (by simp [hx])]
    rfl

/-! ## 2. A hidden scalar by its number -/

theorem hidAt_later {F G : Fork} (h : Later F G) {j : Nat} {a : Hid} (e : hidAt F j = some a) :
    hidAt G j = some a := by
  unfold hidAt at e ⊢
  cases hs : F.shown j with
  | none => rw [hs] at e; simp at e
  | some x => rw [hs] at e; rw [shown_later h hs]; exact e

theorem hidsAt_later {F G : Fork} (h : Later F G) {j n : Nat} {a : Array Hid}
    (e : hidsAt F j n = some a) : hidsAt G j n = some a := by
  unfold hidsAt at e ⊢
  cases hm : (List.range n).mapM (fun i => hidAt F (j + i)) with
  | none => rw [hm] at e; simp at e
  | some l =>
    rw [hm] at e
    rw [mapM_mono (f := fun i => hidAt F (j + i)) (g := fun i => hidAt G (j + i))
      (fun i b hb => hidAt_later h hb) _ _ hm]
    exact e

theorem hidsAt_spec {G : Fork} {j n : Nat} {a : Array Hid} (e : hidsAt G j n = some a) :
    a.size = n ∧ ∀ i, i < n → hidAt G (j + i) = some (a.getD i {}) := by
  unfold hidsAt at e
  cases hm : (List.range n).mapM (fun i => hidAt G (j + i)) with
  | none => rw [hm] at e; simp at e
  | some l =>
    rw [hm] at e
    simp only [Option.map_some, Option.some.injEq] at e
    subst e
    obtain ⟨e1, e2⟩ := mapM_spec _ _ hm
    rw [List.length_range] at e1
    refine ⟨by simpa using e1, fun i hi => ?_⟩
    have h3 := e2 i
    rw [List.getElem?_range hi] at h3
    have h4 : hidAt G (j + i) = l[i]? := h3
    rw [h4]
    have hi' : i < l.length := by omega
    simp [Array.getD_eq_getD_getElem?, hi']

theorem slotOf_hidAt {G : Fork} {j : Nat} {a : Hid} (e : hidAt G j = some a) : slotOf a = j := by
  unfold hidAt at e
  cases hs : G.shown j with
  | none => rw [hs] at e; simp at e
  | some x =>
    rw [hs] at e
    simp only [Option.map_some, Option.some.injEq] at e
    subst e
    rfl

theorem slotOf_first {G : Fork} {j n : Nat} {a : Array Hid} (e : hidsAt G j n = some a)
    (hn : 0 < n) : slotOf (a.getD 0 {}) = j :=
  slotOf_hidAt ((hidsAt_spec e).2 0 hn)

theorem hiddenFrom_hidsAt {first n : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid}
    (h : hiddenFrom first n F rs = some (c, G, left)) : hidsAt F first n = some c := by
  have key : hidsAt F first n = ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)).map (·.toArray) := rfl
  rw [key]
  unfold hiddenFrom at h
  cases hr : ((List.range n).mapM fun j => (F.shown (first + j)).map fun x =>
      ({ var := Aff.slot (first + j), shown := x } : Hid)) with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl

/-- What hide lays is read back under its numbers. -/
theorem hide_back {v : List E} {F G : Fork} {rs left : List Fmt.RoundView} {c : Array Hid} (hF : Sized F)
    (h : hide v F rs = some (c, G, left)) : hidsAt G F.next v.length = some c := by
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray oneE with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, _⟩ := h
    obtain ⟨a1, _, a3, _⟩ := hideRun_ok _ _ _ _ _
      (show Sized { F with next := F.next + v.length } from hF) hr
    unfold hidsAt
    rw [mapM_all (g := fun i =>
      ({ var := Aff.slot (F.next + i), shown := v.toArray.getD i zeroE } : Hid))]
    · simp only [Option.map_some, Option.some.injEq]
      apply Array.ext
      · simp
      · intro i h1 h2
        have hv : i < v.length := by simpa using h2
        simp [Array.getD_eq_getD_getElem?, hv]
    · intro i hi
      have hi' : i < v.toArray.size := by simpa using hi
      obtain ⟨b1, _, b3, b4, _⟩ := a3 i hi'
      unfold hidAt
      rw [(shown_iff X (F.next + i) _).2 ⟨by rw [a1.ns]; exact b1, b3, b4.symm⟩]
      rfl

/-! ## 3. The parts of a hearing -/

theorem canonical_tail {r : Fmt.RoundView} {l : List Fmt.RoundView} (h : Canonical (r :: l)) : Canonical l :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem canonical_drop {t : List Fmt.RoundView} (n : Nat) (h : Canonical t) : Canonical (t.drop n) :=
  fun x hx => h x (List.mem_of_mem_drop hx)

theorem roundOf_spec {n k : Nat} {r : Fmt.RoundView} {v g : List E}
    (hr : Part.MaskedSum.roundOf n k r = some (v, g)) :
    v.length = n ∧ g = r.drawn.elems.map E.ofTriple := by
  unfold Part.MaskedSum.roundOf at hr
  cases hs : Part.MaskedSum.scalars r.vals with
  | none => rw [hs] at hr; cases hr
  | some s =>
    rw [hs] at hr
    have hr' : (if s.length == n && r.drawn.elems.length == k then
        some (s, r.drawn.elems.map E.ofTriple) else none) = some (v, g) := hr
    split at hr'
    · rename_i hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      simp only [Bool.and_eq_true, beq_iff_eq] at hq
      exact ⟨hq.1, rfl⟩
    · cases hr'

theorem round_back {n k : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {v g : List E}
    (hc : Canonical rs) (h : Hear.round n k F rs = some ((v, g), G, left)) :
    F = G ∧ Canonical left ∧ v.length = n ∧ ∀ x, x ∈ g → okE x = true := by
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
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨e1, e2⟩ := roundOf_spec hr
      refine ⟨rfl, canonical_tail hc, e1, fun x hx => ?_⟩
      rw [e2] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact (hc r (by simp)).2 y hy

theorem drawPoint_back {n : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {p : Point}
    (hc : Canonical rs) (h : drawPoint n F rs = some (p, G, left)) : F = G ∧ Canonical left := by
  unfold drawPoint at h
  obtain ⟨⟨v, g⟩, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨rfl, c1, _, _⟩ := round_back hc h1
  obtain ⟨_, rfl, rfl⟩ := pure_some k1
  exact ⟨rfl, c1⟩

theorem send_back {n rows : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {W : Array Hid} {g : E}
    (hF : Sized F) (hc : Canonical rs) (h : sendThenBatch n rows F rs = some ((W, g), G, left)) :
    Later F G ∧ Canonical left ∧ hidsAt G F.next n = some W ∧ okE g = true := by
  unfold sendThenBatch at h
  obtain ⟨⟨v, gs⟩, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨rfl, c1, hv, hg⟩ := round_back hc h1
  dsimp only at k1
  obtain ⟨W', G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨rfl, _⟩ := hide_some h2
  obtain ⟨g', G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨e3, rfl, rfl⟩ := need_some h3
  obtain ⟨e4, rfl, rfl⟩ := pure_some k3
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  refine ⟨keeps_hide v _ _ _ _ _ h2, c1, ?_, ?_⟩
  · rw [← hv]; exact hide_back hF h2
  · cases gs with
    | nil => simp at e3
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at e3
      subst e3
      exact hg _ (by simp)

theorem leadScalars_length {k : Part.MaskedSum.Call} {rs : List Fmt.RoundView} {ld : List E}
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
      have hl := (roundOf_spec hr).1
      simp [hl]

/-- At the variables of HeadParts.lean's sumchecks the way to the program's weights and back is the
identity. -/
theorem vars_back (lead : Nat) (z : Point) (e : Nat) :
    ((callOf lead z e).all).map (fun v => varOf (weightOf v)) = (callOf lead z e).all := by
  refine map_fix _ fun v hv => ?_
  simp only [callOf, Part.MaskedSum.Call.all, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with ⟨x, _, rfl⟩ | rfl <;> rfl

/-- A sumcheck's record reads back at the ledger G: its n end values under their numbers; the rest of
what was heard. -/
structure SumBack (G : Fork) (s : Sum) (n : Nat) : Prop where
  ends : hidsAt G (slotOf (s.end_ 0)) n = some s.ends
  psc : ∃ h, s.psc = some h ∧ h.sEnd = slotOf (s.end_ 0) ∧
    h.vars.map (fun v => varOf (weightOf v)) = h.vars

theorem SumBack.later {F G : Fork} {s : Sum} {n : Nat} (h : Later F G) (b : SumBack F s n) :
    SumBack G s n := ⟨hidsAt_later h b.ends, b.psc⟩

theorem heardBy_back {lead : Nat} {C : Array Hid → Form} {z : Point} {ends : Nat} {F0 F1 : Fork}
    {t left : List Fmt.RoundView} {c : Array Hid} {s : Sum} (hF : Sized F0) (hc : Canonical t)
    (hn : 0 < ends) (h : heardBy lead C z ends F0 t = some ((c, s), F1, left)) :
    Later F0 F1 ∧ Canonical left ∧ hidsAt F1 F0.next lead = some c ∧ SumBack F1 s ends ∧
      s.claimed = {} ∧ s.down = zeroE ∧ s.r.size ≤ z.size := by
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hst : F0 = Fx ∧ t.drop (z.size + 3) = l0 := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact ⟨h1.2.1, h1.2.2⟩
  obtain ⟨rfl, rfl⟩ := hst
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨e2, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  obtain ⟨rfl, _⟩ := hide_some h3
  have L1 : Later F0 Fa := keeps_hide ld _ _ _ _ _ h3
  have B1 := hide_back hF h3
  rw [leadScalars_length e2] at B1
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, hhd, hrun2⟩ := Part.MaskedSum.hear_spec e5
  have L2 : Later Fa G := (later_next Fa _ (by omega)).trans (hideRun_keeps hrun2)
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : Later G Fr := hideRun_keeps e6
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  have B8 := hiddenFrom_hidsAt h8
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨e9, rfl, rfl⟩ := pure_some k8
  simp only [Prod.mk.injEq] at e9
  obtain ⟨rfl, rfl⟩ := e9
  have hs0 : slotOf (es.getD 0 {}) = hd.sEnd := slotOf_first B8 hn
  refine ⟨(L1.trans L2).trans L3, canonical_drop _ hc, hidsAt_later (L2.trans L3) B1,
    ⟨?_, hd, rfl, hs0.symm, ?_⟩, rfl, rfl, ?_⟩
  · show hidsAt _ (slotOf (es.getD 0 {})) ends = some es
    rw [hs0]; exact B8
  · rw [hhd]
    exact vars_back lead z ends
  · show ((Part.MaskedSum.challenges _ hd).toArray).size ≤ z.size
    unfold Part.MaskedSum.challenges
    simp only [List.size_toArray, List.length_take, List.length_map, Array.length_toList]
    omega

theorem sumcheck_back {z : Point} {n : Nat} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (hF : Sized F0) (hc : Canonical t) (hn : 0 < n)
    (h : sumcheck z n F0 t = some (s, F1, left)) :
    Later F0 F1 ∧ Canonical left ∧ SumBack F1 s n ∧
      hidAt F1 (slotOf s.claimed) = some s.claimed ∧ s.down = zeroE ∧ s.r.size ≤ z.size := by
  unfold sumcheck at h
  obtain ⟨⟨c, s0⟩, G1, l1, h1, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k1
  obtain ⟨L, c1, hm, sb, _, hd, hr⟩ := heardBy_back hF hc hn h1
  have hc0 := (hidsAt_spec hm).2 0 (by omega)
  refine ⟨L, c1, ⟨sb.ends, sb.psc⟩, ?_, hd, hr⟩
  show hidAt _ (slotOf (c.getD 0 {})) = some (c.getD 0 {})
  rw [slotOf_hidAt hc0]; exact hc0

theorem level_back {z : Point} {start : Form} {F0 F1 : Fork} {t left : List Fmt.RoundView} {s : Sum}
    (hF : Sized F0) (hc : Canonical t) (h : level z start F0 t = some (s, F1, left)) :
    Later F0 F1 ∧ Canonical left ∧ SumBack F1 s 2 ∧ s.claimed = {} := by
  unfold level at h
  obtain ⟨⟨c, s0⟩, G1, l1, h1, k1⟩ := bind_some h
  dsimp only at k1
  obtain ⟨L, c1, _, sb, hcl, _, _⟩ := heardBy_back hF hc (by omega) h1
  obtain ⟨⟨a, g⟩, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨rfl, c2, _, _⟩ := round_back c1 h2
  dsimp only at k2
  obtain ⟨x, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  exact ⟨L, c2, ⟨sb.ends, sb.psc⟩, hcl⟩

/-! ## 4. The whole hearing -/

/-- What of a heard H makes the way back return it, at the ledger G. -/
structure Back (G : Fork) (H : HeardAll) : Prop where
  W : hidsAt G (slotOf (H.1.W.getD 0 {})) 9 = some H.1.W
  gam : okE H.1.gam = true
  rhoI : H.1.rhoI = #[]
  squares : SumBack G H.1.squares 2
  squaresClaimed : H.1.squares.claimed = {}
  P : hidsAt G (slotOf (H.1.P.getD 0 {})) 7 = some H.1.P
  om : okE H.1.om = true
  products : SumBack G H.1.products 4
  productsClaimed : hidAt G (slotOf H.1.products.claimed) = some H.1.products.claimed
  productsDown : H.1.products.down = zeroE
  normed : SumBack G H.2.1.normed 2
  normedClaimed : hidAt G (slotOf H.2.1.normed.claimed) = some H.2.1.normed.claimed
  normedDown : H.2.1.normed.down = zeroE
  logits : SumBack G H.2.2.logits 2
  logitsClaimed : hidAt G (slotOf H.2.2.logits.claimed) = some H.2.2.logits.claimed
  logitsDown : H.2.2.logits.down = zeroE

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- **Where the head's hearing returns**, from a ledger with a place for each number and rounds whose
words are below the prime. -/
theorem hear_back {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hF : Sized F)
    (hc : Canonical rs) (h : hear F rs = some (H, G, left)) :
    Back G H ∧ H.2.2.logits.r.size ≤ (FinalNorm.zt).size + lPd := by
  unfold hear at h
  obtain ⟨n, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨f, F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨lg, F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  unfold Norm.hear at h1
  obtain ⟨pV, Fa, la, a1, a2⟩ := bind_some h1
  unfold Norm.hearPoint at a1
  obtain ⟨rfl, ca⟩ := drawPoint_back hc a1
  unfold Norm.hearRest at a2
  obtain ⟨⟨W, gam⟩, Fb, lb, b1, b2⟩ := bind_some a2
  dsimp only at b2
  obtain ⟨Lb, cb, hW, hgam⟩ := send_back hF ca b1
  obtain ⟨rhoI, Fc, lc, c1, c2⟩ := bind_some b2
  have c1' : (pure #[] : Hear Point) Fb lb = some (rhoI, Fc, lc) := c1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some c1'
  obtain ⟨sq, Fd, ld, d1, d2⟩ := bind_some c2
  have sb := Lb.sized hF
  obtain ⟨Ld, cd, sbq, hq⟩ := level_back sb cb d1
  have sd := Ld.sized sb
  obtain ⟨⟨P, om⟩, Fe, le, e1, e2⟩ := bind_some d2
  dsimp only at e2
  obtain ⟨Le, ce, hP, hom⟩ := send_back sd cd e1
  have se := Le.sized sd
  obtain ⟨pr, Ff, lf, f1, f2⟩ := bind_some e2
  obtain ⟨Lf, cf, sbp, hpc, hpd, _⟩ := sumcheck_back se ce (show 0 < 4 * 1 by omega) f1
  have sf := Lf.sized se
  obtain ⟨rfl, rfl, rfl⟩ := pure_some f2
  unfold FinalNorm.hear at h2
  obtain ⟨nm, Fg, lg', g1, g2⟩ := bind_some h2
  obtain ⟨rfl, rfl, rfl⟩ := pure_some g2
  obtain ⟨Lg, cg, sbn, hnc, hnd, _⟩ := sumcheck_back sf cf (by omega) g1
  have sg := Lg.sized sf
  obtain ⟨Lh, _, sbl, hlc, hld, hlr⟩ := sumcheck_back sg cg (by omega) h3
  have hW9 : hidsAt Fb F.next 9 = some W := hW
  have hP7 : hidsAt Fe Fd.next 7 = some P := hP
  have sbp4 : SumBack Ff pr 4 := sbp
  have LgG := Lg.trans Lh
  have LfG := Lf.trans LgG
  have LeG := Le.trans LfG
  have LdG := Ld.trans LeG
  refine ⟨⟨?_, hgam, rfl, sbq.later LeG, hq, ?_, hom, sbp4.later LgG, hidAt_later LgG hpc, hpd,
    sbn.later Lh, hidAt_later Lh hnc, hnd, sbl, hlc, hld⟩, ?_⟩
  · show hidsAt _ (slotOf (W.getD 0 {})) 9 = some W
    rw [slotOf_first hW9 (by omega)]
    exact hidsAt_later LdG hW9
  · show hidsAt _ (slotOf (P.getD 0 {})) 7 = some P
    rw [slotOf_first hP7 (by omega)]
    exact hidsAt_later LfG hP7
  · have e : (FinalNorm.zt ++ halves lPd).size = (FinalNorm.zt).size + lPd := by
      simp [halves]
    rw [← e]; exact hlr

end Classes

/-! ## 5. The way back -/

theorem keptOf_pscOf (h : Part.MaskedSum.Heard) (b : Bool)
    (hv : h.vars.map (fun v => varOf (weightOf v)) = h.vars) :
    keptOf (pscOf (some h) b) h.sEnd = h := by
  obtain ⟨start, target, eps, claim, first, vars, r, sEnd⟩ := h
  show ({ start := start, target := target, eps := eps, claim := claim, first := first,
          vars := (vars.map weightOf).map varOf, r := r, sEnd := sEnd } : Part.MaskedSum.Heard) = _
  have hv' : (vars.map weightOf).map varOf = vars := by
    rw [List.map_map]; exact hv
  rw [hv']

theorem sumOf_back {G : Fork} {s : Sum} {n : Nat} (rr r' : Point) (S0 : E) (hr : r' = s.r)
    (sb : SumBack G s n) (hc : hidAt G (slotOf s.claimed) = some s.claimed)
    (hd : s.down = zeroE) : sumOf G (tscOf s rr S0) r' n = some s := by
  obtain ⟨h, hp, hs, hv⟩ := sb.psc
  have he := sb.ends
  unfold sumOf tscOf
  dsimp only
  rw [hc, he, hp, ← hs, keptOf_pscOf h true hv]
  obtain ⟨r, claimed, ends, down, psc⟩ := s
  dsimp only at hr hp hd
  subst hr hp hd
  rfl

theorem squares_eta (s : Sum) (k : Part.MaskedSum.Heard) (hcl : s.claimed = {})
    (hsize : s.ends.size = 2) (hk : s.psc = some k) :
    ({ r := s.r, ends := #[s.end_ 0, s.end_ 1], down := s.down, psc := some k } : Sum) = s := by
  obtain ⟨r, claimed, ends, down, psc⟩ := s
  dsimp only at hcl hsize hk
  subst hcl hk
  show ({ r := r, ends := #[ends.getD 0 {}, ends.getD 1 {}], down := down, psc := some k } : Sum) = _
  rw [two_eta ends hsize]

theorem norm_eta (n : Norm.Heard) (sq : Sum) (hr : n.rhoI = #[]) (hs : sq = n.squares) :
    ({ pV := n.pV, W := n.W, gam := n.gam, rhoI := #[], squares := sq, P := n.P, om := n.om,
       products := n.products } : Norm.Heard) = n := by
  subst hs
  obtain ⟨pV, W, gam, rhoI, squares, P, om, products⟩ := n
  dsimp only at hr
  subst hr
  rfl

theorem extract_back (r : Point) (a b : Nat) (h : r.size ≤ a + b) :
    r.extract 0 a ++ ((r.extract a (a + b)).reverse).reverse = r := by
  rw [Array.reverse_reverse]
  apply Array.toList_inj.1
  simp only [Array.toList_append, Array.toList_extract]
  have hl : r.toList.length ≤ a + b := by simpa using h
  have h2 : (r.toList.drop a).take b = r.toList.drop a :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  simp [h2]

/-- **The way back returns what was heard.** -/
theorem allOf_back [Sizes] [Request] [Token] {G : Fork} (g1 : OnBytes.Model.Forest.Heard)
    {H : HeardAll} (b : Back G H) (hl : H.2.2.logits.r.size ≤ lt + lPd) :
    allOf G (heardOf g1 H) (some (keptOf (pscOf H.1.squares.psc false) (heardOf g1 H).wpl.sL))
      = some H := by
  obtain ⟨n, f, h⟩ := H
  obtain ⟨k, hk, hks, hkv⟩ := b.squares.psc
  obtain ⟨hsz, hsp⟩ := hidsAt_spec b.squares.ends
  have q0 := hsp 0 (by omega)
  have q1 := hsp 1 (by omega)
  have e1 : hidsAt G (heardOf g1 (n, f, h)).sW 9 = some n.W := b.W
  have e2 : (heardOf g1 (n, f, h)).gp[1]? = some n.gam := powersOf_one b.gam 9 (by omega)
  have e3 : hidAt G (heardOf g1 (n, f, h)).wpl.sL = some (n.squares.end_ 0) := q0
  have e4 : hidAt G (heardOf g1 (n, f, h)).wpl.sR = some (n.squares.end_ 1) := by
    show hidAt G (slotOf (n.squares.end_ 1)) = _
    rw [show slotOf (n.squares.end_ 1) = slotOf (n.squares.end_ 0) + 1 from slotOf_hidAt q1]
    exact q1
  have e5 : hidsAt G (heardOf g1 (n, f, h)).sPv 7 = some n.P := b.P
  have e6 : (heardOf g1 (n, f, h)).omV[1]? = some n.om := powersOf_one b.om 7 (by omega)
  have e7 : sumOf G (heardOf g1 (n, f, h)).tV (heardOf g1 (n, f, h)).tV.r 4 = some n.products :=
    sumOf_back _ _ _ rfl b.products b.productsClaimed b.productsDown
  have e8 : sumOf G (heardOf g1 (n, f, h)).tN (heardOf g1 (n, f, h)).tN.r 2 = some f.normed :=
    sumOf_back _ _ _ rfl b.normed b.normedClaimed b.normedDown
  have e9 : sumOf G (heardOf g1 (n, f, h)).tH
      ((heardOf g1 (n, f, h)).tH.r ++ (heardOf g1 (n, f, h)).rs.reverse) 2 = some h.logits :=
    sumOf_back _ _ _ (extract_back _ _ _ hl) b.logits b.logitsClaimed b.logitsDown
  have e0 : keptOf (pscOf n.squares.psc false) (heardOf g1 (n, f, h)).wpl.sL = k := by
    show keptOf (pscOf n.squares.psc false) (slotOf (n.squares.end_ 0)) = k
    rw [show n.squares.psc = some k from hk, ← show k.sEnd = slotOf (n.squares.end_ 0) from hks]
    exact keptOf_pscOf k false hkv
  unfold allOf
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  show some (({ pV := n.pV, W := n.W, gam := n.gam, rhoI := #[],
                squares := { r := n.squares.r, ends := #[n.squares.end_ 0, n.squares.end_ 1],
                             down := n.squares.down, psc := some k },
                P := n.P, om := n.om, products := n.products } : Norm.Heard),
              ({ normed := f.normed } : FinalNorm.Heard), ({ logits := h.logits } : Heard))
    = some (n, f, h)
  rw [norm_eta n _ b.rhoI (squares_eta n.squares k b.squaresClaimed hsz hk)]

/-! ## 6. The seat -/

/-- **The premise on a seat, at a record**: behind the three layings of the block's decision the seat
reads back the ledger that the hearing returned, what it heard, the same letters and the same points
of the lookup. -/
def SeatBackHeard {S : Type} (p : Par) (L : Seat S) (s : S) : Prop :=
  ∀ (g : Given) (rs left : List Fmt.RoundView) (F : Fork) (H : HeardAll) (w : SumOnMatrix) (s1 s2 : S),
    given p L s = .ok g → WellLaid (L.ledger s) → Canonical rs →
    hear (L.ledger s) rs = some (H, F, left) →
    L.setLedger s F = .ok s1 → L.setHeard s1 H = .ok s2 →
    L.ledger (L.setWeightClaim s2 w) = F ∧ L.heard (L.setWeightClaim s2 w) = some H ∧
      given p L (L.setWeightClaim s2 w) = given p L s ∧
      L.lookup (L.setWeightClaim s2 w) = L.lookup s

theorem given_form {S : Type} {p : Par} {L : Seat S} {s : S} {g : Given}
    (h : given p L s = .ok g) :
    ∃ (z : Point × (Nat → Point)) (y : Nat),
      g = { sizes := p.sizes, policy := p.policy, request := L.request s, token := ⟨y⟩,
            normIn := (@fromLookup p.sizes p.floor z.1 z.2).norm,
            headIn := (@fromLookup p.sizes p.floor z.1 z.2).head,
            calls := (@fromLookup p.sizes p.floor z.1 z.2).calls } := by
  unfold given at h
  cases hz : L.lookup s with
  | none => simp [hz, named, bind, Except.bind] at h
  | some z =>
    cases hy : Reply.token L.toSeat s with
    | none => simp [hz, hy, named, bind, Except.bind] at h
    | some y0 =>
      simp only [hz, hy, named, need, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        exact ⟨z, y0, h.symm⟩

theorem given_congr {S : Type} (p : Par) (L : Seat S) {s s' : S} (h1 : L.lookup s' = L.lookup s)
    (h2 : L.reply s' = L.reply s) (h3 : L.request s' = L.request s) :
    given p L s' = given p L s := by
  unfold given Reply.token
  rw [h1, h2, h3]

theorem last_size (z : Point) (n : Nat) : (z.last n).size ≤ n := by
  unfold Point.last
  simp only [Array.size_extract]
  omega

variable (h : OnBytes.Model.Head.Shape) (iU3 work : Nat)

/-- Where the seat's setHeard returns: what it lays. -/
theorem setHeard_form {s s2 : S} {H : HeardAll} (e : (seatAt h iU3).setHeard s H = .ok s2) :
    ∃ (o : VerifiableInference.Desc.First.HeadOwn) (x : OnBytes.Model.Forest.Heard),
      s.here = .head o ∧ o.lookHeard = some x ∧
      s2 = { s with here := .head { o with
        x := some (@heardOf (sizesOf h) (requestOf s)
          ⟨(s.out.reply.map OnBytes.Desc.Reply.tokOf).getD 0⟩ x H),
        squaresP := some (pscOf H.1.squares.psc false) } } := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · rename_i o ho
    split at e
    · rename_i x hx
      simp only [Except.ok.injEq] at e
      exact ⟨o, x, ho, hx, e.symm⟩
    · cases e
  · cases e

theorem req_putFork (s : S) (F : Fork) : (s.putFork F).req = s.req := by
  unfold S.putFork
  split <;> (try split) <;> rfl

theorem requestOf_congr {s t : S} (e : t.req = s.req) : requestOf t = requestOf s := by
  unfold requestOf S.tokv S.rowR S.rowE S.reqT
  rw [e]

/-- The lookup's value has a field of its own, which the laying does not write. (Over State.lean,
the seat reads S.lookHeard?.) -/
theorem look_back (s t : S) (a b : VerifiableInference.Desc.First.HeadOwn)
    (hs : s.here = .head a) (ht : t.here = .head b)
    (ho : b.opened = a.opened) (hl : b.lookHeard = a.lookHeard) : t.lookHeard? = s.lookHeard? := by
  unfold S.lookHeard?
  rw [hs, ht]
  dsimp only
  rw [ho, hl]

/-- **heard_back: the real seat reads back what the hearing laid, at every record.** -/
theorem seatBack_at (s : S) : SeatBackHeard (parOf h work) (seatAt h iU3) s := by
  intro g rs left F H w s1 s2 hg hW hc hh e1 e2
  have fit := seatAt_fit h iU3 s F H w s1 s2 e1 e2
  obtain ⟨bk, hl⟩ := hear_back (sized_of_wellLaid hW) hc hh
  obtain ⟨z, y, rfl⟩ := given_form hg
  have hl' : letI := sizesOf h; H.2.2.logits.r.size ≤ lt + lPd :=
    Nat.le_trans hl (Nat.add_le_add_right (last_size z.1 _) _)
  have e1' : s.putFork? F = .ok s1 := e1
  have hs1 := putFork?_ok e1'
  have hsome : s.fork?.isSome = true := by
    unfold S.putFork? at e1'
    split at e1'
    · assumption
    · cases e1'
  obtain ⟨o, x, ho, hx, rfl⟩ := setHeard_form h iU3 e2
  subst hs1
  cases hh' : s.here with
  | head a =>
    by_cases hop : a.opened = true
    · simp only [S.putFork, hh', hop, if_true] at ho
      simp only [VerifiableInference.Desc.First.Here.head.injEq] at ho
      subst ho
      refine ⟨fit, ?_, ?_, ?_⟩
      · exact @allOf_back (sizesOf h) (requestOf (s.putFork F))
          ⟨((s.putFork F).out.reply.map OnBytes.Desc.Reply.tokOf).getD 0⟩ F x H bk hl'
      · exact given_congr _ _
          (congrArg (Option.map _) (look_back s _ a _ hh' rfl hop.symm rfl))
          (congrArg (·.reply) (out_putFork s F)) (requestOf_congr (req_putFork s F))
      · exact congrArg (Option.map _) (look_back s _ a _ hh' rfl hop.symm rfl)
    · simp [S.fork?, hh', hop] at hsome
  | lay a => simp [S.putFork, hh'] at ho
  | att a => simp [S.putFork, hh'] at ho
  | between => simp [S.fork?, hh'] at hsome
  | fin a => simp [S.fork?, hh'] at hsome
  | mem a => simp [S.fork?, hh'] at hsome

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.allOf_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_back
#print axioms VerifiableInference.Desc.Kinds.Head.Law.seatBack_at
