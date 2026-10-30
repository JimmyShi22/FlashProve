-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/DoorFacts.lean
(kind K9's soundness lemma): THEOREMS: three of the four public premises of (T2b)
are no premises where K9.door returns: the door's own tests on the row that it lays give them.
  addTerms_forms   each term leaves a form on the oracle message that holds its array.
  asRow_shape      so the row that K9.asRow makes has such a form for each term, and, if the
                   equation has coefficients on masks, the run of these coefficients on the mask
                   row.
  door_facts       **door .. = .ok out, and the layout's blocks lie inside their arrays: then
                   RowPremises holds at the equation made, with N any number from the number of
                   oracle messages on.** From the tests "the forms fit their places" and "the runs
                   fit their places" of the call that adds a row (each summand's oracle message has
                   the table; the last index of a run is within the table).
  equation_goodIn' the piece of the equation's block is good (Law/GoodInEq.lean), with "inside" and
                   "N is at least the number of oracle messages" in the place of RowPremises.

-/
import Johnson.Desc.First.Batch.Law.GoodInEq
import Johnson.Desc.Own.RowsAgree
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St door takeN Lens)

theorem addTerms_forms (Rr : ReqRows) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row row' : OnBytes.Row), Rr.addTerms f S ts row = some row' →
      (∀ fm ∈ row.forms.toList, fm ∈ row'.forms.toList) ∧ row'.runs = row.runs ∧
      ∀ t ∈ ts, ∀ a o, reqArray Rr.layout t.born t.array = some a →
        f.whereIs t.born a.message = some o → ∃ fm ∈ row'.forms.toList, fm.oracle = o
  | [], row, row', h => by
    have e : row = row' := Option.some.inj h
    subst e
    simp
  | t :: ts, row, row', h => by
    rw [ReqRows.addTerms] at h
    obtain ⟨a, ha, h⟩ := some_bind h
    obtain ⟨o', ho, h⟩ := some_bind h
    obtain ⟨c, _, h⟩ := some_bind h
    obtain ⟨i1, i2, i3⟩ := addTerms_forms Rr f S ts (row.addForm o' c) row' h
    refine ⟨fun fm hfm => i1 fm (by simp [Row.addForm, hfm]), by rw [i2]; rfl, ?_⟩
    intro t' ht' a' o ha' ho'
    rcases List.mem_cons.mp ht' with rfl | ht''
    · have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
      subst ea
      have eo : o = o' := Option.some.inj (ho'.symm.trans ho)
      subst eo
      exact ⟨⟨o, c⟩, i1 _ (by simp [Row.addForm]), rfl⟩
    · exact i3 t' ht'' a' o ha' ho'

/-- The summands of the row that K9.asRow makes. -/
theorem asRow_shape {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) :
    (∀ t ∈ q.terms.toList, ∀ a o, reqArray Rr.layout t.born t.array = some a →
      f.whereIs t.born a.message = some o → ∃ fm ∈ row.forms.toList, fm.oracle = o) ∧
    (q.onMasks.isEmpty = false → ∀ o, maskOracle f = some o →
      (⟨o, .mask, 0, 1, .own q.onMasks⟩ : Run) ∈ row.runs.toList) := by
  unfold asRow at h
  obtain ⟨row0, h0, h⟩ := ok_bind h
  obtain ⟨_, _, c3⟩ := addTerms_forms Rr f d.st _ {} row0 (termsRow_ok _ _ _ _ _ _ h0)
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e1 : row = { row0 with target := subE zeroE q.constant } :=
      (congrArg Prod.fst (Except.ok.inj h)).symm
    rw [e1]
    exact ⟨c3, fun hx => by simp [he] at hx⟩
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, hm, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', ho, h⟩ := ok_bind h
    obtain ⟨x, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e1 : row = { row0.addRun o' .mask 0 1 (.own q.onMasks) with
        target := subE zeroE q.constant } := (congrArg Prod.fst (Except.ok.inj h)).symm
    have hmo : maskOracle f = some o' := by
      unfold maskOracle
      rw [there_ok hm]
      exact there_ok ho
    rw [e1]
    refine ⟨c3, fun _ o ho => ?_⟩
    have eo : o = o' := Option.some.inj (ho.symm.trans hmo)
    subst eo
    simp [Row.addRun]

theorem takeMaskP_size {X : Type} (d d' : St X) (o n : Nat)
    (h : Ground.takeMaskP d o = some (n, d')) : d'.st.oracles.size = d.st.oracles.size := by
  unfold Ground.takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.mp h
    have e2 : d' = _ := (congrArg Prod.snd e).symm
    rw [e2]
    simp
  · simp at h

theorem takeN_size {X : Type} (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat)
    (x : List Nat × St X), takeN o n d acc = .ok x → x.2.st.oracles.size = d.st.oracles.size
  | 0, d, acc, x, h => by
    have e : (acc.reverse, d) = x := Except.ok.inj h
    rw [← e]
  | n + 1, d, acc, x, h => by
    rw [takeN] at h
    obtain ⟨y, hy, h⟩ := ok_bind h
    rw [takeN_size o n y.2 _ x h, takeMaskP_size d y.2 o y.1 (there_ok hy)]

theorem asRow_size {X : Type} (Rr : ReqRows) (f : ReqFrame) (q : Equation) (d d' : St X)
    (row : OnBytes.Row) (h : asRow Rr f q d = .ok (row, d')) :
    d'.st.oracles.size = d.st.oracles.size := by
  unfold asRow at h
  obtain ⟨row0, _, h⟩ := ok_bind h
  by_cases he : q.onMasks.isEmpty = true
  · simp only [he, if_true] at h
    have e : d = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
  · simp only [he, Bool.false_eq_true, if_false] at h
    obtain ⟨m, _, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    obtain ⟨o', _, h⟩ := ok_bind h
    obtain ⟨x, hx, h⟩ := ok_bind h
    obtain ⟨_, _, h⟩ := ok_bind h
    have e : x.2 = d' := congrArg Prod.snd (Except.ok.inj h)
    rw [← e]
    exact takeN_size o' _ d [] x hx

theorem has_lt (S : Statement) (o : Nat) (part : OnBytes.Part) (h : S.has o part = true) :
    o < S.oracles.size := by
  unfold Statement.has at h
  split at h
  · rename_i x hx
    exact (Array.getElem?_eq_some_iff.mp hx).1
  · simp at h

/-- **Where the door returns, its own tests give three of the four public premises.** -/
theorem door_facts {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (N : Nat) (hN : d.st.oracles.size ≤ N)
    (inside : ∀ born name a, reqArray L.check.rows.layout born name = some a →
      ∀ b ∈ a.blocks, Inside a b)
    (h : door owed laid L F d = .ok out) :
    ∀ q G, equation L F = .ok (q, G) → RowPremises L.check d.st N q := by
  intro q G hq
  unfold door at h
  obtain ⟨n, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨y, hy, h⟩ := ok_bind h
  obtain ⟨d2, hd, h⟩ := ok_bind h
  have ex : x = (q, G) := Except.ok.inj (hx.symm.trans hq)
  subst ex
  have hd' := there_ok hd
  unfold Ground.addRowP at hd'
  split at hd'
  · rename_i hok
    simp only [Ground.ok, Ground.rowL, List.all_cons, List.all_nil, Bool.and_eq_true,
      Bool.and_true] at hok
    obtain ⟨hg, _, _, _, _, hruns, hforms, _⟩ := hok
    obtain ⟨G0, hG0⟩ := Option.isSome_iff_exists.mp hg
    simp only [Ground.has, hG0, Option.map_some, Option.getD_some, Array.all_eq_true_iff_forall_mem,
      Bool.and_eq_true] at hruns hforms
    obtain ⟨s1, s2⟩ := asRow_shape _ _ _ _ _ _ hy
    have hsz := asRow_size _ _ _ _ _ _ hy
    have hbits := asRow_bits _ _ _ _ _ _ hy
    refine ⟨inside, fun t ht a o ha ho => ?_, fun o he ho => ?_, fun o ho => ?_⟩
    · obtain ⟨fm, hfm, rfl⟩ := s1 t ht a o ha ho
      have hp := (hforms fm (Array.mem_toList_iff.mp hfm)).1
      simp only [← Own.placeFits_agrees, Blk.placeOk, Bool.and_eq_true] at hp
      have := has_lt _ _ _ hp.1.1.2
      omega
    · have hw := (hruns _ (Array.mem_toList_iff.mp (s2 he o ho))).2
      simp only [← Own.placeFits_agrees, Blk.placeOk, Bool.and_eq_true] at hw
      have := has_lt _ _ _ hw.1.1.2
      omega
    · by_cases he : q.onMasks.isEmpty = true
      · have hz : q.onMasks.size = 0 := by simpa using he
        rw [hz]
        exact Nat.zero_le _
      · have he' : q.onMasks.isEmpty = false := by simpa using he
        have hw := (hruns _ (Array.mem_toList_iff.mp (s2 he' o ho))).2
        simp only [← Own.placeFits_agrees, Blk.placeOk, Bool.and_eq_true, decide_eq_true_eq,
          Coeffs.size, Statement.tableBits] at hw
        have hlt := hw.2
        rw [(hbits o .mask).1, (hbits o .mask).2] at hlt
        omega
  · simp at hd'

variable {T W K Cl : Type} {C : CK} {F : Frame} [CommRing K]

/-- **The piece of the equation's block is good**, with the door's own tests in the place of three
premises. -/
theorem equation_goodIn' (X : Lens T) (ρ : Reading K) (pw : K9.Where) (N : Nat)
    (p : Piece C F T Cl W) (hb : p.b = below (K9.oneEquation X pw))
    (hext : ∀ a τ w, p.ext a τ w = w) (on on' : T × F.E.Str → Prop)
    (tabOf : T × F.E.Str → W → Nat → OnBytes.Part → Nat → K)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (hcarry : ∀ a τ b w, on a → p.ior.red.out a τ = some b → tabOf b w = tabOf a w)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hN : ∀ s, on s → ∀ a, X.get? s.1 = some a → a.d.st.oracles.size ≤ N)
    (inside : ∀ s, on s → ∀ a, X.get? s.1 = some a → ∀ born name r,
      reqArray a.L.check.rows.layout born name = some r → ∀ b ∈ r.blocks, Inside r b) :
    p.GoodIn on on'
      (fun a w => oneK X ρ a.1 a.1 (dataAt X a.1 (tabOf a w)) = 0 ∧
        GroupHoldsAt X ρ N a.1 (tabOf a w))
      (fun b w => GroupHoldsAt X ρ N b.1 (tabOf b w)) := by
  intro a ha
  refine _root_.Iop.Doomed.of_forall _ _ fun τ b hout => ⟨hhands a τ b ha hout, ?_⟩
  intro w hw
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hstep⟩ := fold_one hfold
  rw [hcarry a τ b w ha hout] at hw
  obtain ⟨a0, out, ha0, hdoor, _⟩ := oneEquation_inv X pw F.ft a.1 _ _ b.1 k hstep
  refine oneEquation_joint X ρ pw F.ft a.1 _ _ b.1 k N (tabOf a w) lens (fun a1 q G h1 hq => ?_)
    hstep hw
  have e : a1 = a0 := Option.some.inj (h1.symm.trans ha0)
  subst e
  exact door_facts _ _ _ _ _ out N (hN a ha a1 h1) (inside a ha a1 h1) hdoor q G hq

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.door_facts
#print axioms VerifiableInference.Desc.K9L.equation_goodIn'
