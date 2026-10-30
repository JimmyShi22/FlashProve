--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns6.lean: the flat hearing functions return: an open sumcheck's slots
stay free, and a row made late returns. Over OnBytes/K/Kc/Returns/FlReturns2.lean. Definitions,
statements and proofs.

Why. pscRowR (FlReturns.lean) is stated at "Ended": at the ledger just behind the sumcheck's end
values. Some callers make the row later, behind other hearing. And the whole functions' statements
(levelInR, tscInR) say "what was filled stays filled", which does not keep anything free.

Main names:
  `Open p G`: what Fl.pscRow asks, and no more: its four flags' tests; the arrays' size; the
    sumcheck's own slots [p.first, p.first + taken p) are there and free. It names no "next".
  Ended.isOpen: a sumcheck behind its end values is open.
  pscRowO: under Open alone Fl.pscRow returns; it fills the sumcheck's own slots and touches no
    other; next and ns stay.
  Open.keep: whatever leaves the arrays' size, the number of slots, and "filled or free" at the
    sumcheck's own slots, keeps it open.
  `Below F G`: G has F's number of slots, sized arrays if F has, and below F.next the same slots are
    filled. Below.refl, Below.trans.
  Open.below: so a function with "Below F G" keeps open every sumcheck whose slots lie below F.next.
  tscLoopN, levelRoundsN: the loops once more, with the next slot by number. Mid.room, Ended.room.
  claimsIn_below, levelIn_below, tscIn_below: the functions once more, with Below, the next slot and
    the slots that are handed back by number, and which of them are filled.
  room_row: a row made late leaves Room as it was, if the sumcheck's own slots lie below G.next (a
    premise).

Limits. As in FlReturns4.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

/-- What Fl.pscRow asks, and no more. -/
structure Open (p : Psc) (G : Fork) : Prop where
  noRow : p.rowMade = false
  started : p.started = true
  sizes : p.r.size = p.vars.size
  some : p.vars.toList ≠ []
  pos : ∀ w ∈ p.vars.toList, 1 ≤ w.d
  sized : Sized G
  fits : p.first + taken p ≤ G.ns
  own : ∀ j, p.first ≤ j → j < p.first + taken p → ¬ Filled G j

theorem Ended.isOpen {p : Psc} {G : Fork} {e n k : Nat} (h : Ended p G e n k) : Open p G :=
  ⟨h.noRow, h.started, h.sizes, h.some, h.pos, h.sized, by
    have h1 := h.first
    have h2 := h.next
    have h3 := h.fits
    omega, fun j h1 h2 => h.own j h1 (by rw [h.first]; exact h2)⟩

theorem Open.keep {p : Psc} {G G' : Fork} (h : Open p G) (hs : Sized G') (hns : G'.ns = G.ns)
    (hf : ∀ j, p.first ≤ j → j < p.first + taken p → (Filled G' j ↔ Filled G j)) : Open p G' :=
  ⟨h.noRow, h.started, h.sizes, h.some, h.pos, hs, by rw [hns]; exact h.fits,
    fun j h1 h2 hj => h.own j h1 h2 ((hf j h1 h2).1 hj)⟩

theorem walk_taken {p : Psc} {G : Fork} (h : Open p G) : p.walk.1.length = taken p := by
  have hl : p.vars.toList.length = p.r.toList.length := by
    rw [Array.length_toList, Array.length_toList, h.sizes]
  have hz : (p.vars.toList.zip p.r.toList).map Prod.fst = p.vars.toList :=
    List.map_fst_zip (Nat.le_of_eq hl)
  have hne : p.vars.toList.zip p.r.toList ≠ [] := by
    intro h0
    rw [h0] at hz
    exact h.some hz.symm
  unfold Psc.walk taken
  rw [zipT_eq, OnBytes.G4.hidingWalk_length _ hne (fun x hx => h.pos x.1 (by
    rw [← hz]
    exact List.mem_map_of_mem hx))]
  have e2 : (p.vars.toList.zip p.r.toList).map (fun x => x.1.d - 1) =
      ((p.vars.toList.zip p.r.toList).map Prod.fst).map fun w => w.d - 1 := by
    rw [List.map_map]
    rfl
  rw [e2, hz]

/-- **A row made at any ledger at which the sumcheck is still open.** -/
theorem pscRowO {p : Psc} {G : Fork} (h : Open p G) (S0 : E) (kept : Aff) (t : Tape) :
    ∃ H, Fl.pscRow p S0 kept G t = some ((p.rowForm S0 kept, { p with rowMade := true }), H, t) ∧
      Sized H ∧ H.next = G.next ∧ H.ns = G.ns ∧
      (∀ j, p.first ≤ j → j < p.first + taken p → Filled H j) ∧
      ∀ j, (j < p.first ∨ p.first + taken p ≤ j) → (Filled H j ↔ Filled G j) := by
  have hlen := walk_taken h
  have hsz : (Array.replicate p.walk.1.length zeroE : Array E).size = taken p := by
    rw [Array.size_replicate, hlen]
  obtain ⟨H, hH⟩ := hideRun_free (F := G) p.first (Array.replicate p.walk.1.length zeroE)
    (subE zeroE oneE) h.sized (by
      intro i hi
      rw [hsz] at hi
      have h3 := h.fits
      exact ⟨by omega, h.own _ (by omega) (by omega)⟩)
  obtain ⟨a1, a2, a3, a4⟩ := hideRun_ok G H p.first _ _ h.sized hH
  refine ⟨H, ?_, a2, a1.next, a1.ns, fun j h1 h2 => ?_, fun j hj =>
    (a4 j (by rw [hsz]; exact hj)).2.2⟩
  · unfold Fl.pscRow
    refine bindR (mustR (by
      have hv : p.vars.isEmpty = false := by
        cases hq : p.vars.toList with
        | nil => exact absurd hq h.some
        | cons a l =>
          have : p.vars.size ≠ 0 := by
            rw [← Array.length_toList, hq]
            simp
          simpa [Array.isEmpty] using this
      rw [h.noRow, h.started, hv, h.sizes]
      simp) _ _) ?_
    refine bindR (changeR hH t) ?_
    rfl
  · have e' : p.first + (j - p.first) = j := by omega
    have := (a3 (j - p.first) (by rw [hsz]; omega)).2.2.1
    rw [e'] at this
    exact this

/-- Below F.next nothing has turned from free to filled or back. -/
structure Below (F G : Fork) : Prop where
  ns : G.ns = F.ns
  sized : Sized F → Sized G
  next : F.next ≤ G.next
  same : ∀ j, j < F.next → (Filled G j ↔ Filled F j)

theorem Below.refl (F : Fork) : Below F F := ⟨rfl, id, Nat.le_refl _, fun _ _ => Iff.rfl⟩

theorem Below.trans {F G H : Fork} (a : Below F G) (b : Below G H) : Below F H :=
  ⟨b.ns.trans a.ns, fun s => b.sized (a.sized s), Nat.le_trans a.next b.next, fun j hj =>
    (b.same j (Nat.lt_of_lt_of_le hj a.next)).trans (a.same j hj)⟩

theorem below_next (F : Fork) (m : Nat) (h : F.next ≤ m) : Below F ({ F with next := m } : Fork) :=
  ⟨rfl, sized_next, h, fun _ _ => filled_next⟩

/-- **What is heard behind an open sumcheck keeps it open.** -/
theorem Open.below {p : Psc} {F G : Fork} (h : Open p F) (hb : Below F G)
    (hp : p.first + taken p ≤ F.next) : Open p G :=
  h.keep (hb.sized h.sized) hb.ns fun j _ h2 => hb.same j (by omega)

/-- A row made late leaves the room as it was. -/
theorem room_row {p : Psc} {G H : Fork} {k : Nat} (hr : Room G k) (hp : p.first + taken p ≤ G.next)
    (hs : Sized H) (hn : H.next = G.next) (hns : H.ns = G.ns)
    (hf : ∀ j, (j < p.first ∨ p.first + taken p ≤ j) → (Filled H j ↔ Filled G j)) : Room H k :=
  ⟨hs, by rw [hn, hns]; exact hr.fits, fun j hj hfj => by
    rw [hn] at hj
    exact hr.free j hj ((hf j (Or.inr (by omega))).1 hfj)⟩

/-! ## The loops once more, with the next slot by number -/

/-- The rounds of a token sumcheck: the next slot by number. -/
theorem tscLoopN : ∀ (zs : List E) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
    (n : Nat) (u : Tape), rs.length = zs.length → (∀ x ∈ rs, IsVar x) →
    Mid p F (2 * zs.length + n) →
    ∃ r' q G, Fl.tscLoop zs r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.next = F.next + 2 * zs.length ∧ G.ns = F.ns ∧
      ∀ j, Filled G j ↔ Filled F j
  | [], [], r, p, F, n, u, _, _, h => by
    have e2 : 2 * ([] : List E).length + n = n := by simp
    rw [e2] at h
    exact ⟨r, p, F, rfl, h, rfl, rfl, rfl, fun _ => Iff.rfl⟩
  | [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | z :: zs, x :: rs, r, p, F, n, u, hl, hv, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (by simp))
    have hlen : 2 * (z :: zs).length + n = 2 + (2 * zs.length + n) := by
      rw [List.length_cons]
      omega
    rw [hlen] at h
    obtain ⟨h1, h2⟩ := roundInR h z w sent c (rs ++ u) hs
    obtain ⟨r', q, G, h3, h4, h5, h6, h7, h8⟩ := tscLoopN zs rs (r.push c) _ _ n u
      (by simpa using hl) (fun y hy => hv y (by simp [hy])) h2
    have h6' : G.next = F.next + 2 + 2 * zs.length := h6
    refine ⟨r', q, G, ?_, h4, h5.trans (stepQ_first _ _ _ _), ?_, h7,
      fun j => (h8 j).trans filled_next⟩
    · rw [List.cons_append]
      unfold Fl.tscLoop
      exact bindR h1 h3
    · rw [h6', List.length_cons]
      omega

/-- The rounds of a layer: the next slot by number. -/
theorem levelRoundsN (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (rs : List FlatRound)
    (r : Array E) (p : Psc) (F : Fork) (n : Nat) (u : Tape), rs.length = order.length →
    (∀ x ∈ rs, IsVar x) → (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) →
    Mid p F (2 * order.length + n) →
    ∃ r' q G, Fl.levelRounds mu rho order r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.next = F.next + 2 * order.length ∧ G.ns = F.ns ∧
      ∀ j, Filled G j ↔ Filled F j
  | [], [], r, p, F, n, u, _, _, _, h => by
    have e2 : 2 * ([] : List Nat).length + n = n := by simp
    rw [e2] at h
    exact ⟨r, p, F, rfl, h, rfl, rfl, rfl, fun _ => Iff.rfl⟩
  | [], _ :: _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _, _ => by simp at hl
  | v :: order, x :: rs, r, p, F, n, u, hl, hv, ho, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (by simp))
    have hlen : 2 * (v :: order).length + n = 2 + (2 * order.length + n) := by
      rw [List.length_cons]
      omega
    rw [hlen] at h
    obtain ⟨h1, h2⟩ := roundInR h (rho.getD (mu - 1 - v) zeroE) w sent c (rs ++ u) hs
    obtain ⟨r', q, G, h3, h4, h5, h6, h7, h8⟩ := levelRoundsN mu rho order rs
      (r.set! (mu - 1 - v) c) _ _ n u (by simpa using hl) (fun y hy => hv y (by simp [hy]))
      (fun y hy => ho y (by simp [hy])) h2
    have h6' : G.next = F.next + 2 + 2 * order.length := h6
    refine ⟨r', q, G, ?_, h4, h5.trans (stepQ_first _ _ _ _), ?_, h7,
      fun j => (h8 j).trans filled_next⟩
    · rw [List.cons_append]
      unfold Fl.levelRounds
      refine bindR (mustR (by
        obtain ⟨a1, a2⟩ := ho v (by simp)
        simp [a1, a2]) _ _) ?_
      exact bindR h1 h3
    · rw [h6', List.length_cons]
      omega

/-- A sumcheck in course has room; so has one behind its end values. -/
theorem Mid.room {p : Psc} {F : Fork} {n : Nat} (h : Mid p F n) : Room F n :=
  ⟨h.sized, h.fits, fun j hj => h.free j (by
    have := h.next
    omega)⟩

theorem Ended.room {p : Psc} {G : Fork} {e n k : Nat} (h : Ended p G e n k) : Room G k :=
  ⟨h.sized, h.fits, h.beyond⟩

/-! ## The functions once more, with Below -/

theorem claimsIn_below {F : Fork} {n k : Nat} (h : Room F (n + k)) (nm : Option String) (z w : Nat)
    (xs s d : List E) (t : Tape) (hx : xs.length = n) :
    ∃ G, Fl.claimsIn n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = some (F.next, G, ⟨nm, z, w, s, d⟩ :: t) ∧
      Room G k ∧ Below F G := by
  obtain ⟨G, a1, a2, a3, a4, _, a6⟩ := claimsInR h nm z w xs s d t hx
  exact ⟨G, a1, a2, a4, fun _ => a2.sized, by omega, a6⟩

/-- From the ledger in front of a sumcheck's beginning to the one behind its row. -/
theorem levelIn_below {F : Fork} {mu k : Nat} (h : Room F (1 + (2 * mu + (2 + 2 + k)))) {C : Aff}
    {T : E} (hT : F.publicPart C = some T) (rho : Array E) (order : List Nat)
    (ho : order.length = mu) (hv : ∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) (mu0 eps : E)
    (w0 : Nat) (rs : List FlatRound) (hrs : rs.length = mu) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat)
    (sentY : List E) (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
    (hvals : vals.length = 2) (wT : Nat) (tau : E) (u : Tape) :
    ∃ L G, Fl.levelIn mu rho C order F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
          (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
            ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)) = some (L, G, u) ∧
      Room G k ∧ Below F G ∧ G.next = F.next + (1 + (2 * mu + (2 + 2))) ∧
      L.sL = F.next + (1 + (2 * mu + 2)) ∧ L.sR = L.sL + 1 ∧ Filled G L.sL ∧ Filled G L.sR := by
  obtain ⟨p0, b1, b2, b3⟩ := pscBeginR h hT mu0 eps w0
    (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
      ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)
  rw [← ho] at b2
  obtain ⟨r1, p1, G1, c1, c2, c3, cN, c4, c5⟩ := levelRoundsN mu rho order rs
    (Array.replicate mu zeroE) p0 _ (2 + 2 + k)
    (⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
      ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u) (by rw [hrs, ho]) hvar hv b2
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR c2 (by omega) (by omega) wY wV sentY vals beta
    (⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u) hsY hvals
  have hfit := d2.fits
  have hnx := d2.next
  obtain ⟨H, e1, e2, e3, e4, e5, e6⟩ := pscRowO d2.isOpen
    (mulE (G2.vp.getD (G1.next + 2) zeroE) (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} u
  have f0 := d2.ends 0 (by omega)
  have f1 := d2.ends 1 (by omega)
  rw [Nat.add_zero] at f0
  have hfirst : p2.first = F.next := by rw [d3, c3, b3]
  have hG1 : F.next < G1.next := by
    have a1 := c2.next
    have a2 := one_le_taken p1
    rw [c3, b3] at a1
    omega
  have hown : p2.first + taken p2 ≤ G2.next := by
    have := d2.first
    omega
  refine ⟨{ r := r1, sL := G1.next + 2, sR := G1.next + 2 + 1, tau := tau,
            row := p2.rowForm (mulE (G2.vp.getD (G1.next + 2) zeroE)
              (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} }, H, ?_,
    room_row d2.room hown e2 e3 e4 e6,
    ⟨by rw [e4, d4, c4], fun _ => e2, by omega, fun j hj => ?_⟩, ?_, ?_, rfl, ?_, ?_⟩
  · unfold Fl.levelIn
    refine bindR (mustR (by simp [ho]) _ _) ?_
    refine bindR b1 ?_
    refine bindR c1 ?_
    refine bindR d1 ?_
    refine bindR (answerR .line wT tau _ u) ?_
    refine bindR (shownR (by omega) f0 u) ?_
    refine bindR (shownR (by omega) f1 u) ?_
    refine bindR e1 ?_
    rfl
  · exact (e6 j (Or.inl (by omega))).trans
      (((d5 j (by omega)).trans (c5 j)).trans filled_next)
  · have cN' : G1.next = F.next + 1 + 2 * order.length := cN
    rw [e3, hnx, cN', ho]
    omega
  · have cN' : G1.next = F.next + 1 + 2 * order.length := cN
    show G1.next + 2 = _
    rw [cN', ho]
    omega
  · exact (e6 (G1.next + 2) (Or.inr (by
      have := d2.first
      omega))).2 f0
  · exact (e6 (G1.next + 2 + 1) (Or.inr (by
      have := d2.first
      omega))).2 f1

/-- A token sumcheck: it is left OPEN, with room behind it, and nothing below has turned. -/
theorem tscIn_below {F : Fork} {lt n k : Nat} (P : Array E) (hP : lt ≤ P.size) (hn : 1 ≤ n)
    (h : Room F (1 + (1 + (2 * lt + (2 + n + k))))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
    (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
    (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = n)
    (u : Tape) :
    ∃ o G, Fl.tscIn P lt n 2 F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (o, G, u) ∧
      Open o.p G ∧ o.p.first + taken o.p ≤ G.next ∧ Room G k ∧ Below F G ∧ o.sCl = F.next ∧
      Filled G F.next ∧ o.p.first = F.next + 1 ∧ o.sEnd = F.next + (1 + (1 + (2 * lt + 2))) ∧
      G.next = o.sEnd + n ∧ ∀ i, i < n → Filled G (o.sEnd + i) := by
  have hzl : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    omega
  obtain ⟨G0, a1, a2, a3, a4, a5, a6⟩ := claimsInR (n := 1) h
    (some Model.RoundName.pscEpsilon.name) 0 w0 [cl] [mu] [eps]
    (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u) rfl
  have f0 := a5 0 (by omega)
  rw [Nat.add_zero] at f0
  obtain ⟨T, hT⟩ := publicPart_some G0 (Aff.slot F.next) (by
    intro x hx
    have hx' : x = (F.next, oneE) := by simpa [Aff.slot] using hx
    rw [hx']
    have := a2.fits
    exact ⟨by show F.next < G0.ns; omega, f0⟩)
  obtain ⟨p0, b1, b2, b3⟩ := pscBeginR a2 hT mu eps w0
    (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)
  rw [← hzl] at b2
  obtain ⟨r1, p1, G1, c1, c2, c3, cN, c4, c5⟩ := tscLoopN (P.toList.take lt) rs #[] p0 _ (2 + n + k)
    (⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u) (by rw [hrs, hzl]) hvar b2
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR c2 (by omega) hn wY wV sentY vals beta u hsY hvals
  have hG1 : F.next + 1 < G1.next := by
    have e1 := c2.next
    have e2 := one_le_taken p1
    rw [c3, b3, a3] at e1
    omega
  have hnx := d2.next
  have hrounds : Fl.tscRounds P lt F
      (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
        (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) =
      some ({ sCl := F.next, r := r1, p := p1 }, G1,
        ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u) := by
    unfold Fl.tscRounds
    refine bindR (mustR (by simpa using hP) _ _) ?_
    refine bindR a1 ?_
    refine bindR b1 ?_
    refine bindR c1 ?_
    rfl
  refine ⟨{ sCl := F.next, r := r1, p := p2, sEnd := G1.next + 2 }, G2, ?_, d2.isOpen, ?_,
    d2.room, ⟨by rw [d4, c4]; exact a4, fun _ => d2.sized, by omega,
      fun j hj => ?_⟩, rfl, ?_, ?_, ?_, hnx, d2.ends⟩
  · unfold Fl.tscIn
    refine bindR hrounds ?_
    refine bindR d1 ?_
    rfl
  · have := d2.first
    show p2.first + taken p2 ≤ G2.next
    omega
  · exact ((d5 j (by omega)).trans (c5 j)).trans (filled_next.trans (a6 j hj))
  · exact (d5 _ (by omega)).2 ((c5 _).2 (filled_next.mpr f0))
  · show p2.first = F.next + 1
    rw [d3, c3, b3, a3]
  · have cN' : G1.next = G0.next + 1 + 2 * (P.toList.take lt).length := cN
    show G1.next + 2 = _
    rw [cN', a3, hzl]
    omega

end D6.Ret

#print axioms D6.Ret.pscRowO
#print axioms D6.Ret.Open.below
#print axioms D6.Ret.room_row
#print axioms D6.Ret.levelIn_below
#print axioms D6.Ret.tscIn_below
