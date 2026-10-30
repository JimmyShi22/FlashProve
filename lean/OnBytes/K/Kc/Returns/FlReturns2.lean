--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns2.lean: the flat hearing functions return, second part: the loops and
the whole functions, over the steps of OnBytes/K/Kc/Returns/FlReturns.lean. Statements and proofs.

The tests that these functions add to those listed in FlReturns.lean's head, and what each reads:
  levelRounds   must (v < mu, mu - 1 - v < rho.size) for each member v of the order.
                                                                                [public numbers]
  levelIn       must (order.length == mu); shown sL, shown (sL + 1): both end slots are filled.
                                                                                [public; ledger]
  tscRounds     must (lt <= P.size).                                          [the point's size]
  shownRun      shown at each slot.                                                     [ledger]
None reads a sent or a drawn value.

Main names:
  `IsVar x`: a round of a sumcheck's variable of the form eq2: its name, no never-0 draw, two
    elements sent, one drawn.
  tscLoopR, levelRoundsR: one such round for each coordinate.
  levelInR: a layer of a product tree returns on: the beginning (mu0 | eps), mu rounds, the further
    variable's round (two elements | beta; one never-0 draw by the round's word), the two end
    values, the round of the line (tau).
  tscInR: a token sumcheck returns on: the beginning (the claimed sum, mu | eps), lt rounds, the
    further variable's round, the n end values. It leaves the sumcheck "Ended": pscRowR goes on from
    there.
  shownRunR.
The form of these statements: the tape's shape and Room F (what the function takes, plus k) give a
value and a ledger G with f F (tape ++ u) = some (value, G, u), Room G k (or Mid, or Ended), G.ns =
F.ns, and what was filled below F.next is filled.

Limits. As in FlReturns.lean. "What was filled stays filled" keeps nothing free: the stronger forms
stand in OnBytes/K/Kc/Returns/FlReturns6.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

/-- A round of a variable of the form eq2. -/
def IsVar (x : FlatRound) : Prop :=
  x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.sent.length = 2 ∧ x.drawn.length = 1

theorem isVar_lit {x : FlatRound} (h : IsVar x) : ∃ (w : Nat) (sent : List E) (c : E),
    x = ⟨some Model.RoundName.pscRound.name, 0, w, sent, [c]⟩ ∧ sent.length = 2 := by
  obtain ⟨nm, z, w, sent, d⟩ := x
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h1' : nm = some Model.RoundName.pscRound.name := h1
  have h2' : z = 0 := h2
  have h4' : d.length = 1 := h4
  subst h1' h2'
  cases d with
  | nil => simp at h4'
  | cons c d' =>
    cases d' with
    | nil => exact ⟨w, sent, c, rfl, h3⟩
    | cons _ _ => simp at h4'

/-- **The rounds of a token sumcheck.** -/
theorem tscLoopR : ∀ (zs : List E) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
    (n : Nat) (u : Tape), rs.length = zs.length → (∀ x ∈ rs, IsVar x) →
    Mid p F (2 * zs.length + n) →
    ∃ r' q G, Fl.tscLoop zs r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  | [], [], r, p, F, n, u, _, _, h => by
    have e2 : 2 * ([] : List E).length + n = n := by simp
    rw [e2] at h
    exact ⟨r, p, F, rfl, h, rfl, rfl, fun _ => Iff.rfl⟩
  | [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | z :: zs, x :: rs, r, p, F, n, u, hl, hv, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (by simp))
    have hlen : 2 * (z :: zs).length + n = 2 + (2 * zs.length + n) := by
      rw [List.length_cons]
      omega
    rw [hlen] at h
    obtain ⟨h1, h2⟩ := roundInR h z w sent c (rs ++ u) hs
    obtain ⟨r', q, G, h3, h4, h5, h6, h7⟩ := tscLoopR zs rs (r.push c) _ _ n u (by simpa using hl)
      (fun y hy => hv y (by simp [hy])) h2
    refine ⟨r', q, G, ?_, h4, h5.trans (stepQ_first _ _ _ _), h6,
      fun j => (h7 j).trans filled_next⟩
    rw [List.cons_append]
    unfold Fl.tscLoop
    exact bindR h1 h3

/-- **The rounds of a layer, in a given order.** -/
theorem levelRoundsR (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (rs : List FlatRound)
    (r : Array E) (p : Psc) (F : Fork) (n : Nat) (u : Tape), rs.length = order.length →
    (∀ x ∈ rs, IsVar x) → (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) →
    Mid p F (2 * order.length + n) →
    ∃ r' q G, Fl.levelRounds mu rho order r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  | [], [], r, p, F, n, u, _, _, _, h => by
    have e2 : 2 * ([] : List Nat).length + n = n := by simp
    rw [e2] at h
    exact ⟨r, p, F, rfl, h, rfl, rfl, fun _ => Iff.rfl⟩
  | [], _ :: _, _, _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _, _, _ => by simp at hl
  | v :: order, x :: rs, r, p, F, n, u, hl, hv, ho, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (by simp))
    have hlen : 2 * (v :: order).length + n = 2 + (2 * order.length + n) := by
      rw [List.length_cons]
      omega
    rw [hlen] at h
    obtain ⟨h1, h2⟩ := roundInR h (rho.getD (mu - 1 - v) zeroE) w sent c (rs ++ u) hs
    obtain ⟨r', q, G, h3, h4, h5, h6, h7⟩ := levelRoundsR mu rho order rs
      (r.set! (mu - 1 - v) c) _ _ n u (by simpa using hl) (fun y hy => hv y (by simp [hy]))
      (fun y hy => ho y (by simp [hy])) h2
    refine ⟨r', q, G, ?_, h4, h5.trans (stepQ_first _ _ _ _), h6,
      fun j => (h7 j).trans filled_next⟩
    rw [List.cons_append]
    unfold Fl.levelRounds
    refine bindR (mustR (by
      obtain ⟨a1, a2⟩ := ho v (by simp)
      simp [a1, a2]) _ _) ?_
    exact bindR h1 h3

/-- What was shown under a slot that is there and filled. -/
theorem shownR {G : Fork} {j : Nat} (h1 : j < G.ns) (h2 : Filled G j) (t : Tape) :
    Fl.shown j G t = some (G.vp.getD j zeroE, G, t) :=
  askR ((shown_iff G j _).2 ⟨h1, h2, rfl⟩) t

theorem one_le_taken (p : Psc) : 1 ≤ taken p := by
  unfold taken
  omega

/-- **A LAYER OF A PRODUCT TREE RETURNS.** -/
theorem levelInR {F : Fork} {mu k : Nat} (h : Room F (1 + (2 * mu + (2 + 2 + k)))) {C : Aff} {T : E}
    (hT : F.publicPart C = some T) (rho : Array E) (order : List Nat) (ho : order.length = mu)
    (hv : ∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) (mu0 eps : E) (w0 : Nat)
    (rs : List FlatRound) (hrs : rs.length = mu) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat)
    (sentY : List E) (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
    (hvals : vals.length = 2) (wT : Nat) (tau : E) (u : Tape) :
    ∃ L G, Fl.levelIn mu rho C order F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
          (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
            ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)) = some (L, G, u) ∧
      Room G k ∧ G.ns = F.ns ∧ ∀ j, j < F.next → Filled F j → Filled G j := by
  obtain ⟨p0, b1, b2, b3⟩ := pscBeginR h hT mu0 eps w0
    (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
      ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)
  rw [← ho] at b2
  obtain ⟨r1, p1, G1, c1, c2, c3, c4, c5⟩ := levelRoundsR mu rho order rs
    (Array.replicate mu zeroE) p0 _ (2 + 2 + k)
    (⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
      ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u) (by rw [hrs, ho]) hvar hv b2
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR c2 (by omega) (by omega) wY wV sentY vals beta
    (⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u) hsY hvals
  have hfit := d2.fits
  have hnx := d2.next
  obtain ⟨H, e1, e2, e3, e4, e5⟩ := pscRowR d2
    (mulE (G2.vp.getD (G1.next + 2) zeroE) (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} u
  have f0 := d2.ends 0 (by omega)
  have f1 := d2.ends 1 (by omega)
  rw [Nat.add_zero] at f0
  have hG1 : F.next < G1.next := by
    have a1 := c2.next
    have a2 := one_le_taken p1
    rw [c3, b3] at a1
    omega
  refine ⟨{ r := r1, sL := G1.next + 2, sR := G1.next + 2 + 1, tau := tau,
            row := p2.rowForm (mulE (G2.vp.getD (G1.next + 2) zeroE)
              (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} }, H, ?_, e2, ?_, ?_⟩
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
  · rw [e4, d4, c4]
  · intro j hj hf
    exact e5 j ((d5 j (by omega)).2 ((c5 j).2 (filled_next.mpr hf)))

/-- **A TOKEN SUMCHECK RETURNS.** -/
theorem tscInR {F : Fork} {lt n k : Nat} (P : Array E) (hP : lt ≤ P.size) (hn : 1 ≤ n)
    (h : Room F (1 + (1 + (2 * lt + (2 + n + k))))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
    (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
    (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = n)
    (u : Tape) :
    ∃ o G, Fl.tscIn P lt n 2 F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (o, G, u) ∧
      Ended o.p G o.sEnd n k ∧ o.sCl = F.next ∧ G.ns = F.ns ∧ Filled G F.next ∧
      ∀ j, j < F.next → Filled F j → Filled G j := by
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
  obtain ⟨r1, p1, G1, c1, c2, c3, c4, c5⟩ := tscLoopR (P.toList.take lt) rs #[] p0 _ (2 + n + k)
    (⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u) (by rw [hrs, hzl]) hvar b2
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR c2 (by omega) hn wY wV sentY vals beta u hsY hvals
  have hG1 : F.next + 1 < G1.next := by
    have e1 := c2.next
    have e2 := one_le_taken p1
    rw [c3, b3, a3] at e1
    omega
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
  refine ⟨{ sCl := F.next, r := r1, p := p2, sEnd := G1.next + 2 }, G2, ?_, d2, rfl, ?_, ?_, ?_⟩
  · unfold Fl.tscIn
    refine bindR hrounds ?_
    refine bindR d1 ?_
    rfl
  · rw [d4, c4]
    exact a4
  · exact (d5 _ (by omega)).2 ((c5 _).2 (filled_next.mpr f0))
  · intro j hj hf
    exact (d5 j (by omega)).2 ((c5 j).2 (filled_next.mpr ((a6 j hj).2 hf)))

/-- **What was shown in n slots that are there and filled.** -/
theorem shownRunR (first : Nat) (G : Fork) (t : Tape) : ∀ (n : Nat),
    (∀ i, i < n → first + i < G.ns ∧ Filled G (first + i)) →
    ∃ a, Fl.shownRun first n G t = some (a, G, t) := by
  intro n h
  have key : ∀ (l : List Nat) (b : Array E), (∀ j ∈ l, first + j < G.ns ∧ Filled G (first + j)) →
      ∃ a, (l.foldlM (fun (a : Array E) (j : Nat) =>
        (do pure (a.push (← Fl.shown (first + j))) : Fl (Array E))) b) G t = some (a, G, t) := by
    intro l
    induction l with
    | nil => exact fun b _ => ⟨b, rfl⟩
    | cons j l ih =>
      intro b hl
      obtain ⟨h1, h2⟩ := hl j (by simp)
      obtain ⟨a, ha⟩ := ih (b.push (G.vp.getD (first + j) zeroE)) fun i hi => hl i (by simp [hi])
      refine ⟨a, ?_⟩
      rw [List.foldlM_cons]
      refine bindR (bindR (shownR h1 h2 t) rfl) ha
  unfold Fl.shownRun
  exact key (List.range n) #[] fun j hj => h j (List.mem_range.mp hj)

end D6.Ret

#print axioms D6.Ret.levelInR
#print axioms D6.Ret.tscInR
#print axioms D6.Ret.shownRunR
