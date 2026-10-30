--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns4.lean: the flat hearing functions return: one theorem for all:
flat_hears_return. Over OnBytes/K/Kc/Returns/FlReturns.lean, FlReturns2.lean, FlReturns3.lean.
Statements and proofs.

Main names:
  tscRoundsR: a token sumcheck that its caller goes on with. flatLogitsR: the last of the head's
    five routines.
  pscRoundG, roundInG, roundsInR: every form of a round (.eq2 .sum2 .sum3 .nodes .eq: equality
    weights and the plain sum's), and Fl.roundsIn (which lies in OnBytes/K/Kc/FlatHear.lean). What a
    form adds to the tests: it admits the degree (1 to 64 for .nodes and .eq): a public number.
  `FlatHearsReturn`: a structure of the statements, twenty-two fields: Fl.claimsIn, batch, point,
    answer, pscBegin, pscRound, roundIn, roundsIn, pscEnds, pscRow, levelRounds, levelIn, tscLoop,
    tscRounds, tscIn, shownRun, channelRounds; flatPoint, flatSquares, flatProducts, flatStream,
    flatLogits: every function of Flat.lean of the type Fl that reads the tape or writes the ledger,
    but for the bare steps (read, readSum, empty, takeSlots, shown, publicPart, pscBeginAt), which
    stand as lemmas in FlReturns.lean. Each field is the statement of the theorem named in
    flat_hears_return, to the letter.
  `flat_hears_return : FlatHearsReturn`.

What it says, in one sentence: on a tape whose next rounds have the names, the never-0 words, the
rows and the numbers of sent and drawn elements that a function asks, from a ledger whose arrays
have their size, in which the slots that the function takes fit and are free (and every slot that
its start form names is filled), the function returns, hands back the tape behind these rounds, and
leaves a ledger with the room that is left.

Limits. What the value is it does not say (the lemmas "from a return" say that). The loops
levelRounds, tscLoop, channelRounds run in the form .eq2, as the text has them. The rest of
FlatHear.lean (lkDraws, lkTie, lkLevel, lkPad, flatHear) is not covered, and by that file's own head
flatHear does test two values (flatReplyToken, flatMergedPoint). That a tape of this shape comes
from a view is not touched. The refusals (FlReturns3.lean) are not in the structure. THE FIELD
pscRow ASKS "Ended", the ledger just behind the sumcheck's end values: a caller that makes the row
later, behind other hearing, cannot pay that: for such a caller stands
OnBytes/K/Kc/Returns/FlReturns8.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns3
import OnBytes.K.Kc.FlatHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

/-- **A token sumcheck that its caller goes on with.** -/
theorem tscRoundsR {F : Fork} {lt m : Nat} (P : Array E) (hP : lt ≤ P.size)
    (h : Room F (1 + (1 + (2 * lt + m)))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
    (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (u : Tape) :
    ∃ o G, Fl.tscRounds P lt F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: (rs ++ u)) =
        some (o, G, u) ∧ Mid o.p G m ∧ o.sCl = F.next ∧ G.ns = F.ns := by
  have hzl : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    omega
  obtain ⟨G0, a1, a2, a3, a4, a5, a6⟩ := claimsInR (n := 1) h
    (some Model.RoundName.pscEpsilon.name) 0 w0 [cl] [mu] [eps] (rs ++ u) rfl
  have f0 := a5 0 (by omega)
  rw [Nat.add_zero] at f0
  obtain ⟨T, hT⟩ := publicPart_some G0 (Aff.slot F.next) (by
    intro x hx
    have hx' : x = (F.next, oneE) := by simpa [Aff.slot] using hx
    rw [hx']
    have := a2.fits
    exact ⟨by show F.next < G0.ns; omega, f0⟩)
  obtain ⟨p0, b1, b2, b3⟩ := pscBeginR a2 hT mu eps w0 (rs ++ u)
  rw [← hzl] at b2
  obtain ⟨r1, p1, G1, c1, c2, c3, c4, c5⟩ := tscLoopR (P.toList.take lt) rs #[] p0 _ m u
    (by rw [hrs, hzl]) hvar b2
  refine ⟨{ sCl := F.next, r := r1, p := p1 }, G1, ?_, c2, rfl, by rw [c4]; exact a4⟩
  unfold Fl.tscRounds
  refine bindR (mustR (by simpa using hP) _ _) ?_
  refine bindR a1 ?_
  refine bindR b1 ?_
  refine bindR c1 ?_
  rfl

/-- **The token sumcheck of the activations times the head's weights, with rounds over the
channels.** -/
theorem flatLogitsR {F : Fork} {lt lam k : Nat} (zt : Array E) (hzt : lt ≤ zt.size)
    (h : Room F (1 + (1 + (2 * lt + (2 * lam + (2 + 2 + k)))))) (cl mu eps : E) (w0 : Nat)
    (rs1 : List FlatRound) (hrs1 : rs1.length = lt) (hvar1 : ∀ x ∈ rs1, IsVar x)
    (rs2 : List FlatRound) (hrs2 : rs2.length = lam) (hvar2 : ∀ x ∈ rs2, IsVar x) (wY : Nat)
    (sentY : List E) (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
    (hvals : vals.length = 2) (u : Tape) :
    ∃ a G, flatLogits lt lam zt F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs1 ++ (rs2 ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u))) = some (a, G, u) ∧
      Room G k ∧ G.ns = F.ns := by
  obtain ⟨o, G0, a1, a2, a3, a4⟩ := tscRoundsR zt hzt h cl mu eps w0 rs1 hrs1 hvar1
    (rs2 ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)
  obtain ⟨r1, p1, G1, c1, c2, c3, c4, c5⟩ := channelRoundsR lam rs2 #[] o.p G0 (2 + 2 + k)
    (⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u) hrs2 hvar2 a2
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR c2 (by omega) (by omega) wY wV sentY vals beta u
    hsY hvals
  have e1 := d2.next
  have e2 := d2.fits
  have f0 := d2.ends 0 (by omega)
  have f1 := d2.ends 1 (by omega)
  rw [Nat.add_zero] at f0
  obtain ⟨H, g1, g2, g3, g4, _⟩ := pscRowR d2
    (mulE (G2.vp.getD (G1.next + 2) zeroE) (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} u
  refine ⟨({ o with sEnd := G1.next + 2, p := { p2 with rowMade := true },
                    rowU := p2.rowForm (mulE (G2.vp.getD (G1.next + 2) zeroE)
                      (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} }, r1.reverse), H, ?_, g2,
    by rw [g4, d4, c4, a4]⟩
  unfold flatLogits
  refine bindR a1 ?_
  refine bindR c1 ?_
  refine bindR d1 ?_
  refine bindR (shownR (by omega) f0 u) ?_
  refine bindR (shownR (by omega) f1 u) ?_
  refine bindR g1 ?_
  rfl

/-! ## Every form of a round; rounds of one form in a row -/

/-- **One round at any weight that the program admits**, closed under a name. -/
theorem pscRoundG (p : Psc) (w : OnBytes.Psc.Weight) (hf : w.fits = true) (hh : weightHeld w = true)
    (name : String) (nz k : Nat) (sent : List E) (x : E) (t : Tape) (F : Fork)
    (hs : sent.length + 1 = w.d) :
    Fl.pscRound p w (closeOne name nz) F (⟨some name, nz, k, sent, [x]⟩ :: t) =
      some ((x, stepQ p w sent x), { F with next := F.next + (w.d - 1) }, t) := by
  have hread := readR (some name) nz k [x] t sent [] (w.d - 1) (by omega) F
  rw [List.append_nil] at hread
  unfold Fl.pscRound
  refine bindR (mustR (by rw [Bool.and_eq_true]; exact ⟨hf, hh⟩) _ _) ?_
  refine bindR hread ?_
  refine bindR (mustR (by show (sent.toArray.size + 1 == w.d) = true; simp [hs]) _ _) ?_
  refine bindR (onTapeR (closeOne_mk name nz k x t) F) ?_
  refine bindR (takeSlotsR (w.d - 1) F t) ?_
  rfl

theorem mid_stepG {p : Psc} {F : Fork} {n : Nat} (w : OnBytes.Psc.Weight) (hd : 2 ≤ w.d)
    (h : Mid p F (w.d - 1 + n)) (sent : List E) (x : E) :
    Mid (stepQ p w sent x) { F with next := F.next + (w.d - 1) } n := by
  refine ⟨by rw [stepQ_ended]; exact h.notEnded, by rw [stepQ_rowMade]; exact h.noRow,
    by rw [stepQ_started]; exact h.started, ?_, ?_, sized_next h.sized, ?_, ?_,
    fun j hj hf => h.free j (by rw [stepQ_first] at hj; exact hj) (filled_next.mp hf)⟩
  · show (p.r.push x).size = (p.vars.push _).size
    rw [Array.size_push, Array.size_push, h.sizes]
  · intro v hv
    have hv' : v ∈ p.vars.toList ++ [w] := by simpa [stepQ] using hv
    rcases List.mem_append.mp hv' with h1 | h1
    · exact h.pos v h1
    · rw [List.mem_singleton] at h1
      rw [h1]
      omega
  · rw [stepQ_first]
    show F.next + (w.d - 1) = p.first + taken (stepQ p w sent x)
    rw [taken_step, h.next]
    omega
  · show F.next + (w.d - 1) + n ≤ F.ns
    have := h.fits
    omega

/-- The weight of a form that admits its degree is one that a round admits; its number of
coefficients. -/
theorem weight_held {form : RoundForm} {z : E} {deg : Nat} {w : OnBytes.Psc.Weight}
    (h : form.weight z deg = some w) :
    w.fits = true ∧ weightHeld w = true ∧ w.d = roundValues form deg + 1 := by
  unfold RoundForm.weight at h
  by_cases hok : form.degreeOK deg = true
  · rw [if_pos hok] at h
    have hd : 2 ≤ roundValues form deg + 1 := by
      cases form <;> simp [roundValues, RoundForm.degreeOK] at hok ⊢ <;> omega
    have e : (if form.equality = true then
        OnBytes.Psc.Weight.equality z (roundValues form deg + 1)
        else OnBytes.Psc.Weight.plain (roundValues form deg + 1)) = w := Option.some.inj h
    by_cases he : form.equality = true
    · rw [if_pos he] at e
      rw [← e]
      exact ⟨(fits_equality z _).mpr hd, weightHeld_equality z _, rfl⟩
    · rw [if_neg he] at e
      rw [← e]
      exact ⟨(fits_plain _).mpr hd, weightHeld_plain _ hd, rfl⟩
  · rw [if_neg hok] at h
    cases h

/-- **One round of any form.** What it asks beyond the shape: the form admits the degree. -/
theorem roundInG {p : Psc} {F : Fork} {n : Nat} (form : RoundForm) (z : E) (deg : Nat)
    (hok : form.degreeOK deg = true) (h : Mid p F (roundValues form deg + n)) (k : Nat)
    (sent : List E) (x : E) (t : Tape) (hs : sent.length = roundValues form deg) :
    ∃ q, Fl.roundIn form p z deg F (⟨some Model.RoundName.pscRound.name, 0, k, sent, [x]⟩ :: t) =
        some ((x, q), { F with next := F.next + roundValues form deg }, t) ∧
      Mid q { F with next := F.next + roundValues form deg } n ∧ q.first = p.first := by
  obtain ⟨w, hw⟩ : ∃ w, form.weight z deg = some w := by
    unfold RoundForm.weight
    rw [if_pos hok]
    exact ⟨_, rfl⟩
  obtain ⟨hf, hh, hd⟩ := weight_held hw
  have e1 : w.d - 1 = roundValues form deg := by omega
  have hm := mid_stepG (n := n) w (by
    have := (weight_held hw).1
    unfold OnBytes.Psc.Weight.fits at this
    simp at this
    omega) (by rw [e1]; exact h) sent x
  have hr := pscRoundG p w hf hh Model.RoundName.pscRound.name 0 k sent x t F (by omega)
  rw [e1] at hm hr
  refine ⟨stepQ p w sent x, ?_, hm, stepQ_first _ _ _ _⟩
  unfold Fl.roundIn
  refine bindR (mustR (by rw [h.notEnded]; rfl) _ _) ?_
  refine bindR (needR hw _ _) ?_
  exact hr

/-- A round of a variable of a given form and degree. -/
def IsRoundOf (form : RoundForm) (deg : Nat) (x : FlatRound) : Prop :=
  x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.sent.length = roundValues form deg ∧
    x.drawn.length = 1

/-- The slots that rounds of one form take. -/
def slotsOf (form : RoundForm) (zs : List (E × Nat)) : Nat :=
  (zs.map fun z => roundValues form z.2).sum

/-- Rounds of one form in a row: the fold. -/
theorem roundsFoldR (form : RoundForm) : ∀ (zs : List (E × Nat)) (rs : List FlatRound)
    (s : Array E × Psc) (F : Fork) (n : Nat) (u : Tape), rs.length = zs.length →
    (∀ y ∈ zs.zip rs, form.degreeOK y.1.2 = true ∧ IsRoundOf form y.1.2 y.2) →
    Mid s.2 F (slotsOf form zs + n) →
    ∃ r' q G, (zs.foldlM (fun (s : Array E × Psc) z => (do
          let (r, q) ← Fl.roundIn form s.2 z.1 z.2
          pure (s.1.push r, q) : Fl (Array E × Psc))) s) F (rs ++ u) = some ((r', q), G, u) ∧
      Mid q G n ∧ q.first = s.2.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  | [], [], s, F, n, u, _, _, h => by
    have e2 : slotsOf form [] + n = n := by simp [slotsOf]
    rw [e2] at h
    exact ⟨s.1, s.2, F, rfl, h, rfl, rfl, fun _ => Iff.rfl⟩
  | [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl
  | z :: zs, x :: rs, s, F, n, u, hl, hall, h => by
    obtain ⟨hok, a1, a2, a3, a4⟩ := hall (z, x) (by simp)
    obtain ⟨nm, nz, k, sent, d⟩ := x
    have a1' : nm = some Model.RoundName.pscRound.name := a1
    have a2' : nz = 0 := a2
    have a3' : sent.length = roundValues form z.2 := a3
    have a4' : d.length = 1 := a4
    subst a1' a2'
    obtain ⟨c, rfl⟩ : ∃ c, d = [c] := by
      cases d with
      | nil => simp at a4'
      | cons c d' =>
        cases d' with
        | nil => exact ⟨c, rfl⟩
        | cons _ _ => simp at a4'
    have hlen : slotsOf form (z :: zs) + n = roundValues form z.2 + (slotsOf form zs + n) := by
      simp [slotsOf]
      omega
    rw [hlen] at h
    obtain ⟨q0, b1, b2, b3⟩ := roundInG form z.1 z.2 hok h k sent c (rs ++ u) a3'
    obtain ⟨r', q, G, c1, c2, c3, c4, c5⟩ := roundsFoldR form zs rs (s.1.push c, q0) _ n u
      (by simpa using hl) (fun y hy => hall y (by simp [hy])) b2
    refine ⟨r', q, G, ?_, c2, c3.trans b3, c4, fun j => (c5 j).trans filled_next⟩
    rw [List.cons_append, List.foldlM_cons]
    exact bindR (bindR b1 rfl) c1

/-- **Rounds of one form in a row** (OnBytes/K/Kc/FlatHear.lean: Fl.roundsIn). -/
theorem roundsInR (form : RoundForm) (p : Psc) (zs : List (E × Nat)) (rs : List FlatRound)
    (F : Fork)
    (n : Nat) (u : Tape) (hl : rs.length = zs.length)
    (hall : ∀ y ∈ zs.zip rs, form.degreeOK y.1.2 = true ∧ IsRoundOf form y.1.2 y.2)
    (h : Mid p F (slotsOf form zs + n)) :
    ∃ r' q G, Fl.roundsIn form p zs F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j :=
  roundsFoldR form zs rs (#[], p) F n u hl hall h

/-! ## The row's one theorem -/

/-- **What it is for the flat hearing functions to return**: the statements of the twenty-two
theorems named in flat_hears_return, to the letter. -/
structure FlatHearsReturn : Prop where
  claimsIn {F : Fork} {n k : Nat} (h : Room F (n + k)) (nm : Option String) (z w : Nat)
      (xs s d : List E) (t : Tape) (hx : xs.length = n) :
      ∃ G, Fl.claimsIn n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = some (F.next, G, ⟨nm, z, w, s, d⟩ :: t) ∧
        Room G k ∧ G.next = F.next + n ∧ G.ns = F.ns ∧ (∀ i, i < n → Filled G (F.next + i)) ∧
        ∀ j, j < F.next → (Filled G j ↔ Filled F j)
  batch (rows : Nat) (hr : rows ≠ 0) (x : E) (F : Fork) (t : Tape) :
      Fl.batch rows F (⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: t) =
        some (Model.powers x rows, F, t)
  point (r : Model.RoundName) (n w : Nat) (d : List E) (hd : d.length = n) (F : Fork)
      (t : Tape) : Fl.point r n F (⟨some r.name, 0, w, [], d⟩ :: t) = some (d.toArray, F, t)
  answer (r : Model.RoundName) (w : Nat) (x : E) (F : Fork) (t : Tape) :
      Fl.answer r F (⟨some r.name, 0, w, [], [x]⟩ :: t) = some (x, F, t)
  pscBegin {F : Fork} {n : Nat} (h : Room F (1 + n)) {C : Aff} {T : E}
      (hT : F.publicPart C = some T) (mu eps : E) (w : Nat) (t : Tape) :
      ∃ p, Fl.pscBegin C F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: t) =
          some (p, { F with next := F.next + 1 }, t) ∧
        Mid p { F with next := F.next + 1 } n ∧ p.first = F.next
  pscRound (p : Psc) (w : OnBytes.Psc.Weight) (hf : w.fits = true) (hh : weightHeld w = true)
      (name : String) (nz k : Nat) (sent : List E) (x : E) (t : Tape) (F : Fork)
      (hs : sent.length + 1 = w.d) :
      Fl.pscRound p w (closeOne name nz) F (⟨some name, nz, k, sent, [x]⟩ :: t) =
        some ((x, stepQ p w sent x), { F with next := F.next + (w.d - 1) }, t)
  roundIn {p : Psc} {F : Fork} {n : Nat} (form : RoundForm) (z : E) (deg : Nat)
      (hok : form.degreeOK deg = true) (h : Mid p F (roundValues form deg + n)) (k : Nat)
      (sent : List E) (x : E) (t : Tape) (hs : sent.length = roundValues form deg) :
      ∃ q, Fl.roundIn form p z deg F (⟨some Model.RoundName.pscRound.name, 0, k, sent, [x]⟩ :: t) =
          some ((x, q), { F with next := F.next + roundValues form deg }, t) ∧
        Mid q { F with next := F.next + roundValues form deg } n ∧ q.first = p.first
  roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) (rs : List FlatRound) (F : Fork)
      (n : Nat) (u : Tape) (hl : rs.length = zs.length)
      (hall : ∀ y ∈ zs.zip rs, form.degreeOK y.1.2 = true ∧ IsRoundOf form y.1.2 y.2)
      (h : Mid p F (slotsOf form zs + n)) :
      ∃ r' q G, Fl.roundsIn form p zs F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  pscEnds {p : Psc} {F : Fork} {dY n k : Nat} (h : Mid p F (dY + n + k)) (h1 : 1 ≤ dY)
      (h2 : 1 ≤ n) (w w' : Nat) (sentY vals : List E) (beta : E) (t : Tape) (hs : sentY.length = dY)
      (hv : vals.length = n) :
      ∃ q G, Fl.pscEnds p dY n F (⟨some Model.RoundName.pscY.name, 1, w, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, w', vals, []⟩ :: t) =
          some ((F.next + dY, q), G, t) ∧ Ended q G (F.next + dY) n k ∧ q.first = p.first ∧
        G.ns = F.ns ∧ ∀ j, j < F.next → (Filled G j ↔ Filled F j)
  pscRow {p : Psc} {G : Fork} {e n k : Nat} (h : Ended p G e n k) (S0 : E) (kept : Aff)
      (t : Tape) :
      ∃ H, Fl.pscRow p S0 kept G t = some ((p.rowForm S0 kept, { p with rowMade := true }), H, t) ∧
        Room H k ∧ H.next = G.next ∧ H.ns = G.ns ∧ ∀ j, Filled G j → Filled H j
  levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (rs : List FlatRound)
      (r : Array E) (p : Psc) (F : Fork) (n : Nat) (u : Tape), rs.length = order.length →
      (∀ x ∈ rs, IsVar x) → (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) →
      Mid p F (2 * order.length + n) →
      ∃ r' q G, Fl.levelRounds mu rho order r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  levelIn {F : Fork} {mu k : Nat} (h : Room F (1 + (2 * mu + (2 + 2 + k)))) {C : Aff} {T : E}
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
        Room G k ∧ G.ns = F.ns ∧ ∀ j, j < F.next → Filled F j → Filled G j
  tscLoop : ∀ (zs : List E) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
      (n : Nat) (u : Tape), rs.length = zs.length → (∀ x ∈ rs, IsVar x) →
      Mid p F (2 * zs.length + n) →
      ∃ r' q G, Fl.tscLoop zs r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  tscRounds {F : Fork} {lt m : Nat} (P : Array E) (hP : lt ≤ P.size)
      (h : Room F (1 + (1 + (2 * lt + m)))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
      (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (u : Tape) :
      ∃ o G, Fl.tscRounds P lt F
          (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: (rs ++ u)) =
          some (o, G, u) ∧ Mid o.p G m ∧ o.sCl = F.next ∧ G.ns = F.ns
  tscIn {F : Fork} {lt n k : Nat} (P : Array E) (hP : lt ≤ P.size) (hn : 1 ≤ n)
      (h : Room F (1 + (1 + (2 * lt + (2 + n + k))))) (cl mu eps : E) (w0 : Nat)
        (rs : List FlatRound)
      (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
      (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = n)
      (u : Tape) :
      ∃ o G, Fl.tscIn P lt n 2 F
          (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
            (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
              ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (o, G, u) ∧
        Ended o.p G o.sEnd n k ∧ o.sCl = F.next ∧ G.ns = F.ns ∧ Filled G F.next ∧
        ∀ j, j < F.next → Filled F j → Filled G j
  shownRun (first : Nat) (G : Fork) (t : Tape) : ∀ (n : Nat),
      (∀ i, i < n → first + i < G.ns ∧ Filled G (first + i)) →
      ∃ a, Fl.shownRun first n G t = some (a, G, t)
  channelRounds : ∀ (lam : Nat) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
      (n : Nat) (u : Tape), rs.length = lam → (∀ x ∈ rs, IsVar x) → Mid p F (2 * lam + n) →
      ∃ r' q G, Fl.channelRounds lam r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  flatPoint (lt w : Nat) (d : List E) (hd : d.length = lt) (F : Fork) (t : Tape) :
      flatPoint lt F (⟨some Model.RoundName.zero.name, 0, w, [], d⟩ :: t) = some (d.toArray, F, t)
  flatSquares {F : Fork} {XL lPd lt k : Nat} (hXL : 1 ≤ XL) (PV : Array E)
      (hPV : PV.size = lt)
      (h : Room F (ledNS XL + (1 + (2 * (lPd + lt) + (2 + 2 + k))))) (sums : List E)
      (hsums : sums.length = ledNS XL) (gam mu0 eps : E) (w0 : Nat) (rs : List FlatRound)
      (hrs : rs.length = lPd + lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
      (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = 2)
      (wT : Nat) (tau : E) (u : Tape) :
      ∃ a G, flatSquares XL lPd lt PV F
          (⟨some Model.RoundName.batSigma.name, 0, ledNS XL, sums, [gam]⟩ ::
            ⟨some Model.RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
            (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
              ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
              ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)) = some (a, G, u) ∧
        Room G k ∧ G.ns = F.ns
  flatProducts {F : Fork} {XL lt k : Nat} (PV : Array E) (hPV : lt ≤ PV.size)
      (h : Room F (ledNP XL + (1 + (1 + (2 * lt + (2 + ledNO XL + k)))))) (prods : List E)
      (hprods : prods.length = ledNP XL) (om cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
      (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
      (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
      (hvals : vals.length = ledNO XL) (u : Tape) :
      ∃ a G, flatProducts XL lt PV F
          (⟨some Model.RoundName.batSigma.name, 0, ledNP XL, prods, [om]⟩ ::
            ⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
            (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
              ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (a, G, u) ∧
        Room G k ∧ G.ns = F.ns
  flatStream {F : Fork} {lt k : Nat} (zt : Array E) (hzt : lt ≤ zt.size)
      (h : Room F (1 + (1 + (2 * lt + (2 + 2 + k))))) (cl mu eps : E) (w0 : Nat)
        (rs : List FlatRound)
      (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
      (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = 2)
      (u : Tape) :
      ∃ a G, flatStream lt zt F
          (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
            (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
              ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (a, G, u) ∧
        Room G k ∧ G.ns = F.ns
  flatLogits {F : Fork} {lt lam k : Nat} (zt : Array E) (hzt : lt ≤ zt.size)
      (h : Room F (1 + (1 + (2 * lt + (2 * lam + (2 + 2 + k)))))) (cl mu eps : E) (w0 : Nat)
      (rs1 : List FlatRound) (hrs1 : rs1.length = lt) (hvar1 : ∀ x ∈ rs1, IsVar x)
      (rs2 : List FlatRound) (hrs2 : rs2.length = lam) (hvar2 : ∀ x ∈ rs2, IsVar x) (wY : Nat)
      (sentY : List E) (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
      (hvals : vals.length = 2) (u : Tape) :
      ∃ a G, flatLogits lt lam zt F
          (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
            (rs1 ++ (rs2 ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
              ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u))) = some (a, G, u) ∧
        Room G k ∧ G.ns = F.ns

/-- **THE FLAT HEARING FUNCTIONS RETURN.** -/
theorem flat_hears_return : FlatHearsReturn where
  claimsIn := claimsInR
  batch := batchR
  point := pointR
  answer := answerR
  pscBegin := pscBeginR
  pscRound := pscRoundG
  roundIn := roundInG
  roundsIn := roundsInR
  pscEnds := pscEndsR
  pscRow := pscRowR
  levelRounds := levelRoundsR
  levelIn := levelInR
  tscLoop := tscLoopR
  tscRounds := tscRoundsR
  tscIn := tscInR
  shownRun := shownRunR
  channelRounds := channelRoundsR
  flatPoint := flatPointR
  flatSquares := flatSquaresR
  flatProducts := flatProductsR
  flatStream := flatStreamR
  flatLogits := flatLogitsR

end D6.Ret

#print axioms D6.Ret.flatLogitsR
#print axioms D6.Ret.roundsInR
#print axioms D6.Ret.flat_hears_return
