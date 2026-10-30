--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns7.lean: the flat hearing functions return: the rest of the functions
once more, with "Below" and the next slot by number; and some small lemmas. Over
OnBytes/K/Kc/Returns/FlReturns4.lean and OnBytes/K/Kc/Returns/FlReturns6.lean. Statements and
proofs.

Why. The loops and routines of FlReturns2.lean to FlReturns4.lean hand back Room (an upper bound on
the next slot), while callers test the next slot to the unit; the five routines and tscRounds say
nothing there on which slots are filled; Fl.slot, Fl.owe, Fl.slots (OnBytes/K/Kc/FlatHear.lean) have
no statement there; room_fresh speaks of the empty ledger alone.

Main names:
  slotR, oweR, slotsR: the three small functions. owe_room, owe_below: entering an owed claim turns
    neither room nor marks.
  room_slots: Fork.slots n on any ledger whose next slot is 0 has Room for n.
  channelRoundsN, roundsInN: the two other loops, with the next slot by number.
  tscRounds_below, flatSquares_below, flatProducts_below, flatStream_below, flatLogits_below: each:
    returns; Room G k (tscRounds: Mid); Below F G; G.next = F.next + (the number).

Limits. As in FlReturns4.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns4
import OnBytes.K.Kc.Returns.FlReturns6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

/-! ## Three small functions -/

theorem slotR (F : Fork) (t : Tape) : Fl.slot F t = some (F.next, F, t) := rfl

theorem oweR (what : String) (F : Fork) (t : Tape) :
    Fl.owe what F t = some ((F.owe what).1, (F.owe what).2, t) := rfl

theorem slotsR (n : Nat) (F : Fork) (t : Tape) : Fl.slots n F t = some ((), F.slots n, t) := rfl

theorem owe_below (what : String) (F : Fork) : Below F (F.owe what).2 :=
  ⟨rfl, owe_sized what, Nat.le_refl _, fun _ _ => Iff.rfl⟩

theorem owe_room {F : Fork} {n : Nat} (what : String) (h : Room F n) : Room (F.owe what).2 n :=
  ⟨owe_sized what h.sized, h.fits, h.free⟩

/-- Setting up n slots on a ledger whose next slot is 0. -/
theorem room_slots (F : Fork) (h : F.next = 0) (n : Nat) : Room (F.slots n) n := by
  refine ⟨slots_sized _ n, ?_, fun j _ => ?_⟩
  · show F.next + n ≤ n
    omega
  · show ¬ ((Array.replicate n false).getD j false = true)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> simp

/-! ## The two other loops -/

theorem channelRoundsN : ∀ (lam : Nat) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
    (n : Nat) (u : Tape), rs.length = lam → (∀ x ∈ rs, IsVar x) → Mid p F (2 * lam + n) →
    ∃ r' q G, Fl.channelRounds lam r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.next = F.next + 2 * lam ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  | 0, [], r, p, F, n, u, _, _, h => by
    have e2 : 2 * 0 + n = n := by omega
    rw [e2] at h
    exact ⟨r, p, F, rfl, h, rfl, rfl, rfl, fun _ => Iff.rfl⟩
  | 0, _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ + 1, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | lam + 1, x :: rs, r, p, F, n, u, hl, hv, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (by simp))
    have hlen : 2 * (lam + 1) + n = 2 + (2 * lam + n) := by omega
    rw [hlen] at h
    obtain ⟨h1, h2⟩ := roundInR h Model.Head.half w sent c (rs ++ u) hs
    obtain ⟨r', q, G, h3, h4, h5, h6, h7, h8⟩ := channelRoundsN lam rs (r.push c) _ _ n u
      (by simpa using hl) (fun y hy => hv y (by simp [hy])) h2
    have h6' : G.next = F.next + 2 + 2 * lam := h6
    refine ⟨r', q, G, ?_, h4, h5.trans (stepQ_first _ _ _ _), by omega, h7,
      fun j => (h8 j).trans filled_next⟩
    rw [List.cons_append]
    unfold Fl.channelRounds
    exact bindR h1 h3

/-! ## The functions -/

/-- A token sumcheck that its caller goes on with. -/
theorem tscRounds_below {F : Fork} {lt m : Nat} (P : Array E) (hP : lt ≤ P.size)
    (h : Room F (1 + (1 + (2 * lt + m)))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
    (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (u : Tape) :
    ∃ o G, Fl.tscRounds P lt F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: (rs ++ u)) =
        some (o, G, u) ∧ Mid o.p G m ∧ Below F G ∧ o.sCl = F.next ∧ Filled G F.next ∧
      o.p.first = F.next + 1 ∧ G.next = F.next + (1 + (1 + 2 * lt)) := by
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
  obtain ⟨r1, p1, G1, c1, c2, c3, cN, c4, c5⟩ := tscLoopN (P.toList.take lt) rs #[] p0 _ m u
    (by rw [hrs, hzl]) hvar b2
  have cN' : G1.next = G0.next + 1 + 2 * (P.toList.take lt).length := cN
  refine ⟨{ sCl := F.next, r := r1, p := p1 }, G1, ?_, c2,
    ⟨by rw [c4]; exact a4, fun _ => c2.sized, by omega, fun j hj =>
      ((c5 j).trans filled_next).trans (a6 j hj)⟩, rfl, (c5 _).2 (filled_next.mpr f0), ?_, ?_⟩
  · unfold Fl.tscRounds
    refine bindR (mustR (by simpa using hP) _ _) ?_
    refine bindR a1 ?_
    refine bindR b1 ?_
    refine bindR c1 ?_
    rfl
  · show p1.first = F.next + 1
    rw [c3, b3, a3]
  · rw [cN', a3, hzl]
    omega

/-- The sums of limb products, the element that batches them, and the product layer. -/
theorem flatSquares_below {F : Fork} {XL lPd lt k : Nat} (hXL : 1 ≤ XL) (PV : Array E)
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
      Room G k ∧ Below F G ∧ a.1 = F.next ∧
      G.next = F.next + (ledNS XL + (1 + (2 * (lPd + lt) + (2 + 2)))) ∧
      ∀ i, i < ledNS XL → Filled G (F.next + i) := by
  have hn0 : ledNS XL ≠ 0 := by
    unfold ledNS
    omega
  have a0 := claimsInR h (some Model.RoundName.batSigma.name) 0 (ledNS XL) sums [] [gam]
    (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
      (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
        ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ ::
        ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)) hsums
  rw [List.append_nil] at a0
  obtain ⟨G0, a1, a2, a3, a4, a5, a6⟩ := a0
  obtain ⟨T, hT⟩ := publicPart_some G0
    ((List.range (ledNS XL)).foldl (fun C s => Aff.addMul C (Aff.slot (F.next + s))
      (mulE ((Model.powers gam (ledNS XL)).getD s zeroE) (powE Head.half lPd))) {}) (by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := startSlots F.next _ (List.range (ledNS XL)) {} (ledNS XL)
      (fun s hs => List.mem_range.mp hs) (by intro y hy; simp at hy) x hx
    rw [hxs]
    have := a2.fits
    exact ⟨by omega, a5 s hs⟩)
  obtain ⟨L, G, b1, b2, b3, b4, _, _, _, _⟩ := levelIn_below a2 hT
    (Array.replicate lPd Head.half ++ PV) (orderDefault (lPd + lt)) (by simp [orderDefault]) (by
      intro v hv
      have hv' : v < lPd + lt := by simpa [orderDefault] using hv
      refine ⟨hv', ?_⟩
      rw [Array.size_append, Array.size_replicate, hPV]
      omega) mu0 eps w0 rs hrs hvar wY sentY hsY beta wV vals hvals wT tau u
  have hB0 : Below F G0 := ⟨a4, fun _ => a2.sized, by omega, a6⟩
  refine ⟨(F.next, Model.powers gam (ledNS XL), L), G, ?_, b2, hB0.trans b3, rfl, by omega,
    fun i hi => (b3.same _ (by omega)).2 (a5 i hi)⟩
  unfold flatSquares
  refine bindR a1 ?_
  refine bindR (batchR (ledNS XL) hn0 gam G0 _) ?_
  refine bindR b1 ?_
  rfl

/-- The row products, the element that batches them, and the token sumcheck at the norm's point. -/
theorem flatProducts_below {F : Fork} {XL lt k : Nat} (PV : Array E) (hPV : lt ≤ PV.size)
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
      Room G k ∧ Below F G ∧ a.1 = F.next ∧
      G.next = F.next + (ledNP XL + (1 + (1 + (2 * lt + (2 + ledNO XL))))) ∧
      ∀ i, i < ledNP XL → Filled G (F.next + i) := by
  have hP0 : ledNP XL ≠ 0 := by
    unfold ledNP
    split <;> omega
  have hO1 : 1 ≤ ledNO XL := by
    unfold ledNO
    split <;> omega
  have a0 := claimsInR h (some Model.RoundName.batSigma.name) 0 (ledNP XL) prods [] [om]
    (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
      (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
        ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) hprods
  rw [List.append_nil] at a0
  obtain ⟨G0, a1, a2, a3, a4, a5, a6⟩ := a0
  obtain ⟨o, G1, b1, b2, b3, b4, b5, _, _, b8, b9, b10, b11⟩ := tscIn_below PV hPV hO1 a2 cl mu eps
    w0 rs hrs hvar wY sentY hsY beta wV vals hvals u
  obtain ⟨sh, c1⟩ := shownRunR o.sEnd G1 u (ledNO XL) (fun i hi => by
    have e2 := b4.fits
    exact ⟨by omega, b11 i hi⟩)
  obtain ⟨H, d1, d2, d3, d4, _, d6⟩ := pscRowO b2
    (Head.productsShown XL (Model.powers om (ledNP XL)) sh) {} u
  have e2 := b4.fits
  refine ⟨(F.next, Model.powers om (ledNP XL),
    { o with p := { o.p with rowMade := true },
             rowU := o.p.rowForm (Head.productsShown XL (Model.powers om (ledNP XL)) sh) {} }), H,
               ?_,
    room_row b4 b3 d2 d3 d4 d6,
    ⟨by rw [d4, b5.ns, a4], fun _ => d2, by omega, fun j hj =>
      ((d6 j (Or.inl (by omega))).trans (b5.same j (by omega))).trans (a6 j hj)⟩, rfl, by omega,
    fun i hi => (d6 _ (Or.inl (by omega))).2 ((b5.same _ (by omega)).2 (a5 i hi))⟩
  unfold flatProducts
  refine bindR a1 ?_
  refine bindR (batchR (ledNP XL) hP0 om G0 _) ?_
  refine bindR b1 ?_
  refine bindR c1 ?_
  refine bindR d1 ?_
  rfl

/-- The token sumcheck of the stream times the reciprocal. -/
theorem flatStream_below {F : Fork} {lt k : Nat} (zt : Array E) (hzt : lt ≤ zt.size)
    (h : Room F (1 + (1 + (2 * lt + (2 + 2 + k))))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
    (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
    (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = 2)
    (u : Tape) :
    ∃ a G, flatStream lt zt F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (a, G, u) ∧
      Room G k ∧ Below F G ∧ a.sCl = F.next ∧ G.next = F.next + (1 + (1 + (2 * lt + (2 + 2)))) := by
  obtain ⟨o, G1, b1, b2, b3, b4, b5, b6, _, b8, b9, b10, b11⟩ :=
    tscIn_below zt hzt (by omega) h cl mu
    eps w0 rs hrs hvar wY sentY hsY beta wV vals hvals u
  have e2 := b4.fits
  have f0 := b11 0 (by omega)
  have f1 := b11 1 (by omega)
  rw [Nat.add_zero] at f0
  obtain ⟨H, d1, d2, d3, d4, _, d6⟩ := pscRowO b2
    (mulE (G1.vp.getD o.sEnd zeroE) (G1.vp.getD (o.sEnd + 1) zeroE)) {} u
  refine ⟨{ o with p := { o.p with rowMade := true },
                   rowU := o.p.rowForm (mulE (G1.vp.getD o.sEnd zeroE)
                     (G1.vp.getD (o.sEnd + 1) zeroE)) {} }, H, ?_, room_row b4 b3 d2 d3 d4 d6,
    ⟨by rw [d4, b5.ns], fun _ => d2, by omega, fun j hj =>
      (d6 j (Or.inl (by omega))).trans (b5.same j hj)⟩, b6, by omega⟩
  unfold flatStream
  refine bindR b1 ?_
  refine bindR (shownR (by omega) f0 u) ?_
  refine bindR (shownR (by omega) f1 u) ?_
  refine bindR d1 ?_
  rfl

/-- The token sumcheck of the activations times the head's weights, with rounds over the
channels. -/
theorem flatLogits_below {F : Fork} {lt lam k : Nat} (zt : Array E) (hzt : lt ≤ zt.size)
    (h : Room F (1 + (1 + (2 * lt + (2 * lam + (2 + 2 + k)))))) (cl mu eps : E) (w0 : Nat)
    (rs1 : List FlatRound) (hrs1 : rs1.length = lt) (hvar1 : ∀ x ∈ rs1, IsVar x)
    (rs2 : List FlatRound) (hrs2 : rs2.length = lam) (hvar2 : ∀ x ∈ rs2, IsVar x) (wY : Nat)
    (sentY : List E) (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E)
    (hvals : vals.length = 2) (u : Tape) :
    ∃ a G, flatLogits lt lam zt F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs1 ++ (rs2 ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u))) = some (a, G, u) ∧
      Room G k ∧ Below F G ∧ a.1.sCl = F.next ∧
      G.next = F.next + (1 + (1 + (2 * lt + (2 * lam + (2 + 2))))) := by
  obtain ⟨o, G0, a1, a2, a3, a4, _, a6, a7⟩ := tscRounds_below zt hzt h cl mu eps w0 rs1 hrs1 hvar1
    (rs2 ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)
  obtain ⟨r1, p1, G1, c1, c2, c3, cN, c4, c5⟩ := channelRoundsN lam rs2 #[] o.p G0 (2 + 2 + k)
    (⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
      ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u) hrs2 hvar2 a2
  obtain ⟨p2, G2, d1, d2, d3, d4, d5⟩ := pscEndsR c2 (by omega) (by omega) wY wV sentY vals beta u
    hsY hvals
  have e1 := d2.next
  have e2 := d2.fits
  have e3 := d2.first
  have f0 := d2.ends 0 (by omega)
  have f1 := d2.ends 1 (by omega)
  rw [Nat.add_zero] at f0
  obtain ⟨H, g1, g2, g3, g4, _, g6⟩ := pscRowO d2.isOpen
    (mulE (G2.vp.getD (G1.next + 2) zeroE) (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} u
  have hfirst : p2.first = F.next + 1 := by rw [d3, c3, a6]
  refine ⟨({ o with sEnd := G1.next + 2, p := { p2 with rowMade := true },
                    rowU := p2.rowForm (mulE (G2.vp.getD (G1.next + 2) zeroE)
                      (G2.vp.getD (G1.next + 2 + 1) zeroE)) {} }, r1.reverse), H, ?_,
    room_row d2.room (by omega) g2 g3 g4 g6,
    ⟨by rw [g4, d4, c4, a3.ns], fun _ => g2, by omega, fun j hj =>
      (((g6 j (Or.inl (by omega))).trans (d5 j (by omega))).trans (c5 j)).trans (a3.same j hj)⟩,
    a4, by omega⟩
  unfold flatLogits
  refine bindR a1 ?_
  refine bindR c1 ?_
  refine bindR d1 ?_
  refine bindR (shownR (by omega) f0 u) ?_
  refine bindR (shownR (by omega) f1 u) ?_
  refine bindR g1 ?_
  rfl

/-- Rounds of one form in a row: the fold, with the next slot by number. -/
theorem roundsFoldN (form : RoundForm) : ∀ (zs : List (E × Nat)) (rs : List FlatRound)
    (s : Array E × Psc) (F : Fork) (n : Nat) (u : Tape), rs.length = zs.length →
    (∀ y ∈ zs.zip rs, form.degreeOK y.1.2 = true ∧ IsRoundOf form y.1.2 y.2) →
    Mid s.2 F (slotsOf form zs + n) →
    ∃ r' q G, (zs.foldlM (fun (s : Array E × Psc) z => (do
          let (r, q) ← Fl.roundIn form s.2 z.1 z.2
          pure (s.1.push r, q) : Fl (Array E × Psc))) s) F (rs ++ u) = some ((r', q), G, u) ∧
      Mid q G n ∧ q.first = s.2.first ∧ G.next = F.next + slotsOf form zs ∧ G.ns = F.ns ∧
      ∀ j, Filled G j ↔ Filled F j
  | [], [], s, F, n, u, _, _, h => by
    have e2 : slotsOf form [] + n = n := by simp [slotsOf]
    rw [e2] at h
    exact ⟨s.1, s.2, F, rfl, h, rfl, by simp [slotsOf], rfl, fun _ => Iff.rfl⟩
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
    have hsl : slotsOf form (z :: zs) = roundValues form z.2 + slotsOf form zs := by
      simp [slotsOf]
    have hlen : slotsOf form (z :: zs) + n = roundValues form z.2 + (slotsOf form zs + n) := by
      omega
    rw [hlen] at h
    obtain ⟨q0, b1, b2, b3⟩ := roundInG form z.1 z.2 hok h k sent c (rs ++ u) a3'
    obtain ⟨r', q, G, c1, c2, c3, cN, c4, c5⟩ := roundsFoldN form zs rs (s.1.push c, q0) _ n u
      (by simpa using hl) (fun y hy => hall y (by simp [hy])) b2
    have cN' : G.next = F.next + roundValues form z.2 + slotsOf form zs := cN
    refine ⟨r', q, G, ?_, c2, c3.trans b3, by omega, c4, fun j => (c5 j).trans filled_next⟩
    rw [List.cons_append, List.foldlM_cons]
    exact bindR (bindR b1 rfl) c1

/-- **Rounds of one form in a row**, with the next slot by number. -/
theorem roundsInN (form : RoundForm) (p : Psc) (zs : List (E × Nat)) (rs : List FlatRound)
    (F : Fork)
    (n : Nat) (u : Tape) (hl : rs.length = zs.length)
    (hall : ∀ y ∈ zs.zip rs, form.degreeOK y.1.2 = true ∧ IsRoundOf form y.1.2 y.2)
    (h : Mid p F (slotsOf form zs + n)) :
    ∃ r' q G, Fl.roundsIn form p zs F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.next = F.next + slotsOf form zs ∧ G.ns = F.ns ∧
      ∀ j, Filled G j ↔ Filled F j :=
  roundsFoldN form zs rs (#[], p) F n u hl hall h

end D6.Ret

#print axioms D6.Ret.room_slots
#print axioms D6.Ret.tscRounds_below
#print axioms D6.Ret.flatSquares_below
#print axioms D6.Ret.flatProducts_below
#print axioms D6.Ret.flatStream_below
#print axioms D6.Ret.flatLogits_below
#print axioms D6.Ret.roundsInN
