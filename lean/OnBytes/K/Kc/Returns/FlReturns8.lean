--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns8.lean: the flat hearing functions return: one theorem for all, in the
stronger forms: flat_hears_return2. Over OnBytes/K/Kc/Returns/FlReturns7.lean. One structure and one
theorem; every proof lies in the files beneath.

Why. The field pscRow of FlatHearsReturn (OnBytes/K/Kc/Returns/FlReturns4.lean, which stands beside
this) asks "Ended", the ledger just behind the sumcheck's end values, and a caller that makes the
row later, behind other hearing, cannot pay that. And the loops and routines there hand back Room,
an upper bound on the next slot, where callers test the next slot to the unit; they say "what was
filled stays filled", which keeps nothing free.

`FlatHearsReturn2`: a structure of the statements, twenty-five fields. Against the twenty-two:
  pscRow: under Open alone (what Fl.pscRow asks, and no more; it names no "next"); which slots it
    fills, and that it touches no other.
  levelRounds, tscLoop, channelRounds, roundsIn: with the next slot by number.
  levelIn, tscRounds, tscIn, flatSquares, flatProducts, flatStream, flatLogits: with Below F G
    (below F.next the same slots are filled: both ways), the next slot by number, and the slots
    handed back by number with which of them are filled; tscIn leaves its sumcheck Open.
  slot, owe, slots: new: three small functions of OnBytes/K/Kc/FlatHear.lean.
  The other ten fields are the same to the letter.
Each field is the statement of the theorem named in flat_hears_return2, to the letter.

Limits. As in the head of FlReturns4.lean. tscIn's field says Open, not Ended: whoever wants Ended
takes FlatHearsReturn's field.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

/-- **What it is for the flat hearing functions to return**, in the stronger forms: the statements
of the twenty-five theorems named in flat_hears_return2, to the letter. -/
structure FlatHearsReturn2 : Prop where
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
  slot (F : Fork) (t : Tape) : Fl.slot F t = some (F.next, F, t)
  owe (what : String) (F : Fork) (t : Tape) :
      Fl.owe what F t = some ((F.owe what).1, (F.owe what).2, t)
  slots (n : Nat) (F : Fork) (t : Tape) : Fl.slots n F t = some ((), F.slots n, t)
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
        q.first = p.first ∧ G.next = F.next + slotsOf form zs ∧ G.ns = F.ns ∧
        ∀ j, Filled G j ↔ Filled F j
  pscEnds {p : Psc} {F : Fork} {dY n k : Nat} (h : Mid p F (dY + n + k)) (h1 : 1 ≤ dY)
      (h2 : 1 ≤ n) (w w' : Nat) (sentY vals : List E) (beta : E) (t : Tape) (hs : sentY.length = dY)
      (hv : vals.length = n) :
      ∃ q G, Fl.pscEnds p dY n F (⟨some Model.RoundName.pscY.name, 1, w, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, w', vals, []⟩ :: t) =
          some ((F.next + dY, q), G, t) ∧ Ended q G (F.next + dY) n k ∧ q.first = p.first ∧
        G.ns = F.ns ∧ ∀ j, j < F.next → (Filled G j ↔ Filled F j)
  pscRow {p : Psc} {G : Fork} (h : Open p G) (S0 : E) (kept : Aff) (t : Tape) :
      ∃ H, Fl.pscRow p S0 kept G t = some ((p.rowForm S0 kept, { p with rowMade := true }), H, t) ∧
        Sized H ∧ H.next = G.next ∧ H.ns = G.ns ∧
        (∀ j, p.first ≤ j → j < p.first + taken p → Filled H j) ∧
        ∀ j, (j < p.first ∨ p.first + taken p ≤ j) → (Filled H j ↔ Filled G j)
  levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (rs : List FlatRound)
      (r : Array E) (p : Psc) (F : Fork) (n : Nat) (u : Tape), rs.length = order.length →
      (∀ x ∈ rs, IsVar x) → (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) →
      Mid p F (2 * order.length + n) →
      ∃ r' q G, Fl.levelRounds mu rho order r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.next = F.next + 2 * order.length ∧ G.ns = F.ns ∧
        ∀ j, Filled G j ↔ Filled F j
  levelIn {F : Fork} {mu k : Nat} (h : Room F (1 + (2 * mu + (2 + 2 + k)))) {C : Aff}
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
        L.sL = F.next + (1 + (2 * mu + 2)) ∧ L.sR = L.sL + 1 ∧ Filled G L.sL ∧ Filled G L.sR
  tscLoop : ∀ (zs : List E) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
      (n : Nat) (u : Tape), rs.length = zs.length → (∀ x ∈ rs, IsVar x) →
      Mid p F (2 * zs.length + n) →
      ∃ r' q G, Fl.tscLoop zs r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.next = F.next + 2 * zs.length ∧ G.ns = F.ns ∧
        ∀ j, Filled G j ↔ Filled F j
  tscRounds {F : Fork} {lt m : Nat} (P : Array E) (hP : lt ≤ P.size)
      (h : Room F (1 + (1 + (2 * lt + m)))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
      (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (u : Tape) :
      ∃ o G, Fl.tscRounds P lt F
          (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ :: (rs ++ u)) =
          some (o, G, u) ∧ Mid o.p G m ∧ Below F G ∧ o.sCl = F.next ∧ Filled G F.next ∧
        o.p.first = F.next + 1 ∧ G.next = F.next + (1 + (1 + 2 * lt))
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
        Open o.p G ∧ o.p.first + taken o.p ≤ G.next ∧ Room G k ∧ Below F G ∧ o.sCl = F.next ∧
        Filled G F.next ∧ o.p.first = F.next + 1 ∧ o.sEnd = F.next + (1 + (1 + (2 * lt + 2))) ∧
        G.next = o.sEnd + n ∧ ∀ i, i < n → Filled G (o.sEnd + i)
  shownRun (first : Nat) (G : Fork) (t : Tape) : ∀ (n : Nat),
      (∀ i, i < n → first + i < G.ns ∧ Filled G (first + i)) →
      ∃ a, Fl.shownRun first n G t = some (a, G, t)
  channelRounds : ∀ (lam : Nat) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
      (n : Nat) (u : Tape), rs.length = lam → (∀ x ∈ rs, IsVar x) → Mid p F (2 * lam + n) →
      ∃ r' q G, Fl.channelRounds lam r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
        q.first = p.first ∧ G.next = F.next + 2 * lam ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
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
        Room G k ∧ Below F G ∧ a.1 = F.next ∧
        G.next = F.next + (ledNS XL + (1 + (2 * (lPd + lt) + (2 + 2)))) ∧
        ∀ i, i < ledNS XL → Filled G (F.next + i)
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
        Room G k ∧ Below F G ∧ a.1 = F.next ∧
        G.next = F.next + (ledNP XL + (1 + (1 + (2 * lt + (2 + ledNO XL))))) ∧
        ∀ i, i < ledNP XL → Filled G (F.next + i)
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
        Room G k ∧ Below F G ∧ a.sCl = F.next ∧ G.next = F.next + (1 + (1 + (2 * lt + (2 + 2))))
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
        Room G k ∧ Below F G ∧ a.1.sCl = F.next ∧
        G.next = F.next + (1 + (1 + (2 * lt + (2 * lam + (2 + 2)))))

/-- **THE FLAT HEARING FUNCTIONS RETURN**, in the stronger forms. -/
theorem flat_hears_return2 : FlatHearsReturn2 where
  claimsIn := claimsInR
  batch := batchR
  point := pointR
  answer := answerR
  slot := slotR
  owe := oweR
  slots := slotsR
  pscBegin := pscBeginR
  pscRound := pscRoundG
  roundIn := roundInG
  roundsIn := roundsInN
  pscEnds := pscEndsR
  pscRow := pscRowO
  levelRounds := levelRoundsN
  levelIn := levelIn_below
  tscLoop := tscLoopN
  tscRounds := tscRounds_below
  tscIn := tscIn_below
  shownRun := shownRunR
  channelRounds := channelRoundsN
  flatPoint := flatPointR
  flatSquares := flatSquares_below
  flatProducts := flatProducts_below
  flatStream := flatStream_below
  flatLogits := flatLogits_below

end D6.Ret

#print axioms D6.Ret.flat_hears_return2
