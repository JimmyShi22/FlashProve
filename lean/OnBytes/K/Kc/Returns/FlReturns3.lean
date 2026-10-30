--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Kc/Returns/FlReturns3.lean: the flat hearing functions return, third part: four of the
output head's five routines, and the refusals. Over OnBytes/K/Kc/Returns/FlReturns.lean and
OnBytes/K/Kc/Returns/FlReturns2.lean. Statements and proofs.

A. The routines (OnBytes/K/Kc/Flat.lean, at its end): flatPointR, flatSquaresR, flatProductsR,
flatStreamR (flatLogits: OnBytes/K/Kc/Returns/FlReturns4.lean): each returns on a tape of its shape
from a ledger with room. They add no test of their own: flatSquares needs its number of sums, 2 XL -
1, to be other than 0 (Fl.batch's test), so XL >= 1. channelRoundsR: the rounds over the channels.
startSlots: the squares' start form names the slots of the sums alone.
B. The refusals: why the premises on shape and room are not idle. For each premise in this list
there is a theorem: the premise is dropped, and the function refuses:
     the tape is at its end:       claimsIn_end, batch_end, point_end, answer_end, roundIn_end
     a wrong name:                 answer_name, point_name
     a wrong number of rows:       batch_rows            no rows: batch_none
     a wrong number of draws:      point_short
     too few elements sent:        claimsIn_few, roundIn_few        too many: roundIn_many
     a never-0 word that differs:  answer_nz
     no room:                      claimsIn_tight        a slot that is taken: claimsIn_filled
     the record's flags:           roundIn_ended, pscRow_twice, pscRow_unbegun
     a start form on a free slot:  pscBegin_free
     public numbers:               pscEnds_noValue (n = 0), levelIn_order, levelRounds_range,
                                   levelRounds_point, tscIn_point

Limits. Premises without a refusal theorem here: pscEnds' 1 <= degreeInY and its number of end
values; the further variable's round and the rounds of the values and of the line by name; "as many
challenges as variables" and "some variable" at pscRow; shownRun on a free slot; flatSquares' 1 <=
XL (it comes down to batch_none) and PV.size = lt (to levelRounds_point). These are not all the ways
to refuse. As in FlReturns.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.Returns.FlReturns2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Ret
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun

variable {α β : Type}

/-! ## A. The head's routines -/

/-- **The norm's point.** -/
theorem flatPointR (lt w : Nat) (d : List E) (hd : d.length = lt) (F : Fork) (t : Tape) :
    flatPoint lt F (⟨some Model.RoundName.zero.name, 0, w, [], d⟩ :: t) = some (d.toArray, F, t) :=
  pointR .zero lt w d hd F t

/-- Pushing f x onto a, for each x of b in order. (Copied from OnBytes/Model/HideLaws.lean,
foldl_push_toList, which stands over Mathlib; this file does not.) -/
theorem foldl_push_list {γ δ : Type} (f : γ → δ) (b : Array γ) (a : Array δ) :
    (b.foldl (fun l x => l.push (f x)) a).toList = a.toList ++ b.toList.map f := by
  rw [← Array.foldl_toList]
  generalize b.toList = l
  induction l generalizing a with
  | nil => simp
  | cons x l _ => simp

/-- The squares' start form names the slots of the sums alone. -/
theorem startSlots (sW : Nat) (c : Nat → E) : ∀ (l : List Nat) (C : Aff) (n : Nat),
    (∀ s ∈ l, s < n) → (∀ x ∈ C.slots.toList, ∃ s, s < n ∧ x.1 = sW + s) →
    ∀ x ∈ (l.foldl (fun C s => Aff.addMul C (Aff.slot (sW + s)) (c s)) C).slots.toList,
      ∃ s, s < n ∧ x.1 = sW + s
  | [], _, _, _, hC => hC
  | s :: l, C, n, hl, hC => by
    rw [List.foldl_cons]
    refine startSlots sW c l _ n (fun y hy => hl y (by simp [hy])) ?_
    intro x hx
    have hx' : x ∈ C.slots.toList ++
        (Aff.slot (sW + s)).slots.toList.map fun y => (y.1, mulE y.2 (c s)) := by
      have e := foldl_push_list (fun y : Nat × E => (y.1, mulE y.2 (c s)))
        (Aff.slot (sW + s)).slots C.slots
      have hx2 : x ∈ ((Aff.slot (sW + s)).slots.foldl
          (fun l y => l.push (y.1, mulE y.2 (c s))) C.slots).toList := hx
      rw [e] at hx2
      exact hx2
    rcases List.mem_append.mp hx' with h1 | h1
    · exact hC x h1
    · have h2 : x = (sW + s, mulE oneE (c s)) := by simpa [Aff.slot] using h1
      rw [h2]
      exact ⟨s, hl s (by simp), rfl⟩

/-- **The sums of limb products, the element that batches them, and the product layer.** -/
theorem flatSquaresR {F : Fork} {XL lPd lt k : Nat} (hXL : 1 ≤ XL) (PV : Array E)
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
      Room G k ∧ G.ns = F.ns := by
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
  obtain ⟨L, G, b1, b2, b3, _⟩ := levelInR a2 hT (Array.replicate lPd Head.half ++ PV)
    (orderDefault (lPd + lt)) (by simp [orderDefault]) (by
      intro v hv
      have hv' : v < lPd + lt := by simpa [orderDefault] using hv
      refine ⟨hv', ?_⟩
      rw [Array.size_append, Array.size_replicate, hPV]
      omega) mu0 eps w0 rs hrs hvar wY sentY hsY beta wV vals hvals wT tau u
  refine ⟨(F.next, Model.powers gam (ledNS XL), L), G, ?_, b2, b3.trans a4⟩
  unfold flatSquares
  refine bindR a1 ?_
  refine bindR (batchR (ledNS XL) hn0 gam G0 _) ?_
  refine bindR b1 ?_
  rfl

/-- **The row products, the element that batches them, and the token sumcheck at the norm's
point.** -/
theorem flatProductsR {F : Fork} {XL lt k : Nat} (PV : Array E) (hPV : lt ≤ PV.size)
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
      Room G k ∧ G.ns = F.ns := by
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
  obtain ⟨o, G1, b1, b2, b3, b4, _, _⟩ := tscInR PV hPV hO1 a2 cl mu eps w0 rs hrs hvar wY sentY hsY
    beta wV vals hvals u
  obtain ⟨sh, c1⟩ := shownRunR o.sEnd G1 u (ledNO XL) (fun i hi => by
    have e1 := b2.next
    have e2 := b2.fits
    exact ⟨by omega, b2.ends i hi⟩)
  obtain ⟨H, d1, d2, d3, d4, _⟩ := pscRowR b2
    (Head.productsShown XL (Model.powers om (ledNP XL)) sh) {} u
  refine ⟨(F.next, Model.powers om (ledNP XL),
    { o with p := { o.p with rowMade := true },
             rowU := o.p.rowForm (Head.productsShown XL (Model.powers om (ledNP XL)) sh) {} }), H,
               ?_, d2,
    by rw [d4, b4, a4]⟩
  unfold flatProducts
  refine bindR a1 ?_
  refine bindR (batchR (ledNP XL) hP0 om G0 _) ?_
  refine bindR b1 ?_
  refine bindR c1 ?_
  refine bindR d1 ?_
  rfl

/-- **The token sumcheck of the stream times the reciprocal.** -/
theorem flatStreamR {F : Fork} {lt k : Nat} (zt : Array E) (hzt : lt ≤ zt.size)
    (h : Room F (1 + (1 + (2 * lt + (2 + 2 + k))))) (cl mu eps : E) (w0 : Nat) (rs : List FlatRound)
    (hrs : rs.length = lt) (hvar : ∀ x ∈ rs, IsVar x) (wY : Nat) (sentY : List E)
    (hsY : sentY.length = 2) (beta : E) (wV : Nat) (vals : List E) (hvals : vals.length = 2)
    (u : Tape) :
    ∃ a G, flatStream lt zt F
        (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu], [eps]⟩ ::
          (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, wV, vals, []⟩ :: u)) = some (a, G, u) ∧
      Room G k ∧ G.ns = F.ns := by
  obtain ⟨o, G1, b1, b2, b3, b4, _, _⟩ :=
    tscInR zt hzt (by omega) h cl mu eps w0 rs hrs hvar wY sentY
    hsY beta wV vals hvals u
  have e1 := b2.next
  have e2 := b2.fits
  have f0 := b2.ends 0 (by omega)
  have f1 := b2.ends 1 (by omega)
  rw [Nat.add_zero] at f0
  obtain ⟨H, d1, d2, d3, d4, _⟩ := pscRowR b2
    (mulE (G1.vp.getD o.sEnd zeroE) (G1.vp.getD (o.sEnd + 1) zeroE)) {} u
  refine ⟨{ o with p := { o.p with rowMade := true },
                   rowU := o.p.rowForm (mulE (G1.vp.getD o.sEnd zeroE)
                     (G1.vp.getD (o.sEnd + 1) zeroE)) {} }, H, ?_, d2, by rw [d4, b4]⟩
  unfold flatStream
  refine bindR b1 ?_
  refine bindR (shownR (by omega) f0 u) ?_
  refine bindR (shownR (by omega) f1 u) ?_
  refine bindR d1 ?_
  rfl

/-- **The rounds over the channels.** -/
theorem channelRoundsR : ∀ (lam : Nat) (rs : List FlatRound) (r : Array E) (p : Psc) (F : Fork)
    (n : Nat) (u : Tape), rs.length = lam → (∀ x ∈ rs, IsVar x) → Mid p F (2 * lam + n) →
    ∃ r' q G, Fl.channelRounds lam r p F (rs ++ u) = some ((r', q), G, u) ∧ Mid q G n ∧
      q.first = p.first ∧ G.ns = F.ns ∧ ∀ j, Filled G j ↔ Filled F j
  | 0, [], r, p, F, n, u, _, _, h => by
    have e2 : 2 * 0 + n = n := by omega
    rw [e2] at h
    exact ⟨r, p, F, rfl, h, rfl, rfl, fun _ => Iff.rfl⟩
  | 0, _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _ + 1, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | lam + 1, x :: rs, r, p, F, n, u, hl, hv, h => by
    obtain ⟨w, sent, c, rfl, hs⟩ := isVar_lit (hv x (by simp))
    have hlen : 2 * (lam + 1) + n = 2 + (2 * lam + n) := by omega
    rw [hlen] at h
    obtain ⟨h1, h2⟩ := roundInR h Model.Head.half w sent c (rs ++ u) hs
    obtain ⟨r', q, G, h3, h4, h5, h6, h7⟩ := channelRoundsR lam rs (r.push c) _ _ n u
      (by simpa using hl) (fun y hy => hv y (by simp [hy])) h2
    refine ⟨r', q, G, ?_, h4, h5.trans (stepQ_first _ _ _ _), h6,
      fun j => (h7 j).trans filled_next⟩
    rw [List.cons_append]
    unfold Fl.channelRounds
    exact bindR h1 h3

/-! ## B. The refusals -/

theorem bindN {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} (h : x F t = none) :
    (x >>= f) F t = none := by
  show Fl.andThen x f F t = none
  unfold Fl.andThen
  rw [h]

theorem mustN {b : Bool} (h : b = false) (F : Fork) (t : Tape) : Fl.must b F t = none := by
  unfold Fl.must
  rw [h]
  rfl

theorem onTapeN {g : Tape → Option (α × Tape)} {t : Tape} (h : g t = none) (F : Fork) :
    Fl.onTape g F t = none := by
  unfold Fl.onTape
  rw [h]
  rfl

theorem changeN {f : Fork → Option Fork} {F : Fork} (h : f F = none) (t : Tape) :
    Fl.change f F t = none := by
  unfold Fl.change
  rw [h]
  rfl

theorem askN {f : Fork → Option α} {F : Fork} (h : f F = none) (t : Tape) :
    Fl.ask f F t = none := by
  unfold Fl.ask
  rw [h]
  rfl

/-! ### The tape is at its end -/

theorem claimsIn_end (n : Nat) (F : Fork) : Fl.claimsIn (n + 1) F [] = none := by
  unfold Fl.claimsIn
  exact bindN (onTapeN rfl F)

theorem batch_end (rows : Nat) (F : Fork) : Fl.batch rows F [] = none := by
  refine onTapeN ?_ F
  unfold Fl.batchOn
  split <;> rfl

theorem point_end (r : Model.RoundName) (n : Nat) (F : Fork) : Fl.point r n F [] = none :=
  onTapeN rfl F

theorem answer_end (r : Model.RoundName) (F : Fork) : Fl.answer r F [] = none := onTapeN rfl F

theorem roundIn_end (p : Psc) (hp : p.ended = false) (z : E) (F : Fork) :
    Fl.roundIn .eq2 p z 0 F [] = none := by
  unfold Fl.roundIn
  refine bindR (mustR (by rw [hp]; rfl) _ _) ?_
  refine bindR (needR (a := OnBytes.Psc.Weight.equality z 3) rfl _ _) ?_
  unfold Fl.pscRound
  refine bindR (mustR (by
    rw [Bool.and_eq_true]
    exact ⟨(fits_equality z 3).mpr (by omega), weightHeld_equality z 3⟩) _ _) ?_
  exact bindN (onTapeN rfl F)

/-! ### A word of the round that differs -/

theorem answer_name (r : Model.RoundName) (nm : String) (hnm : nm ≠ r.name) (w : Nat) (x : E)
    (F : Fork) (t : Tape) : Fl.answer r F (⟨some nm, 0, w, [], [x]⟩ :: t) = none := by
  refine onTapeN ?_ F
  simp [closeOne, hnm]

theorem answer_nz (r : Model.RoundName) (z : Nat) (hz : z ≠ 0) (w : Nat) (x : E) (F : Fork)
    (t : Tape) : Fl.answer r F (⟨some r.name, z, w, [], [x]⟩ :: t) = none := by
  refine onTapeN ?_ F
  simp [closeOne, hz]

theorem point_name (r : Model.RoundName) (nm : String) (hnm : nm ≠ r.name) (n w : Nat) (d : List E)
    (F : Fork) (t : Tape) : Fl.point r n F (⟨some nm, 0, w, [], d⟩ :: t) = none := by
  refine onTapeN ?_ F
  simp [Fl.pointOn, closeN, hnm]

theorem point_short (r : Model.RoundName) (n w : Nat) (d : List E) (hd : d.length ≠ n) (F : Fork)
    (t : Tape) : Fl.point r n F (⟨some r.name, 0, w, [], d⟩ :: t) = none := by
  refine onTapeN ?_ F
  simp [Fl.pointOn, closeN, hd]

theorem batch_rows (rows w : Nat) (hw : w ≠ rows) (x : E) (F : Fork) (t : Tape) :
    Fl.batch rows F (⟨some Model.RoundName.batSigma.name, 0, w, [], [x]⟩ :: t) = none := by
  refine onTapeN ?_ F
  unfold Fl.batchOn
  split
  · simp [closeRows, hw]
  · rfl

theorem batch_none (F : Fork) (t : Tape) : Fl.batch 0 F t = none := onTapeN rfl F

/-! ### Too few elements, or too many -/

theorem recvLoop_few (nm : Option String) (z w : Nat) (d : List E) (t : Tape) :
    ∀ (xs : List E) (n : Nat) (a : Array E), xs.length < n →
    recvLoop n a (⟨nm, z, w, xs, d⟩ :: t) = none
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | [], _ + 1, _, _ => rfl
  | x :: xs, n + 1, a, h => by
    show recvLoop n (a.push x) (⟨nm, z, w, xs, d⟩ :: t) = none
    exact recvLoop_few nm z w d t xs n _ (by simpa using h)

theorem claimsIn_few (n : Nat) (nm : Option String) (z w : Nat) (xs d : List E) (t : Tape)
    (h : xs.length < n) (F : Fork) : Fl.claimsIn n F (⟨nm, z, w, xs, d⟩ :: t) = none := by
  unfold Fl.claimsIn
  exact bindN (onTapeN (recvLoop_few nm z w d t xs n _ h) F)

theorem roundIn_few (p : Psc) (hp : p.ended = false) (z : E) (w : Nat) (sent : List E) (x : E)
    (hs : sent.length < 2) (F : Fork) (t : Tape) :
    Fl.roundIn .eq2 p z 0 F (⟨some Model.RoundName.pscRound.name, 0, w, sent, [x]⟩ :: t) =
      none := by
  unfold Fl.roundIn
  refine bindR (mustR (by rw [hp]; rfl) _ _) ?_
  refine bindR (needR (a := OnBytes.Psc.Weight.equality z 3) rfl _ _) ?_
  unfold Fl.pscRound
  refine bindR (mustR (by
    rw [Bool.and_eq_true]
    exact ⟨(fits_equality z 3).mpr (by omega), weightHeld_equality z 3⟩) _ _) ?_
  exact bindN (onTapeN (recvLoop_few _ 0 w [x] t sent 2 _ hs) F)

theorem roundIn_many (p : Psc) (hp : p.ended = false) (z : E) (w : Nat) (a b c : E) (more : List E)
    (x : E) (F : Fork) (t : Tape) :
    Fl.roundIn .eq2 p z 0 F
      (⟨some Model.RoundName.pscRound.name, 0, w, a :: b :: c :: more, [x]⟩ :: t) = none := by
  unfold Fl.roundIn
  refine bindR (mustR (by rw [hp]; rfl) _ _) ?_
  refine bindR (needR (a := OnBytes.Psc.Weight.equality z 3) rfl _ _) ?_
  unfold Fl.pscRound
  refine bindR (mustR (by
    rw [Bool.and_eq_true]
    exact ⟨(fits_equality z 3).mpr (by omega), weightHeld_equality z 3⟩) _ _) ?_
  refine bindR (readR (some Model.RoundName.pscRound.name) 0 w [x] t [a, b] (c :: more) 2 rfl F) ?_
  refine bindR (mustR rfl _ _) ?_
  exact bindN (onTapeN rfl F)

/-! ### The ledger -/

/-- Beyond the last slot nothing can be put. -/
theorem hideRun_tight {F : Fork} (hF : Sized F) (first : Nat) (v : Array E) (f : E)
    (hv : 0 < v.size) (h : F.ns < first + v.size) : F.hideRun first v f = none := by
  cases hq : F.hideRun first v f with
  | none => rfl
  | some G =>
    exfalso
    have := ((hideRun_ok F G first v f hF hq).2.2.1 (v.size - 1) (by omega)).1
    omega

/-- Under a slot that is filled nothing can be put. -/
theorem hideRun_filled {F : Fork} (hF : Sized F) (first : Nat) (v : Array E) (f : E) (i : Nat)
    (hi : i < v.size) (h : Filled F (first + i)) : F.hideRun first v f = none := by
  cases hq : F.hideRun first v f with
  | none => rfl
  | some G => exact absurd h ((hideRun_ok F G first v f hF hq).2.2.1 i hi).2.1

theorem claimsIn_tight {F : Fork} (hF : Sized F) (n : Nat) (hn : 0 < n) (h : F.ns < F.next + n)
    (nm : Option String) (z w : Nat) (xs s d : List E) (t : Tape) (hx : xs.length = n) :
    Fl.claimsIn n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = none := by
  unfold Fl.claimsIn
  refine bindR (readR nm z w d t xs s n hx.symm F) ?_
  refine bindR (mustR (by show (xs.toArray.size == n) = true; simp [hx]) _ _) ?_
  refine bindR (takeSlotsR n F _) ?_
  refine bindN (changeN (hideRun_tight (sized_next hF) F.next xs.toArray oneE
    (by simpa [hx] using hn) (by
      show F.ns < F.next + xs.toArray.size
      simpa [hx] using h)) _)

theorem claimsIn_filled {F : Fork} (hF : Sized F) (n i : Nat) (hi : i < n)
    (h : Filled F (F.next + i)) (nm : Option String) (z w : Nat) (xs s d : List E) (t : Tape)
    (hx : xs.length = n) : Fl.claimsIn n F (⟨nm, z, w, xs ++ s, d⟩ :: t) = none := by
  unfold Fl.claimsIn
  refine bindR (readR nm z w d t xs s n hx.symm F) ?_
  refine bindR (mustR (by show (xs.toArray.size == n) = true; simp [hx]) _ _) ?_
  refine bindR (takeSlotsR n F _) ?_
  refine bindN (changeN (hideRun_filled (sized_next hF) F.next xs.toArray oneE i
    (by simpa [hx] using hi) (filled_next.mpr h)) _)

theorem publicLoop_inv (F : Fork) : ∀ (l : List (Nat × E)) (v t : E),
    l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some t → ∀ x ∈ l, Filled F x.1
  | [], _, _, _ => by simp
  | x :: l, v, t, h => by
    rw [List.foldlM_cons] at h
    cases hs : F.shown x.1 with
    | none =>
      rw [hs] at h
      simp at h
    | some y =>
      rw [hs] at h
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ((shown_iff F _ _).1 hs).2.1
      · exact publicLoop_inv F l _ t h z hz

/-- A start form that names a free slot: the sumcheck does not begin. -/
theorem pscBegin_free {F : Fork} {C : Aff} (x : Nat × E) (hx : x ∈ C.slots.toList)
    (hfree : ¬ Filled F x.1) (t : Tape) : Fl.pscBegin C F t = none := by
  have hp : F.publicPart C = none := by
    cases hq : F.publicPart C with
    | none => rfl
    | some T =>
      unfold Fork.publicPart at hq
      rw [← Array.foldlM_toList] at hq
      exact absurd (publicLoop_inv F _ _ _ hq x hx) hfree
  unfold Fl.pscBegin
  exact bindN (askN hp t)

/-! ### The record's flags, and public numbers -/

theorem roundIn_ended (form : RoundForm) (p : Psc) (hp : p.ended = true) (z : E) (deg : Nat)
    (F : Fork) (t : Tape) : Fl.roundIn form p z deg F t = none := by
  unfold Fl.roundIn
  exact bindN (mustN (by rw [hp]; rfl) F t)

theorem pscRow_twice (p : Psc) (hp : p.rowMade = true) (S0 : E) (kept : Aff) (F : Fork) (t : Tape) :
    Fl.pscRow p S0 kept F t = none := by
  unfold Fl.pscRow
  exact bindN (mustN (by simp [hp]) F t)

theorem pscRow_unbegun (p : Psc) (hp : p.started = false) (S0 : E) (kept : Aff) (F : Fork)
    (t : Tape) : Fl.pscRow p S0 kept F t = none := by
  unfold Fl.pscRow
  exact bindN (mustN (by simp [hp]) F t)

theorem pscEnds_noValue (p : Psc) (dY : Nat) (F : Fork) (t : Tape) :
    Fl.pscEnds p dY 0 F t = none := by
  unfold Fl.pscEnds
  exact bindN (mustN (by simp) F t)

theorem levelIn_order (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat)
    (h : order.length ≠ mu) (F : Fork) (t : Tape) : Fl.levelIn mu rho C order F t = none := by
  unfold Fl.levelIn
  exact bindN (mustN (by simpa using h) F t)

theorem levelRounds_range (mu : Nat) (rho : Array E) (v : Nat) (order : List Nat) (hv : mu ≤ v)
    (r : Array E) (p : Psc) (F : Fork) (t : Tape) :
    Fl.levelRounds mu rho (v :: order) r p F t = none := by
  unfold Fl.levelRounds
  exact bindN (mustN (by
    have : ¬ v < mu := by omega
    simp [this]) F t)

theorem levelRounds_point (mu : Nat) (rho : Array E) (v : Nat) (order : List Nat)
    (hv : rho.size ≤ mu - 1 - v) (r : Array E) (p : Psc) (F : Fork) (t : Tape) :
    Fl.levelRounds mu rho (v :: order) r p F t = none := by
  unfold Fl.levelRounds
  exact bindN (mustN (by
    have : ¬ mu - 1 - v < rho.size := by omega
    simp [this]) F t)

theorem tscIn_point (P : Array E) (lt n dY : Nat) (h : P.size < lt) (F : Fork) (t : Tape) :
    Fl.tscIn P lt n dY F t = none := by
  unfold Fl.tscIn
  refine bindN ?_
  unfold Fl.tscRounds
  exact bindN (mustN (by
    have : ¬ lt ≤ P.size := by omega
    simp [this]) F t)

end D6.Ret

#print axioms D6.Ret.flatSquaresR
#print axioms D6.Ret.flatProductsR
#print axioms D6.Ret.flatStreamR
#print axioms D6.Ret.channelRoundsR
#print axioms D6.Ret.claimsIn_tight
#print axioms D6.Ret.claimsIn_filled
#print axioms D6.Ret.pscBegin_free
#print axioms D6.Ret.roundIn_many
