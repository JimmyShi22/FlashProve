-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/More.lean: THE LAW OF THE MASKED SUMCHECK's HONEST PART: six
bridges for callers, beside the seven statements of Honest/SumLaw/Statement.lean. Statements with
their proofs, and one definition that a statement needs.
  1  WHICH CHALLENGES THE ROUNDS BEAR, AND HOW MANY THE ROUNDS ARE: general in the part: the rounds
     of moves that were played alone bear the challenges, in order; so they are as many.
  2  From the frame's test on challenges at a sub-protocol's declared rounds (`drawsFit`,
     Honest/Frame.lean) to `drawsOk` at the call: where the declared rounds state, round by round,
     as many sampled elements as the call's entries.
  3  For a caller that makes its form by `rowForm` (Johnson/Desc/Part/MaskedSumMore.lean) and writes
     the ledger apart, or late: what that form is worth IN ANY WORLD that has the coins spent for
     the hiding polynomial under the sumcheck's own slots: no later ledger and no mask entry is
     named.
  4 For a caller that knows its summand's partial sums as a function of the challenges passed, WHERE
     THE CHALLENGES ARE AS MANY AS THE VARIABLES: from "each round's list, cut or filled to the
     variable's number of coefficients, sums to the partial sum, and its value at the challenge is
     the next one" to `SumsTo`.
  5  THE COINS THEMSELVES: `hidingCoin c i` and the readings of the two stretches' members are the
     coins that the part was handed, as elements of the library's field.
  6  WHERE EVERY VARIABLE HAS AT LEAST ONE COEFFICIENT AND THE CHALLENGES ARE AS MANY AS THE
     VARIABLES, `SumsTo` is the library's `Chain` (OnBytes/Desc/First/P1/SumCore.lean) at the
     polynomials of the job's lists, cut or filled: for a caller that holds a lemma on `Chain`.
Main names:
  `aloneFrom_drawn`, `alone_drawn`, `alone_length`: the first.
  `elems_of_fit`, `drawsOk_of_fit`: the second.
  `rowForm_worth`: **the third**: eps (S0 + kept - cf), where the summand sums from the claimed
    form's value in that world to cf.
  `sumsTo_of_vals`: the fourth.
  `coinsE_getD`, `firstRun_coin`, `hidingCoin_coin`, `endCoins_coin`: the fifth. At the indices over
    which the statements' premises run: Counts.lean of this folder.
  `polyMoves`, `sumsTo_iff_chain`: the sixth.

Limits. Those of Honest/SumLaw/Statement.lean. Nothing on soundness or on any property of a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part.MaskedSum
open OnBytes.Desc.First.P1 (Chain)
open Polynomial

variable {V W X : Type}

/-! ## 1 Which challenges the rounds bear -/

/-- **The rounds of moves that were played alone bear the challenges, in order.** -/
theorem aloneFrom_drawn {C : Type} (c : C) : ∀ (mvs : List (Move C W X)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (out : List Fmt.RoundView),
    aloneFrom c mvs t seen ds = some out → out.map (·.drawn) = ds
  | [], _, _, [], out, h => by
    have e : out = [] := (Option.some.inj h).symm
    rw [e]
    rfl
  | mv :: mvs, t, seen, d :: ds, out, h => by
    cases hs : mv.say c seen t with
    | error e =>
      simp only [aloneFrom, hs] at h
      cases h
    | ok x =>
      simp only [aloneFrom, hs, Option.map_eq_some_iff] at h
      obtain ⟨out', h', rfl⟩ := h
      rw [List.map_cons, aloneFrom_drawn c mvs _ _ ds out' h']
  | [], _, _, _ :: _, _, h => by simp [aloneFrom] at h
  | _ :: _, _, _, [], _, h => by simp [aloneFrom] at h

/-- The same of a part. -/
theorem alone_drawn (p : Part V W X) (c : p.Coins) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (out : List Fmt.RoundView) (h : alone p c t seen ds = some out) :
    out.map (·.drawn) = ds :=
  aloneFrom_drawn c p.moves t seen ds out h

/-- The rounds are as many as the challenges. -/
theorem alone_length (p : Part V W X) (c : p.Coins) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (out : List Fmt.RoundView) (h : alone p c t seen ds = some out) :
    out.length = ds.length := by
  rw [← alone_drawn p c t seen ds out h, List.length_map]

/-! ## 2 From the frame's test on challenges -/

/-- Challenges that fit declared rounds have the rounds' numbers of elements. -/
theorem elems_of_fit : ∀ (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit rs ds = true →
    ds.map (·.elems.length) = rs.map (·.entry.drawE)
  | [], [], _ => rfl
  | r :: rs, d :: ds, h => by
    have h' : (drawFit r d && drawsFit rs ds) = true := h
    rw [Bool.and_eq_true] at h'
    have h1 : d.elems.length = r.entry.drawE := by
      have := h'.1
      unfold drawFit at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1.1.1.1.1.1.1
    rw [List.map_cons, List.map_cons, h1, elems_of_fit rs ds h'.2]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- **From the frame's test on challenges to `drawsOk`.** -/
theorem drawsOk_of_fit (k : Call) (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn)
    (hr : rs.map (·.entry.drawE) = (entries k).map (·.drawE)) (h : drawsFit rs ds = true) :
    drawsOk k ds = true := by
  unfold drawsOk
  rw [elems_of_fit rs ds h, hr]
  exact beq_self_eq_true _

/-! ## 3 `rowForm` in any world -/

/-- **What `rowForm` is worth, in any world that has the coins under the own slots.** -/
theorem rowForm_worth (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff)
    (F G : Fork) (h : Heard) (S0 : E) (kept : Aff) (Wd : World GE) (cf : GE)
    (hd : drawsOk (J.callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds)
    (hh : hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots (J.callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hS : SumsTo Reading.gl (J.callAt t.input (frontOf t seen)).all
      (jobPoly J t.input (frontOf t seen) (endRun c)) [] h.r (C.value Reading.gl Wd) cf) :
    (rowForm h S0 kept).value Reading.gl Wd =
      Reading.gl.val h.eps * (Reading.gl.val S0 + kept.value Reading.gl Wd - cf) := by
  obtain ⟨_, _, hlen⟩ := heard_lenK hh
  have hval := rowForm_value Reading.gl Wd h S0 kept
  obtain ⟨d0, dv, dl, T, rfl, hv, hs, _, rfl⟩ := heard_spec hd ha hh
  have hc := claim_reads J c t seen d0 dv hs hv T _ cf hS
  have hdot : dotFrom Reading.gl (fun i => Wd.slot (F.next + i))
      (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 =
      dotFrom Reading.gl (hidingCoin c)
        (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 :=
    dotFrom_congr Reading.gl _ _ _ fun i hi => hm i (by rw [← hlen]; exact hi)
  rw [hval]
  show dotFrom Reading.gl (fun i => Wd.slot (F.next + i))
      (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).1 +
      Reading.gl.val (elemOf d0) *
        Reading.gl.val (hidingAt ((J.callAt t.input (frontOf t seen)).all.zip (dv.map elemOf))).2 *
        (Reading.gl.val T - C.value Reading.gl Wd) +
      Reading.gl.val (elemOf d0) * kept.value Reading.gl Wd -
      (Reading.gl.val (after _ _ _) - Reading.gl.val (elemOf d0) * Reading.gl.val S0) = _
  rw [hdot, hc]
  show _ = Reading.gl.val (elemOf d0) * _
  ring

/-! ## 4 From partial sums -/

/-- **From the summand's partial sums to `SumsTo`**, where the challenges are as many as the
variables (else `SumsTo` is false by its last arm). val: the partial sum behind the challenges
passed. -/
theorem sumsTo_of_vals {K : Type} [CommRing K] (ρ : Reading K) (poly : List E → List E)
    (val : List E → K) : ∀ (vs : List Var) (past rs : List E), vs.length = rs.length →
    (∀ i, i < vs.length →
      ρ.val (sumOf (vs.getD i (.plain 0))
          (padTo (vs.getD i (.plain 0)).d (poly (past ++ rs.take i)))) = val (past ++ rs.take i) ∧
        ρ.val (valueAt (padTo (vs.getD i (.plain 0)).d (poly (past ++ rs.take i)))
          (rs.getD i zeroE)) = val (past ++ rs.take (i + 1))) →
    SumsTo ρ vs poly past rs (val past) (val (past ++ rs))
  | [], past, [], _, _ => by
    show val past = val (past ++ [])
    rw [List.append_nil]
  | v :: vs, past, r :: rs, hl, h => by
    obtain ⟨h1, h2⟩ := h 0 (Nat.succ_pos _)
    have e0 : past ++ (r :: rs).take 0 = past := by
      rw [List.take_zero, List.append_nil]
    have e1 : past ++ (r :: rs).take (0 + 1) = past ++ [r] := by
      show past ++ r :: rs.take 0 = _
      rw [List.take_zero]
    rw [e0] at h1 h2
    rw [e1] at h2
    refine ⟨h1, ?_⟩
    have h2' : ρ.val (valueAt (padTo v.d (poly past)) r) = val (past ++ [r]) := h2
    rw [h2']
    have e2 : past ++ r :: rs = (past ++ [r]) ++ rs := by
      rw [List.append_assoc]
      rfl
    rw [e2]
    refine sumsTo_of_vals ρ poly val vs (past ++ [r]) rs
      (by simp only [List.length_cons] at hl; omega) fun i hi => ?_
    have := h (i + 1) (by simp only [List.length_cons]; omega)
    have e3 : ∀ n, past ++ (r :: rs).take (n + 1) = (past ++ [r]) ++ rs.take n := by
      intro n
      show past ++ r :: rs.take n = _
      rw [List.append_assoc]
      rfl
    rw [e3 i, e3 (i + 1)] at this
    exact this
  | [], _, _ :: _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, [], hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega

/-! ## 5 The coins themselves -/

/-- A member of coins laid as the program's elements reads as the coin. -/
theorem coinsE_getD {d : Due} (c : Cs d) (i : Nat) (h : i < d.e) :
    Reading.gl.val ((coinsE c).getD i zeroE) = c.e ⟨i, h⟩ := by
  unfold coinsE
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
  show OnBytes.Slice.toE (E.ofTriple (OnBytes.Slice.ofE (c.e ⟨i, h⟩))).triple = _
  rw [E.triple_ofTriple, OnBytes.Slice.toE_ofE]

/-- A member of the first stretch reads as the coin. -/
theorem firstRun_coin {name endName : String} {J : SumJob W X} (c : SumCoins name endName J)
    (i : Nat) (h : i < ownRun J.shape) :
    Reading.gl.val ((firstRun c).getD i zeroE) = c.2.1.1.e ⟨i, h⟩ :=
  coinsE_getD c.2.1.1 i h

/-- **`hidingCoin c i` is the coin number lead + i of the first stretch.** -/
theorem hidingCoin_coin {name endName : String} {J : SumJob W X} (c : SumCoins name endName J)
    (i : Nat) (h : J.shape.lead + i < ownRun J.shape) :
    hidingCoin c i = c.2.1.1.e ⟨J.shape.lead + i, h⟩ :=
  firstRun_coin c (J.shape.lead + i) h

/-- A member of coins for end values, laid as the program's elements, reads as the coin. -/
theorem endCoins_coin (endName : String) (e : Ends) (c : CsAll (endRuns endName (some e))) (j : Nat)
    (h : j < e.n) :
    Reading.gl.val ((endCoins endName (some e) c).getD j zeroE) = c.1.e ⟨j, h⟩ :=
  coinsE_getD c.1 j h

/-! ## 6 `SumsTo` is the library's `Chain` -/

/-- The job's lists, cut or filled, as polynomials, with the challenges read. IT STOPS AT THE
SHORTER OF THE TWO LISTS, in silence. -/
noncomputable def polyMoves {K : Type} [Field K] (ρ : Reading K) :
    List Var → (List E → List E) → List E → List E → List (K[X] × K)
  | v :: vs, poly, past, r :: rs =>
    (polyOf ρ (padTo v.d (poly past)), ρ.val r) :: polyMoves ρ vs poly (past ++ [r]) rs
  | _, _, _, _ => []

/-- **Where every variable has at least one coefficient and the challenges are as many as the
variables, `SumsTo` is the library's `Chain` at these polynomials.** -/
theorem sumsTo_iff_chain {K : Type} [Field K] (ρ : Reading K) (poly : List E → List E) :
    ∀ (vs : List Var) (past rs : List E) (c c' : K), (∀ v ∈ vs, 1 ≤ v.d) →
      vs.length = rs.length →
      (SumsTo ρ vs poly past rs c c' ↔
        Chain (vs.map (Var.wt ρ)) (polyMoves ρ vs poly past rs) c c')
  | [], _, [], _, _, _, _ => Iff.rfl
  | v :: vs, past, r :: rs, c, c', h1, hl => by
    have hd : 1 ≤ v.d := h1 v List.mem_cons_self
    have ih := sumsTo_iff_chain ρ poly vs (past ++ [r]) rs
      (ρ.val (valueAt (padTo v.d (poly past)) r)) c'
      (fun u hu => h1 u (List.mem_cons_of_mem _ hu))
      (by simp only [List.length_cons] at hl; omega)
    show (ρ.val (sumOf v (padTo v.d (poly past))) = c ∧ SumsTo ρ vs poly (past ++ [r]) rs _ c') ↔
      ((polyOf ρ (padTo v.d (poly past))).natDegree < (v.wt ρ).d ∧
        (v.wt ρ).sum (polyOf ρ (padTo v.d (poly past))) = c ∧
        Chain (vs.map (Var.wt ρ)) (polyMoves ρ vs poly (past ++ [r]) rs)
          ((polyOf ρ (padTo v.d (poly past))).eval (ρ.val r)) c')
    rw [sumOf_val ρ v _ (padTo_length _ _), polyOf_eval, ih]
    have hdeg : (polyOf ρ (padTo v.d (poly past))).natDegree < (v.wt ρ).d := by
      have := polyOf_natDegree_lt ρ (padTo v.d (poly past)) (by rw [padTo_length]; omega)
      rw [padTo_length] at this
      rw [Var.wt_d]
      exact this
    exact ⟨fun h => ⟨hdeg, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  | [], _, _ :: _, _, _, _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, [], _, _, _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.aloneFrom_drawn
#print axioms ProofFile.Honest.SumLaw.alone_drawn
#print axioms ProofFile.Honest.SumLaw.alone_length
#print axioms ProofFile.Honest.SumLaw.elems_of_fit
#print axioms ProofFile.Honest.SumLaw.drawsOk_of_fit
#print axioms ProofFile.Honest.SumLaw.rowForm_worth
#print axioms ProofFile.Honest.SumLaw.sumsTo_of_vals
#print axioms ProofFile.Honest.SumLaw.coinsE_getD
#print axioms ProofFile.Honest.SumLaw.firstRun_coin
#print axioms ProofFile.Honest.SumLaw.hidingCoin_coin
#print axioms ProofFile.Honest.SumLaw.endCoins_coin
#print axioms ProofFile.Honest.SumLaw.sumsTo_iff_chain
#print axioms ProofFile.Honest.SumLaw.polyMoves
