-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ReturnsAtoms.lean: conditional: "it returns", for each
routine of a lookup's hearing that reads rounds itself: a round of samples; a masked sumcheck
with end values; one that is left open; one level of a product tree. On any rounds that fit: no
honest prover is in it. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there hearing, round, entry, sample, sumcheck, level, ledger and
stretch.

What is shown.
  `readAll_ret_none`: rounds that fit the entries of a call without end values are read.
  `nz_Y`, `whole_returns`: the masked sumcheck's own text returns, and the challenge of the round
    "PSC Y" is not 0 in the hearing's own sense: from the library's test on elements that are stated
    as "never 0".
  `drawsV_returns`, `drawV_returns`: a round of samples.
  `sumV_returns`: a masked sumcheck with end values, its row made at once.
  `openV_returns`: a masked sumcheck without end values, left open.
  `level_returns`: one level of a product tree.
Helpers: `fitV_of_fits`, `vars_last`, `entries_level`, `shapeOk_level`.

Hypotheses that remain.
  `hL`: the library's promise on the ledger in front (`LedgerReady`,
    Johnson/Desc/Part/MaskedSumReady.lean).
  `hs`: the library's test on the call's public numbers (`shapeOk`,
    Johnson/Desc/Part/MaskedSum4.lean).
  `hR`: the stretch of rounds fits the call's own entries (`Str`, Honest/K3/Shape/Stretch.lean).
  `hm`: (in `level_returns` and `entries_level`) the order has the level's length.
  `h`: (in `readAll_ret_none`) the rounds fit the call's entries (`Fits`).
  `h`, `he`: (in `nz_Y`) the library's test `drawsMarkedNonzeroHaveNonzeroWords` accepts the round "PSC Y"; g is the one element
    sampled in it.
  Without a name, in front of an arrow: in `fitV_of_fits`, that the rounds fit the variables'
    entries (`Fits`); in `vars_last`, the library's sentence that the variables' rounds were read
    (`VarsRead`).

Users. Honest/K3/Shape/Returns.lean imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
No test on a value is among the hypotheses but "not all three words are 0", at one round of each
sumcheck with end values. What stands behind a return is said in Honest/K3/Shape/Walk.lean and
Honest/K3/Shape/HeardWalk.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.Stretch
import Johnson.Desc.Part.MaskedSumReady
import Johnson.Desc.Part.MaskedSumTie
import Johnson.Desc.Part.MaskedSumKeeps
import Johnson.Desc.First.Look.Via.Rounds
import Johnson.Desc.First.ProdV.LevelKit
import OnBytes.KeyPlan.LookupRoundsDecl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open OnBytes (E zeroE isZeroE)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc (drawsMarkedNonzeroHaveNonzeroWords)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends Read Heard Fits Fit FitV entries entry
  readAll varRounds firstRound roundOf shapeOk LedgerReady VarsRead Sent)
open VerifiableInference.Desc.K3 (drawsV drawV sumV openV roundsOf drawEntry)
open VerifiableInference.Desc.First.ProdV (elementsAlone level levelVars levelEnds levelEntries
  LevelOut layBack)

/-! ## Reading -/

theorem fitV_of_fits : ∀ {vs : List Var} {used : List Fmt.RoundView},
    Fits (vs.map fun v => entry "PSC round" (v.d - 1) 1 0) used → FitV vs used
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨h.1, fitV_of_fits h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **Rounds that fit the entries of a call without end values are read.** Conditional on their
fitting. No instance of these hypotheses is exhibited in this file. -/
theorem readAll_ret_none {lead : Nat} {vs : List Var} {rs : List Fmt.RoundView}
    (h : Fits (entries ⟨lead, vs, none⟩) rs) : ∃ R, readAll ⟨lead, vs, none⟩ rs = some R := by
  have h' : Fits (([entry "PSC epsilon" (lead + 1) 1 0] ++
      (vs.map fun v => entry "PSC round" (v.d - 1) 1 0)) ++ []) rs := h
  rw [List.append_nil] at h'
  obtain ⟨x0, u, e2, h0, hu⟩ := Fits.cut h'
  obtain ⟨r0, e3, f0⟩ := h0.one
  subst e3 e2
  obtain ⟨s0, b1, b2⟩ := MaskedSum.roundOf_ret f0
  obtain ⟨eps, b3⟩ := MaskedSum.one_of_length (r0.drawn.elems.map E.ofTriple)
    (by rw [List.length_map]; exact f0.2)
  obtain ⟨mu, b4⟩ := MaskedSum.one_of_length (s0.drop lead) (by rw [List.length_drop, b2]; omega)
  rw [b3] at b1
  obtain ⟨l, b5⟩ := MaskedSum.varRounds_ret vs u [] (fitV_of_fits hu)
  rw [List.append_nil] at b5
  have hfirst : firstRound ⟨lead, vs, none⟩ r0 = some (s0.take lead, [mu], [eps]) := by
    simp only [firstRound, b1, Option.map_some, b4]
  have hall : varRounds (Call.all ⟨lead, vs, none⟩) u = some (l, []) := b5
  refine ⟨⟨mu, eps, l, []⟩, ?_⟩
  show readAll ⟨lead, vs, none⟩ (r0 :: u) = _
  simp only [readAll, hfirst, hall]

/-! ## Y's challenge -/

/-- The library's test at the round "PSC Y": the one element sampled has not three words 0.
Conditional on that test and on one element being sampled. -/
theorem nz_Y {dY : Nat} {r : Fmt.RoundView} {g : E}
    (h : drawsMarkedNonzeroHaveNonzeroWords { entry := entry "PSC Y" dY 1 1 } r = true)
    (he : [g] = r.drawn.elems.map E.ofTriple) : isZeroE g = false := by
  unfold drawsMarkedNonzeroHaveNonzeroWords at h
  have hk : Fmt.kindOf (entry "PSC Y" dY 1 1).name = some .elems := OnBytes.KeyPlan.kind_y
  rw [hk] at h
  cases hel : r.drawn.elems with
  | nil => rw [hel] at he; cases he
  | cons t l =>
    rw [hel] at he h
    have hg : g = E.ofTriple t := (List.cons.inj he).1
    have h1 : (t != (0, 0, 0)) = true := by
      simpa [Fmt.dsElems, entry] using h
    subst hg
    cases hz : isZeroE (E.ofTriple t) with
    | false => rfl
    | true =>
      exfalso
      have e0 := OnBytes.Model.isZeroE_eq hz
      have e1 : t = (0, 0, 0) := by
        have := congrArg E.triple e0
        rwa [E.triple_ofTriple] at this
      rw [e1] at h1
      cases h1

/-- The last of the variables' rounds. Conditional on the library's sentence that they were read. -/
theorem vars_last (v : Var) : ∀ (vs : List Var) (used : List Fmt.RoundView) (l : List (List E × E)),
    VarsRead (vs ++ [v]) used l → ∃ u r l0 s g, used = u ++ [r] ∧ u.length = vs.length ∧
      l = l0 ++ [(s, g)] ∧ Sent r (v.d - 1) 1 s [g]
  | [], [r], [(s, g)], h => ⟨[], r, [], s, g, rfl, rfl, rfl, h.1⟩
  | [], [], _, h => h.elim
  | [], _ :: _, [], h => h.elim
  | [], _ :: _ :: _, _ :: _, h => h.2.elim
  | [], [_], _ :: _ :: _, h => h.2.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim
  | _ :: vs, r :: used, x :: l, h => by
    obtain ⟨u, r', l0, s, g, e1, e2, e3, e4⟩ := vars_last v vs used l h.2
    exact ⟨r :: u, r', x :: l0, s, g, by rw [e1]; rfl, by simp [e2], by rw [e3]; rfl, e4⟩

/-- **The masked sumcheck's own text returns, and Y's challenge is not 0.** Conditional on the
library's promise on the ledger, its test on the call and a stretch that fits. No instance of these
hypotheses is exhibited in this file. -/
theorem whole_returns {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F : Fork}
    {x : List Fmt.RoundView} (endTerm : List E → List E → E)
    (hL : LedgerReady C ⟨lead, vs, some e⟩ F) (hs : shapeOk ⟨lead, vs, some e⟩ = true)
    (hR : Str (entries ⟨lead, vs, some e⟩) x) :
    ∃ h row G, MaskedSum.whole C ⟨lead, vs, some e⟩ endTerm F x = some (h, row, G) ∧
      isZeroE (h.r.getLastD zeroE) = false := by
  obtain ⟨R, hRd, _⟩ := MaskedSum.readAll_ret hR.fits
  have hw : (MaskedSum.whole C ⟨lead, vs, some e⟩ endTerm F x).isSome :=
    (MaskedSum.whole_returns_iff hL endTerm x).2 ⟨hs, by rw [hRd]; rfl, rfl⟩
  obtain ⟨⟨h, row, G⟩, hw⟩ := Option.isSome_iff_exists.1 hw
  refine ⟨h, row, G, hw, ?_⟩
  obtain ⟨_, G1, _, _, hh, _, _⟩ := MaskedSum.whole_parts hw
  obtain ⟨_, T, R', _, hR', hEq, _⟩ := MaskedSum.hear_spec hh
  obtain rfl : R = R' := Option.some.inj (hRd.symm.trans hR')
  obtain ⟨r0, used, rv, _, ex, _, _, hV, _⟩ := MaskedSum.readAll_spec hRd
  obtain ⟨u, rY, l0, s, g, e1, e2, e3, e4⟩ := vars_last _ vs used R.rounds hV
  have hr : h.r.getLastD zeroE = g := by
    rw [hEq]
    show (R.rounds.map (·.2)).getLastD zeroE = g
    rw [e3]
    simp
  rw [hr]
  have hnz : nzAll (([entry "PSC epsilon" (lead + 1) 1 0] ++
      (vs.map fun v => entry "PSC round" (v.d - 1) 1 0)) ++
      [entry "PSC Y" e.dY 1 1, entry "PSC values" e.n 0 0]) x = true := hR.nz
  have h2 := (nzAll_split hnz).2
  have hd : x.drop ([entry "PSC epsilon" (lead + 1) 1 0] ++
      (vs.map fun v => entry "PSC round" (v.d - 1) 1 0)).length = [rY, rv] := by
    rw [ex, e1]
    have hl : ([entry "PSC epsilon" (lead + 1) 1 0] ++
        (vs.map fun v => entry "PSC round" (v.d - 1) 1 0)).length = (r0 :: u).length := by
      simp [e2]
    rw [hl]
    show (r0 :: ((u ++ [rY]) ++ [rv])).drop (r0 :: u).length = _
    have : r0 :: ((u ++ [rY]) ++ [rv]) = (r0 :: u) ++ [rY, rv] := by simp
    rw [this, List.drop_left]
  rw [hd] at h2
  have h3 : (drawsMarkedNonzeroHaveNonzeroWords { entry := entry "PSC Y" e.dY 1 1 } rY &&
      nzAll [entry "PSC values" e.n 0 0] [rv]) = true := h2
  rw [Bool.and_eq_true] at h3
  exact nz_Y h3.1 e4.2.2.2

/-! ## The routines -/

/-- A round of samples. Conditional on a stretch of one round that fits. No instance of these
hypotheses is exhibited in this file. -/
theorem drawsV_returns {name : String} {n : Nat} {F : Fork} {rs : List Fmt.RoundView}
    (hR : Str [drawEntry name n] (rs.take 1)) :
    ∃ a, drawsV n F rs = some (a, F, rs.drop 1) ∧ a.size = n := by
  obtain ⟨r, er, fr⟩ := hR.fits.one
  cases rs with
  | nil => cases er
  | cons r' rest =>
    obtain rfl : r' = r := (List.cons.inj er).1
    obtain ⟨s, b1, _⟩ := MaskedSum.roundOf_ret fr
    have ha : elementsAlone [r'] = true := hR.alone
    refine ⟨(r'.drawn.elems.map E.ofTriple).toArray, ?_, ?_⟩
    · simp only [drawsV, ha, if_true, b1, Option.map_some, List.drop_succ_cons, List.drop_zero]
    · rw [List.size_toArray, List.length_map]
      exact fr.2

theorem drawV_returns {name : String} {F : Fork} {rs : List Fmt.RoundView}
    (hR : Str [drawEntry name 1] (rs.take 1)) : ∃ a, drawV F rs = some (a, F, rs.drop 1) := by
  obtain ⟨a, e, hs⟩ := drawsV_returns (F := F) hR
  refine ⟨a.getD 0 zeroE, ?_⟩
  simp only [drawV, e, hs, beq_self_eq_true, if_true]

/-- **A masked sumcheck with end values, its row made at once.** Conditional on the same three as
`whole_returns`. No instance of these hypotheses is exhibited in this file. -/
theorem sumV_returns {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F : Fork}
    {rs : List Fmt.RoundView} (endTerm : List E → List E → E)
    (hL : LedgerReady C ⟨lead, vs, some e⟩ F) (hs : shapeOk ⟨lead, vs, some e⟩ = true)
    (hR : Str (entries ⟨lead, vs, some e⟩) (rs.take (roundsOf ⟨lead, vs, some e⟩))) :
    ∃ a G, sumV C ⟨lead, vs, some e⟩ endTerm F rs =
      some (a, G, rs.drop (roundsOf ⟨lead, vs, some e⟩)) := by
  obtain ⟨h, row, G, hw, hz⟩ := whole_returns endTerm hL hs hR
  refine ⟨(h, row), G, ?_⟩
  simp only [sumV, hR.alone, Bool.not_true, Bool.false_eq_true, if_false, hw, hz]

/-- **A masked sumcheck without end values, left open.** Conditional on the like three. No instance
of these hypotheses is exhibited in this file. -/
theorem openV_returns {C : Aff} {vs : List Var} {F : Fork} {rs : List Fmt.RoundView}
    (hL : LedgerReady C ⟨0, vs, none⟩ F) (hs : shapeOk ⟨0, vs, none⟩ = true)
    (hR : Str (entries ⟨0, vs, none⟩) (rs.take (vs.length + 1))) :
    ∃ a G, openV C vs F rs = some (a, G, rs.drop (vs.length + 1)) := by
  obtain ⟨R, hRd⟩ := readAll_ret_none hR.fits
  have hh : (MaskedSum.hear C ⟨0, vs, none⟩ F (rs.take (vs.length + 1))).isSome :=
    (MaskedSum.hear_returns_iff hL _).2 ⟨hs, by rw [hRd]; rfl⟩
  obtain ⟨⟨h, G⟩, hh⟩ := Option.isSome_iff_exists.1 hh
  refine ⟨h, G, ?_⟩
  simp only [openV, hR.alone, Bool.not_true, Bool.false_eq_true, if_false, hh, Option.map_some]

/-- A level's entries are its call's, then LINE's. Conditional on the order's length. -/
theorem entries_level {m : Nat} (z : Array E) {order : List Nat} (hm : order.length = m) :
    levelEntries m =
      entries ⟨0, levelVars m z order, some levelEnds⟩ ++ [entry "LINE" 0 1 0] := by
  subst hm
  unfold levelEntries entries levelVars
  simp [List.map_replicate, Function.comp_def, Var.d, List.map_const']

theorem shapeOk_level (m : Nat) (z : Array E) (order : List Nat) :
    shapeOk ⟨0, levelVars m z order, some levelEnds⟩ = true := by
  simp [shapeOk, levelVars, levelEnds, Var.d]

/-- **One level of a product tree.** Conditional on the library's promise on the ledger, an order of
the level's length and a stretch that fits. No instance of these hypotheses is exhibited in this
file. -/
theorem level_returns {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F : Fork}
    {rs : List Fmt.RoundView} (hL : LedgerReady C ⟨0, levelVars m z order, some levelEnds⟩ F)
    (hm : order.length = m) (hR : Str (levelEntries m) (rs.take (m + 4))) :
    ∃ o G, level m z order C F rs = some (o, G, rs.drop (m + 4)) ∧ o.r.size = m := by
  rw [entries_level z hm] at hR
  have hlen : (entries ⟨0, levelVars m z order, some levelEnds⟩).length = m + 3 := by
    simp [entries, levelVars, hm]
  obtain ⟨h1, h2⟩ := hR.split
  rw [hlen, List.take_take, Nat.min_eq_left (by omega)] at h1
  rw [hlen, List.drop_take] at h2
  obtain ⟨h, row, G, hw, hz⟩ := whole_returns
    (fun _ v => OnBytes.mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) hL (shapeOk_level m z order) h1
  have h2' : Str [entry "LINE" 0 1 0] ((rs.drop (m + 3)).take 1) := by
    have : m + 4 - (m + 3) = 1 := by omega
    rwa [this] at h2
  obtain ⟨line, el, fl⟩ := h2'.fits.one
  cases hd : rs.drop (m + 3) with
  | nil => rw [hd] at el; cases el
  | cons line' rest =>
    rw [hd] at el
    obtain rfl : line' = line := (List.cons.inj el).1
    obtain ⟨s, b1, _⟩ := MaskedSum.roundOf_ret fl
    obtain ⟨xi, b3⟩ := MaskedSum.one_of_length (line'.drawn.elems.map E.ofTriple)
      (by rw [List.length_map]; exact fl.2)
    rw [b3] at b1
    have hrest : rs.drop (m + 4) = rest := by
      have : rs.drop (m + 4) = (rs.drop (m + 3)).drop 1 := by rw [List.drop_drop]
      rw [this, hd]
      rfl
    refine ⟨⟨layBack m order (h.r.take m), h.sEnd, h.sEnd + 1, xi, row⟩, G, ?_,
      VerifiableInference.Desc.First.ProdV.layBack_size _ _ _⟩
    simp only [level, hR.alone, Bool.not_true, Bool.false_eq_true, if_false, hw, hd, b1, hz, hrest]

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.fitV_of_fits
#print axioms ProofFile.Honest.K3.Shape.readAll_ret_none
#print axioms ProofFile.Honest.K3.Shape.nz_Y
#print axioms ProofFile.Honest.K3.Shape.vars_last
#print axioms ProofFile.Honest.K3.Shape.whole_returns
#print axioms ProofFile.Honest.K3.Shape.drawsV_returns
#print axioms ProofFile.Honest.K3.Shape.drawV_returns
#print axioms ProofFile.Honest.K3.Shape.sumV_returns
#print axioms ProofFile.Honest.K3.Shape.openV_returns
#print axioms ProofFile.Honest.K3.Shape.entries_level
#print axioms ProofFile.Honest.K3.Shape.shapeOk_level
#print axioms ProofFile.Honest.K3.Shape.level_returns
