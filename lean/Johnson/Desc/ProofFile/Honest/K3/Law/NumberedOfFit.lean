-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/NumberedOfFit.lean: the facts on the numbering of a course's
challenges (`Numbered R`, Honest/K3/Law/SpecLawful.lean) follow from `Fit R`. Conditional: at one
part of keys. Theorems.

Terms. Honest/K3/GLOSSARY.md ("course", "fit", "mask, mask row", "stage").

What is shown, by the file's sections.
  1. `own_at`, `r_take`: one lemma for four clauses: the first n challenges of a stage's variables,
     as the course cuts them off its own list, are those that the reader of points takes by number.
  2. `head_behind`, `key_of_fit`, `tab_of_fit`: the point behind a level is made of the level's own
     challenges and the line's sample.
  3. `zb0_of_fit`, `zb1_of_fit`: the two points that the claims on the planes read.
  4. `endCoins_len`, `masks_len`: a mask entry for each end value; without a hypothesis.
  5. `numbered_of_fit`: the main theorem.

Hypotheses that remain. `hF`: `Fit R`; `hp`: one part of keys (`R.f.parts = [v]`): a proof file's
lookup has one. In the steps: `hs`, `hk`, `hn`: (in `r_take`) the stage is one of the row's, with
the call k; n is at most the number of its variables; `hm`, `hl`: a level's number is in range;
`hj`: (in `own_at`) j lies within the cut.

Users. `LawfulSpec` (SpecLawful.lean) has three hypotheses. One of them, `Numbered R`, reads no
summand and no input: seven clauses on which challenge is which. Two are shown in
Honest/K3/Law/SpecNumbered.lean (what a stage reads in front of it is what the whole run's points
hold; a challenge for each variable). This file shows the other five and puts the seven together. It
is imported by Honest/K3/Law/JoinedMember.lean [not in this library], Honest/K3/Law/SpecAtSite.lean
and Honest/K3/Law/SpentFlat.lean [not in this library].

Limits. Nothing is said on summands.
Instances of the hypotheses: the courses of Honest/K3/Law/Members.lean (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecNumbered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE)
open OnBytes.Model (orderDefault)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open ProofFile.Honest.SumLaw (drawsOk varsOf ownOf endRun)

variable {W : Type}

/-! ## 1 A stage's challenges, by number -/

/-- Entry j of a stretch of challenges, as an element: what the reader by number finds at the
stretch's place in the whole list. T: what stands in front of the list. -/
theorem own_at (T ds : List Fmt.Drawn) (a b j : Nat) (hj : j < ((ds.drop a).take b).length) :
    (drawnE ((ds.drop a).take b))[j]? = some (elemAt (T ++ ds) (T.length + a + j)) := by
  have hjb : j < b := Nat.lt_of_lt_of_le hj (by rw [List.length_take]; exact Nat.min_le_left _ _)
  have h1 : ((ds.drop a).take b)[j]? = ds[a + j]? := by
    rw [List.getElem?_take_of_lt hjb, List.getElem?_drop]
  have hd : ((ds.drop a).take b)[j]? = some ((ds.drop a).take b)[j] := List.getElem?_eq_getElem hj
  have e : T.length + a + j - T.length = a + j := by omega
  unfold drawnE elemAt elemsAt
  rw [List.getElem?_map, hd, List.getElem?_append_right (by omega), e, ← h1, hd]
  show some ((((ds.drop a).take b)[j].elems.head?.map E.ofTriple).getD zeroE) =
    some ((((ds.drop a).take b)[j].elems.map E.ofTriple).headD zeroE)
  cases ((ds.drop a).take b)[j].elems <;> rfl

/-- **Conditional on `Fit R`: the first n challenges of a stage's variables are those that
`varChals` takes by number.** Instances of `Fit`: Honest/K3/Law/Members.lean (by evaluation). -/
theorem r_take (R : Course W) (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call}
    (hk : s.call R.f = some k) {n : Nat} (hn : n ≤ k.vs.length) :
    (R.r s).take n = varChals R.f R.a.base (R.t.heard ++ R.ds) s n := by
  have hlen := len_of_fit R hF s hs
  rw [shapeAt_eq R s k hk] at hlen
  have hall : k.vs.length ≤ k.all.length := by
    unfold Call.all
    cases k.ends <;> simp
  have hN : (R.call s).all.length = k.all.length := by rw [all_len, shapeAt_eq R s k hk]
  have hD := draws_len R hF hs hk
  apply List.ext_getElem?
  intro l
  by_cases hl : l < n
  · have hb : 1 + l < (R.draws s).length := by rw [hD]; omega
    have e1 : ((R.r s).take n)[l]? = some (elemAt (R.t.heard ++ R.ds)
        (R.t.heard.length + firstRound R.f s + (1 + l))) := by
      rw [List.getElem?_take_of_lt hl]
      show (((drawnE (R.draws s)).drop 1).take (R.call s).all.length)[l]? = _
      rw [List.getElem?_take_of_lt (by rw [hN]; omega), List.getElem?_drop]
      exact own_at R.t.heard R.ds (firstRound R.f s) (s.rounds R.f) (1 + l) hb
    have e2 : (varChals R.f R.a.base (R.t.heard ++ R.ds) s n)[l]? =
        some (elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base s + 1 + l)) := by
      unfold varChals
      rw [List.getElem?_map, List.getElem?_range hl]
      rfl
    rw [e1, e2]
    unfold roundAt
    rw [hF.base, Nat.add_assoc (R.a.base + firstRound R.f s) 1 l]
  · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
      List.getElem?_eq_none (by unfold varChals; rw [List.length_map, List.length_range]; omega)]

/-! ## 2 The point behind a level -/

theorem head_behind (m : Nat) (o : List Nat) (cs : List E) (xi : E) :
    (behind m o cs xi).getD 0 zeroE = xi := by
  unfold behind
  simp

theorem key_of_fit (R : Course W) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R) (m : Nat)
    (hm : m < v) : R.pts.keyPt 0 (m + 1) =
      behind m (R.f.orders 0 m) ((R.r (.key 0 m)).take m) (R.xiK 0 m) := by
  have e : R.pts.keyPt 0 (m + 1) = behind m (R.f.orders 0 m)
      (varChals R.f R.a.base (R.t.heard ++ R.ds) (.key 0 m) m)
      (elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (.keyLine 0 m))) := rfl
  have ex : R.xiK 0 m = elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (.keyLine 0 m)) := by
    show (R.pts.keyPt 0 (m + 1)).getD 0 zeroE = _
    rw [e, head_behind]
  rw [ex, r_take R hF (mem_key hp hm) (k := levelCall m) rfl (by rw [levelCall_len]), e]

theorem tab_of_fit (R : Course W) (hF : Fit R) (l : Nat) (hl : l < R.f.d) :
    R.pts.tabPt (l + 1) = behind (R.f.mu + l) (orderDefault (R.f.mu + l))
      ((R.r (.tab l)).take (R.f.mu + l)) (R.xiT l) := by
  have e : R.pts.tabPt (l + 1) = behind (R.f.mu + l) (orderDefault (R.f.mu + l))
      (varChals R.f R.a.base (R.t.heard ++ R.ds) (.tab l) (R.f.mu + l))
      (elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (.tabLine l))) := rfl
  have ex : R.xiT l = elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (.tabLine l)) := by
    show (R.pts.tabPt (l + 1)).getD 0 zeroE = _
    rw [e, head_behind]
  rw [ex, r_take R hF (mem_tabOf hl) (k := levelCall (R.f.mu + l)) rfl (by rw [levelCall_len]), e]

/-! ## 3 The two points that the claims on the planes read -/

theorem zb0_of_fit (R : Course W) (hF : Fit R) : R.zb0 = (R.r .leaves).toArray := by
  have hk : Stage.call R.f .leaves =
      some { lead := 0, vs := VerifiableInference.Desc.K3.leafVars R.f #[], ends := none } := rfl
  have hv : (VerifiableInference.Desc.K3.leafVars R.f #[]).length = R.f.mu + R.f.d := by
    simp [VerifiableInference.Desc.K3.leafVars]
  have hlen := len_of_fit R hF .leaves (mem_leaves R.f)
  rw [shapeAt_eq R .leaves _ hk] at hlen
  have hlen' : (R.r .leaves).length = R.f.mu + R.f.d := by rw [hlen]; exact hv
  have e := r_take R hF (mem_leaves R.f) hk (n := R.f.mu + R.f.d) (by rw [hv])
  rw [List.take_of_length_le (by rw [hlen'])] at e
  show (varChals R.f R.a.base (R.t.heard ++ R.ds) .leaves (R.f.mu + R.f.d)).toArray = _
  rw [e]

theorem zb1_of_fit (R : Course W) (hF : Fit R) :
    R.zb1 = ((R.r .bits).take (R.f.mu + R.f.d)).toArray := by
  have hk : Stage.call R.f .bits = some (VerifiableInference.Desc.K3.bitsCall
      (List.replicate (R.f.mu + R.f.d) zeroE)) := rfl
  have hv : (VerifiableInference.Desc.K3.bitsCall
      (List.replicate (R.f.mu + R.f.d) zeroE)).vs.length = R.f.mu + R.f.d := by
    simp [VerifiableInference.Desc.K3.bitsCall]
  show (varChals R.f R.a.base (R.t.heard ++ R.ds) .bits (R.f.mu + R.f.d)).toArray = _
  rw [r_take R hF (mem_bits R.f) hk (by rw [hv])]

/-! ## 4 A mask entry for each end value -/

theorem endCoins_len (name : String) : ∀ (o : Option Ends) (c : CsAll (endRuns name o)),
    (endCoins name o c).length = (o.map (·.n)).getD 0
  | none, _ => rfl
  | some e, c => by
    show (coinsE c.1).length = e.n
    unfold coinsE
    rw [List.length_ofFn]

theorem masks_len (R : Course W) (s : Stage) : (R.masks s).length = s.tail R.f := by
  show (endCoins _ (shapeAt R.a s).ends _).length = _
  rw [endCoins_len]
  unfold shapeAt Stage.tail
  show _ = ((((s.call R.a.face).bind (·.ends)).map (·.n)).getD 0)
  cases s.call R.a.face <;> rfl

/-! ## 5 The theorem -/

/-- **Conditional on `Fit R` and on one part of keys: a course that passes `Fit` has its challenges
numbered as `Numbered` says.** Instances of the hypotheses: the courses of
Honest/K3/Law/Members.lean (`fitC`, `fit_of`; by evaluation), whose face has one part. -/
theorem numbered_of_fit (R : Course W) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R) :
    Numbered R where
  same := fun s hs => same_of_fit R v hp hF s hs
  len := fun s hs => len_of_fit R hF s hs
  key := fun m hm => key_of_fit R v hp hF m (by rw [hp] at hm; exact hm)
  tab := fun l hl => tab_of_fit R hF l hl
  zb0 := zb0_of_fit R hF
  zb1 := zb1_of_fit R hF
  masks := fun s _ => masks_len R s

#print axioms ProofFile.Honest.K3.Law.Spec.own_at
#print axioms ProofFile.Honest.K3.Law.Spec.r_take
#print axioms ProofFile.Honest.K3.Law.Spec.key_of_fit
#print axioms ProofFile.Honest.K3.Law.Spec.tab_of_fit
#print axioms ProofFile.Honest.K3.Law.Spec.zb0_of_fit
#print axioms ProofFile.Honest.K3.Law.Spec.zb1_of_fit
#print axioms ProofFile.Honest.K3.Law.Spec.masks_len
#print axioms ProofFile.Honest.K3.Law.Spec.numbered_of_fit
#print axioms ProofFile.Honest.K3.Law.Spec.head_behind
#print axioms ProofFile.Honest.K3.Law.Spec.endCoins_len

end ProofFile.Honest.K3.Law.Spec
