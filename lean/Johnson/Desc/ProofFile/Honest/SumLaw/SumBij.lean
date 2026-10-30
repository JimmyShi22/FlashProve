-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumBij.lean: THE COINS THAT THE MASKED SUMCHECK's PART SPENDS
AGAINST THE COINS OF THE SIMULATOR BESIDE IT: A MAP THAT IS ONE TO ONE AND ONTO, at a job, a state,
what is shown in front (`Seen`) and challenges, all fixed, under the three premises told under
Limits. Definitions that the statements need, and statements with their proofs.
Main names:
  `Spent`: the part's own coins (none) and the two stretches that it spends.
  `msgsAt`, `toSim`: the messages at such coins, as values; these values in a row, as coins of the
    simulator's.
  `tell_toSim`: at these the simulator yields what the messages show.
  `flatten_inj`, `endCoins_inj`, `toSim_inj`: the map is one to one.
  `card_cs`, `card_ends`, `card_spent`: both types have as many members.
  `toSim_bij`: **the map is one to one and onto.**

Limits. The call passes `shapeFair` (ShapeFair.lean); the variables' challenges, Y's counted, are as
many as the call's variables (the first challenge stands apart; the last round's, at a call with end
values, does not occur here); at a call with end values Y's challenge reads other than 0: premises.
No property of a protocol is stated.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Slice (GE ofE toE)
open VerifiableInference.Desc.Part.MaskedSum

variable {W X Pb : Type}

/-- The part's own coins (none) and the two stretches that it spends. -/
abbrev Spent (name endName : String) (k : Call) : Type :=
  Cs ⟨0, 0⟩ × CsAll ((name, (⟨0, ownRun k⟩ : Due)) :: endRuns endName k.ends)

/-- With what the part carries: nothing. -/
def Spent.all {name endName : String} {J : SumJob W X} (c : Spent name endName J.shape) :
    SumCoins name endName J := (c.1, c.2, ())

/-- The messages at such coins, as values. d0: the first challenge. dv: the variables', Y's last. -/
def msgsAt {name endName : String} (J : SumJob W X) (t : State W X) (seen : Seen)
    (d0 : Fmt.Drawn) (dv : List Fmt.Drawn) (c : Spent name endName J.shape) : List (List GE) :=
  sumMsgs J t.input (frontOf t seen) (elemOf d0) (dv.map elemOf)
    ((drawnE (d0 :: dv)).getLastD zeroE) (uOf c.all) (mOf c.all)

/-- These values in a row, as coins of the simulator's. -/
def toSim {name endName : String} (J : SumJob W X) (t : State W X) (seen : Seen)
    (d0 : Fmt.Drawn) (dv : List Fmt.Drawn) (c : Spent name endName J.shape) :
    Cs ⟨0, runOf J.shape⟩ :=
  ⟨fun i => i.elim0, fun i => (msgsAt J t seen d0 dv c).flatten.getD i.1 0⟩

/-- The values in a row are as many as the simulator has coins: under the first two of the head's
premises (hs, hv). -/
theorem flat_length {name endName : String} (J : SumJob W X) (t : State W X) (seen : Seen)
    (d0 : Fmt.Drawn) (dv : List Fmt.Drawn) (c : Spent name endName J.shape)
    (hs : shapeFair (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length) :
    (msgsAt J t seen d0 dv c).flatten.length = runOf J.shape := by
  rw [List.length_flatten, runOf_sum]
  unfold msgsAt
  rw [sumMsgs_lengths J _ _ _ _ _ _ _ hs (by rw [List.length_map]; exact hv)]

/-- **At these coins the simulator yields what the messages show**: under the first two of the
head's premises (hs, hv). -/
theorem tell_toSim {name endName : String} (J : SumJob W X) (t : State W X) (seen : Seen)
    (d0 : Fmt.Drawn) (dv : List Fmt.Drawn) (c : Spent name endName J.shape)
    (hs : shapeFair (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length) (a' : Addr) (pb : Pb)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks (toSim J t seen d0 dv c) =
      some ((msgsAt J t seen d0 dv c).map fun l => ⟨gotsOf l, []⟩) := by
  have hF := flat_length J t seen d0 dv c hs hv
  have h1 : coinsE (toSim J t seen d0 dv c) =
      ((msgsAt J t seen d0 dv c).map (List.map fun g => E.ofTriple (ofE g))).flatten := by
    rw [← List.map_flatten]
    unfold coinsE
    refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, hF]) ?_
    intro i h1 h2
    rw [List.length_map] at h2
    rw [List.getElem_ofFn, List.getElem_map]
    show E.ofTriple (ofE ((msgsAt J t seen d0 dv c).flatten.getD i 0)) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  have h2 : scalarsOf J.shape =
      ((msgsAt J t seen d0 dv c).map (List.map fun g => E.ofTriple (ofE g))).map List.length := by
    rw [List.map_map]
    have e : (List.length ∘ List.map fun g : GE => E.ofTriple (ofE g)) = List.length :=
      funext fun l => List.length_map _
    rw [e]
    unfold msgsAt
    rw [sumMsgs_lengths J _ _ _ _ _ _ _ hs (by rw [List.length_map]; exact hv)]
  show some ((roundsCut (scalarsOf J.shape) (coinsE (toSim J t seen d0 dv c))).map
    fun l => (⟨l.map fun x => .e x.triple, []⟩ : Shown)) = _
  rw [h1, h2, roundsCut_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  show (⟨(l.map fun g => E.ofTriple (ofE g)).map (fun x => .e x.triple), []⟩ : Shown) = _
  rw [List.map_map]
  rfl

/-- Lists of lists with the same lengths and the same members in a row are the same. -/
theorem flatten_inj {α : Type} : ∀ L L' : List (List α), L.map List.length = L'.map List.length →
    L.flatten = L'.flatten → L = L'
  | [], [], _, _ => rfl
  | l :: L, l' :: L', h, hf => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [List.flatten_cons, List.flatten_cons] at hf
    obtain ⟨e1, e2⟩ := List.append_inj hf h1
    rw [e1, flatten_inj L L' h2 e2]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

/-- Coins of the extension field alone that agree by number are the same. -/
theorem cs_ext {n : Nat} (c c' : Cs ⟨0, n⟩) (h : ∀ i, c.e i = c'.e i) : c = c' := by
  obtain ⟨f, e⟩ := c
  obtain ⟨f', e'⟩ := c'
  have h1 : f = f' := funext fun i => i.elim0
  have h2 : e = e' := funext h
  rw [h1, h2]

/-- Coins that read alike, once laid as the program's elements, are the same. -/
theorem coinsE_inj {n : Nat} (c c' : Cs ⟨0, n⟩)
    (h : ∀ j, j < n → Reading.gl.val ((coinsE c).getD j zeroE) =
      Reading.gl.val ((coinsE c').getD j zeroE)) : c = c' :=
  cs_ext c c' fun i => by
    have := h i.1 i.2
    rwa [coinsE_getD c i.1 i.2, coinsE_getD c' i.1 i.2] at this

/-- The like for the end values' coins. -/
theorem endCoins_inj (endName : String) : ∀ (o : Option Ends) (cs cs' : CsAll (endRuns endName o)),
    (∀ j, j < (o.map (·.n)).getD 0 → Reading.gl.val ((endCoins endName o cs).getD j zeroE) =
      Reading.gl.val ((endCoins endName o cs').getD j zeroE)) → cs = cs'
  | none, _, _, _ => rfl
  | some _, (c, ()), (c', ()), h => by rw [coinsE_inj c c' h]

/-- H has as many coefficients as the sumcheck has slots of its own. -/
theorem slots_all (J : SumJob W X) (w : W) (fr : Front X) :
    slots ((J.callAt w fr).all.map (toK Reading.gl)) = ownSlots J.shape.all := by
  have e1 : ((fun v : VK GE => v.2 - 1) ∘ toK Reading.gl) = fun v : Var => v.d - 1 :=
    funext fun v => by
      show (toK Reading.gl v).2 - 1 = v.d - 1
      rw [toK_snd]
  unfold slots
  rw [List.map_map, e1, ← ownSlots_one_add, ownSlots_callAt]

/-- **The map is one to one**: under the head's three premises (hs, hv, hb). -/
theorem toSim_inj {name endName : String} (J : SumJob W X) (t : State W X) (seen : Seen)
    (d0 : Fmt.Drawn) (dv : List Fmt.Drawn)
    (hs : shapeFair (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length)
    (hb : J.shape.ends.isSome = true →
      Reading.gl.val ((drawnE (d0 :: dv)).getLastD zeroE) ≠ 0) :
    Function.Injective (toSim (name := name) (endName := endName) J t seen d0 dv) := by
  intro c c' h
  have hF := flat_length J t seen d0 dv c hs hv
  have hF' := flat_length J t seen d0 dv c' hs hv
  have hflat : (msgsAt J t seen d0 dv c).flatten = (msgsAt J t seen d0 dv c').flatten := by
    refine List.ext_getElem (by rw [hF, hF']) fun i h1 h2 => ?_
    have := congrFun (congrArg Cs.e h) ⟨i, by rw [← hF]; exact h1⟩
    have e : (msgsAt J t seen d0 dv c).flatten.getD i 0 =
        (msgsAt J t seen d0 dv c').flatten.getD i 0 := this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2] at e
    exact e
  have hlen : ∀ x : Spent name endName J.shape,
      (msgsAt J t seen d0 dv x).map List.length = scalarsOf J.shape := fun x => by
    unfold msgsAt
    rw [sumMsgs_lengths J _ _ _ _ _ _ _ hs (by rw [List.length_map]; exact hv)]
  have hm := flatten_inj _ _ ((hlen c).trans (hlen c').symm) hflat
  unfold msgsAt sumMsgs at hm
  obtain ⟨hu, hmm⟩ := msgsK_inj _ _ _ _ _ _ _
    (by
      intro h0
      exact fair_all_ne hs (List.map_eq_nil_iff.1 h0))
    (fun v hv' => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv'
      rw [toK_snd]
      exact fair_all_two hs x hx)
    (by rw [List.length_map, List.length_map]; exact hv.symm)
    (fun x hx a b hab => by
      obtain ⟨e, he, rfl⟩ := Option.mem_map.1 hx
      exact mul_left_cancel₀ (hb (by rw [Option.mem_def.1 he]; rfl)) hab)
    (fun m m' hmm' => by
      have e : endList m (endsN J.shape) = endList m' (endsN J.shape) := by
        unfold endList
        refine List.map_congr_left fun j hj => ?_
        have hj' := List.mem_range.1 hj
        unfold endsN at hj'
        cases he : J.shape.ends with
        | none =>
          rw [he] at hj'
          simp at hj'
        | some e =>
          rw [he] at hj'
          rw [hmm' (e.n, _, _) (by rw [he]; rfl) j hj']
      rw [e])
    _ _ _ _ hm
  rw [slots_all] at hu
  have key : ∀ j, j < (J.shape.ends.map (·.n)).getD 0 → mOf c.all j = mOf c'.all j := by
    intro j hj
    cases he : J.shape.ends with
    | none =>
      rw [he] at hj
      simp at hj
    | some e =>
      rw [he] at hj
      exact hmm (e.n, _, _) (by rw [he]; rfl) j hj
  refine Prod.ext (cs_ext _ _ fun i => i.elim0) (Prod.ext ?_ ?_)
  · exact coinsE_inj c.2.1 c'.2.1 fun j hj => hu j hj
  · exact endCoins_inj endName J.shape.ends c.2.2 c'.2.2 key

/-! ## Both types have as many members -/

/-- Coins of the extension field alone are a function on numbers. -/
def csFun (n : Nat) : Cs ⟨0, n⟩ ≃ (Fin n → GE) where
  toFun c := c.e
  invFun v := ⟨fun i => i.elim0, v⟩
  left_inv _ := cs_ext _ _ fun _ => rfl
  right_inv _ := rfl

/-- The like for the end values' coins. -/
def endsFun (endName : String) : (o : Option Ends) →
    CsAll (endRuns endName o) ≃ (Fin ((o.map (·.n)).getD 0) → GE)
  | none =>
    { toFun := fun _ i => i.elim0, invFun := fun _ => ()
      left_inv := fun _ => rfl, right_inv := fun _ => funext fun i => i.elim0 }
  | some _ =>
    { toFun := fun c => c.1.e, invFun := fun v => (⟨fun i => i.elim0, v⟩, ())
      left_inv := fun _ => Prod.ext (cs_ext _ _ fun _ => rfl) rfl, right_inv := fun _ => rfl }

/-- Coins for a list of named counts: the first count's, and the others'. -/
def consFun (x : String × Due) (l : List (String × Due)) : CsAll (x :: l) ≃ Cs x.2 × CsAll l where
  toFun c := c
  invFun c := c
  left_inv _ := rfl
  right_inv _ := rfl

/-- So many coins of the extension field: as many members as the field has, to that power. -/
theorem card_cs (n : Nat) : Fintype.card (Cs ⟨0, n⟩) = Fintype.card GE ^ n :=
  (Fintype.card_congr (csFun n)).trans (by rw [Fintype.card_fun, Fintype.card_fin])

/-- The like for the end values' coins. -/
theorem card_ends (endName : String) (o : Option Ends) :
    Fintype.card (CsAll (endRuns endName o)) = Fintype.card GE ^ ((o.map (·.n)).getD 0) :=
  (Fintype.card_congr (endsFun endName o)).trans (by rw [Fintype.card_fun, Fintype.card_fin])

/-- **The coins that the part spends are as many as the simulator's.** -/
theorem card_spent (name endName : String) (k : Call) :
    Fintype.card (Spent name endName k) = Fintype.card (Cs ⟨0, runOf k⟩) := by
  have h1 : Fintype.card (CsAll ((name, (⟨0, ownRun k⟩ : Due)) :: endRuns endName k.ends)) =
      Fintype.card GE ^ ownRun k * Fintype.card GE ^ endsN k :=
    (Fintype.card_congr (consFun _ _)).trans (by
      rw [Fintype.card_prod, card_ends]
      exact congrArg (· * _) (card_cs (ownRun k)))
  rw [Fintype.card_prod, card_cs 0, pow_zero, one_mul, h1, ← pow_add, run_count, card_cs]

/-- **The map is one to one and onto**: under the head's three premises (hs, hv, hb). -/
theorem toSim_bij {name endName : String} (J : SumJob W X) (t : State W X) (seen : Seen)
    (d0 : Fmt.Drawn) (dv : List Fmt.Drawn)
    (hs : shapeFair (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length)
    (hb : J.shape.ends.isSome = true →
      Reading.gl.val ((drawnE (d0 :: dv)).getLastD zeroE) ≠ 0) :
    Function.Bijective (toSim (name := name) (endName := endName) J t seen d0 dv) :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨toSim_inj J t seen d0 dv hs hv hb, card_spent name endName J.shape⟩

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.flat_length
#print axioms ProofFile.Honest.SumLaw.tell_toSim
#print axioms ProofFile.Honest.SumLaw.flatten_inj
#print axioms ProofFile.Honest.SumLaw.cs_ext
#print axioms ProofFile.Honest.SumLaw.coinsE_inj
#print axioms ProofFile.Honest.SumLaw.endCoins_inj
#print axioms ProofFile.Honest.SumLaw.slots_all
#print axioms ProofFile.Honest.SumLaw.toSim_inj
#print axioms ProofFile.Honest.SumLaw.card_cs
#print axioms ProofFile.Honest.SumLaw.card_ends
#print axioms ProofFile.Honest.SumLaw.card_spent
#print axioms ProofFile.Honest.SumLaw.toSim_bij
#print axioms ProofFile.Honest.SumLaw.Spent
#print axioms ProofFile.Honest.SumLaw.Spent.all
#print axioms ProofFile.Honest.SumLaw.msgsAt
#print axioms ProofFile.Honest.SumLaw.toSim
#print axioms ProofFile.Honest.SumLaw.csFun
#print axioms ProofFile.Honest.SumLaw.endsFun
#print axioms ProofFile.Honest.SumLaw.consFun
