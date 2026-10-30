-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/MadeFit.lean: THE PREMISES AND THE TOOLS FOR "EVERY ROW THAT A CODE
SWITCH BETWEEN TWO SEGMENTS LAYS PASSES THE SEVEN CLAUSES ON A ROW's MAKE OF THE GROUND's TEST ON A
NEW OPEN ROW" (`makeClauses`, Returns/RowFit.lean). THAT SENTENCE ITSELF IS THE END OF
`madeRows_make` (Returns/MadeRows.lean): NO THEOREM OF THIS FILE SAYS IT. Statements and proofs.

  `MakeFits`        what these clauses read beside the public premises of `SwitchRowsHold`: g and
                    the copies are members of the group; the tables have at most 63 index bits; the
                    claim's forms and the kept members' stored sample rows fit their tables
  `bits_of_size`, `place_of`   a main table's index bits, off its size; an index below the size
                    fits its place
  `place_lt`, `places_rise`   a place of the rest lies inside g's main table; the places rise
  `fit_stretchF`, `fit_stretchE`   coefficients on a stretch of the rest
  `fit_padUnits`, `fit_addKept`   the single entries at a pad's places; a form on a kept member's
                    table, carried over

Limits. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.PadsProof
import Johnson.Desc.K2.Honest.Returns.RowFit
import Johnson.Desc.K2.Honest.Returns.FormFit
import Johnson.Desc.Own.RowsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Means (tableSize)
open Johnson.Prover.Send (Rows)

/-- What the seven clauses read beside the public premises of `SwitchRowsHold`. -/
structure MakeFits (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (G : Group) : Prop where
  gIn : G.members.contains g = true
  copiesIn : ∀ o ∈ anew.toList, G.members.contains o = true
  bitsG : switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll ≤ 63
  bitsKept : ∀ s ∈ (sizesAt S old T).kept,
    ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll ≤ 63
  claimMain : Own.formFits old.c (S.codes.base.getD old.code default).logEll = true
  claimKept : ∀ f ∈ old.kept.toList, Own.formFits f.c (S.tableBits f.oracle .main) = true
  stored : ∀ o ∈ (switchKept old).toList, ∀ r ∈ (S.oracles.getD o default).sampleRows.toList,
    (∀ t ∈ r.terms.toList, t.v.pairs.length = S.tableBits o .main ∧ Own.InOrder t.v) ∧
      ∀ u ∈ r.units.toList, u.index < 2 ^ S.tableBits o .main

/-- A main table's index bits, off its size; and the table is there. -/
theorem bits_of_size {S : Statement} {o n : Nat} (h : tableSize S o .main = 2 ^ n) :
    S.tableBits o .main = n ∧ Own.tableThere S o .main = true := by
  unfold tableSize at h
  split at h
  · rename_i hh
    exact ⟨Nat.pow_right_injective (le_refl 2) h, by rw [← Own.tableThere_agrees]; exact hh⟩
  · exact absurd h.symm (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))

/-- An index below a main table's size fits its place. -/
theorem place_of {S : Statement} {G : Group} {o n : Nat} (hc : G.members.contains o = true)
    (hs : tableSize S o .main = 2 ^ n) (i : Nat) (hi : i < 2 ^ n) :
    Own.placeFits S G o .main (S.tableBits o .main) i = true := by
  obtain ⟨h1, h2⟩ := bits_of_size hs
  unfold Own.placeFits
  rw [hc, h2, h1, decide_eq_true hi]
  simp

variable {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
  {W : Left} {V : Nat → Rows} {G : Group}

/-- A place of the rest lies inside g's main table. -/
theorem place_lt (A : AtSwitch S old T g anew W V) (i : Nat)
    (hi : i < (rest (sizesAt S old T) W).length) :
    (SwitchPlaces.make S.codes T).get i <
      2 ^ (switchRowBits T .main + (S.codes.base.getD T.shape.code default).logEll) := by
  obtain ⟨_, hrow, hplace, _⟩ := SwitchPlaces.places_of_check A.check
  obtain ⟨_, _, _, c4, _⟩ := Johnson.Top.H.check_facts A.check
  have h1 := (hrow i).2
  have h2 := hplace i (Nat.lt_of_lt_of_le hi (rest_fits A))
  rw [A.restMain] at h1 h2 c4
  exact VerifiableInference.Desc.First.K2Hands.lt_pow_of _ _ _ _ _
    (Nat.lt_of_lt_of_le h1 c4) (SwitchPlaces.le_two_pow_ceilLog2' _) h2
    (SwitchPlaces.le_two_pow_ceilLog2' _)

/-- The places of the rest rise. -/
theorem places_rise (A : AtSwitch S old T g anew W V) (a n : Nat) : ∀ i j, i < j → j < n →
    (SwitchPlaces.make S.codes T).get (a + i) < (SwitchPlaces.make S.codes T).get (a + j) :=
  fun _ _ hij _ => (SwitchPlaces.places_of_check A.check).1 _ _ (by omega)

/-- **Coefficients over the base field on a stretch of the rest.** -/
theorem fit_stretchF (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {r : OnBytes.Row} (h : PartsFit S G r) (a n : Nat) (coeff : Array F) (hn : n ≤ coeff.size)
    (hfit : a + n ≤ (rest (sizesAt S old T) W).length) :
    PartsFit S G
      (switchAddRestF r g .main (switchPieces (SwitchPlaces.make S.codes T) a n) coeff) :=
  PartsFit.restF g .main coeff (fun i => (SwitchPlaces.make S.codes T).get (a + i)) n hn
    (fun i hi => place_of M.gIn (size_g A) _ (place_lt A _ (by omega))) _ _ h
    (pieces_fit _ a n (places_rise A a n))

/-- **Coefficients over the extension field, written out, on a stretch of the rest.** -/
theorem fit_stretchE (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {r : OnBytes.Row} (h : PartsFit S G r) (a : Nat) (coeff : Array E)
    (hfit : a + coeff.size ≤ (rest (sizesAt S old T) W).length) :
    PartsFit S G (switchAddRestE r g .main
      (switchPieces (SwitchPlaces.make S.codes T) a coeff.size) coeff) :=
  PartsFit.restE g .main coeff (fun i => (SwitchPlaces.make S.codes T).get (a + i))
    (fun i hi => place_of M.gIn (size_g A) _ (place_lt A _ (by omega))) _ _ h
    (pieces_fit _ a coeff.size (places_rise A a coeff.size))

/-- The single entries that carry a form's coefficients at a pad's places. -/
theorem fit_padUnits (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G) (a : Nat)
    (s : OracleShape) (o : Nat) (hs : (sizesAt S old T).kept[a]? = some s)
    (ho : anew.toList[a]? = some o) (at_ : Nat) (c : Form) :
    ∀ (l : List (PadPlace × Nat)) (r : OnBytes.Row), PartsFit S G r →
      (∀ p ∈ l, p.1 ∈ padPlaces S.codes s ∧ at_ + p.2 < (rest (sizesAt S old T) W).length) →
      PartsFit S G (l.foldl (fun r p =>
        (r.addUnit o .main p.1.index (negE (c.entry p.1.index))).addUnit g .main
          ((SwitchPlaces.make S.codes T).get (at_ + p.2)) (c.entry p.1.index)) r)
  | [], _, h, _ => h
  | p :: l, r, h, hl => by
    obtain ⟨h1, h2⟩ := hl p (List.mem_cons_self ..)
    rw [List.foldl_cons]
    refine fit_padUnits A M a s o hs ho at_ c l _ ?_ fun q hq => hl q (List.mem_cons_of_mem _ hq)
    refine (h.addUnit _ _ _ _ ?_).addUnit _ _ _ _ ?_
    · exact place_of (M.copiesIn o (List.mem_of_getElem? ho)) (size_copy A a s o hs ho) _
        (pad_inside A a s hs p.1 h1).2
    · exact place_of M.gIn (size_g A) _ (place_lt A _ h2)

/-- **A form on a kept member's table, carried over.** -/
theorem fit_addKept (A : AtSwitch S old T g anew W V) (M : MakeFits S old T g anew G)
    {Fr : SwitchFrame} (hFr : switchFrame S old T g anew = some Fr) (a : Nat) (k : KeptPlace)
    (hk : Fr.kept[a]? = some k) {r : OnBytes.Row} (h : PartsFit S G r) (c : Form)
    (hc : Own.formFits c (k.rowBits + (S.codes.base.getD old.code default).logEll) = true) :
    PartsFit S G (Fr.addKept r k c) := by
  have I := frameIs hFr
  obtain ⟨s, o, hs, ho, e1, e2, e3, _, e5, _, _⟩ := kept_at hFr a k hk
  have hsz := size_copy A a s o hs ho
  have hpf := pad_fits A a s hs
  unfold SwitchFrame.addKept switchAddKept
  rw [e2, e1, I.gIs, I.restPart, A.restMain, I.places, e3]
  refine fit_padUnits A M a s o hs ho _ c _ _ (h.addForm _ _ ?_ ?_) ?_
  · exact place_of (M.copiesIn o (List.mem_of_getElem? ho)) hsz 0 (Nat.two_pow_pos _)
  · rw [(bits_of_size hsz).1, ← e5]
    exact hc
  · intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hp
    rw [List.getElem?_zipIdx] at hi
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hi
    have hlt : i < (padPlaces S.codes s).length := (List.getElem?_eq_some_iff.1 hq).1
    exact ⟨List.mem_of_getElem? hq, by
      show _ + (0 + i) < _
      omega⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_stretchF
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fit_addKept
