-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AllItemsAt.lean: THE SECOND HALF OF THE ATTACK OF Johnson/P5J/AllFilledAt.lean: THE
SIDE OF THE RELATIONS: DOES THE MEANING OF ANY ITEM THAT IS OPEN AT ANY BORDER OF THE FIRST CHAIN
AT THE FULL SIZE FALL TO THE CLOSED MEANING BENEATH (`mgBase`), WHICH SAYS False AT FIFTEEN FIELDS
ON THAT SIDE? NO. WHAT THIS DOES NOT SAY STANDS FIRST: THAT ANY ITEM's MEANING CAN HOLD AT A STATE
AND A WITNESS: a layer's own sentence may itself be unsatisfiable: on that nothing is said here.
  `mgAll_pin_any` … `mgAll_wrow_any`: FOURTEEN FIELDS DO NOT FEEL THE MEANING BENEATH: equations
    over any two, general in the data, by unfolding: pin, pinW, constr, tie, forms, formsT, wo,
    totalB, total, row, carry, pile, pileOne, wrow.
  THE FIFTEENTH, worth, HANDS CASES DOWN (Lean refuses the like equation). For it: `worthSeg_full`
    (by the kernel: every open item worth stands at a segment below 25), `worthFilledBy_full` (the
    kernel's, Johnson/P5J/AllFilledFull.lean: at a piece and under a name that an arm of the
    lookups' layer answers), `open_worth_some` (some open item is a worth: so that "every" is not
    over nothing), `bend_worth` (a negative test: the head's number bent: false); and THE LAW THAT
    TIES THE TEST TO THE FIELD: `worth_any`: from the head: at such a segment, piece and name the
    composed meaning's worth is the same over any meaning beneath (the eleven landed
    `mgAll_worth_…` of Johnson/Desc/Sound/MgAllAt.lean, each at both).
  `k03_calls_some`, `k03_attAt_some`, `k03_attAt_none`, `k03_layAt_some`: the places that these
    eleven ask, from the head. `k3SortBy_true`, `k3SortBy_false`: what the test's sort says of the
    piece.
  `holds_any`: THE END: at every border k, at every item i of the table's own list of open items
    there, at every meaning beneath, state, strings and witness: `Item.holds N (mgAll 𝔇 mgBase) i
    a y w = Item.holds N (mgAll 𝔇 Mg) i a y w`.
Limits. "Open at border k" is membership in `(openSets fullLinks At.ps (start fullLinks))[k]?.getD
[]`, the list that the promise reads (`onQ`); the relation at a border (`relQ`) speaks through
`openAfter`: that the two name the same items is another file's (`openL_iff_openSets`,
Johnson/Desc/Sound/SpineList.lean, is near): NOT HELD HERE. The head h is a premise of `worth_any`
and `holds_any`: a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. No soundness is claimed.

-/
import Johnson.P5J.AllThereAt
import Johnson.P5J.AllFilledAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Item ModelPart openSets start worthFilledBy worthNamedBy
  k3SortBy pieceBy hdOf)
open VerifiableInference.Desc.First.Look (lookAt placeAt P digAt attAt layAt tlAt)

/-! ## 1 Fourteen fields do not feel the meaning beneath -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg Mg' : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

theorem mgAll_pin_any : (mgAll 𝔇 Mg).pin = (mgAll 𝔇 Mg').pin := rfl

theorem mgAll_pinW_any : (mgAll 𝔇 Mg).pinW = (mgAll 𝔇 Mg').pinW := rfl

theorem mgAll_constr_any : (mgAll 𝔇 Mg).constr = (mgAll 𝔇 Mg').constr := rfl

theorem mgAll_tie_any : (mgAll 𝔇 Mg).tie = (mgAll 𝔇 Mg').tie := rfl

theorem mgAll_forms_any : (mgAll 𝔇 Mg).forms = (mgAll 𝔇 Mg').forms := rfl

theorem mgAll_formsT_any : (mgAll 𝔇 Mg).formsT = (mgAll 𝔇 Mg').formsT := rfl

theorem mgAll_wo_any : (mgAll 𝔇 Mg).wo = (mgAll 𝔇 Mg').wo := rfl

theorem mgAll_totalB_any : (mgAll 𝔇 Mg).totalB = (mgAll 𝔇 Mg').totalB := rfl

theorem mgAll_total_any : (mgAll 𝔇 Mg).total = (mgAll 𝔇 Mg').total := rfl

theorem mgAll_row_any : (mgAll 𝔇 Mg).row = (mgAll 𝔇 Mg').row := rfl

theorem mgAll_carry_any : (mgAll 𝔇 Mg).carry = (mgAll 𝔇 Mg').carry := rfl

theorem mgAll_pile_any : (mgAll 𝔇 Mg).pile = (mgAll 𝔇 Mg').pile := rfl

theorem mgAll_pileOne_any : (mgAll 𝔇 Mg).pileOne = (mgAll 𝔇 Mg').pileOne := rfl

theorem mgAll_wrow_any : (mgAll 𝔇 Mg).wrow = (mgAll 𝔇 Mg').wrow := rfl

end

/-! ## 2 The closed facts on the items worth -/

/-- An item worth stands at a segment below 25. -/
def worthSegB : Item → Bool
  | .worth m _ _ => decide (m < 25)
  | _ => true

/-- Is the item a worth? -/
def isWorthB : Item → Bool
  | .worth _ _ _ => true
  | _ => false

theorem worthSeg_full :
    ((openSets fullLinks At.ps (start fullLinks)).all fun O => O.all worthSegB) = true := by
  decide +kernel

/-- Some open item is a worth: "every" is not over nothing. -/
theorem open_worth_some :
    ((openSets fullLinks At.ps (start fullLinks)).any fun O => O.any isWorthB) = true := by
  decide +kernel

/-- **A negative test**: the lookups' number of the head's segment bent. -/
theorem bend_worth : worthFilledBy 23 fullLinks At.ps = false := by decide +kernel

/-! ## 3 The places, from the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- A place of a lookup on the calls, with its shape. -/
theorem k03_calls_some (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25) :
    ∃ x, lookAt (At.X Zp) l false = some x ∧
      (P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).shape = some x.fs := by
  obtain ⟨b', hb'⟩ := k03_const_some h hl false
  obtain ⟨-, p, hp, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  unfold placeAt at hp
  obtain ⟨x', hx', -⟩ := Option.map_eq_some_iff.1 hp
  exact ⟨x', hx', shape_calls_at h.pubOne _ hx'⟩

theorem k03_attAt_some (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12) :
    ∃ x A tl, attAt (At.X Zp) (2 * g + 1) = some (x, A, tl) := by
  obtain ⟨p4, -, -, hA⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨x, hx, hs⟩ := k03_calls_some h (l := 2 * g + 1) (by omega)
  obtain ⟨a, ha, -⟩ := hA g hg
  refine ⟨{ x with fs := x.fs }, a.S, a.seam.tl, ?_⟩
  unfold attAt
  rw [if_pos ⟨p4, by omega⟩, hx, show (2 * g + 1) / 2 = g by omega, ha]
  show ((P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).shape.map fun k =>
    (({ x with fs := k } : VerifiableInference.Desc.First.Look.Place), a.S, a.seam.tl)) = _
  rw [hs]
  rfl

theorem k03_attAt_none (X : Verify.Public) (g : ℕ) : attAt X (2 * g) = none := by
  unfold attAt
  rw [if_neg (by omega)]

theorem k03_layAt_some (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {g : ℕ} (hg : g < 12) :
    ∃ x tl, layAt (At.X Zp) (2 * g) = some x ∧ tlAt (At.X Zp) (2 * g) = some tl := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨x, hx, hs⟩ := k03_calls_some h (l := 2 * g) (by omega)
  have hsub : At.links[2 * g]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨tl, ht⟩ := Option.isSome_iff_exists.1 (h.opts.tlAt (2 * g) hsub)
  refine ⟨{ x with fs := x.fs }, tl, ?_, ht⟩
  unfold layAt VerifiableInference.Desc.First.Look.stepOf
  rw [p4, ng, hx]
  have e : ((2 * g % (if true = true then 2 else 1) == 0) &&
      (2 * g != (if true = true then 2 else 1) * 12)) = true := by
    rw [if_pos rfl, Bool.and_eq_true]
    exact ⟨beq_iff_eq.2 (by omega), bne_iff_ne.2 (by omega)⟩
  rw [if_pos e]
  show ((P.ofPlace (Params.settingOf (At.X Zp).P.frame) false x).shape.map fun k =>
    ({ x with fs := k } : VerifiableInference.Desc.First.Look.Place)) = _
  rw [hs]
  rfl

/-! ## 4 The law that ties the test to the field -/

theorem k3SortBy_true {hd m pc : ℕ} (e : k3SortBy hd m pc = some true) :
    pc = pieceBy hd m true := by
  unfold k3SortBy at e
  by_cases h1 : (pc == pieceBy hd m true) = true
  · exact beq_iff_eq.1 h1
  · rw [if_neg h1] at e
    by_cases h2 : (pc == pieceBy hd m false) = true
    · rw [if_pos h2] at e
      cases e
    · rw [if_neg h2] at e
      cases e

theorem k3SortBy_false {hd m pc : ℕ} (e : k3SortBy hd m pc = some false) :
    pc = pieceBy hd m false := by
  unfold k3SortBy at e
  by_cases h1 : (pc == pieceBy hd m true) = true
  · rw [if_pos h1] at e
    cases e
  · rw [if_neg h1] at e
    by_cases h2 : (pc == pieceBy hd m false) = true
    · exact beq_iff_eq.1 h2
    · rw [if_neg h2] at e
      cases e

/-- **worth DOES NOT FEEL THE MEANING BENEATH AT A NAMED ITEM OF A SEGMENT BELOW 25.** -/
theorem worth_any (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    {m k : ℕ} {nm : String} (hm : m < 25) (hn : worthNamedBy 24 (.worth m k nm) = true)
    (a : ProofFile.InstPub × VerifiableInference.Desc.First.S) (y : Strs)
    (w : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT) :
    (mgAll h.𝔇 mgBase).worth m k nm a y w = (mgAll h.𝔇 Mg).worth m k nm a y w := by
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have ePc : ∀ d, VerifiableInference.Desc.K3.pieceAt (At.X Zp) m d = pieceBy 24 m d := by
    intro d
    show pieceBy ((if (At.X Zp).p4 then 2 else 1) * (At.X Zp).NGr) m d = _
    rw [p4, ng]
    rfl
  have hn' : (match k3SortBy 24 m k with
    | some true => nm == "planes" || nm == "keys"
    | some false => nm == "planes" || nm == "keys" || nm == "rider"
    | none => false) = true := hn
  cases hk : k3SortBy 24 m k with
  | none =>
    rw [hk] at hn'
    cases hn'
  | some dg =>
    rw [hk] at hn'
    cases dg with
    | true =>
      obtain rfl := k3SortBy_true hk
      rw [← ePc true]
      obtain ⟨x, tl, hx⟩ := k03_digAt_some h hm
      have hn2 : (nm == "planes" || nm == "keys") = true := hn'
      rcases Bool.or_eq_true_iff.1 hn2 with e | e
      · obtain rfl := beq_iff_eq.1 e
        exact (mgAll_worth_dig_planes h.𝔇 mgBase m hx a y w).trans
          (mgAll_worth_dig_planes h.𝔇 Mg m hx a y w).symm
      · obtain rfl := beq_iff_eq.1 e
        exact (mgAll_worth_dig_keys h.𝔇 mgBase m hx a y w).trans
          (mgAll_worth_dig_keys h.𝔇 Mg m hx a y w).symm
    | false =>
      obtain rfl := k3SortBy_false hk
      have hn2 : (nm == "planes" || nm == "keys" || nm == "rider") = true := hn'
      have hn3 : nm = "planes" ∨ nm = "keys" ∨ nm = "rider" := by
        rcases Bool.or_eq_true_iff.1 hn2 with e | e
        · rcases Bool.or_eq_true_iff.1 e with e | e
          · exact Or.inl (beq_iff_eq.1 e)
          · exact Or.inr (Or.inl (beq_iff_eq.1 e))
        · exact Or.inr (Or.inr (beq_iff_eq.1 e))
      by_cases e24 : m = 24
      · subst e24
        have e3 : pieceBy 24 24 false = 3 := rfl
        rw [e3, ← h24]
        rcases hn3 with rfl | rfl | rfl
        · exact (mgAll_worth_head_planes h.𝔇 mgBase h.headAt a y w).trans
            (mgAll_worth_head_planes h.𝔇 Mg h.headAt a y w).symm
        · exact (mgAll_worth_head_keys h.𝔇 mgBase h.headAt a y w).trans
            (mgAll_worth_head_keys h.𝔇 Mg h.headAt a y w).symm
        · exact (mgAll_worth_head_rider h.𝔇 mgBase h.headAt a y w).trans
            (mgAll_worth_head_rider h.𝔇 Mg h.headAt a y w).symm
      · rw [← ePc false]
        rcases Nat.even_or_odd' m with ⟨g, rfl | rfl⟩
        · obtain ⟨x, tl, hx, ht⟩ := k03_layAt_some h (g := g) (by omega)
          have hna := k03_attAt_none (At.X Zp) g
          rcases hn3 with rfl | rfl | rfl
          · exact (mgAll_worth_lay_planes h.𝔇 mgBase _ hna hx ht a y w).trans
              (mgAll_worth_lay_planes h.𝔇 Mg _ hna hx ht a y w).symm
          · exact (mgAll_worth_lay_keys h.𝔇 mgBase _ hna hx ht a y w).trans
              (mgAll_worth_lay_keys h.𝔇 Mg _ hna hx ht a y w).symm
          · exact (mgAll_worth_lay_rider h.𝔇 mgBase _ hna hx ht a y w).trans
              (mgAll_worth_lay_rider h.𝔇 Mg _ hna hx ht a y w).symm
        · obtain ⟨x, A, tl, hx⟩ := k03_attAt_some h (g := g) (by omega)
          rcases hn3 with rfl | rfl | rfl
          · exact (mgAll_worth_att_planes h.𝔇 mgBase _ hx a y w).trans
              (mgAll_worth_att_planes h.𝔇 Mg _ hx a y w).symm
          · exact (mgAll_worth_att_keys h.𝔇 mgBase _ hx a y w).trans
              (mgAll_worth_att_keys h.𝔇 Mg _ hx a y w).symm
          · exact (mgAll_worth_att_rider h.𝔇 mgBase _ hx a y w).trans
              (mgAll_worth_att_rider h.𝔇 Mg _ hx a y w).symm

/-! ## 5 The end -/

/-- **THE BASE's False IS NEVER READ ON THE RELATIONS' SIDE**: at every border, at every open item,
at every meaning beneath, state, strings and witness. -/
theorem holds_any (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    (N : VerifiableInference.Desc.First.Numbers) {k : ℕ} {i : Item}
    (hi : i ∈ (openSets fullLinks At.ps (start fullLinks))[k]?.getD [])
    (a : ProofFile.InstPub × VerifiableInference.Desc.First.S) (y : Strs)
    (w : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT) :
    Item.holds N (mgAll h.𝔇 mgBase) i a y w = Item.holds N (mgAll h.𝔇 Mg) i a y w := by
  cases i with
  | worth m pc nm =>
    cases hO : (openSets fullLinks At.ps (start fullLinks))[k]? with
    | none =>
      rw [hO] at hi
      cases hi
    | some O =>
      rw [hO] at hi
      have hi' : Item.worth m pc nm ∈ O := hi
      have hOm := List.mem_of_getElem? hO
      have h1 := List.all_eq_true.1 (List.all_eq_true.1 worthSeg_full O hOm) _ hi'
      have h2 := List.all_eq_true.1 (List.all_eq_true.1 worthFilledBy_full O hOm) _ hi'
      exact worth_any h Mg (of_decide_eq_true h1) h2 a y w
  | _ => rfl

end P5J

#print axioms P5J.mgAll_pin_any
#print axioms P5J.mgAll_pinW_any
#print axioms P5J.mgAll_constr_any
#print axioms P5J.mgAll_tie_any
#print axioms P5J.mgAll_forms_any
#print axioms P5J.mgAll_formsT_any
#print axioms P5J.mgAll_wo_any
#print axioms P5J.mgAll_totalB_any
#print axioms P5J.mgAll_total_any
#print axioms P5J.mgAll_row_any
#print axioms P5J.mgAll_carry_any
#print axioms P5J.mgAll_pile_any
#print axioms P5J.mgAll_pileOne_any
#print axioms P5J.mgAll_wrow_any
#print axioms P5J.worthSeg_full
#print axioms P5J.open_worth_some
#print axioms P5J.bend_worth
#print axioms P5J.k03_calls_some
#print axioms P5J.k03_attAt_some
#print axioms P5J.k03_attAt_none
#print axioms P5J.k03_layAt_some
#print axioms P5J.k3SortBy_true
#print axioms P5J.k3SortBy_false
#print axioms P5J.worth_any
#print axioms P5J.holds_any
