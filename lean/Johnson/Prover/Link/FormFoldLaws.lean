-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormFoldLaws.lean: THE FORM's HALF AT A FOLD: the description's fold and the
proximity test's part over it RETURN ok, and what they return is written out: from the test
on a view's format (roundsFit, Johnson/Desc/Block.lean), one test on the plan (foldCut) and the
record in front (FoldFront): Johnson/Prover/Link/FormFold.lean.

Main names.
  elemEntry_of, fit_one, foldCut_of   what a yes of the tests holds, unfolded.
  heard_yes     one round of elements is heard.
  rounds_yes    the rounds "FOLD round".
  foldRowFits_spent   the test on the row does not read the mark "spent as a mask".
  foldD_yes     foldD RETURNS ok, where the mask has come.
  foldE_yes, foldJ_yes, fold5_yes   the plain part; the part of Johnson/Desc/K12/Join.lean;
    THE PART OF guardedProximityTestParts.
  foldT_keeps   seven equations on the record behind.

Limits. ONE PREMISE READS ELEMENTS: FoldFront.rowFits: Own.foldRowFits calls formFits, which asks of
each vector of product form in the row's form that every written-out variable has the pair (1, 1):
an equality of elements on the row's coefficients (the head of Johnson/Desc/Own/Fold.lean says so);
these come from drawn values: it is owed for all draws, by the row's make. No other premise reads a
value that is sent or drawn. The premises are premises: that a record meets FoldFront is not shown
here. The arm in which the fold's own first message brings the mask is not served. Nothing on
soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFold
import Johnson.Desc.K12.Law.TrOnto
import Johnson.Desc.K12.Law.FitWritten
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.First.Close

/-! ## The tests, unfolded -/

theorem elemEntry_of {name : String} {items : Nat} {e : Fmt.Entry}
    (h : elemEntry name items e = true) :
    (e.name == name) = true ∧ e.drawNZ = 0 ∧ e.count = 1 ∧ e.msg = 24 * items ∧ e.roots = 0 ∧
      e.answers = 0 ∧ e.poss = 0 ∧ e.trits = 0 ∧ e.drawE = 1 ∧ e.rows = 0 := by
  unfold elemEntry at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨beq_iff_eq.2 h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- A list of shown items that are all elements. -/
theorem all_e : ∀ (vs : List Fmt.ItemValue) (n : Nat), vs.map itemOf = List.replicate n Fmt.Item.e →
    (vs.mapM fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none) = some (vs.filterMap fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none) ∧
    (vs.filterMap fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none).length = n ∧ vs.length = n
  | [], n, h => by
    cases n with
    | zero => exact ⟨rfl, rfl, rfl⟩
    | succ n => cases h
  | v :: vs, n, h => by
    cases n with
    | zero => cases h
    | succ n =>
      rw [List.map_cons, List.replicate_succ] at h
      obtain ⟨hv, ht⟩ := List.cons.inj h
      obtain ⟨i1, i2, i3⟩ := all_e vs n ht
      cases v with
      | e x =>
        refine ⟨?_, congrArg (· + 1) i2, congrArg (· + 1) i3⟩
        rw [List.mapM_cons, i1]
        rfl
      | f x => cases hv
      | word x => cases hv
      | root x => cases hv
      | answer x => cases hv

/-- What roundsFit holds of one round of elements. -/
theorem fit_one {name : String} {items : Nat} {d : Fmt.DeclaredRound} {r : Fmt.RoundView}
    (he : elemEntry name items d.entry = true) (hf : roundsFit [d] [r] = true) :
    r.vals.map itemOf = List.replicate items Fmt.Item.e ∧ r.drawn.elems.length = 1 ∧
      r.drawn.poss.length = 0 ∧ r.drawn.trits.length = 0 := by
  obtain ⟨_, _, _, h4, h5, h6, h7, h8, h9, _⟩ := elemEntry_of he
  unfold roundsFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, _⟩, _⟩, _⟩, _⟩ := hf
  refine ⟨?_, f2.trans h9, f3.trans h7, f4.trans h8⟩
  rw [f1]
  show (d.entry.cut).filter (· != .root) = _
  unfold Fmt.Entry.cut
  rw [h4, h5, h6]
  simp

/-! ## The plain functions -/

/-- **One round of elements is heard.** -/
theorem heard_yes (name : String) (items : Nat) (d : Fmt.DeclaredRound) (r : Fmt.RoundView)
    (he : elemEntry name items d.entry = true) (hf : roundsFit [d] [r] = true) :
    heard name items d.entry r 0 = .ok (sentOf r, drawnOf r) ∧ (sentOf r).length = items := by
  obtain ⟨g1, g2, g3, g4⟩ := fit_one he hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := elemEntry_of he
  obtain ⟨a1, a2, a3⟩ := all_e r.vals items g1
  refine ⟨?_, a2⟩
  obtain ⟨x, hx⟩ : ∃ x, r.drawn.elems = [x] := List.length_eq_one_iff.1 g2
  unfold heard
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, a3, g2, g3, g4, hx]
  erw [a1]
  simp only [First.Close.need, got, beq_self_eq_true, Bool.and_self, Nat.mul_zero, Nat.add_zero]
  show (Except.ok (sentOf r, E.ofTriple x) : Except String (List E × E)) = _
  unfold drawnOf
  rw [hx]
  rfl

theorem claimOf_cons (r : Fmt.RoundView) (rs : List Fmt.RoundView) (claim : E) :
    claimOf (r :: rs) claim = claimOf rs
      (foldClaimRound claim ((sentOf r).getD 0 zeroE) ((sentOf r).getD 1 zeroE) (drawnOf r)) := by
  unfold claimOf
  rw [List.foldl_cons]
  unfold claimStep
  rfl

/-- **The rounds "FOLD round".** -/
theorem rounds_yes : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) (claim : E),
    (ds.all fun d => elemEntry "FOLD round" 2 d.entry) = true → roundsFit ds rs = true →
    rounds (ds.map (·.entry)) rs claim = .ok (rs.map drawnOf, claimOf rs claim)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | d :: ds, r :: rs, claim, ha, hf => by
    rw [List.all_cons, Bool.and_eq_true] at ha
    obtain ⟨hf1, hf2⟩ := Bool.and_eq_true_iff.1 ((H2K.Fit.roundsFit_cons _ _ _ _).symm.trans hf)
    obtain ⟨hh, hl⟩ := heard_yes "FOLD round" 2 d r ha.1 hf1
    obtain ⟨c0, c2, hs⟩ : ∃ c0 c2, sentOf r = [c0, c2] := List.length_eq_two.1 hl
    rw [List.map_cons, rounds, hh, hs]
    show (do
      let x ← rounds (ds.map (·.entry)) rs (foldClaimRound claim c0 c2 (drawnOf r))
      pure (drawnOf r :: x.1, x.2) : Except String (List E × E)) = _
    rw [rounds_yes ds rs _ ha.2 hf2]
    show (Except.ok (drawnOf r :: rs.map drawnOf,
      claimOf rs (foldClaimRound claim c0 c2 (drawnOf r))) : Except String (List E × E)) = _
    rw [List.map_cons, claimOf_cons, hs]
    rfl

/-! ## The mark "spent as a mask" is read by none of the row's tests -/

theorem spent_get (S : Statement) (id o : Nat) :
    (spent S id).oracles[o]? =
      (S.oracles[o]?).map fun x => if id = o then { x with spentAsMask := true } else x := by
  show (S.oracles.modify id fun x => { x with spentAsMask := true })[o]? = _
  rw [Array.getElem?_modify]
  by_cases e : id = o
  · simp [e]
  · simp [e]

theorem tableBits_spent (S : Statement) (id o : Nat) (part : OnBytes.Part) :
    (spent S id).tableBits o part = S.tableBits o part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [spent_get]
  cases h : S.oracles[o]? with
  | none => rfl
  | some x =>
    by_cases e : id = o
    · simp only [Option.map_some, e, if_true]
      rfl
    · simp only [Option.map_some, e, if_false]
      rfl

/-- **The test on the row does not read the mark.** -/
theorem foldRowFits_spent (S : Statement) (F : FoldShape) (row : GroupRow) (id : Nat) :
    Own.foldRowFits (spent S id) F row = Own.foldRowFits S F row := by
  unfold Own.foldRowFits
  simp only [tableBits_spent]
  rfl

/-! ## The fold -/

theorem named_ok {l : Ground.Clauses} (h : Ground.ok l = true) :
    First.Close.named l = .ok () := by
  unfold First.Close.named
  have : l.find? (!·.2) = none := by
    rw [List.find?_eq_none]
    intro c hc
    unfold Ground.ok at h
    rw [List.all_eq_true] at h
    simp [h c hc]
  rw [this]

theorem foldCut_of {k : Nat} {dE : Fmt.DeclaredRound} {dR : List Fmt.DeclaredRound}
    (h : foldCut k (dE :: dR) = true) :
    elemEntry "FOLD epsilon" 1 dE.entry = true ∧ dR.length = k ∧
      (dR.all fun d => elemEntry "FOLD round" 2 d.entry) = true ∧
      ((dE :: dR).all fun d => d.stored.isEmpty && d.opens.isEmpty) = true := by
  unfold foldCut at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **foldD returns ok**, where the mask has come. -/
theorem foldD_yes {Lc : Type} (firstTree : Nat) (d : _root_.Desc.Plain.DState Lc) (F : FoldShape)
    (row : GroupRow) (id : Nat) (cut : List Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (hc : foldCut F.layout.k cut = true) (hf : roundsFit cut rs = true)
    (h1 : Own.foldShapeFits d.st F = true) (h2 : Own.foldMaskFits d.st F id = true)
    (h3 : Ground.ok (Ground.spendAsMaskL d.st id) = true)
    (h4 : Own.foldRowFits d.st F row = true) :
    foldD firstTree d F row (some id) (cut.map (·.entry)) rs =
      .ok (foldOutAt d.st F row id rs, { d with st := spent d.st id }) := by
  cases cut with
  | nil => cases hc
  | cons dE dR =>
    cases rs with
    | nil => cases hf
    | cons rE rR =>
      obtain ⟨c1, c2, c3, _⟩ := foldCut_of hc
      obtain ⟨f1, f2⟩ := Bool.and_eq_true_iff.1 ((H2K.Fit.roundsFit_cons _ _ _ _).symm.trans hf)
      obtain ⟨hh, hl⟩ := heard_yes "FOLD epsilon" 1 dE rE c1 f1
      obtain ⟨sum, hs⟩ : ∃ x, sentOf rE = [x] := List.length_eq_one_iff.1 hl
      have hrows : ((dE :: dR).map (·.entry)).all (·.rows == 0) = true := by
        rw [List.all_map, List.all_cons, Bool.and_eq_true]
        refine ⟨beq_iff_eq.2 (elemEntry_of c1).2.2.2.2.2.2.2.2.2, ?_⟩
        rw [List.all_eq_true] at c3 ⊢
        exact fun x hx => beq_iff_eq.2 (elemEntry_of (c3 x hx)).2.2.2.2.2.2.2.2.2
      have hsp : Ground.spendAsMaskP d id = some { d with st := spent d.st id } := by
        unfold Ground.spendAsMaskP
        rw [if_pos h3]
        rfl
      have hlen : ((dR.map (·.entry)).length == F.layout.k && rR.length == F.layout.k) = true := by
        rw [List.length_map, ← H2K.Sw.roundsFit_length _ _ f2, c2]
        simp
      rw [List.map_cons, foldD, hlen, ← List.map_cons, hrows, h1]
      simp only [First.Close.need, if_true]
      show (do
        First.Close.need "K10.maskfits" (Own.foldMaskFits d.st F id)
        First.Close.named (Ground.spendAsMaskL d.st id)
        let d2 ← got "K10.maskfits" (Ground.spendAsMaskP d id)
        match ← heard "FOLD epsilon" 1 dE.entry rE (d.roots - d.roots) with
        | ([sum], eps) =>
          First.Close.need "K10.rowfits" (Own.foldRowFits d2.st F row)
          let (gamma, claim) ← rounds (dR.map (·.entry)) rR (maddE sum eps row.target)
          pure (foldOutput d2.st F row id eps gamma claim, d2)
        | _ => .error "K10.items" :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc)) = _
      rw [h2, named_ok h3, hsp, Nat.sub_self, hh, hs]
      show (do
        First.Close.need "K10.rowfits" (Own.foldRowFits (spent d.st id) F row)
        let (gamma, claim) ← rounds (dR.map (·.entry)) rR (maddE sum (drawnOf rE) row.target)
        pure (foldOutput (spent d.st id) F row id (drawnOf rE) gamma claim,
          { d with st := spent d.st id }) :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc)) = _
      rw [foldRowFits_spent, h4, rounds_yes dR rR _ c3 f2]
      show (Except.ok (foldOutput (spent d.st id) F row id (drawnOf rE) (rR.map drawnOf)
        (claimOf rR (maddE sum (drawnOf rE) row.target)), { d with st := spent d.st id }) :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc)) = _
      show _ = (Except.ok (foldOutput (spent d.st id) F row id (drawnOf rE) (rR.map drawnOf)
        (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target)),
          { d with st := spent d.st id }) :
          Except String (SingleRows × _root_.Desc.Plain.DState Lc))
      rw [hs]
      rfl

/-! ## The part in the kind's block -/

section Part
variable {p : P12} {j : Nat} {cur : Fmt.M1.Stage} {cut : List Fmt.DeclaredRound} {t : T12}
  {row : GroupRow} {L : GroupLayout} {c : IoppStage} {n : Nat × Nat} {id : Nat}

/-- A fold's cut opens nothing: no column is keyed. -/
theorem keyed_nil (p : P12) (cut : List Fmt.DeclaredRound) : keyed p cut [] = [] := by
  unfold keyed
  rw [List.zip_nil_right]
  rfl

/-- **The plain part returns ok.** -/
theorem foldE_yes (H : FoldFront p j cur t row L c n id) (hc : foldCut c.k cut = true)
    (rs : List Fmt.RoundView) (hf : roundsFit cut rs = true) :
    H2K.foldE (ioppFoldShape c L) row t.mask (lay p cut none t rs []) =
      .ok (foldOut t row L c id rs,
        { lay p cut none t rs [] with
          d := { (lay p cut none t rs []).d with st := spent t.st id }
          entries := [], rounds := [], last := (cut.map (·.entry)).getLast?, asked := false }) := by
  have hk : (ioppFoldShape c L).layout.k = c.k := rfl
  have lc : cut.length = 1 + c.k := by
    cases cut with
    | nil => cases hc
    | cons dE dR =>
      rw [List.length_cons, (foldCut_of hc).2.1]
      omega
  have lr : rs.length = 1 + c.k := (H2K.Sw.roundsFit_length _ _ hf).symm.trans lc
  have hD := foldD_yes p.nums.firstTree (lay p cut none t rs []).d (ioppFoldShape c L) row id cut rs
    hc hf H.shape H.maskFits H.spend H.rowFits
  unfold H2K.foldE
  rw [H.mask]
  have e1 : (lay p cut none t rs []).entries.take (1 + (ioppFoldShape c L).layout.k) =
      cut.map (·.entry) := by
    show (cut.map (·.entry)).take (1 + c.k) = _
    exact List.take_of_length_le (by rw [List.length_map, lc])
  have e2 : (lay p cut none t rs []).rounds.take (1 + (ioppFoldShape c L).layout.k) = rs :=
    List.take_of_length_le (le_of_eq lr)
  have e3 : (lay p cut none t rs []).entries.drop (1 + (ioppFoldShape c L).layout.k) = [] := by
    show (cut.map (·.entry)).drop (1 + c.k) = _
    exact List.drop_eq_nil_of_le (by rw [List.length_map, lc])
  have e4 : (lay p cut none t rs []).rounds.drop (1 + (ioppFoldShape c L).layout.k) = [] :=
    List.drop_eq_nil_of_le (le_of_eq lr)
  have g1 : (lay p cut none t rs []).owed.isNone = true := rfl
  have g2 : (decide (1 + (ioppFoldShape c L).layout.k ≤ (lay p cut none t rs []).entries.length) &&
      decide (1 + (ioppFoldShape c L).layout.k ≤ (lay p cut none t rs []).rounds.length)) =
      true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨?_, le_of_eq lr.symm⟩
    show 1 + c.k ≤ (cut.map (·.entry)).length
    rw [List.length_map, lc]
  simp only [g1, g2, e1, e2, e3, e4, H2K.need, if_true]
  show (do
    let x ← (First.Close.foldD p.nums.firstTree (lay p cut none t rs []).d (ioppFoldShape c L) row
      (some id) (cut.map (·.entry)) rs).mapError ("fold: " ++ ·)
    pure (x.1,
      { lay p cut none t rs [] with
        d := x.2, entries := [], rounds := [], last := (cut.map (·.entry)).getLast?
        asked := false }) : Except String (SingleRows × H2K.PS)) = _
  rw [hD]
  rfl

/-- **The part of Johnson/Desc/K12/Join.lean says yes, and the record behind is foldT.** -/
theorem foldJ_yes (H : FoldFront p j cur t row L c n id) (hc : foldCut c.k cut = true)
    (rs : List Fmt.RoundView) (hf : roundsFit cut rs = true) :
    (foldJ p j cur cut).decide t rs [] = .ok (foldT t row L c n id rs) := by
  have hg : Ground.ok (Ground.newGroupL (spent t.st id) n.1 n.2) = true := H.group
  simp only [foldJ, H.pass, H.stage, H.next]
  rw [foldE_yes H hc rs hf]
  show (do
    let y ← H2K.newGroupE n.1 n.2
      { lay p cut none t rs [] with
        d := { (lay p cut none t rs []).d with st := spent t.st id }
        entries := [], rounds := [], last := (cut.map (·.entry)).getLast?, asked := false }
    back t y.2 (.single (foldOut t row L c id rs) y.1) t.mask : Except String T12) = _
  unfold H2K.newGroupE Ground.newGroupP
  rw [if_pos hg]
  simp only [H2K.opt, Except.map]
  unfold back
  show (do
    VerifiableInference.Desc.need "(v): a round, an entry or a column is left over"
      (([] : List Fmt.RoundView).isEmpty && ([] : List Fmt.Entry).isEmpty && (keyed p cut []).isEmpty)
    pure { t with
      st := Ground.withGroup (spent t.st id) n.1 n.2, book := t.book, roots := t.roots
      pass := .single (foldOut t row L c id rs) (spent t.st id).groups.size
      mask := t.mask } : Except String T12) = _
  rw [keyed_nil]
  rfl

/-- No position is drawn in a fold's rounds. -/
theorem inRange_fold : ∀ {cut : List Fmt.DeclaredRound} {rs : List Fmt.RoundView},
    roundsFit cut rs = true → inRange cut rs = true
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, r :: rs, h => by
    have h1 := Bool.and_eq_true_iff.1 ((H2K.Fit.roundsFit_cons _ _ _ _).symm.trans h)
    have ih := inRange_fold h1.2
    unfold inRange at ih ⊢
    rw [List.zip_cons_cons, List.all_cons, ih, Bool.and_true]
    have h2 := h1.1
    unfold roundsFit at h2
    simp only [Bool.and_eq_true] at h2
    exact h2.1.1.1.2

/-- **THE FOLD's PART OF guardedProximityTestParts SAYS YES, AND THE RECORD BEHIND IS foldT.** rs: its rounds as the
view has them; Block.step shows them without the sealed digest. -/
theorem fold5_yes (H : FoldFront p j cur t row L c n id) (hc : foldCut c.k cut = true)
    (rs : List Fmt.RoundView) (hf : roundsFit cut rs = true) :
    (guardedProximityTestParts.fold p j cur cut).decide t (rs.map noDigest) [] =
      .ok (foldT t row L c n id (rs.map noDigest)) := by
  have hf' : roundsFit cut (rs.map noDigest) = true :=
    (H2K.Onto.roundsFit_noDigest cut rs).trans hf
  show (do
    VerifiableInference.Desc.need "(z): a drawn position is out of its round's range"
      (inRange cut (rs.map noDigest))
    (foldJ p j cur cut).decide t (rs.map noDigest) [] : Except String T12) = _
  rw [inRange_fold hf', foldJ_yes H hc _ hf']
  rfl

end Part

/-- **The record behind the fold**: seven equations. -/
theorem foldT_keeps (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat)
    (id : Nat) (rs : List Fmt.RoundView) :
    (foldT t row L c n id rs).st.codes = t.st.codes ∧ (foldT t row L c n id rs).book = t.book ∧
    (foldT t row L c n id rs).roots = t.roots ∧ (foldT t row L c n id rs).g = t.g ∧
    (foldT t row L c n id rs).mask = t.mask ∧
    (foldT t row L c n id rs).st.oracles =
      t.st.oracles.modify id (fun x => { x with spentAsMask := true }) ∧
    (foldT t row L c n id rs).st.groups = t.st.groups.push { code := n.1, maskCode := n.2 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.elemEntry_of
#print axioms Johnson.Prover.Link.all_e
#print axioms Johnson.Prover.Link.fit_one
#print axioms Johnson.Prover.Link.heard_yes
#print axioms Johnson.Prover.Link.claimOf_cons
#print axioms Johnson.Prover.Link.rounds_yes
#print axioms Johnson.Prover.Link.spent_get
#print axioms Johnson.Prover.Link.tableBits_spent
#print axioms Johnson.Prover.Link.foldRowFits_spent
#print axioms Johnson.Prover.Link.named_ok
#print axioms Johnson.Prover.Link.foldCut_of
#print axioms Johnson.Prover.Link.foldD_yes
#print axioms Johnson.Prover.Link.keyed_nil
#print axioms Johnson.Prover.Link.foldE_yes
#print axioms Johnson.Prover.Link.foldJ_yes
#print axioms Johnson.Prover.Link.inRange_fold
#print axioms Johnson.Prover.Link.fold5_yes
#print axioms Johnson.Prover.Link.foldT_keeps
