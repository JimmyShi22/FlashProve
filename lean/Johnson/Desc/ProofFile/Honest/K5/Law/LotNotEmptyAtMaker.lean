-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotNotEmptyAtMaker.lean: a test of the theorems on the lot of
the attention segments' own rounds (kind K5: the label of that sub-protocol in the description)
against emptiness: under the library's head, at what the maker returns, with the reader of the key
points laid at the lookups' own text, the lot is not empty and the book names the kind as a spender.

  shapesOf_sum, k5_has_sum   a script with a masked sumcheck has a part of that shape; K5's has
  r5_row_ne           a row of the lot has parts: no premise
  k5_part_stated      conditional: the maker states a stretch for a part of K5's member
  filterMap_map_all   general: where a function yields at every member, its images can be read off
  k5_rows_places      conditional: the places of the lot's rows, group by group
  k5_spender_at_maker conditional: at each of the twelve groups an entry of the book that the maker
                      returns has its spender at the group's place of the kind
  k5_lot_not_empty_at_return   conditional: h; hA: the lot has twelve rows, at twelve different
                      places, each with parts and with a side that Side.seated makes, and each
                      place is the spender's place of an entry of the book
  k5_lot_not_empty_at_identity_cells   the same at cells := id

What it is for. k5_good_rows_at_return (Honest/K5/Law/OwnsNothingAtMaker.lean) says Good at every row
of the lot, and k5_owner_elsewhere says that no entry of the book has its owner at a place of the
kind. Both are "for every" statements, and each would hold of an empty list. This file shows that at
keyOfK3 the list of rows has twelve members and that the book names these places.

Limits. h, the library's head, and hA, that the maker returns at the filling P, are hypotheses here:
that they can be met is not shown in this file. P is a free variable. A count of rows, places, parts
and entries: no distribution occurs. Good's fields exact and fresh speak of the side's members: by
membersOf's text (Honest/Side.lean) each part of the row is one, but that is not stated here. Nothing
here says what Good says. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnsNothingAtMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.SLotAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Part (MaskedSum.Var MaskedSum.Ends)
open VerifiableInference.Desc.First.Att.P (Stage script products)
open H2K5.Honest (PartShape shapes shapesOf)
open P5J (AtMgA TS)

/-! ## 1 A row has parts -/

/-- A list of stages that holds a masked sumcheck has a part of that shape. -/
theorem shapesOf_sum : ∀ (l : List Stage) (lead : Nat) (vs : List MaskedSum.Var) (e : MaskedSum.Ends),
    Stage.sum vs e ∈ l → ∃ k, PartShape.sum k ∈ shapesOf lead l
  | [], _, _, _, h => by cases h
  | .scalars n :: l, lead, vs, e, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact shapesOf_sum l (lead + n) vs e h
  | .batch _ :: l, _, vs, e, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · obtain ⟨k, hk⟩ := shapesOf_sum l 0 vs e h
      exact ⟨k, List.mem_cons_of_mem _ hk⟩
  | .point _ :: l, _, vs, e, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · obtain ⟨k, hk⟩ := shapesOf_sum l 0 vs e h
      exact ⟨k, List.mem_cons_of_mem _ hk⟩
  | .sum _ _ :: _, _, _, _, _ => ⟨_, List.mem_cons_self ..⟩

/-- **K5's script has a masked sumcheck among its shapes.** No premise. -/
theorem k5_has_sum (x : OnBytes.Params.AttentionRounds) : ∃ k, PartShape.sum k ∈ shapes x := by
  have hm : products x.e x.pairs ∈ script x := by
    unfold script
    dsimp only
    refine List.mem_append_right _ ?_
    iterate 3 apply List.mem_cons_of_mem
    exact List.mem_cons_self ..
  exact shapesOf_sum (script x) 0 _ _ hm

section
variable {W₀ Rc Xi Tr X Pb : Type}

/-- **A row of the lot has parts.** No premise. -/
theorem r5_row_ne (cells : Tr → Cells) (Z : Seat5) :
    (r5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells Z).row ≠ [] := by
  have hn : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.length =
      (shapes Z.P.x).length := by
    have e := congrArg List.length (half_cut (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z)
    rw [List.length_map] at e
    rw [e]
    exact List.length_map _
  obtain ⟨k, hk⟩ := k5_has_sum Z.P.x
  intro h0
  have e : ((k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.zip
      (simsOf (Pb := Pb) Z.place Z.P.x)).length = 0 := by
    have h1 := congrArg List.length h0
    exact h1
  rw [List.length_zip, hn, sims_length, Nat.min_self] at e
  have := List.length_pos_of_mem hk
  omega

end

/-- **The maker states a stretch for a part of K5's member.** CONDITIONAL: as k5_stated. -/
theorem k5_part_stated {S Cl : Type} (blk : VerifiableInference.Desc.Block S Cl)
    (p : VerifiableInference.Desc.First.Att.P.Par) (Z : Seat5) (hpl : blk.place = Z.place)
    (hr : blk.rounds = VerifiableInference.Desc.First.Att.P.rounds p) (hx : p.own = Z.P.x)
    (hok : VerifiableInference.Desc.First.Att.P.planOk p = true) :
    ∃ (q : PartAt) (i : Nat), (planParts blk)[i]? = some q ∧ stated q ≠ [] := by
  obtain ⟨k, hk⟩ := k5_has_sum Z.P.x
  obtain ⟨j, hj⟩ := OnBytes.Maker.mem_zipIdx_of_mem _ 0 _ hk
  have hmem : spendsOf Z.place (PartShape.sum k, j) ∈ (k5Row Z).map (·.spends) := by
    refine List.mem_map.2 ⟨partAt Z.place (chalOf Z) (jobs Z.P) (PartShape.sum k, j), ?_,
      partAt_spends _ _ _ _⟩
    show _ ∈ (shapes Z.P.x).zipIdx.map (partAt Z.place (chalOf Z) (jobs Z.P))
    exact List.mem_map.2 ⟨_, hj, rfl⟩
  rw [← k5_stated blk p Z hpl hr hx hok] at hmem
  obtain ⟨q, hq, eq⟩ := List.mem_map.1 hmem
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hq
  refine ⟨q, i, hi, ?_⟩
  rw [eq]
  exact List.cons_ne_nil _ _

/-! ## 2 The places of the rows -/

/-- Where a function yields at every member, with a value of known image, the images can be read
off the list. -/
theorem filterMap_map_all {α β γ : Type} (f : α → Option β) (g : β → γ) (k : α → γ) :
    ∀ l : List α, (∀ x ∈ l, (f x).map g = some (k x)) → (l.filterMap f).map g = l.map k
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x List.mem_cons_self
    cases e : f x with
    | none =>
      rw [e] at hx
      cases hx
    | some y =>
      rw [e] at hx
      rw [List.filterMap_cons_some e, List.map_cons, List.map_cons,
        filterMap_map_all f g k l fun z hz => h z (List.mem_cons_of_mem _ hz)]
      exact congrArg (· :: _) (Option.some.inj hx)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PLACES OF THE LOT's ROWS, GROUP BY GROUP.** CONDITIONAL: the head; hG; hKey. -/
theorem k5_rows_places {W₀ Rc Xi Tr X Pb : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) (cells : Tr → Cells)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)}
    (hKey : KeysFitAll keyOf Zp G cF) :
    ((k5SLot (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells keyOf).rows Zp G).map
        (·.place) =
      (List.range 12).map fun g => (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) := by
  show ((H2K5.k5Places G).filterMap fun y =>
    (seatAtK keyOf Zp G y.1 y.2.1 y.2.2).map
      (r5 (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells)).map (·.place) = _
  rw [filterMap_map_all _ _ (fun y => (⟨1, some y.1, 3, .K5⟩ : Place)),
    H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG, List.map_map]
  · exact List.map_congr_left fun _ _ => rfl
  intro y hy
  rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
  obtain ⟨_, a, -, Pl, -⟩ := k5_member h (List.mem_range.1 hg)
  show ((seatAtK keyOf Zp G (2 * g + 1) ("A" ++ toString g) g).map _).map _ = _
  rw [(seatAt_returns_at_head h (List.mem_range.1 hg) hG Pl.plan
    (hKey g (List.mem_range.1 hg) a Pl.plan)).2]
  rfl

/-- **AT EACH OF THE TWELVE GROUPS AN ENTRY OF THE BOOK THAT THE MAKER RETURNS HAS ITS SPENDER AT THE
GROUP's PLACE OF THE KIND.** CONDITIONAL: h; hA: the maker returns A at a filling P, P a free
variable. -/
theorem k5_spender_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {g : Nat} (hg : g < 12)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∃ e ∈ A.B.ahead, e.spender.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  obtain ⟨m, -⟩ := parts_of_atPure hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := m.book
  rw [eF] at hB
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨blk, a', hm, -, Dc⟩ := k5_member h hg
  have hb : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  obtain ⟨q, i, hi, hne⟩ := k5_part_stated blk (parAt Zp g a') (seatOf keyOfK3 Zp A.G cF g a')
    Dc.place Dc.rounds rfl Dc.plan
  have hpl : blk.place = ⟨1, some (2 * g + 1), 3, .K5⟩ := Dc.place
  have h5 : blk.place.kind = .K5 := by rw [hpl]
  obtain ⟨e, he, es⟩ := stated_has_entry hB hp hb (l := 2 * g + 1) (by rw [hpl]) hi
    (ProofFile.Honest.Small.no_merge_of_kind _ _
      (by show blk.place.kind ≠ _; rw [h5]; exact fun c => nomatch c)
      (by show blk.place.kind ≠ _; rw [h5]; exact fun c => nomatch c)) hne
  refine ⟨e, he, ?_⟩
  rw [es]
  exact hpl

variable {W₀ Rc Tr X₀ X W₀' Rc' Tr' X' Xi Pb : Type}

/-- **AT WHAT THE MAKER RETURNS, AT keyOfK3, THE LOT IS NOT EMPTY AND THE BOOK NAMES IT: TWELVE ROWS,
AT TWELVE DIFFERENT PLACES, EACH WITH PARTS AND WITH A SIDE THAT Side.seated MAKES, AND AT EACH PLACE
THE SPENDER OF AN ENTRY OF THE BOOK.** CONDITIONAL: h; hA. -/
theorem k5_lot_not_empty_at_return (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (cells : Tr' → Cells)
    (fs₀ : List (Fall TS)) :
    ∀ rows, rows = (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (X := X') (Pb := Pb) cells
        keyOfK3).rows A.Z A.G →
      rows.length = 12 ∧ (rows.map (·.place)).Nodup ∧
      ∀ r ∈ rows, r.row ≠ [] ∧ (∃ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) ∧
        ∃ e ∈ A.B.ahead, e.spender.place = r.place := by
  intro rows er
  have m := (parts_of_atPure hA).1
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := eZ ▸ m.ground
  rw [eZ] at er
  subst er
  refine ⟨rows_twelve_K3 h hG cells, ?_, fun r hr => ⟨?_, rows_seated h hG cells keyOfK3 fs₀ r hr, ?_⟩⟩
  · rw [k5_rows_places h hG cells (keysFitAll_K3 h hG)]
    refine List.Nodup.map (fun a b e => ?_) List.nodup_range
    have e2 := Option.some.inj (congrArg (fun p : Place => p.link) e)
    omega
  · obtain ⟨_, _, Y, _, rfl⟩ := row_of_lot hr
    exact r5_row_ne cells Y
  · obtain ⟨y, hy, Y, hY, rfl⟩ := row_of_lot hr
    rw [H2K5.Row.k5Places_scope h.scope h.reads h.laid.pub hG] at hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hl, -⟩ := seat_facts hY
    obtain ⟨e, he, es⟩ := k5_spender_at_maker h (List.mem_range.1 hg) hA
    refine ⟨e, he, ?_⟩
    rw [es]
    show (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) = ⟨1, some Y.link, 3, .K5⟩
    rw [hl]

/-- **The same at cells := id.** CONDITIONAL: h; hA. -/
theorem k5_lot_not_empty_at_identity_cells (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (fs₀ : List (Fall TS)) :
    ∀ rows, rows = (k5SLot (W₀ := W₀') (Rc := Rc') (Xi := Xi) (Tr := Cells) (X := X') (Pb := Pb) id
        keyOfK3).rows A.Z A.G →
      rows.length = 12 ∧ (rows.map (·.place)).Nodup ∧
      ∀ r ∈ rows, r.row ≠ [] ∧ (∃ σ₀, Side.seated cF.blocksInOrder r.place r.row fs₀ = some σ₀) ∧
        ∃ e ∈ A.B.ahead, e.spender.place = r.place :=
  k5_lot_not_empty_at_return h hA id fs₀

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.shapesOf_sum
#print axioms ProofFile.Honest.K5.k5_has_sum
#print axioms ProofFile.Honest.K5.r5_row_ne
#print axioms ProofFile.Honest.K5.k5_part_stated
#print axioms ProofFile.Honest.K5.filterMap_map_all
#print axioms ProofFile.Honest.K5.k5_rows_places
#print axioms ProofFile.Honest.K5.k5_spender_at_maker
#print axioms ProofFile.Honest.K5.k5_lot_not_empty_at_return
#print axioms ProofFile.Honest.K5.k5_lot_not_empty_at_identity_cells
