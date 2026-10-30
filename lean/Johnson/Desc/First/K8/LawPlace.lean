-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPlace.lean: THE SMALLNESS TEST, ITS FIRST HALF: THE PROVED BLOCK'S SIZES
ARE MADE OF THE PLACE'S NUMBERS ALONE, AND A YES OF THE KIND'S BLOCK SAYS THAT THE RECORD HAS THEM.

The proved block's caller is fixed before any statement; its sizes (the library's `sizeOf`,
OnBytes/Tie/Pv/Tail/SizeOf.lean) are read off a public record tl0: the number of matrices, each
matrix's rows and columns, the number of combinations, and THE SHAPES OF THE TABLES of reads. A
plan's own record has no table yet. Since the kind's text holds the record's rows (e) and the closed
list's shapes (t) against the place's numbers, all of these are numbers of the place:
  `PlaceRec p tl`: the record tl has the place's numbers: five equations of plain lists.
  `placeRec_of_yes`: **A YES OF THE BLOCK, as the fold calls it, AT A RECORD IN WHICH tl LIES, GIVES
    `PlaceRec p tl`**: from tests (d), (e), (f), (t). No premise.
  `sameSize_of_place`: two records with one place's numbers have the same numbers (`SameSize`,
    Johnson/Desc/First/K8/LawLay.lean): so the same sizes.
  `fits_of_place`: the law's premise `Fits` is paid at such a record.
  `recP tlL p`: A PUBLIC RECORD WITH THE PLACE'S NUMBERS, MADE OF THE PLACE'S NUMBERS: the layout of
    tlL (a link's planned record), with matrices of the place's rows and columns and with tables of
    the place's shapes (without weights). `placeRec_recP`: it has them, if the place lists as many
    numbers of rows as of columns (a test on the plan). `sameLay_recP`: it has tlL's layout.
  TEETH: `PlaceAtYes b`: the law `placeRec_of_yes` of ANY family of blocks; `hear_placeAtYes`: the
    kind's text has it; `noT`: the kind's text without test (t); `noT_placeAtYes`: it has it not: it
    says yes at a record whose closed list holds a table, at a place that lists none.
Definitions, statements and proofs.
Limits. THAT THE PLACE'S NUMBERS ARE THE RIGHT ONES (that `Par.asks` lists the families of tables
which the link's kind makes) is asked at every run by test (t), and said by no theorem. Nothing on
the weights. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawTie
import Johnson.Desc.First.K8.LawTeeth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail OnBytes.Slice

/-- The record tl has the place's numbers. -/
structure PlaceRec (p : Par) (tl : HTailF2) : Prop where
  nm : tl.NM = p.ks.length
  ks : tl.mats.toList.map (·.k) = p.ks
  ms : tl.mats.toList.map (·.m) = p.ms
  tau : tl.tau = p.tau
  tabs : (tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p

/-- **A yes of the block gives it.** -/
theorem placeRec_of_yes {Cl : Type} (p : Par) (tl : HTailF2) (ft : Nat) (st st' : S) (n : Nat)
    (rs : List Fmt.RoundView) (cols : List Col) (hst : st.tl? = some tl)
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols = .ok (st', n)) : PlaceRec p tl := by
  obtain ⟨_, _, _, _, _, _, _, c4, c5, c7, c6, c8, _⟩ := step_ok atS p ft st st' rs cols n h
  exact ⟨by simpa [atS, hst] using c4, by simpa [atS, hst] using c5, by simpa [atS, hst] using c7,
    by simpa [atS, hst] using c6, by simpa [atS, hst] using c8⟩

/-- A number of a matrix, place by place, off the list of these numbers. -/
theorem map_getD (f : TMat → ℕ) (hf : f {} = 0) (a : Array TMat) (μ : ℕ) :
    (a.toList.map f).getD μ 0 = f (a.getD μ {}) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases a[μ]? with
  | none => exact hf.symm
  | some x => rfl

/-- Two records with one place's numbers have the same numbers. -/
theorem sameSize_of_place {p : Par} {tl tl0 : HTailF2} (h : PlaceRec p tl) (h0 : PlaceRec p tl0) :
    SameSize tl tl0 where
  nm := h.nm.trans h0.nm.symm
  m := fun μ => by
    rw [← map_getD (·.m) rfl, ← map_getD (·.m) rfl, h.ms, h0.ms]
  k := fun μ => by
    rw [← map_getD (·.k) rfl, ← map_getD (·.k) rfl, h.ks, h0.ks]
  tau := h.tau.trans h0.tau.symm
  tabs := by
    have e : ∀ a : Array HFun, (a.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) =
        (a.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)).map
          fun x : ℕ × ℕ × ℕ => (⟨x.1, x.2.1, x.2.2⟩ : Tab) := by
      intro a
      rw [List.map_map]
      rfl
    unfold SameShapes
    rw [e, e, h.tabs, h0.tabs]

/-- The law's premise is paid at a record with the place's numbers. -/
theorem fits_of_place {p : Par} {tl0 : HTailF2} (h : PlaceRec p tl0) :
    Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl0).size :=
  fits_of_tests tl0 p h.nm h.ks h.tau

/-- A public record with the place's numbers, made of the place's numbers; its layout is tlL's. -/
def recP (tlL : HTailF2) (p : Par) : HTailF2 :=
  { tlL with
    NM := p.ks.length
    mats := ((p.ms.zip p.ks).map fun x => ({ m := x.1, k := x.2 } : TMat)).toArray
    tau := p.tau
    funs := ((tabs p).map fun x => ({ mat := x.1, len := x.2.1, start := x.2.2 } : HFun)).toArray }

theorem placeRec_recP (tlL : HTailF2) (p : Par) (h : p.ms.length = p.ks.length) :
    PlaceRec p (recP tlL p) where
  nm := rfl
  ks := by
    show (((p.ms.zip p.ks).map fun x => ({ m := x.1, k := x.2 } : TMat)).toArray.toList.map
      (·.k)) = p.ks
    rw [List.toList_toArray, List.map_map]
    exact List.map_snd_zip (Nat.le_of_eq h.symm)
  ms := by
    show (((p.ms.zip p.ks).map fun x => ({ m := x.1, k := x.2 } : TMat)).toArray.toList.map
      (·.m)) = p.ms
    rw [List.toList_toArray, List.map_map]
    exact List.map_fst_zip (Nat.le_of_eq h)
  tau := rfl
  tabs := by
    show (((tabs p).map fun x => ({ mat := x.1, len := x.2.1, start := x.2.2 } :
      HFun)).toArray.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) = tabs p
    rw [List.toList_toArray, List.map_map]
    exact List.map_id _

theorem sameLay_recP (tlL : HTailF2) (p : Par) : SameLay (recP tlL p) tlL := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Teeth -/

/-- The law `placeRec_of_yes`, of any family of blocks. -/
def PlaceAtYes {Cl : Type} (b : Par → Block S Cl) : Prop :=
  ∀ (p : Par) (tl : HTailF2) (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List Col),
    st.tl? = some tl → (b p).step ft st rs cols = .ok (st', n) → PlaceRec p tl

/-- The kind's own text has it. -/
theorem hear_placeAtYes {Cl : Type} : PlaceAtYes (approximateRangeProofDrawKind (Cl := Cl) atS) :=
  fun p tl ft st st' n rs cols hst h => placeRec_of_yes p tl ft st st' n rs cols hst h

/-- The kind's text without test (t). -/
def noT (p : Par) : Block S Unit :=
  { approximateRangeProofDrawKind atS p with
    decide := fun s rs _ =>
      match rs with
      | [r] =>
        if !atS.closed s then .error "a"
        else if !atS.nothingOwed s then .error "b"
        else if atS.drawn s then .error "c"
        else if atS.matrices s != p.ks.length then .error "d"
        else if atS.ks s != p.ks then .error "e"
        else if atS.ms s != p.ms then .error "e"
        else if atS.tau s != p.tau then .error "f"
        else atS.lay s r.drawn.trits.toArray (firstColumns p)
      | _ => .error "rounds" }

/-- A record of the smallness test with the toy place's matrix, and one table in its closed list. -/
def toyTab : HTailF2 :=
  { funClosed := true, NM := 1, mats := #[{ m := 1, k := 1 }], tau := 1,
    funs := #[{ mat := 0, len := 1, start := 0 }] }

/-- **Without (t) the law fails**: a yes at a record whose closed list holds a table, at the toy
place, which lists no family of tables. -/
theorem noT_placeAtYes : ¬ PlaceAtYes noT := fun h => by
  have hs : ∃ st', (noT toyPar).step 0 (toyIn toyTab) [toyRound] [] = .ok (st', 0) := by
    rw [step_at_round (noT toyPar) toyPar rfl 0 _ _ _ (by decide)]
    exact ⟨_, rfl⟩
  obtain ⟨st', hs⟩ := hs
  have e := (h toyPar toyTab 0 _ st' 0 _ _ rfl hs).tabs
  exact absurd e (by decide)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.placeRec_of_yes
#print axioms VerifiableInference.Desc.First.K8.sameSize_of_place
#print axioms VerifiableInference.Desc.First.K8.fits_of_place
#print axioms VerifiableInference.Desc.First.K8.placeRec_recP
#print axioms VerifiableInference.Desc.First.K8.sameLay_recP
#print axioms VerifiableInference.Desc.First.K8.hear_placeAtYes
#print axioms VerifiableInference.Desc.First.K8.noT_placeAtYes
