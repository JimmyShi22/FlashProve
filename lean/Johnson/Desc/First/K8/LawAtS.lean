-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawAtS.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS LAW AT THE FIRST CHAIN'S
CARRIED RECORD.

Johnson/Desc/First/K8/Law.lean has the law at any seat, under the premise `Fits`: the place's
numbers are the typed block's.
Here the seat is that of Johnson/Desc/First/K8/AtS.lean, the place's numbers are read off the record
of the smallness test (each matrix's columns; the number of combinations), and the typed block's
sizes are the library's `sizeOf` of that record (OnBytes/Tie/Pv/Tail/SizeOf.lean). Then:
  `fits_parOf`: `Fits` holds, if the record's number of matrices is the length of its list: the
    premise is paid.
  `firstColumns_parOf`: the first columns that the kind lays are the walk that the library's laws on
    the test's equations ask under the name hfirst (LinkPort.lean, InSubLay.lean, InSubAll.lean,
    LinkLayers.lean in OnBytes/Tie/Pv/Tail/).
  `fits_of_tests`: the kind's own tests (d), (e), (f) give `Fits` at the record that lies in S.
  `yes_atS`: a yes of the block in the fold hands on the carried record in which the record of the
    smallness test has cfF := the list of the typed challenge and cfFirst := that walk, and is
    otherwise as it was: with no premise on the place's numbers.
  `yes_atS_frame`: the block fills no slot and lays no mark: of the carried record it turns the
    smallness test's record alone.
  `block_good_atS`: the proved block's one condition on public numbers holds at the library's sizes
    of every record.
Definitions, statements and proofs. Limits: those of Law.lean.


-/
import Johnson.Desc.First.K8.AtS
import Johnson.Desc.First.K8.Law
import OnBytes.Tie.Pv.Tail.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.Slice

/-- A place's numbers, read off the record of the smallness test. -/
def parOf (tl : HTailF2) (link piece : Nat) (matsIn readsIn : List Nat)
    (asks : List (Nat × Nat × Nat)) : Par :=
  { link := link, piece := piece, ks := tl.mats.toList.map (·.k), ms := tl.mats.toList.map (·.m),
    tau := tl.tau, asks := asks, matsIn := matsIn, readsIn := readsIn }

/-- `Fits` reads a place's columns and its number of combinations alone. -/
theorem fits_congr {p q : Par} {s : Size} (hk : p.ks = q.ks) (ht : p.tau = q.tau) (h : Fits p s) :
    Fits q s :=
  ⟨by rw [← hk]; exact h.nm, by rw [← hk]; exact h.k, by rw [← ht]; exact h.tau⟩

/-- The premise of the law is paid. -/
theorem fits_parOf (tl : HTailF2) (h : tl.NM = tl.mats.size) (link piece : Nat) (matsIn readsIn :
    List Nat) (asks : List (Nat × Nat × Nat)) :
    Fits (parOf tl link piece matsIn readsIn asks) (OnBytes.Tie.Pv.Tail.sizeOf tl).size := by
  refine ⟨?_, ?_, rfl⟩
  · show tl.NM = _
    simp [parOf, h]
  · intro i hi
    have hi' : i < tl.mats.size := by simpa [parOf] using hi
    show (tl.mats.getD i {}).k = _
    simp [parOf, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hi']

/-- The first columns that the kind lays are the walk that the library's laws ask. -/
theorem firstColumns_parOf (tl : HTailF2) (link piece : Nat) (matsIn readsIn : List Nat)
    (asks : List (Nat × Nat × Nat)) :
    firstColumns (parOf tl link piece matsIn readsIn asks) =
      tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] := by
  unfold firstColumns parOf
  rw [List.foldl_map, ← Array.foldl_toList]

/-- What the seat's one writing does. -/
theorem atS_lay (s s' : S) (m : Array Int) (first : Array Nat) (h : atS.lay s m first = .ok s') :
    ∃ tl, s.tl? = some tl ∧ s' = s.putTl { tl with cfF := m, cfFirst := first } := by
  unfold atS at h
  cases ht : s.tl? with
  | none => simp [ht] at h
  | some tl =>
    simp only [ht, Except.ok.injEq] at h
    exact ⟨tl, rfl, h.symm⟩

/-- The kind's own tests (d), (e) and (f), at that seat, pay the law's premise: the place's numbers
are the typed block's, at the library's sizes of the record that lies in S. -/
theorem fits_of_tests (tl : HTailF2) (p : Par) (hd : tl.NM = p.ks.length)
    (he : tl.mats.toList.map (·.k) = p.ks) (hf : tl.tau = p.tau) : Fits p
        (OnBytes.Tie.Pv.Tail.sizeOf tl).size := by
  have hNM : tl.NM = tl.mats.size := by rw [hd, ← he]; simp
  exact fits_congr he hf (fits_parOf tl hNM p.link p.piece p.matsIn p.readsIn p.asks)

theorem firstColumns_of_tests (tl : HTailF2) (p : Par) (he : tl.mats.toList.map (·.k) = p.ks) :
    firstColumns p = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] := by
  rw [← firstColumns_parOf tl p.link p.piece p.matsIn p.readsIn p.asks]
  unfold firstColumns parOf
  rw [he]

/-- **A yes of the block in the fold, at the carried record: NO PREMISE ON THE PLACE'S NUMBERS.**
Whatever the place's numbers: if the block says yes at a record in which the smallness test's record
tl lies, then these numbers are the typed block's at the library's sizes of tl, and the record
handed on has cfF := the list of the typed challenge to which the library's maps carry the written
verifier message, cfFirst := the walk that the library's laws ask, and is otherwise as it was. -/
theorem yes_atS {Cl : Type} (p : Par) (tl : HTailF2) (c : (wRound (rd p)).Chal)
    (ft : Nat) (st st' : S) (n : Nat) (cols : List Col) (r : Fmt.RoundView) (hst : st.tl? = some tl)
    (h1 : r.vals = []) (h2 : r.drawn.elems = []) (h3 : r.drawn.poss = []) (h4 : r.drawn.trits =
        kitTrits c)
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st [r] cols = .ok (st', n)) :
    ∃ hf : Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size,
      st' = st.putTl { tl with
        cfF := listOf (matrixOf hf c)
        cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0] } ∧ n = 0 :=
            by
  obtain ⟨_, _, _, _, _, _, _, c4, c5, _, c6, _, _⟩ := step_ok atS p ft st st' [r] cols n h
  have hd : tl.NM = p.ks.length := by simpa [atS, hst] using c4
  have he : tl.mats.toList.map (·.k) = p.ks := by simpa [atS, hst] using c5
  have hτ : tl.tau = p.tau := by simpa [atS, hst] using c6
  have hf := fits_of_tests tl p hd he hτ
  obtain ⟨_, _, _, _, _, _, _, _, hl, hn⟩ := (hear_law (Cl := Cl) hf atS c ft st st' n cols r h1 h2
      h3 h4).1 h
  obtain ⟨tl', e, hs⟩ := atS_lay st st' _ _ hl
  rw [hst] at e
  obtain rfl : tl = tl' := by simpa using e
  rw [firstColumns_of_tests tl p he] at hs
  exact ⟨hf, hs, hn⟩

/-! ## What the block leaves as it was -/

theorem putTl_fork (s : S) (tl : HTailF2) : (s.putTl tl).fork? = s.fork? := by
  unfold S.putTl S.fork?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

theorem putTl_link (s : S) (tl : HTailF2) : (s.putTl tl).link? = s.link? := by
  unfold S.putTl S.link?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho]
  | _ => simp [h]

theorem putTl_tl (s : S) (t tl : HTailF2) (ht : s.tl? = some t) : (s.putTl tl).tl? = some tl := by
  unfold S.tl? at ht
  unfold S.putTl S.tl?
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [h, ho] at ht ⊢
  | lay a => simp
  | att a => simp
  | between => simp [h] at ht
  | fin a => simp [h] at ht
  | mem a => simp [h] at ht

theorem putTl_rest (s : S) (tl : HTailF2) :
    (s.putTl tl).st = s.st ∧ (s.putTl tl).book = s.book ∧ (s.putTl tl).roots = s.roots ∧
      (s.putTl tl).rowsOwed = s.rowsOwed ∧ (s.putTl tl).failed = s.failed ∧ (s.putTl tl).check =
          s.check ∧
      (s.putTl tl).out = s.out ∧ (s.putTl tl).req = s.req := by
  unfold S.putTl
  cases h : s.here with
  | head a => by_cases ho : a.opened <;> simp [ho]
  | _ => simp

/-- **The block fills no slot and lays no mark.** A yes leaves the ledger, the link's record, the
chain's statement, the book of trees, the count of roots, what is owed, the mark, the state of the
calls, what was put out and the request as they were: of the carried record it turns the smallness
test's record alone, and of that the two fields of `yes_atS`. -/
theorem yes_atS_frame {Cl : Type} (p : Par) (tl : HTailF2) (c : (wRound (rd p)).Chal)
    (ft : Nat) (st st' : S) (n : Nat) (cols : List Col) (r : Fmt.RoundView) (hst : st.tl? = some tl)
    (h1 : r.vals = []) (h2 : r.drawn.elems = []) (h3 : r.drawn.poss = []) (h4 : r.drawn.trits =
        kitTrits c)
    (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st [r] cols = .ok (st', n)) :
    st'.fork? = st.fork? ∧ st'.link? = st.link? ∧ st'.st = st.st ∧ st'.book = st.book ∧ st'.roots =
        st.roots ∧
      st'.rowsOwed = st.rowsOwed ∧ st'.failed = st.failed ∧ st'.check = st.check ∧ st'.out = st.out
          ∧
      st'.req = st.req := by
  obtain ⟨_, rfl, _⟩ := yes_atS (Cl := Cl) p tl c ft st st' n cols r hst h1 h2 h3 h4 h
  exact ⟨putTl_fork _ _, putTl_link _ _, putTl_rest _ _⟩

/-- The proved block's one condition on public numbers holds at the library's sizes of every record
(the library's `sizeOf_ok`): so the block is good at every caller with these sizes. -/
theorem block_good_atS (d : VerifiableInference.OnPublicFiles.TailCallerOn) (tl : HTailF2)
    (h : d.c.s = (OnBytes.Tie.Pv.Tail.sizeOf tl).size) : (KObj.KTailRngOn.blk d).Good :=
  block_good d (h ▸ sizeOf_ok tl)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.yes_atS_frame
#print axioms VerifiableInference.Desc.First.K8.putTl_tl
#print axioms VerifiableInference.Desc.First.K8.block_good_atS
#print axioms VerifiableInference.Desc.First.K8.fits_parOf
#print axioms VerifiableInference.Desc.First.K8.firstColumns_parOf
#print axioms VerifiableInference.Desc.First.K8.fits_of_tests
#print axioms VerifiableInference.Desc.First.K8.yes_atS
