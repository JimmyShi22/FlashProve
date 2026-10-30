-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorChain.lean: the sub-protocol without a round "K9: the one
equation" against the shape of the first chain's state (chainSh,
Johnson/Desc/First/Shape/Chain.lean): ONE STEP ON THE SHAPE, and the laws "carries" and "returns"
for the bare sub-protocol's decision. General laws; nothing is evaluated.

  `eqSh`, `doorSh`, `laidSh`, `owedSh`: the tests eqB and doorB (DoorCut.lean), the number of
    indices that is laid and the count of rows owed, ON SHAPES. `eqB_sh`, `doorB_sh`, `laidOf_sh`,
    `owedOf_sh`: they are the same tests. eqSh's last clause is asked of a list, not of an array by
    index (`all_take`): whoever evaluates it at some thousands of marks is spared the array's loop.
  `shutSh F`: the ledger's shape with the door shut (`ledSh_shut`). `doorS_blank`: a tool.
  **`oneG`**: THE STEP: a link's context, a ledger and the smallness test's structure are there ·
    the number of indices is laid · eqSh and doorSh accept · the door on the shape of statement,
    book and roots returns (doorS, DoorRow.lean): then: the door is shut, that shape is laid, no
    count of rows is owed.
  **`one_carries`**: the decision accepts from s to t and oneG returns u at chainSh s: then
    u = chainSh t.
  `OneRest s`: WHAT THE SHAPE DOES NOT HOLD YET, gathered in one structure: the slots in use are
    told (this one the shape does hold: BatchDraw.lean's usedOf_sh) · FOUR TESTS ON SIZES, read off
    the ledger and the statement themselves: termsB, madeB, seatsB, maskB (three sizes of a virtual
    row are not in the ledger's shape), and that the statement has the link's group · FOUR TESTS ON
    VALUES: outsideV, termsV, slotsV, and padB: the row that is made has no coefficient on a pad.
  **`one_returns`**: oneG returns at chainSh s, and OneRest holds at s: then the decision accepts.
    "The row is made" and "the row fits" are no premises any more: made_pays (DoorMade.lean) and
    fits_pays (DoorFits.lean) are laid in.

Limits. OneRest IS A PREMISE AT THE STATE, NOT AT ITS SHAPE. Its last field, pad, is asked "for
every equation that K9.equation returns and every row that asRow makes". The bare sub-protocol: for
the seated member see Johnson/AtFull/Shape/EquationStepAtHead.lean. That oneG returns at a shape
that the chain reaches, or that OneRest holds in an honest prover's run, is not shown. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.DoorMember
import Johnson.Desc.First.Batch.Shape.DoorFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Ground.Sh (CoreSh)

/-! ## 1 The tests on shapes -/

/-- A test on the first k members of a list, asked through an array's loop by index, is the test on
the list's first k members. General. -/
theorem all_take (p : Bool → Bool) (l : List Bool) (k : Nat) :
    l.toArray.all p 0 k = (l.take k).all p := by
  rw [Bool.eq_iff_iff, Array.all_iff_forall, List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.1 hx
    exact h i (by simp; omega) ⟨Nat.zero_le _, by omega⟩
  · intro h i hi hk
    exact h _ (List.mem_take_iff_getElem.2 ⟨i, by simp at hi; omega, rfl⟩)

/-- eqB (DoorCut.lean) on shapes. Its last clause, "the first used marks are set", is asked of the
list itself, where eqB asks an array by index: all_take ties the two. -/
def eqSh (L : LinkSh) (F : LedSh) : Bool :=
  (L.list.link && !L.list.walked && !L.done) && L.handed &&
    (F.planClaims != 0 && F.claims == F.planClaims) &&
    (F.handed.length == F.planClaims && F.handed.all id) &&
    (L.arrayOf.size == L.list.nt.size) && decide (L.list.nt.size ≤ F.trees.length) &&
    (decide (L.list.used ≤ F.ns) && F.got.length == F.ns && F.coefs == F.ns &&
      F.shown == F.ns && F.factors == F.ns) &&
    F.owed.all id && (F.got.take L.list.used).all id

theorem eqB_sh (L : LinkCtx) (F : Fork) : eqB L F = eqSh (linkSh L) (ledSh F) := by
  unfold eqB eqSh
  show _ = ((L.list.link && !L.list.walked && !L.done) && L.handed &&
    (F.planClaimsF != 0 && F.nClaim == F.planClaimsF) &&
    (F.kapMapF.toList.length == F.planClaimsF && F.kapMapF.toList.all id) &&
    (L.arrayOf.size == L.list.nt.size) &&
    decide (L.list.nt.size ≤ (F.trees.toList.map treeSh).length) &&
    (decide (L.list.used ≤ F.ns) && F.gotF.toList.length == F.ns && F.LS.size == F.ns &&
      F.vp.size == F.ns && F.mf.size == F.ns) &&
    (F.owed.toList.map (·.added)).all id && (F.gotF.toList.take L.list.used).all id)
  rw [← all_take, Array.length_toList, Array.all_toList, List.length_map, Array.length_toList,
    Array.length_toList, List.all_map, Array.all_toList, Array.toArray_toList]
  rfl

def doorSh (owed : Option Nat) (n : Nat) (L : LinkSh) (F : LedSh) : Bool :=
  (owed == some (F.claims + n)) && (L.link == L.check.link) &&
    (L.check.inLink && L.check.moments == L.check.blank.momentsDue)

theorem doorB_sh (owed : Option Nat) (n : Nat) (L : LinkCtx) (F : Fork) :
    doorB owed n L F = doorSh owed n (linkSh L) (ledSh F) := rfl

def laidSh (t : TailSh) : Option Nat :=
  if t.eqFirst.size != t.NM + 1 then none
  else some (t.eqFirst.getD t.NM 0 + t.nX4Laid * 2 ^ clog2 t.tau)

theorem laidOf_sh (tl : HTailF2) : laidOf tl = laidSh (tailSh tl) := rfl

def owedSh (a : ChainSh) : Option Nat :=
  match a.rowsOwed with
  | some 0 => none
  | x => x

theorem owedOf_sh (s : S) : owedOf s = owedSh (chainSh s) := rfl

/-- The ledger's shape with the door shut. -/
def shutSh (F : LedSh) : LedSh :=
  LedSh.mk F.ns F.shown F.factors F.got F.owed F.planClaims F.trees F.next F.coefs F.claims F.drawn
    F.handed true

theorem ledSh_shut (F : Fork) : ledSh { F with doorShutF := true } = shutSh (ledSh F) := rfl

theorem doorS_blank (f : ReqFrame) (n g : Nat) (a : CoreSh) :
    doorS (frameSh f).blank n g a = doorS f n g a := rfl

/-! ## 2 The step -/

/-- **THE STEP ON THE SHAPE.** -/
def oneG (a : ChainSh) : Except String ChainSh :=
  match a.link, a.led, a.tl with
  | some L, some F, some t =>
    match laidSh t with
    | none => .error "K9.equations-laid"
    | some n =>
      if eqSh L F && doorSh (owedSh a) n L (shutSh F) then
        match doorS L.check.frame.blank F.ns L.check.frame.group a.core with
        | some c => .ok (((a.setLed (shutSh F)).setCore c).setRowsOwed none)
        | none => .error "the one equation: the statement's shape"
      else .error "the one equation: the shape"
  | _, _, _ => .error "K9.in-a-segment"

variable {Cl : Type}

theorem one_carries (p : Where) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (u : ChainSh) (h : (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t)
    (hg : oneG (chainSh s) = .ok u) : u = chainSh t := by
  obtain ⟨F, hF, ht⟩ := one_turns p s t rs gs h
  obtain ⟨L, F', hL, hF', hc⟩ := one_core p s t rs gs h
  obtain rfl : F = F' := Option.some.inj (hF.symm.trans hF')
  have ec : coreS t = Ground.Sh.coreSh ⟨t.st, s.book, s.roots⟩ := by
    obtain ⟨e1, e2⟩ := doorS_rest hc
    show CoreSh.mk (Ground.Sh.stSh t.st) (Ground.Sh.bookSh t.book) t.roots =
      CoreSh.mk (Ground.Sh.stSh t.st) (Ground.Sh.bookSh s.book) s.roots
    have e1' : Ground.Sh.bookSh t.book = Ground.Sh.bookSh s.book := e1
    have e2' : t.roots = s.roots := e2
    rw [e1', e2']
  unfold oneG at hg
  have l1 : (chainSh s).link = some (linkSh L) := by
    show s.link?.map linkSh = _
    rw [hL]
    rfl
  have l2 : (chainSh s).led = some (ledSh F) := by
    show s.fork?.map ledSh = _
    rw [hF]
    rfl
  rw [l1, l2] at hg
  cases l3 : (chainSh s).tl with
  | none => rw [l3] at hg; exact nomatch hg
  | some tsh =>
    rw [l3] at hg
    simp only at hg
    cases l4 : laidSh tsh with
    | none => rw [l4] at hg; exact nomatch hg
    | some n =>
      rw [l4] at hg
      simp only at hg
      split at hg
      · have hc' : doorS (linkSh L).check.frame.blank (ledSh F).ns (linkSh L).check.frame.group
            (chainSh s).core = some (coreS t) := hc
        rw [hc'] at hg
        rw [ht, ← ec, ledSh_shut]
        exact (Except.ok.inj hg).symm
      · exact nomatch hg

/-- **What the shape does not hold yet.** -/
structure OneRest (s : S) : Prop where
  /-- the slots in use are told -/
  used : (usedOf s).isSome = true
  /-- tests on sizes, read off the ledger and the statement themselves -/
  terms : ∀ L F, s.link? = some L → s.fork? = some F →
    termsB L { F with doorShutF := true } = true ∧
      madeB L { F with doorShutF := true } s.st = true ∧
      ∃ G, s.st.groups[L.check.group]? = some G ∧
        seatsB L { F with doorShutF := true } s.st G = true ∧
        maskB L.check.frame s.st G F.ns = true
  /-- three tests on values -/
  values : ∀ L F, s.link? = some L → s.fork? = some F →
    outsideV L F = true ∧ termsV L { F with doorShutF := true } = true ∧
      slotsV { F with doorShutF := true } = true
  /-- the fourth test on values: the row that is made has no coefficient on a pad -/
  pad : ∀ L F q F' y, s.link? = some L → s.fork? = some F → equation L F = .ok (q, F') →
    asRow L.check.rows L.check.frame q
      ({ st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } : St Unit) =
        .ok y →
    padB y.2.st L.check.group y.1 = true

theorem one_returns (p : Where) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (u : ChainSh) (hg : oneG (chainSh s) = .ok u) (hR : OneRest s) :
    ∃ t, (oneEquation (Cl := Cl) atS p).decide s rs gs = .ok t := by
  unfold oneG at hg
  cases hL : s.link? with
  | none =>
    have l1 : (chainSh s).link = none := by
      show s.link?.map linkSh = _
      rw [hL]
      rfl
    rw [l1] at hg
    exact nomatch hg
  | some L =>
    cases hF : s.fork? with
    | none =>
      have l1 : (chainSh s).link = some (linkSh L) := by
        show s.link?.map linkSh = _
        rw [hL]
        rfl
      have l2 : (chainSh s).led = none := by
        show s.fork?.map ledSh = _
        rw [hF]
        rfl
      rw [l1, l2] at hg
      exact nomatch hg
    | some F =>
      cases hT : s.tl? with
      | none =>
        have l1 : (chainSh s).link = some (linkSh L) := by
          show s.link?.map linkSh = _
          rw [hL]
          rfl
        have l2 : (chainSh s).led = some (ledSh F) := by
          show s.fork?.map ledSh = _
          rw [hF]
          rfl
        have l3 : (chainSh s).tl = none := by
          show s.tl?.map tailSh = _
          rw [hT]
          rfl
        rw [l1, l2, l3] at hg
        exact nomatch hg
      | some tl =>
        have l1 : (chainSh s).link = some (linkSh L) := by
          show s.link?.map linkSh = _
          rw [hL]
          rfl
        have l2 : (chainSh s).led = some (ledSh F) := by
          show s.fork?.map ledSh = _
          rw [hF]
          rfl
        have l3 : (chainSh s).tl = some (tailSh tl) := by
          show s.tl?.map tailSh = _
          rw [hT]
          rfl
        rw [l1, l2, l3] at hg
        simp only at hg
        obtain ⟨us, hu⟩ := Option.isSome_iff_exists.1 hR.used
        have hP : atS.get? s = some
            { owed := owedOf s, used := us, laid := laidOf tl, L := L, F := F,
              d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } := by
          show (do
            let L ← s.link?
            let F ← s.fork?
            let tl ← s.tl?
            let used ← usedOf s
            pure ({ owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
                    d := { st := s.st, book := s.book, roots := s.roots, opened := [],
                           loc := () } } : Part) : Option Part) = _
          rw [hL, hF, hT, hu]
          rfl
        cases l4 : laidSh (tailSh tl) with
        | none => rw [l4] at hg; exact nomatch hg
        | some n =>
          rw [l4] at hg
          simp only at hg
          split at hg
          · rename_i hb
            rw [Bool.and_eq_true] at hb
            cases hc : doorS (linkSh L).check.frame.blank (ledSh F).ns
                (linkSh L).check.frame.group (chainSh s).core with
            | none => rw [hc] at hg; exact nomatch hg
            | some c =>
              obtain ⟨t1, t2, G, hG, t3, t4⟩ := hR.terms L F hL hF
              obtain ⟨v1, v2, v3⟩ := hR.values L F hL hF
              exact one_accepts p s rs gs _ n c hP l4 (by rw [eqB_sh]; exact hb.1) t1 hb.2 hc
                v1 v2 v3 (fun q F' hq => made_pays L F s.st t2 q F' hq)
                (fun q F' y hq hy => fits_pays L F _ G hG t3 t4
                  (fun q F' y hq hy => hR.pad L F q F' y hL hF hq hy) q F' y hq hy)
          · exact nomatch hg

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.all_take
#print axioms VerifiableInference.Desc.K9.Shape.eqB_sh
#print axioms VerifiableInference.Desc.K9.Shape.one_carries
#print axioms VerifiableInference.Desc.K9.Shape.one_returns
#print axioms VerifiableInference.Desc.K9.Shape.eqSh
#print axioms VerifiableInference.Desc.K9.Shape.doorSh
#print axioms VerifiableInference.Desc.K9.Shape.doorB_sh
#print axioms VerifiableInference.Desc.K9.Shape.laidSh
#print axioms VerifiableInference.Desc.K9.Shape.laidOf_sh
#print axioms VerifiableInference.Desc.K9.Shape.owedSh
#print axioms VerifiableInference.Desc.K9.Shape.owedOf_sh
#print axioms VerifiableInference.Desc.K9.Shape.shutSh
#print axioms VerifiableInference.Desc.K9.Shape.ledSh_shut
#print axioms VerifiableInference.Desc.K9.Shape.doorS_blank
#print axioms VerifiableInference.Desc.K9.Shape.oneG
#print axioms VerifiableInference.Desc.K9.Shape.OneRest
