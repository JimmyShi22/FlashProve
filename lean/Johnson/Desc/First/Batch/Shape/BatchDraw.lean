-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/BatchDraw.lean: THE BATCHING's DRAW (K9.drawAlone with K9.drawnClean,
Johnson/Desc/First/Batch/Kind.lean) against the shape of the first chain's state (chainSh,
Johnson/Desc/First/Shape/Chain.lean): one step on the shape, and the two laws at the bare
sub-protocol's decision. General laws; nothing is evaluated.

  `set_sh`: laying the segment's part back, seen through the shape: four components are laid.
  `usedSh`, `usedOf_sh`: the slots that the open segment's messages have taken, on the shape.
  `fillT`, `fillS`, `fill_sh`: t2FillL (OnBytes/Model/Trees.lean) on shapes: each virtual row of a
    listed array gets K column weights.
  `drawB`: the seven tests on numbers and marks: K9.nothing-owed · slots-used · link-ready ·
    drawn-once · claims-planned · no-claim-yet · a-coefficient-a-slot.
  **`drawG rows`**: THE STEP: a link's context, a ledger and the smallness test's structure are
    there, the slots in use are told, drawB accepts: then: rows are owed; the link's list notes the
    slots in use, and the link is handed; the ledger is filled, its element drawn, and no claim's
    weight is handed out yet.
  **`draw_carries`**: the decision accepts from s to t: then drawG returns chainSh t at chainSh s.
  **`draw_returns`**: drawG returns at chainSh s, the round has drawn just one element, AND THE ONE
    TEST ON VALUES accepts (K9.ledger-empty: every column weight, every slot's coefficient and the
    constant are 0): then the decision accepts.

Limits. ledgerEmpty is a premise at the state. The bare sub-protocol. That drawG returns at a shape
that the chain reaches is not shown. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.DoorChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-! ## 1 The part laid back -/

theorem set_sh (s : S) (P : Part) :
    chainSh (atS.set s P) = ((((chainSh s).setLink (linkSh P.L)).setLed (ledSh P.F)).setCore
      (Ground.Sh.coreSh ⟨P.d.st, s.book, s.roots⟩)).setRowsOwed P.owed := by
  have e : ∀ (z : S) (st' : Statement) (o : Option Nat),
      chainSh { z with st := st', rowsOwed := o } =
        ((chainSh z).setCore (Ground.Sh.coreSh ⟨st', z.book, z.roots⟩)).setRowsOwed o :=
    fun _ _ _ => rfl
  have eb : ((s.putLink P.L).putFork P.F).book = s.book ∧
      ((s.putLink P.L).putFork P.F).roots = s.roots := by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> (try (rename_i a; cases hO : a.opened)) <;> simp_all [S.putLink, S.putFork]
  show chainSh { (s.putLink P.L).putFork P.F with st := P.d.st, rowsOwed := P.owed } = _
  rw [e, eb.1, eb.2, chainSh_putFork, chainSh_putLink]

theorem chainSh_core (s : S) :
    (chainSh s).core = Ground.Sh.coreSh ⟨s.st, s.book, s.roots⟩ := rfl

/-- Laying a shape's own core back turns nothing, in the one form in which it is spent here. -/
theorem core_same (a : ChainSh) (L : LinkSh) (F : LedSh) (r : Option Nat) :
    (((a.setLink L).setLed F).setCore a.core).setRowsOwed r =
      ((a.setLink L).setLed F).setRowsOwed r := rfl

/-- The slots that the open segment's messages have taken, on the shape. -/
def usedSh (a : ChainSh) : Option Nat :=
  match a.here with
  | 1 => a.tl.map (·.slotB)
  | 2 => a.led.map (·.next)
  | 3 => a.head.bind (·.slot)
  | _ => none

theorem usedOf_sh (s : S) : usedOf s = usedSh (chainSh s) := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head a =>
    cases ho : a.opened <;>
      simp [usedOf, usedSh, chainSh, ChainSh.mk, ChainSh.here, ChainSh.head, hereNo, headOf, headSh,
        ho]
  | _ => rfl

/-! ## 2 The filling -/

/-- An array's shape with K column weights on every virtual row. -/
def fillT (X : TreeSh) : TreeSh :=
  X.setRows (X.rows.map fun r =>
    if r.entries != X.K then RowSh.mk r.coef X.K r.col0 r.form r.ones r.first else r)

/-- The first n arrays filled. -/
def fillS (trees : List TreeSh) (n : Nat) : List TreeSh :=
  (List.range n).foldl (fun t ti => modAt t ti fillT) trees

theorem fill_one (X : HTree) :
    treeSh { X with rows := X.rows.map fun r =>
      if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r } =
      fillT (treeSh X) := by
  show TreeSh.mk X.name (X.kind == .symbols) X.R X.K ((X.rows.map _).toList.map rowSh)
      X.root.isSome =
    TreeSh.mk X.name (X.kind == .symbols) X.R X.K ((X.rows.toList.map rowSh).map _) X.root.isSome
  congr 1
  rw [Array.toList_map, List.map_map, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  show rowSh (if r.L.size != X.K then { r with L := Array.replicate X.K zeroE } else r) =
    (if r.L.size != X.K then
      RowSh.mk r.coef.size X.K r.L0 r.rowForm r.rowOnes r.rowFirst else rowSh r)
  split
  · show RowSh.mk r.coef.size (Array.replicate X.K zeroE).size r.L0 r.rowForm r.rowOnes
      r.rowFirst = _
    rw [Array.size_replicate]
  · rfl

theorem fill_sh (F : Fork) (T : Tail2) :
    (t2FillL F T).trees.toList.map treeSh = fillS (F.trees.toList.map treeSh) T.nt.size := by
  unfold t2FillL fillS
  dsimp only
  generalize List.range T.nt.size = l
  generalize F.trees = trees
  induction l generalizing trees with
  | nil => rfl
  | cons ti l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, map_modify trees ti _ treeSh fillT fill_one]

/-! ## 3 The step -/

/-- The seven tests on numbers and marks. -/
def drawB (owed : Option Nat) (used : Nat) (L : LinkSh) (F : LedSh) : Bool :=
  owed.isNone && (L.list.planned && used == F.ns) &&
    (L.list.link && !L.handed && L.moments == L.check.blank.momentsOf L.link) && !F.drawn &&
    F.planClaims != 0 && F.claims == 0 && F.coefs == F.ns

/-- The link's context behind the draw, on shapes. -/
def drawnLink (L : LinkSh) (used : Nat) : LinkSh :=
  { L with list := { L.list with used := used }, handed := true }

/-- The ledger behind the draw, on shapes. -/
def drawnLed (F : LedSh) (n : Nat) : LedSh :=
  LedSh.mk F.ns F.shown F.factors F.got F.owed F.planClaims (fillS F.trees n) F.next F.coefs
    F.claims true (List.replicate F.planClaims false) F.shut

/-- **THE STEP ON THE SHAPE.** rows: the rows that the round's entry counts. -/
def drawG (rows : Nat) (a : ChainSh) : Except String ChainSh :=
  match a.link, a.led, a.tl, usedSh a with
  | some L, some F, some _, some used =>
    if drawB (owedSh a) used L F then
      .ok (((a.setLink (drawnLink L used)).setLed (drawnLed F L.list.nt.size)).setRowsOwed
        (some rows))
    else .error "the batching draw: the shape"
  | _, _, _, _ => .error "K9.in-a-segment"

/-- drawnClean, cut. -/
theorem clean_iff (rows : Nat) (chi : E) (owed : RowsOwed) (used : Nat) (L : LinkCtx) (F : Fork)
    (o : Drawn) :
    drawnClean rows chi owed used L F = .ok o ↔
      drawB owed used (linkSh L) (ledSh F) = true ∧ ledgerEmpty F = true ∧
        o = { owed := some rows
              L := { L with list := { L.list with used := used }, handed := true }
              F := { t2FillL F L.list with
                theta := chi, thetaDrawnF := true
                kapMapF := Array.replicate F.planClaimsF false } } := by
  unfold drawnClean drawn drawB
  show _ ↔ (owed.isNone && (L.list.planned && used == F.ns) &&
    (L.list.link && !L.handed && L.moments == L.check.momentsOf L.link) && !F.thetaDrawnF &&
    F.planClaimsF != 0 && F.nClaim == 0 && F.LS.size == F.ns) = true ∧ _
  simp only [ans_bind, need_ok, exists_const, Bool.and_eq_true]
  constructor
  · rintro ⟨x, ⟨a1, a2, a3, a4, a5, e⟩, a6, a7, a8, e'⟩
    obtain rfl := Except.ok.inj e
    obtain rfl := Except.ok.inj e'
    exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a7⟩, a8⟩, a6, rfl⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a7⟩, a8⟩, a6, rfl⟩
    exact ⟨_, ⟨a1, a2, a3, a4, a5, rfl⟩, a6, a7, a8, rfl⟩

theorem led_drawn (F : Fork) (T : Tail2) (chi : E) :
    ledSh { t2FillL F T with theta := chi, thetaDrawnF := true
                             kapMapF := Array.replicate F.planClaimsF false } =
      drawnLed (ledSh F) T.nt.size := by
  show LedSh.mk F.ns F.vp.size F.mf.size F.gotF.toList (F.owed.toList.map (·.added)) F.planClaimsF
    ((t2FillL F T).trees.toList.map treeSh) F.next F.LS.size F.nClaim true
    (Array.replicate F.planClaimsF false).toList F.doorShutF = _
  rw [fill_sh, Array.toList_replicate]
  rfl

variable {Cl : Type}

/-- The decision of the draw, cut. -/
theorem drawAlone_iff (p : Where) (s t : S) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (drawAlone (Cl := Cl) atS p).decide s [r] gs = .ok t ↔
      ∃ P chi o, atS.get? s = some P ∧ chiOf r = .ok chi ∧
        drawnClean p.rows chi P.owed P.used P.L P.F = .ok o ∧
        t = atS.set s { P with owed := o.owed, L := o.L, F := o.F } := by
  show (atS.part s >>= fun P => chiOf r >>= fun chi =>
    drawnClean p.rows chi P.owed P.used P.L P.F >>= fun o =>
      (pure (atS.set s { P with owed := o.owed, L := o.L, F := o.F }) : Ans S)) = .ok t ↔ _
  simp only [ans_bind]
  constructor
  · rintro ⟨P, hP, chi, hc, o, ho, e⟩
    exact ⟨P, chi, o, (there_ok _ _ _).1 hP, hc, ho, (Except.ok.inj e).symm⟩
  · rintro ⟨P, chi, o, hP, hc, ho, rfl⟩
    exact ⟨P, (there_ok _ _ _).2 hP, chi, hc, o, ho, rfl⟩

/-- The segment's part, read through the shape: its link, ledger, slots in use, rows owed and
statement. Of P.laid, P.d.book and P.d.roots it says nothing: the record under "there is" is tied to
the shape's tl alone. -/
theorem part_sh {s : S} {P : Part} (h : atS.get? s = some P) :
    (chainSh s).link = some (linkSh P.L) ∧ (chainSh s).led = some (ledSh P.F) ∧
      (∃ tl, (chainSh s).tl = some (tailSh tl)) ∧ usedSh (chainSh s) = some P.used ∧
      P.owed = owedSh (chainSh s) ∧ P.d.st = s.st := by
  have h' : (do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    let used ← usedOf s
    pure ({ owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } :
      Part) : Option Part) = some P := h
  cases hL : s.link? with
  | none => rw [hL] at h'; exact nomatch h'
  | some L =>
    cases hF : s.fork? with
    | none => rw [hL, hF] at h'; exact nomatch h'
    | some F =>
      cases ht : s.tl? with
      | none => rw [hL, hF, ht] at h'; exact nomatch h'
      | some tl =>
        cases hu : usedOf s with
        | none => rw [hL, hF, ht, hu] at h'; exact nomatch h'
        | some u =>
          rw [hL, hF, ht, hu] at h'
          obtain rfl := Option.some.inj h'
          refine ⟨?_, ?_, ⟨tl, ?_⟩, ?_, rfl, rfl⟩
          · show s.link?.map linkSh = _
            rw [hL]
            rfl
          · show s.fork?.map ledSh = _
            rw [hF]
            rfl
          · show s.tl?.map tailSh = _
            rw [ht]
            rfl
          · rw [← usedOf_sh, hu]

theorem draw_carries (p : Where) (s t : S) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (drawAlone (Cl := Cl) atS p).decide s [r] gs = .ok t) :
    drawG p.rows (chainSh s) = .ok (chainSh t) := by
  obtain ⟨P, chi, o, hP, -, ho, rfl⟩ := (drawAlone_iff p s t r gs).1 h
  obtain ⟨hb, -, rfl⟩ := (clean_iff _ _ _ _ _ _ _).1 ho
  obtain ⟨l1, l2, ⟨tl, l3⟩, l4, l5, l6⟩ := part_sh hP
  unfold drawG
  rw [l1, l2, l3, l4]
  simp only
  rw [← l5, if_pos hb, set_sh]
  dsimp only
  rw [led_drawn, l6, ← chainSh_core]
  exact congrArg Except.ok (core_same _ _ _ _).symm

theorem draw_returns (p : Where) (s : S) (r : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (u : ChainSh) (hg : drawG p.rows (chainSh s) = .ok u) (x : UInt64 × UInt64 × UInt64)
    (hr : r.drawn.elems = [x])
    (hv : ∀ F, s.fork? = some F → ledgerEmpty F = true) :
    ∃ t, (drawAlone (Cl := Cl) atS p).decide s [r] gs = .ok t := by
  unfold drawG at hg
  cases hL : s.link? with
  | none =>
    have : (chainSh s).link = none := by
      show s.link?.map linkSh = _
      rw [hL]
      rfl
    rw [this] at hg
    exact nomatch hg
  | some L =>
    cases hF : s.fork? with
    | none =>
      have a1 : (chainSh s).link = some (linkSh L) := by
        show s.link?.map linkSh = _
        rw [hL]
        rfl
      have a2 : (chainSh s).led = none := by
        show s.fork?.map ledSh = _
        rw [hF]
        rfl
      rw [a1, a2] at hg
      exact nomatch hg
    | some F =>
      cases ht : s.tl? with
      | none =>
        have a1 : (chainSh s).link = some (linkSh L) := by
          show s.link?.map linkSh = _
          rw [hL]
          rfl
        have a2 : (chainSh s).led = some (ledSh F) := by
          show s.fork?.map ledSh = _
          rw [hF]
          rfl
        have a3 : (chainSh s).tl = none := by
          show s.tl?.map tailSh = _
          rw [ht]
          rfl
        rw [a1, a2, a3] at hg
        exact nomatch hg
      | some tl =>
        have a1 : (chainSh s).link = some (linkSh L) := by
          show s.link?.map linkSh = _
          rw [hL]
          rfl
        have a2 : (chainSh s).led = some (ledSh F) := by
          show s.fork?.map ledSh = _
          rw [hF]
          rfl
        have a3 : (chainSh s).tl = some (tailSh tl) := by
          show s.tl?.map tailSh = _
          rw [ht]
          rfl
        rw [a1, a2, a3, ← usedOf_sh] at hg
        cases hu : usedOf s with
        | none => rw [hu] at hg; exact nomatch hg
        | some used =>
          rw [hu] at hg
          simp only at hg
          split at hg
          · rename_i hb
            have hP : atS.get? s = some
                { owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
                  d := { st := s.st, book := s.book, roots := s.roots, opened := [],
                         loc := () } } := by
              show (do
                let L ← s.link?
                let F ← s.fork?
                let tl ← s.tl?
                let used ← usedOf s
                pure ({ owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
                        d := { st := s.st, book := s.book, roots := s.roots, opened := [],
                               loc := () } } : Part) : Option Part) = _
              rw [hL, hF, ht, hu]
              rfl
            have hc : chiOf r = .ok (E.ofTriple x) := by
              unfold chiOf
              rw [hr]
              rfl
            exact ⟨_, (drawAlone_iff p s _ r gs).2 ⟨_, _, _, hP, hc,
              (clean_iff _ _ _ _ _ _ _).2 ⟨hb, hv F hF, rfl⟩, rfl⟩⟩
          · exact nomatch hg

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.clean_iff
#print axioms VerifiableInference.Desc.K9.Shape.draw_carries
#print axioms VerifiableInference.Desc.K9.Shape.draw_returns
#print axioms VerifiableInference.Desc.K9.Shape.set_sh
#print axioms VerifiableInference.Desc.K9.Shape.usedOf_sh
#print axioms VerifiableInference.Desc.K9.Shape.fill_sh
#print axioms VerifiableInference.Desc.K9.Shape.chainSh_core
#print axioms VerifiableInference.Desc.K9.Shape.core_same
#print axioms VerifiableInference.Desc.K9.Shape.usedSh
#print axioms VerifiableInference.Desc.K9.Shape.fillT
#print axioms VerifiableInference.Desc.K9.Shape.fillS
#print axioms VerifiableInference.Desc.K9.Shape.fill_one
#print axioms VerifiableInference.Desc.K9.Shape.drawB
#print axioms VerifiableInference.Desc.K9.Shape.drawnLink
#print axioms VerifiableInference.Desc.K9.Shape.drawnLed
#print axioms VerifiableInference.Desc.K9.Shape.drawG
#print axioms VerifiableInference.Desc.K9.Shape.led_drawn
#print axioms VerifiableInference.Desc.K9.Shape.drawAlone_iff
#print axioms VerifiableInference.Desc.K9.Shape.part_sh
