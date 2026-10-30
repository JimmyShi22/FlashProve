-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/TablesAgree.lean: kind K5: a segment's tables are made by two texts,
and the two give one value. The step that closes the list of tables makes them by Tab.tables
(Johnson/Desc/First/Att/Tables.lean), over the plain records of OnBytes/Model; the claims make them
anew by tablesP (Johnson/Desc/First/Att/TablesP.lean), over the kind's own records.

Main names:
  `Spec.TablesOne`, `tables_one`: at all shapes, matrices, lengths, lookup's records and four
    records: tablesP (geoOf S) (matsOf mats) nW (lookOf S.cf.lmb g) (ptsOfOwn planes scores d x) =
    (Tab.tables S mats nW g planes scores d x).map tabsFull. They refuse together; where they
    return, all 23 fields are one (`tabsFull`: field for field; the list for the smallness test
    member by member: `funOf`).
  `tablesAgree_of`: where the carried record's tables were made by Tab.tables from its own four
    records and lookup's record, TablesAgree (Johnson/Desc/First/Att/Claims/Seated.lean) holds.
  `Sim φ r r'`: a routine of the one state monad and one of the other, from states that are one
    (`plOf`), refuse together or return values that are one under φ and end in states that are one.
    Rules: pure, bind, lift, must, mapM, forM, discard; then routine by routine (add, total, addAs,
    lng, addRow, addLong, placeAll).
Used of OnBytes: plain records, pure functions and lemmas on them alone; no routine in a context and
no theorem on a run: the records Attention.Placed, Tables, ScoreTables, the four records, Shape,
Model.HFun, TMat, Forest.Heard; the pure functions Attention.fits, lastCoords, lastN, tok,
scoreTiles, pointM, pointD, mergedPlanes, mergedTokens, tileSums, Model.eqTab, cutLast, blockRows
(through Tables.lean); the seat's tool lookOf (Forest.planeCols, phiB, phiP: named, not opened).
Not claimed: that the tables are right.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Any
import Johnson.Desc.First.Att.Tables

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (TablesP ScoreT Fun1 geoOf ptsOfOwn lookOf)

variable {α β γ δ : Type}

def funOf (f : HFun) : Fun1 := { mat := f.mat, len := f.len, phi := f.phi, tree := f.tree, start := f.start }

/-- The record of OnBytes/Model of the tables placed so far, as the kind's. -/
def plOf (t : Attention.Placed) : P.Placed := { next := t.next, tabLen := t.tabLen, funs := t.funs.map funOf }

/-- The record of OnBytes/Model of tables as the kind's, all 23 fields. -/
def tabsFull (t : Attention.Tables) : TablesP := { tabsOld t with funs := t.funs.map funOf }

theorem strip_full (t : Attention.Tables) : stripT (tabsFull t) = tabsOld t := rfl

/-- From states that are one: both refuse, or the values are one under φ and the states are one. -/
def Sim (φ : α → β) (r : Tab.T α) (r' : P.T β) : Prop :=
  ∀ st, r' (plOf st) = (r st).map fun x => (φ x.1, plOf x.2)

theorem Sim.pure (φ : α → β) (a : α) : Sim φ (Pure.pure a) (Pure.pure (φ a)) := fun _ => rfl

theorem Sim.bind {φ : α → β} {ψ : γ → δ} {r : Tab.T α} {r' : P.T β} {k : α → Tab.T γ}
    {k' : β → P.T δ} (h1 : Sim φ r r') (h2 : ∀ a, Sim ψ (k a) (k' (φ a))) :
    Sim ψ (r >>= k) (r' >>= k') := by
  intro st
  have e := h1 st
  show (r' (plOf st)).bind (fun x => k' x.1 x.2) = ((r st).bind fun x => k x.1 x.2).map _
  rw [e]
  cases r st with
  | none => rfl
  | some x => exact h2 x.1 x.2

theorem Sim.lift {φ : α → β} {x : Option α} {x' : Option β} (h : x' = x.map φ) :
    Sim φ (monadLift x : Tab.T α) (monadLift x' : P.T β) := by
  intro st
  subst h
  cases x <;> rfl

theorem Sim.must (n n' : String) {b b' : Bool} (h : b' = b) :
    Sim id (monadLift (Tab.mustAs n b) : Tab.T Unit) (monadLift (P.mustAs n' b') : P.T PUnit) := by
  subst h
  refine Sim.lift ?_
  unfold Tab.mustAs P.mustAs
  cases b' <;> rfl

theorem Sim.cast {φ : α → β} {r : Tab.T α} {r' r'' : P.T β} (h : Sim φ r r') (e : r' = r'') :
    Sim φ r r'' := e ▸ h

theorem Sim.forM {ι : Type} {f : ι → Tab.T PUnit} {f' : ι → P.T PUnit} (hf : ∀ a, Sim id (f a) (f' a)) :
    ∀ xs : List ι, Sim id (xs.forM f) (xs.forM f')
  | [] => Sim.pure id _
  | a :: xs => Sim.bind (hf a) fun _ => Sim.forM hf xs

theorem Sim.discard {φ : α → β} {r : Tab.T α} {r' : P.T β} (h : Sim φ r r') :
    Sim id (discard r) (discard r') := by
  intro st
  have e := h st
  show (r' (plOf st)).bind (fun x => some (PUnit.unit, x.2)) = ((r st).bind fun x => some (PUnit.unit, x.2)).map _
  rw [e]
  cases r st <;> rfl

theorem Sim.mapML {ι κ : Type} (c : ι → κ) {f : ι → Tab.T α} {f' : κ → P.T α}
    (hf : ∀ a, Sim id (f a) (f' (c a))) : ∀ xs : List ι, Sim id (xs.mapM f) ((xs.map c).mapM f')
  | [] => by
    simp only [List.map_nil, List.mapM_nil]
    exact Sim.pure id _
  | a :: xs => by
    simp only [List.map_cons, List.mapM_cons]
    exact Sim.bind (hf a) fun _ => Sim.bind (Sim.mapML c hf xs) fun _ => Sim.pure id _

theorem Sim.mapM {ι κ : Type} (c : ι → κ) {f : ι → Tab.T α} {f' : κ → P.T α}
    (hf : ∀ a, Sim id (f a) (f' (c a))) (xs : Array ι) : Sim id (xs.mapM f) ((xs.map c).mapM f') := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, Array.toList_map, map_eq_pure_bind,
    map_eq_pure_bind]
  exact Sim.bind (Sim.mapML c hf _) fun _ => Sim.pure id _

/-! ### the routines -/

/-- The matrices as the kind takes them: (rows, columns). -/
def matsOf (mats : Array TMat) : Array (ℕ × ℕ) := mats.map fun M => (M.m, M.k)

theorem fits_old (mats : Array TMat) (mat len elems : ℕ) :
    P.fits (matsOf mats) mat len elems = Attention.fits mats mat len elems := by
  unfold P.fits Attention.fits matsOf
  rw [Array.getElem?_map]
  cases mats[mat]? <;> rfl

theorem sim_add (mats : Array TMat) (mat len : ℕ) (phi : Array E) (elems : ℕ) :
    Sim id (Tab.add mats mat len phi elems) (P.add (matsOf mats) mat len phi elems) := by
  intro st
  unfold Tab.add P.add Tab.mustAs P.mustAs
  rw [fits_old]
  cases Attention.fits mats mat len elems
  · rfl
  · show some _ = some _
    unfold plOf
    simp only [Array.map_push, id]
    rfl

theorem sim_total (start : ℕ) : Sim id (Tab.T.total start) (P.T.total start) := fun _ => rfl

theorem sim_placed : Sim plOf Tab.T.placed P.T.placed := fun _ => rfl

theorem sim_weights (n n' : ℕ) (f f' : Unit → Array E) (h : f' () = f ()) :
    Sim id (Tab.T.weights n f) (P.T.weights n' f') := by
  unfold Tab.T.weights P.T.weights
  rw [h]
  exact Sim.pure id _

theorem sim_addAs (S : Shape) (mats : Array TMat) (phi phi' : Unit → Array E) (h : phi' () = phi ()) :
    Sim id (Tab.addAs S mats phi) (P.addAs (geoOf S) (matsOf mats) phi') := by
  unfold Tab.addAs P.addAs
  refine Sim.bind (sim_weights _ _ _ _ h) fun w => Sim.bind sim_placed fun st => ?_
  exact Sim.bind (Sim.forM (fun q => Sim.discard (sim_add mats q _ w _)) _) fun _ =>
    Sim.bind (sim_total _) fun _ => Sim.pure id _

theorem sim_getAs (n n' : String) {φ : α → β} {x : Option α} {x' : Option β} (h : x' = x.map φ) :
    Sim φ (Tab.T.getAs n x) (P.T.getAs n' x') := by
  subst h
  cases x
  · exact fun _ => rfl
  · exact Sim.pure φ _

theorem sim_lng (S : Shape) (zc : Array E) (ptk ptk' : Unit → Array E) (h : ptk' () = ptk ()) :
    Sim id (Tab.lng S zc ptk) (P.lng (geoOf S) zc ptk') := by
  unfold Tab.lng P.lng
  refine Sim.bind (sim_weights _ _ _ _ h) fun w => Sim.bind (Sim.must _ _ rfl) fun _ => ?_
  refine Sim.bind (φ := id) (sim_getAs _ _ ?_) fun c => sim_weights _ _ _ _ rfl
  rw [cutLast_old, Option.map_id]
  rfl

theorem sim_addRow (S : Shape) (mats : Array TMat) (psi psi' : Unit → Array E) (h : psi' () = psi ()) :
    Sim id (Tab.addRow S mats psi) (P.addRow (geoOf S) (matsOf mats) psi') := by
  unfold Tab.addRow P.addRow
  exact Sim.bind (sim_weights _ _ _ _ h) fun w => sim_add mats _ _ w _

theorem sim_addLong (S : Shape) (mats : Array TMat) (mat : ℕ) (zc : Array E)
    (ptk ptk' : Unit → Array E) (h : ptk' () = ptk ()) (elems : ℕ) :
    Sim id (Tab.addLong S mats mat zc ptk elems) (P.addLong (geoOf S) (matsOf mats) mat zc ptk' elems) := by
  unfold Tab.addLong P.addLong
  exact Sim.bind (sim_lng S zc _ _ h) fun w => sim_add mats _ _ w _

theorem mergedPlanes_old (n : ℕ) (zx : Array E) (planes : Array PlaneClaim) :
    P.mergedPlanes n zx (planes.map remOf) = Attention.mergedPlanes n zx planes := by
  unfold P.mergedPlanes Attention.mergedPlanes
  rw [Array.all_map]
  rfl

theorem sim_placeAll (S : Shape) (mats : Array TMat) (nW : ℕ) (g : Forest.Heard)
    (planes : Array PlaneClaim) (scores : Array Score) (d : Divide) (x : Attain) :
    Sim tabsFull (Tab.placeAll S mats nW g planes scores d x)
      (P.placeAll (geoOf S) (matsOf mats) nW (lookOf S.cf.lmb g) (ptsOfOwn planes scores d x)) := by
  unfold Tab.placeAll P.placeAll
  refine Sim.bind (Sim.must _ _ (mergedPlanes_old _ _ _)) fun _ => ?_
  refine Sim.bind (sim_addAs S mats _ _ rfl) fun tA => ?_
  refine Sim.bind (sim_addAs S mats _ _ rfl) fun tVM => ?_
  refine Sim.bind (sim_addAs S mats _ _ rfl) fun tVD => ?_
  refine Sim.bind (Sim.mapM scoreOf (fun k => sim_addRow S mats _ _ rfl) scores) fun tM => ?_
  refine Sim.bind (sim_addRow S mats _ _ rfl) fun hW => ?_
  refine Sim.bind (sim_addRow S mats _ _ rfl) fun hX => ?_
  refine Sim.bind (sim_addRow S mats _ _ rfl) fun hE => ?_
  refine Sim.bind (sim_addRow S mats _ _ rfl) fun hT => ?_
  refine Sim.bind (sim_addRow S mats _ _ rfl) fun hPi => ?_
  refine Sim.bind (sim_addRow S mats _ _ rfl) fun hR2 => ?_
  refine Sim.bind (Sim.must _ _ rfl) fun _ => ?_
  refine Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun tO => ?_
  refine Sim.bind (Sim.mapM scoreOf (fun k => Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun tQ =>
    Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun tK => Sim.pure id (tQ, tK)) scores) fun tQK => ?_
  refine Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun qO => ?_
  refine Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun qVM => ?_
  refine Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun qVD => ?_
  refine Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun qF => ?_
  refine Sim.bind (sim_addLong S mats _ _ _ _ rfl _) fun qKx => ?_
  refine Sim.bind (Sim.must _ _ rfl) fun _ => ?_
  refine Sim.bind (sim_weights _ _ _ _ rfl) fun phiB0 => ?_
  refine Sim.bind (sim_add mats _ _ _ _) fun tBit0 => ?_
  refine Sim.bind (sim_weights _ _ _ _ rfl) fun phiB1 => ?_
  refine Sim.bind (sim_add mats _ _ _ _) fun tBit1 => ?_
  refine Sim.bind (sim_weights _ _ _ _ rfl) fun phiP => ?_
  refine Sim.bind (sim_add mats _ _ _ _) fun tPin => ?_
  refine Sim.bind sim_placed fun st => ?_
  refine Sim.bind (Sim.must _ _ rfl) fun _ => ?_
  refine (Sim.pure tabsFull _).cast ?_
  simp only [tabsFull, tabsOld, plOf, Array.map_map, id]
  rfl

namespace Spec

/-- **The two texts that make the tables give one value.** -/
def TablesOne : Prop :=
  ∀ (S : Shape) (mats : Array TMat) (nW : ℕ) (g : Forest.Heard) (planes : Array PlaneClaim)
    (scores : Array Score) (d : Divide) (x : Attain),
    P.tablesP (geoOf S) (matsOf mats) nW (lookOf S.cf.lmb g) (ptsOfOwn planes scores d x) =
      (Tab.tables S mats nW g planes scores d x).map tabsFull

end Spec

theorem tables_one : Spec.TablesOne := by
  intro S mats nW g planes scores d x
  unfold P.tablesP Tab.tables
  have e := sim_placeAll S mats nW g planes scores d x {}
  have e0 : plOf {} = {} := by
    unfold plOf
    simp
  rw [e0] at e
  show (P.placeAll _ _ _ _ _ {}).bind (fun y => some y.1) = ((Tab.placeAll _ _ _ _ _ _ _ _ {}).bind fun y => some y.1).map _
  rw [e]
  cases Tab.placeAll S mats nW g planes scores d x {} <;> rfl

/-- Premise (a) of Johnson/Desc/First/Att/Claims/Seated.lean holds wherever the carried record's tables were made by the plain text from the carried record's own four records and lookup's record. -/
theorem tablesAgree_of (A : Plan) (a : VerifiableInference.Desc.First.AttOwn) (f : Four)
    (h : Tab.tables A.S A.mats A.nW f.g f.planes f.scores a.d a.x = some f.t) : TablesAgree A a f := by
  intro t ht
  have e := tables_one A.S A.mats A.nW f.g f.planes f.scores a.d a.x
  rw [h] at e
  have ht' : P.tablesP (geoOf A.S) (matsOf A.mats) A.nW (lookOf A.S.cf.lmb f.g)
      (ptsOfOwn f.planes f.scores a.d a.x) = some t := ht
  rw [e] at ht'
  rw [← Option.some.inj ht']
  rfl

end K5Law
