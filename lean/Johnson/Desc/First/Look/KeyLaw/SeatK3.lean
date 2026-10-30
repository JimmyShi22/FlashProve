-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/SeatK3.lean: THE SEAT OF THE KIND "LOOKUP" AT A KEY FILE: the kind's
own block (lookupKind, for every seat in a carried record and every place) carries the proved typed
lookup with parts between two borders over the carried record (RelLaw,
Johnson/Desc/Sound/KeyRelLaw.lean).

The typed block is the typed lookup A.lamS at the standard places, beside a riding joint R0 on a
part of the record that the block does not touch (bkLam, Pin.lean). The maps from the written rounds
are mapsOf (ViewAt.lean). In front: the typed in-joint itself, read off the record, and an
invariant: the ledger that is open has its sizes. Behind: the riding joint, and: the typed
out-relation Done holds of WHAT THE RECORD HOLDS, READ (outOf, Statement.lean: the hearing's forms
and the three claims that the run "planes" makes of them).

Main names:
  SeatLaws: the seat's "put" is read back by "fork" and "heard", leaves the riding part, and keeps
    an invariant I of the caller's choice.
  HeardOk: what the record holds behind the block.
  ReadsLow: the riding joint reads, of the oracles, the stored table and the trees below a number.
  OutIs: a typed out-statement is the record's, read.
  rowIn, rowOut: the two borders.
  k3_relLaw: THE LAW. k3_good: so the seat's piece is good between the two borders.

Limits. FaceIs, Adm, HomeIs, Pins, ReadsLow, SeatLaws and MadeOf (the written rounds are made of the
lookup's shape) are premises. The border behind speaks of the typed relation at the record, read:
that it is what the rows and the claims on the keys say which a layer lays is another file's
(DoneAt.lean).

-/
import Johnson.Desc.Sound.KeyRelLaw
import Johnson.Desc.Sound.KeyRowsOfBorders
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.First.Look.KeyLaw.BlockLaw
import Johnson.Desc.First.Look.KeyLaw.HeardView
import Johnson.Desc.First.Look.KeyLaw.MeetsAt
import Johnson.Desc.First.Look.KeyLaw.Pin
import Johnson.Desc.First.Look.KeyLaw.TotalB
import Johnson.Desc.First.Look.KeyLaw.KeySizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K3.KeyLaw
open Iop OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker OnBytes.K.Kc KObj
open _root_.Run (ckP)
open OnBytes.Model (Fork)
open Lk6 (Dat Pl)
open VerifiableInference.Desc.Sound (JointRow RelLaw stg Shown groupsAt sLeft_old goodOfRelLaw
  seatPiece)

variable {S Cl : Type} {Fr : VerifiableInference.Desc.Sound.Frame} (σ : SeatG S Cl) (p : PG) (A :
    Dat GE) (sl : Slot → A.J)
  (o k home : ℕ → Slot) (stOf : S → A.St) (I : S → Prop) {Kc M Wp : Type} (R0 : IOR.Rels Kc A.St
      Fr.E (M × Wp))
  (msg : M → A.J → GE)

/-- The seat's "put" is read back, and leaves the riding part of the record. -/
structure SeatLaws : Prop where
  fork : ∀ s g G, σ.fork (σ.put s g G) = some G
  heard : ∀ s g G, σ.heard (σ.put s g G) = some g
  rides : ∀ s g G, stOf (σ.put s g G) = stOf s
  keeps : ∀ s g G, I s → I (σ.put s g G)

/-- The riding joint reads, of the oracles, the stored table and the trees with a number below c. -/
def ReadsLow (c : ℕ) : Prop :=
  ∀ (x : A.St) (y y' : Fr.E.Str), y.1 = y'.1 →
    (∀ q : PosL Fr.all, (Fr.all.get q.1).no < c → y.2 q = y'.2 q) →
    (R0.on (x, y) ↔ R0.on (x, y')) ∧ ∀ w, R0.relR (x, y) w ↔ R0.relR (x, y') w

/-- A typed out-statement is the record's, read: at a ledger later than the one that the run
"planes" leaves, made from a ledger later than the record's. -/
def OutIs (s : S) (b : A.Out) : Prop :=
  ∃ G g H pl H' u K, σ.fork s = some G ∧ σ.heard s = some g ∧ PscRun.Later G H ∧
    planesG p.face g H [] = some (pl, H', u) ∧ PscRun.Later H' K ∧
    b = outOf A sl (stOf s) K home g pl

/-- What the record holds behind the block: a ledger with its sizes, behind the lookup's slots; a
hearing without a shift, with a point and a form a part, the point of the part's number of
coordinates. -/
def HeardOk (s : S) : Prop :=
  ∃ G g, σ.fork s = some G ∧ σ.heard s = some g ∧ PscRun.Sized G ∧
    G.next = p.first + p.face.slots ∧ g.theta = zeroE ∧ g.keys.length = p.face.parts.length ∧
    ∀ q < p.face.parts.length, (g.keys.getD q (#[], {})).1.size = p.face.parts.getD q 0

/-- The border in front: the typed in-joint, read off the record; the open ledger has its sizes. -/
def rowIn : JointRow S Fr :=
  ⟨jIn A Fr.E R0 msg, fun a => (stOf a.1, a.2),
    fun a => (∀ F0, σ.fork a.1 = some F0 → PscRun.Sized F0) ∧ I a.1⟩

/-- The border behind: the riding joint; and Done of the record, read. -/
def rowOut : JointRow S Fr :=
  JointRow.ofBorder (W := M × Wp) (fun a => R0.on (stOf a.1, a.2) ∧ I a.1 ∧ HeardOk σ p a.1)
    fun a w => R0.relR (stOf a.1, a.2) w ∧ ∃ b, OutIs σ p A sl home stOf a.1 b ∧ A.Done (msg w.1) b

variable {σ p A sl o k home stOf I R0 msg}

/-- **The law of the kind's own block.** -/
theorem k3_relLaw (before : List (ℕ × ℕ)) (bits : ℕ) (guests : List (First.Look.Guest S Cl))
    (base : ℕ) (ds : List RDT) (hσ : SeatLaws σ A stOf I) (hnd : (Fr.all.map (·.no)).Nodup)
    (hf : ∀ st, FaceIs A st p.face) (hadm : A.toPub.Adm Cb.Gl.p)
    (hh : HomeIs p.face p.first o k home) (hB : ReadsLow A R0 base)
    (hds : List.Forall₂ MadeOf ds (shapeG p.face)) (st0 : A.St) :
    RelLaw (lookupKind σ before bits guests p) base ds []
      (bkLam A (placesAt A sl o k) Fr.E R0 msg)
      (mapsOf (Lk6.lamS_runs A (placesAt A sl o k) Fr.E).rd ds
        (meets_typed A st0 (placesAt A sl o k) Fr.E p.face (hf st0) hadm ds hds).1.length_eq)
      (fun a => (stOf a.1, a.2)) (rowIn σ A stOf I R0 msg) (rowOut σ p A sl home stOf I R0 msg)
          where
  onIn := fun _ ha => ha.1
  relIn := fun _ w _ hw => ⟨w, hw⟩
  step := fun s s' y τ ha _ hv _ hd => by
    obtain ⟨hM, hN⟩ := meets_typed A st0 (placesAt A sl o k) Fr.E p.face (hf st0) hadm ds hds
    have hd' : (lookupKind σ before bits guests p).decide s ((rvT (ckP .two) ds τ).map noDigest)
        (groupsAt Fr.ft (lookupKind σ before bits guests p)
          ((sView (ckP .two) (stg Fr base ds) y τ).rounds ++ [])
          (sView (ckP .two) (stg Fr base ds) y τ).opened) = .ok s' := by
      rw [List.append_nil] at hd
      exact hd
    obtain ⟨F0, g, G, es, e1, e2, -, -, e5, rfl⟩ := block_law σ before bits guests p hd'
    have hw : viewWordsBelowPrime ⟨(rvT (ckP .two) ds τ).map noDigest, []⟩ = true := okView_shown _ hv
    have hout := lamS_out_heard A (placesAt A sl o k) Fr.E ds hM hN (stOf s) y τ e5
    have hlaw := K03key_law.out A sl (stOf s) p.face p.first o k home es F0 _ g G (hf _) hadm hh hw
      e2 (ha.2.1 F0 e1) e5
    have hy := hB (stOf s) y (y.1, sLeft (ckP .two) (stg Fr base ds) y τ) rfl
      fun q hq => (sLeft_old hnd ds base y τ q hq).symm
    refine ⟨(A.lamRun (placesAt A sl o k) (stOf s) (flatRV ((rvT (ckP .two) ds τ).map noDigest)),
        y),
      ?_, fun hon => ?_, fun hr => ?_⟩
    · refine IOR.red_out_eq_some.2 ⟨hout, ?_⟩
      exact ((Lk6.lamS_copies A (placesAt A sl o k) Fr.E).copy y _).symm
    · obtain ⟨k1, k2⟩ := heard_keys (hf (stOf s)).noShift e5
      refine ⟨⟨?_, hσ.keeps s g G ha.2.2, G, g, hσ.fork s g G, hσ.heard s g G, hlaw.2.2.2.1,
        hlaw.2.2.2.2.1, hlaw.1, k1, k2⟩, trivial⟩
      show R0.on (stOf (σ.put s g G), _)
      rw [hσ.rides]
      have h1 : R0.on ((A.lamRun (placesAt A sl o k) (stOf s)
          (flatRV ((rvT (ckP .two) ds τ).map noDigest))).1, y) := hon
      rw [show (A.lamRun (placesAt A sl o k) (stOf s)
          (flatRV ((rvT (ckP .two) ds τ).map noDigest))).1 = stOf s from
        Lk6.lamS_passes A (placesAt A sl o k) Fr.E _ _ _ _ hout] at h1
      exact hy.1.1 h1
    · have hr' : ∃ w : M × Wp,
          R0.relR (stOf (σ.put s g G), (y.1, sLeft (ckP .two) (stg Fr base ds) y τ)) w ∧
            ∃ b, OutIs σ p A sl home stOf (σ.put s g G) b ∧ A.Done (msg w.1) b := hr
      obtain ⟨w, hw1, b, ⟨G', g', H, pl, H', u, K, f1, f2, fH, f3, fK, rfl⟩, hw2⟩ := hr'
      rw [hσ.fork] at f1
      rw [hσ.heard] at f2
      obtain rfl := Option.some.inj f1
      obtain rfl := Option.some.inj f2
      rw [hσ.rides] at hw1 hw2
      have e := (hlaw.2.2.2.2.2 H H' pl u fH f3).2.2 K fK
      refine ⟨w, ?_, ?_⟩
      · show R0.relR ((A.lamRun (placesAt A sl o k) (stOf s) _).1, y) w
        rw [e]
        exact (hy.2 w).2 hw1
      · show A.Done (msg w.1) (A.lamRun (placesAt A sl o k) (stOf s) _)
        rw [e]
        exact hw2

/-- **So the seat's piece is good between the two borders**: point queries, a local verifier, and
knowledge soundness from the border in front into the border behind, with the typed lookup's own
errors carried by the maps. -/
theorem k3_good (W : Type) (before : List (ℕ × ℕ)) (bits : ℕ)
    (guests : List (First.Look.Guest S Cl)) (base : ℕ) (ds : List RDT) (hσ : SeatLaws σ A stOf I)
    (hnd : (Fr.all.map (·.no)).Nodup) (hf : ∀ st, FaceIs A st p.face)
    (hadm : A.toPub.Adm Cb.Gl.p) (hh : HomeIs p.face p.first o k home)
    (hB : ReadsLow A R0 base) (hds : List.Forall₂ MadeOf ds (shapeG p.face)) (st0 : A.St)
    (hpin : Pins A Fr.E R0) (hne : Nonempty (M × Wp)) :
    ((seatPiece (F := Fr) W (lookupKind σ before bits guests p) base ds []
        (bkLam A (placesAt A sl o k) Fr.E R0 msg)
        (mapsOf (Lk6.lamS_runs A (placesAt A sl o k) Fr.E).rd ds
          (meets_typed A st0 (placesAt A sl o k) Fr.E p.face (hf st0) hadm ds hds).1.length_eq)).bk
      (rowIn σ A stOf I R0 msg).on (rowOut σ p A sl home stOf I R0 msg).on
      (fun a _ => (rowIn σ A stOf I R0 msg).rel a)
      (fun a _ => (rowOut σ p A sl home stOf I R0 msg).rel a)).Good :=
  goodOfRelLaw W _ base ds [] _ _ _ _ _ (bkLam_good A _ Fr.E R0 msg hadm hpin) hne
    (mapsOf_ok _ ds (meets_typed A st0 (placesAt A sl o k) Fr.E p.face (hf st0) hadm ds hds).1) rfl
    (k3_relLaw before bits guests base ds hσ hnd hf hadm hh hB hds st0)

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.k3_relLaw
#print axioms VerifiableInference.Desc.K3.KeyLaw.k3_good
