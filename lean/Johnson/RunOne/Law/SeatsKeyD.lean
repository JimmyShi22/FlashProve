-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/SeatsKeyD.lean: THE THREE
SEATS OF A LOOKUP'S LINK IN A KEY FILE'S FIRST CHAIN, AS Johnson/Desc/Key/Link.lean LAYS IT, between
four borders over the carried record: the caller (a tie without an error), the kind's own block (the
proved typed lookup, KeyLaw/SeatK3.lean), the layer (a tie without an error: THE EXCHANGE).

The letters. one, set, i: the plan's public values, its setting, the lookup's number. id, m, l: the
lookup is Wf.lookupOf id m l. oL, kL, idxN: the mask entries that the two ledgers hand out to this
lookup, and the index-mask message's number: public numbers. A, sl: a typed lookup with that public
record. stOf: the part of the record that rides. R0: the riding joint. msg, wd, mx: how a witness's
messages are read as typed entries, as words, as the matrix.

Main names:
  takeMasksP_same: the ledgers' handing out leaves every table's size (SameTables,
    KeyLaw/SameTables.lean).
  Rides: what the riding part of the record may read.
  homeT, Inv: the table of homes of the letters; the invariant that rides through the link.
  Hands: the two ledgers hand out oL and kL, and the index-mask message has the number idxN.
  row0, row3: the borders in front of the caller and behind the layer (between: rowIn, rowOut).
  callerD_tie, layerD_tie: THE TWO TIES. seatD_laws: the seat's laws. k3D_relLaw: the kind's block.

Limits. Hands and Fits are premises on the record in front of the caller: that the ledgers stand so
at the plan's counts, and that the statement has the tables, is not shown here. Rides, Tied,
KeysAre, FaceIs, Adm and the public tests are premises. M must hold just those messages that the
statement pins.

-/
import Johnson.RunOne.Law.AtKeyD
import Johnson.Desc.First.Look.KeyLaw.SeatK3
import Johnson.Desc.First.Look.KeyLaw.SameTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.SeatsKeyD
open Iop OnBytes OnBytes.Slice OnBytes.K.Kc OnBytes.Params OnBytes.Maker KObj
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc (Block named need claimsIn viewWordsBelowPrime)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound (JointRow RelLaw QuietTie)
open VerifiableInference.Desc.Key (FirstState Claim Lookup LookupRecord lookupSeat caller layer
  rowsInOrder layerOrder lookupPlace)
open Johnson.RunOne.Law.AtKeyD
open Lk6 (Dat pubOf)

/-! ## The ledgers' handing out leaves the tables -/

theorem takeMaskP_same {L : Type} {d d' : _root_.Desc.Plain.DState L} {o n : ℕ}
    (h : takeMaskP d o = some (n, d')) : SameTables d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      cases h
      refine ⟨by simp, fun o' part => ?_⟩
      unfold Means.tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
      simp only [Array.getElem?_modify]
      by_cases ho : o = o'
      · subst ho
        cases hx : d.st.oracles[o]? <;> simp [hx]
      · simp [ho]
  · cases h

theorem takeMasksInto_same {L : Type} (o : ℕ) : ∀ (n : ℕ) (d d' : _root_.Desc.Plain.DState L)
    (acc : Array ℕ) (r : List ℕ), takeMasksInto o n d acc = some (r, d') → SameTables d.st d'.st
  | 0, d, d', acc, r, h => by
    cases h
    exact SameTables.refl _
  | n + 1, d, d', acc, r, h => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1] at h
      exact (takeMaskP_same (n := x.1) (d' := x.2) h1).trans
        (takeMasksInto_same o n x.2 d' _ r h)

/-- **The ledgers' handing out leaves every table's size.** -/
theorem takeMasksP_same {L : Type} {d : _root_.Desc.Plain.DState L} {o n : ℕ}
    {x : List ℕ × _root_.Desc.Plain.DState L} (h : takeMasksP d o n = some x) :
    SameTables d.st x.2.st :=
  takeMasksInto_same o n d x.2 #[] x.1 h

/-! ## The letters -/

variable {Fr : VerifiableInference.Desc.Sound.Frame} (one : OneTime) (set : Setting) (i : ℕ)
  (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (oL kL : List ℕ) (idxN : ℕ) (A : Dat GE)
  (sl : Slot → A.J) (stOf : FirstState → A.St) {Kc M Wp : Type} (R0 : IOR.Rels Kc A.St Fr.E (M ×
      Wp))
  (msg : M → A.J → GE) (wd : M → Means.Words GE) (mx : M → ℕ → ℕ → GE)

/-- **The riding part of the record rides through the link of lookup number i**: it reads neither
the ledger of hidden values, nor what was heard, nor the table of homes; not what a message's ledger
of mask entries has handed out; and of the lookups' rows and claims on the keys the first i alone.
-/
structure Rides {α : Type} (stOf : FirstState → α) (i : ℕ) : Prop where
  base : ∀ (s : FirstState) (f : Option Fork) (h : Option HeardG) (hm : Array Slot),
    stOf { s with base := { s.base with fork := f, heard := h, home := hm } } = stOf s
  hand : ∀ (s : FirstState) (o n : ℕ) (x : List ℕ × VerifiableInference.Desc.Key.PlainState),
    takeMasksP s.d o n = some x → stOf { s with d := x.2 } = stOf s
  app : ∀ (s : FirstState) (r : List Row) (k : List Lkp.Keys), s.base.rows.length = i →
    s.base.keys.length = i →
    stOf { s with base := { s.base with rows := s.base.rows ++ [r], keys := s.base.keys ++ [k] } } =
      stOf s

/-- The table of homes of the letters. -/
def homeT : Array Slot :=
  homes (faceOfLkp (Wf.lookupOf id m l)) (oL.map fun j => ⟨one.ranges.messageId, j⟩)
    (kL.map fun j => ⟨idxN, j⟩)

/-- The statement has the tables that the lookup's rows read. -/
def Fits (S : Statement) : Prop :=
  TablesFit S one.ranges one.codes ∧ ∀ s ∈ (homeT one id m l oL kL idxN).toList,
    s.oracle < S.oracles.size ∧ s.index < Means.tableSize S s.oracle .mask

/-- The invariant that rides through the link: the record's table of homes is the letters'; the
statement has the tables; i lookups have written their rows and their claims on the keys; every
hidden value has a home. -/
def Inv (s : FirstState) : Prop :=
  s.base.home = homeT one id m l oL kL idxN ∧ Fits one id m l oL kL idxN s.d.st ∧
    s.base.rows.length = i ∧ s.base.keys.length = i ∧
    (homeT one id m l oL kL idxN).size = (faceOfLkp (Wf.lookupOf id m l)).slots

/-- The two ledgers hand out oL and kL; the index-mask message has the number idxN. -/
def Hands (s : FirstState) : Prop :=
  s.idx = idxN ∧ ∀ o k,
    takeMasksP s.d one.ranges.messageId ((faceOfLkp (Wf.lookupOf id m l)).slots -
      2 * (faceOfLkp (Wf.lookupOf id m l)).parts.length) = some o →
    takeMasksP o.2 s.idx (2 * (faceOfLkp (Wf.lookupOf id m l)).parts.length) = some k →
    o.1 = oL ∧ k.1 = kL

/-- The border in front of the caller: the typed in-joint, read off the record; the ledgers hand out
the letters' entries; the statement has the tables; i lookups have written their rows. -/
def row0 : JointRow FirstState Fr :=
  ⟨jIn A Fr.E R0 msg, fun a => (stOf a.1, a.2),
    fun a => Hands one id m l oL kL idxN a.1 ∧ Fits one id m l oL kL idxN a.1.d.st ∧
      a.1.base.rows.length = i⟩

/-- The border behind the layer: the riding joint; the statement has the tables; lookup number i's
rows, as the layer has written them, say their claims of the witness's words; the pending rows of
its claims on the keys hold of the witness's matrix. -/
def row3 : JointRow FirstState Fr :=
  JointRow.ofBorder (W := M × Wp)
    (fun a => R0.on (stOf a.1, a.2) ∧ Fits one id m l oL kL idxN a.1.d.st ∧
      a.1.base.rows.length = i + 1 ∧ a.1.base.keys.length = i + 1)
    fun a w => R0.relR (stOf a.1, a.2) w ∧
      ∃ rows keys, a.1.base.rows[i]? = some rows ∧ a.1.base.keys[i]? = some keys ∧
        Means.AllSay Reading.gl a.1.d.st rows (wd w.1) ∧
        ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p →
          (Leaves.readTRow (Wf.pendingRow m l p (keys.getD j default)
            (Wf.eqPlaces m (keys.getD j default).point))).Holds
              ⟨fun s => wd w.1 s.oracle .mask s.index⟩ (mx w.1) m.rows m.kCol

variable {one set i id m l oL kL idxN A sl stOf R0 msg wd mx}

/-- The seat's laws. -/
theorem seatD_laws (hst : Rides stOf i) :
    SeatLaws lookupSeat A stOf (Inv one i id m l oL kL idxN) where
  fork := fun _ _ _ => rfl
  heard := fun _ _ _ => rfl
  rides := fun s g G => hst.base s (some G) (some g) s.base.home
  keeps := fun _ _ _ h => h

/-- **The caller's tie.** -/
theorem callerD_tie (hst : Rides stOf i) :
    QuietTie (caller one i (Wf.lookupOf id m l)) (row0 one i id m l oL kL idxN A stOf R0 msg)
      (rowIn lookupSeat A stOf (Inv one i id m l oL kL idxN) R0 msg) := by
  intro s s' y rs gs ha hd
  obtain ⟨-, hkl, o, k, h1, h2, hsz, rfl⟩ := callerD_law hd
  obtain ⟨hon, ⟨hidx, hh⟩, hfit, hrl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hh o k h1 h2
  have hsame := (takeMasksP_same h1).trans (takeMasksP_same h2)
  have e : stOf ({ s with
      d := k.2
      base := { s.base with
        fork := some (({} : Fork).slots (faceOfLkp (Wf.lookupOf id m l)).slots)
        heard := none
        home := homes (faceOfLkp (Wf.lookupOf id m l))
          (o.1.map fun j => ⟨one.ranges.messageId, j⟩) (k.1.map fun j => ⟨s.idx, j⟩) } } :
              FirstState) =
      stOf s :=
    (hst.base { s with d := k.2 } _ _ _).trans
      ((hst.hand { s with d := o.2 } s.idx _ k h2).trans (hst.hand s _ _ o h1))
  refine ⟨⟨?_, ?_, ?_, ?_, hrl, hkl, by rw [← hidx]; exact hsz⟩, fun hr => ?_⟩
  · show (jIn A Fr.E R0 msg).on (stOf _, y)
    rw [e]
    exact hon
  · intro F0 hF0
    obtain rfl := Option.some.inj hF0
    exact (ready_slots _).sized
  · show homes _ _ _ = homeT one id m l o.1 k.1 idxN
    rw [hidx]
    rfl
  · refine ⟨⟨?_, ?_⟩, fun t ht => ?_⟩
    · show one.ranges.messageId < k.2.st.oracles.size
      rw [hsame.1]
      exact hfit.1.there
    · show Means.tableSize k.2.st _ _ = _
      rw [hsame.2]
      exact hfit.1.size
    · show t.oracle < k.2.st.oracles.size ∧ t.index < Means.tableSize k.2.st t.oracle .mask
      rw [hsame.1, hsame.2]
      exact hfit.2 t ht
  · obtain ⟨w, hw⟩ := hr
    refine ⟨w, ?_⟩
    have hw' : (jIn A Fr.E R0 msg).relR (stOf _, y) w := hw
    rw [e] at hw'
    exact hw'

/-- **The seat of the kind's own block**, at the seat lookupSeat and the place of lookup number i.
-/
theorem k3D_relLaw (before : List (ℕ × ℕ)) (bits : ℕ) (base : ℕ) (ds : List RDT)
    (hst : Rides stOf i) (hnd : (Fr.all.map (·.no)).Nodup)
    (hf : ∀ st, FaceIs A st (faceOfLkp (Wf.lookupOf id m l))) (hadm : A.toPub.Adm Cb.Gl.p)
    (hB : ReadsLow A R0 base)
    (hds : List.Forall₂ MadeOf ds (shapeG (faceOfLkp (Wf.lookupOf id m l)))) (st0 : A.St) :
    RelLaw (lookupKind lookupSeat before bits [] (lookupPlace set i (Wf.lookupOf id m l))) base ds []
      (bkLam A (placesAt A sl
        (fun n => (oL.map fun j => (⟨one.ranges.messageId, j⟩ : Slot)).getD n default)
        (fun n => (kL.map fun j => (⟨idxN, j⟩ : Slot)).getD n default)) Fr.E R0 msg)
      (mapsOf (Lk6.lamS_runs A (placesAt A sl
        (fun n => (oL.map fun j => (⟨one.ranges.messageId, j⟩ : Slot)).getD n default)
        (fun n => (kL.map fun j => (⟨idxN, j⟩ : Slot)).getD n default)) Fr.E).rd ds
        (meets_typed A st0 _ Fr.E (faceOfLkp (Wf.lookupOf id m l)) (hf st0) hadm ds
          hds).1.length_eq)
      (fun a => (stOf a.1, a.2)) (rowIn lookupSeat A stOf (Inv one i id m l oL kL idxN) R0 msg)
      (rowOut lookupSeat (lookupPlace set i (Wf.lookupOf id m l)) A sl
        (fun n => (homeT one id m l oL kL idxN).getD n default) stOf
        (Inv one i id m l oL kL idxN) R0 msg) := by
  by_cases hsz : (homeT one id m l oL kL idxN).size = (faceOfLkp (Wf.lookupOf id m l)).slots
  · exact k3_relLaw (p := lookupPlace set i (Wf.lookupOf id m l)) before bits [] base ds (seatD_laws
      hst)
      hnd hf hadm (homeIs_of_size _ _ _ hsz) hB hds st0
  · exact ⟨fun _ ha => ha.1, fun _ w _ hw => ⟨w, hw⟩,
      fun _ _ _ _ ha => absurd ha.2.2.2.2.2.2 hsz⟩

/-- **The layer's tie: the exchange.** -/
theorem layerD_tie {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ} (hst : Rides
    stOf i)
    (hP : A.toPub = pubOf (Wf.lookupOf id m l)) (hadm : A.toPub.Adm Cb.Gl.p)
    (hlo : Wf.lookupOk Wf.fBits l = true) (hfm : Wf.fitsMatrix m l = true)
    (hi : one.ranges.lookups[i]? = some l)
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true)
    (hT : ∀ u, Tied A sl (msg u) (wd u) one.ranges one.codes i
      (homeT one id m l oL kL idxN).toList)
    (hK : ∀ st u, KeysAre A st (msg u) id m l (mx u)) :
    QuietTie (layer one set i (Wf.lookupOf id m l)
        (claimsIn [b0, lookupKind lookupSeat before bits [] (lookupPlace set i (Wf.lookupOf id m l))]
          [(1, "objects"), (1, "planes"), (1, "guests")]))
      (rowOut lookupSeat (lookupPlace set i (Wf.lookupOf id m l)) A sl
        (fun n => (homeT one id m l oL kL idxN).getD n default) stOf
        (Inv one i id m l oL kL idxN) R0 msg)
      (row3 one i id m l oL kL idxN A stOf R0 wd mx) := by
  intro s s'' y rs gs ha hd
  have ha' : (R0.on (stOf s, y) ∧ Inv one i id m l oL kL idxN s ∧
      HeardOk lookupSeat (lookupPlace set i (Wf.lookupOf id m l)) s) ∧ True := ha
  obtain ⟨⟨hon, ⟨hhome, hfit, hrl, hkl, -⟩, G, g, hG, hg, -, -, hth, k1, k2⟩, -⟩ := ha'
  have hG : s.base.fork = some G := hG
  have hg : s.base.heard = some g := hg
  obtain ⟨cls, s', F, g', rows, keys, c1, c2, c3, c4, c5, rfl⟩ := layerD_law hd
  obtain ⟨pl, H', u, p1, rfl, rfl⟩ := claimsD_law hG hg c1
  obtain rfl : H'.paid g.owedPlanes = F := Option.some.inj c2
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans c3)
  have e : stOf ({ s with base := { s.base with
      fork := some ((H'.paid g.owedPlanes).paid g.owedJoin)
      rows := s.base.rows ++ [rows]
      keys := s.base.keys ++ [keys] } } : FirstState) = stOf s :=
    (hst.base { s with base := { s.base with
      rows := s.base.rows ++ [rows], keys := s.base.keys ++ [keys] } }
      (some ((H'.paid g.owedPlanes).paid g.owedJoin)) s.base.heard s.base.home).trans
      (hst.app s rows keys hrl hkl)
  refine ⟨⟨⟨?_, hfit, ?_, ?_⟩, trivial⟩, fun hr => ?_⟩
  · show R0.on (stOf ({ s with base := { s.base with
      fork := some ((H'.paid g.owedPlanes).paid g.owedJoin)
      rows := s.base.rows ++ [rows]
      keys := s.base.keys ++ [keys] } } : FirstState), y)
    rw [e]
    exact hon
  · show (s.base.rows ++ [rows]).length = i + 1
    rw [List.length_append, hrl]
    rfl
  · show (s.base.keys ++ [keys]).length = i + 1
    rw [List.length_append, hkl]
    rfl
  · obtain ⟨w, hw1, rows', keys', r1, r2, r3, r4⟩ := hr
    have hw1' : R0.relR (stOf ({ s with base := { s.base with
      fork := some ((H'.paid g.owedPlanes).paid g.owedJoin)
      rows := s.base.rows ++ [rows]
      keys := s.base.keys ++ [keys] } } : FirstState), y) w := hw1
    rw [e] at hw1'
    have r1' : (s.base.rows ++ [rows])[i]? = some rows' := r1
    have r2' : (s.base.keys ++ [keys])[i]? = some keys' := r2
    rw [← hrl, List.getElem?_concat_length] at r1'
    rw [← hkl, List.getElem?_concat_length] at r2'
    obtain rfl : rows = rows' := Option.some.inj r1'
    obtain rfl : keys = keys' := Option.some.inj r2'
    rw [filterL, List.length_map] at c4
    have c4' : rowsInOrder (Wf.planesAt one.ranges one.codes i) (layerOrder g.rows.toList.length)
        (H'.paid g.owedPlanes) (homeT one id m l oL kL idxN)
        (g.rows.toList.map Sum.inl ++ pl.map Sum.inr) = some rows := by
      rw [← hhome]
      exact c4
    have c5' : keyClaims (Wf.lookupOf id m l) (H'.paid g.owedPlanes)
        (homeT one id m l oL kL idxN) g = some keys := by
      rw [← hhome]
      exact c5
    have hd' := (doneD_iff id m l c4' c5' (planesG_three p1) (planesG_pairs p1) hth
      (by rw [k1]; exact List.length_map _) (fun q hq => k2 q (by
        show q < (l.parts.map fun p => p.logPlaces + m.kCol).length
        rw [List.length_map]
        exact hq)) A sl (stOf s) hP hadm hlo hfm (msg w.1) (wd w.1) s.d.st (mx w.1) (hT w.1)
      hfit.1 hfit.2 hi hla (hK _ _)).2
    refine ⟨w, hw1', _, ⟨G, g, G.paid g.owedObjects, pl, H', u, H'.paid g.owedPlanes, hG, hg,
      PscRun.paid_later _ _, p1, PscRun.paid_later _ _, rfl⟩, hd'.2 ⟨r3, r4⟩⟩

end Johnson.RunOne.Law.SeatsKeyD

#print axioms Johnson.RunOne.Law.SeatsKeyD.takeMasksP_same
#print axioms Johnson.RunOne.Law.SeatsKeyD.callerD_tie
#print axioms Johnson.RunOne.Law.SeatsKeyD.k3D_relLaw
#print axioms Johnson.RunOne.Law.SeatsKeyD.layerD_tie
