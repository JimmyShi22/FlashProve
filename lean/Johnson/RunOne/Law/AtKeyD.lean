-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/AtKeyD.lean: THE LOOKUP'S
LAW AT THE LINK OF A KEY FILE'S FIRST CHAIN AS Johnson/Desc/Key/Link.lean LAYS IT: the caller
(caller), the kind's own block at the seat lookupSeat, the link's three runs of claims, the layer of
rows (layer), and the block that lays all lookups' rows onto the ranges' group (layRows): what each
leaves where it says yes; and: the typed lookup's out-relation holds of entries read off words and a
matrix EXACTLY IF the rows that the layer has written say their claims of the words and the pending
rows of the claims on the keys hold of the matrix.

Main names:
  callerD_law, claimsD_law, layerD_law, rowsD_law: the blocks' yeses.
  rowsByD_group: the layer's rows in the public table's order are the kind's own groupRows.
  doneD_iff: THE EXCHANGE at what the record holds behind the kind's block.

Limits. The conditions on the typed lookup (FaceIs, Adm, its public record), Tied, TablesFit,
KeysAre and that the homes stand inside the statement's mask tables are premises.

-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.Desc.First.Look.KeyLaw.BlockLaw
import Johnson.Desc.First.Look.KeyLaw.Runs
import Johnson.Desc.First.Look.KeyLaw.GroupSays
import Johnson.Desc.First.Look.KeyLaw.KeyClaim
import Johnson.Desc.First.Look.KeyLaw.KeySizes
import Johnson.Desc.First.Look.KeyLaw.Caller
import Johnson.Desc.First.Look.KeyLaw.TotalB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.AtKeyD
open OnBytes OnBytes.Slice OnBytes.K.Kc OnBytes.Params
open OnBytes.Model (Fork Aff Reading)
open VerifiableInference.Desc (Block named need claimsIn claimsInBy viewWordsBelowPrime)
open VerifiableInference.Desc.Ground (takeMasksP addRowsP addRowsFrom addRowP)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Lookup LookupRecord lookupSeat caller layer
  layRows rowOfClaim rowsInOrder layerOrder lookupPlace lookupsOf)
open Lk6 (Dat pubOf)

/-! ## The caller -/

/-- **The caller's yes.** -/
theorem callerD_law {one : OneTime} {i : ℕ} {x : Lookup} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (caller one i x).decide s rs gs = .ok s') :
    s.base.fork = none ∧ s.base.keys.length = i ∧ ∃ o k,
      takeMasksP s.d one.ranges.messageId
        ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length) = some o ∧
      takeMasksP o.2 s.idx (2 * (faceOfLkp x).parts.length) = some k ∧
      (homes (faceOfLkp x) (o.1.map fun j => ⟨one.ranges.messageId, j⟩)
        (k.1.map fun j => ⟨s.idx, j⟩)).size = (faceOfLkp x).slots ∧
      s' = { s with
        d := k.2
        base := { s.base with
          fork := some (({} : Fork).slots (faceOfLkp x).slots)
          heard := none
          home := homes (faceOfLkp x) (o.1.map fun j => ⟨one.ranges.messageId, j⟩)
            (k.1.map fun j => ⟨s.idx, j⟩) } } := by
  have h' : (do
      need "the caller: a ledger is open" s.base.fork.isNone
      need "the caller: the lookups come in their order" (s.base.keys.length == i)
      let o ← named "the caller: the own message's ledger does not hand out the lookup's entries"
        (takeMasksP s.d one.ranges.messageId
          ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
      let k ← named
        "the caller: the index-mask message's ledger does not hand out the lookup's entries"
        (takeMasksP o.2 s.idx (2 * (faceOfLkp x).parts.length))
      need "the caller: every hidden value has a home"
        ((homes (faceOfLkp x) (o.1.map fun j => ⟨one.ranges.messageId, j⟩)
          (k.1.map fun j => ⟨s.idx, j⟩)).size == (faceOfLkp x).slots)
      pure ({ s with
        d := k.2
        base := { s.base with
          fork := some (({} : Fork).slots (faceOfLkp x).slots)
          heard := none
          home := homes (faceOfLkp x) (o.1.map fun j => ⟨one.ranges.messageId, j⟩)
            (k.1.map fun j => ⟨s.idx, j⟩) } } : FirstState) : Except String FirstState) = .ok s' :=
                h
  obtain ⟨_, h1, h'⟩ := bindX h'
  obtain ⟨_, h2, h'⟩ := bindX h'
  obtain ⟨o, h3, h'⟩ := bindX h'
  obtain ⟨k, h4, h'⟩ := bindX h'
  obtain ⟨_, h5, h'⟩ := bindX h'
  cases h'
  exact ⟨by simpa using needX h1, by simpa using needX h2, o, k, namedX h3, namedX h4,
    by simpa using needX h5, rfl⟩

/-! ## The link's three runs of claims -/

theorem mapM_inrD (s : FirstState) (pl : List PlaneClaim) (l : List Claim)
    (h : pl.mapM (lookupSeat.claimP s) = some l) : l = pl.map .inr := by
  have := mapM_reads (lookupSeat.claimP s) id Sum.inr pl l h fun a _ b hb => by
    cases hb
    rfl
  simpa using this

/-- **The link's three runs.** -/
theorem claimsD_law {b0 : Block FirstState Claim} {before : List (ℕ × ℕ)} {bits : ℕ} {p : PG}
    {s s' : FirstState} {cls : List Claim} {G : Fork} {g : HeardG} (hF : s.base.fork = some G)
    (hg : s.base.heard = some g)
    (h : claimsIn [b0, lookupKind lookupSeat before bits [] p]
      [(1, "objects"), (1, "planes"), (1, "guests")] s = .ok (cls, s')) :
    ∃ pl H' u, planesG p.face g (G.paid g.owedObjects) [] = some (pl, H', u) ∧
      cls = g.rows.toList.map .inl ++ pl.map .inr ∧
      s' = { s with base := { s.base with fork := some (H'.paid g.owedPlanes) } } := by
  unfold claimsIn claimsInBy at h
  simp only [List.foldl_cons, List.foldl_nil] at h
  obtain ⟨x2, h, h3⟩ := bindB h
  obtain ⟨x1, h, h2⟩ := bindB h
  obtain ⟨x0, h0, h1⟩ := bindB h
  cases h0
  obtain ⟨z1, r1, rfl⟩ := runIn_ok (o := (1, "objects")) rfl h1
  obtain ⟨z2, r2, rfl⟩ := runIn_ok (o := (1, "planes")) rfl h2
  obtain ⟨z3, r3, e3⟩ := runIn_ok (o := (1, "guests")) rfl h3
  -- objects
  obtain ⟨F1, a1, r1⟩ := bindX r1
  obtain ⟨g1, a2, r1⟩ := bindX r1
  cases r1
  obtain rfl : G = F1 := Option.some.inj (hF.symm.trans (namedX a1))
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans (namedX a2))
  -- planes
  obtain ⟨F2, b1, r2⟩ := bindX r2
  obtain ⟨g2, b2, r2⟩ := bindX r2
  obtain ⟨_, -, r2⟩ := bindX r2
  obtain ⟨y, b4, r2⟩ := bindX r2
  obtain ⟨l, b5, r2⟩ := bindX r2
  cases r2
  obtain rfl : G.paid g.owedObjects = F2 := Option.some.inj (namedX b1)
  obtain rfl : g = g2 := Option.some.inj (hg.symm.trans (namedX b2))
  have hl : l = y.1.map .inr := mapM_inrD _ _ _ (namedX b5)
  -- guests
  have h9 := namedX r3
  cases h9
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e3
  refine ⟨y.1, y.2.1, y.2.2, namedX b4, ?_, rfl⟩
  rw [hl]
  show (([] ++ g.rows.toList.map Sum.inl) ++ y.1.map Sum.inr) ++ [] = _
  rw [List.append_nil, List.nil_append]

/-! ## The layer -/

/-- **The layer's yes.** -/
theorem layerD_law {one : OneTime} {set : Setting} {i : ℕ}
    {x : Lookup} {claims : FirstState → Except String (List Claim × FirstState)} {s s'' :
        FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (layer one set i x claims).decide s rs gs = .ok s'') :
    ∃ cls s' F g rows keys, claims s = .ok (cls, s') ∧ s'.base.fork = some F ∧
      s'.base.heard = some g ∧
      rowsInOrder (Wf.planesAt one.ranges one.codes i) (layerOrder (cls.filter fun c =>
          c.isLeft).length) F
        s'.base.home cls = some rows ∧
      keyClaims x F s'.base.home g = some keys ∧
      s'' = { s' with base := { s'.base with
        fork := some (F.paid g.owedJoin)
        rows := s'.base.rows ++ [rows]
        keys := s'.base.keys ++ [keys] } } := by
  have h' : (do
      let y ← claims s
      let F ← named "the layer: no ledger is open" y.2.base.fork
      let g ← named "the layer: nothing was heard" y.2.base.heard
      let rows ← named "the layer: a claim has no row"
        (rowsInOrder (Wf.planesAt one.ranges one.codes i) (layerOrder (y.1.filter fun c =>
            c.isLeft).length) F
          y.2.base.home y.1)
      let keys ← named "the layer: a part's form has no claim on its keys"
        (keyClaims x F y.2.base.home g)
      need "the layer: something of the lookup is left open in the ledger (doneG)"
        (doneG (lookupPlace set i x) g (F.paid g.owedJoin))
      pure ({ y.2 with base := { y.2.base with
        fork := some (F.paid g.owedJoin)
        rows := y.2.base.rows ++ [rows]
        keys := y.2.base.keys ++ [keys] } } : FirstState) : Except String FirstState) = .ok s'' := h
  obtain ⟨y, h1, h'⟩ := bindX h'
  obtain ⟨F, h2, h'⟩ := bindX h'
  obtain ⟨g, h3, h'⟩ := bindX h'
  obtain ⟨rows, h4, h'⟩ := bindX h'
  obtain ⟨keys, h5, h'⟩ := bindX h'
  obtain ⟨_, -, h'⟩ := bindX h'
  cases h'
  exact ⟨y.1, y.2, F, g, rows, keys, h1, namedX h2, namedX h3, namedX h4, namedX h5, rfl⟩

theorem filterL (as : List Aff) (ps : List PlaneClaim) :
    ((as.map Sum.inl ++ ps.map Sum.inr : List Claim).filter fun c => c.isLeft) = as.map Sum.inl :=
        by
  rw [List.filter_append]
  have e1 : ((as.map Sum.inl : List Claim).filter fun c => c.isLeft) = as.map Sum.inl :=
    List.filter_eq_self.2 fun c hc => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
      rfl
  have e2 : ((ps.map Sum.inr : List Claim).filter fun c => c.isLeft) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
      simp
  rw [e1, e2, List.append_nil]

theorem filterR (as : List Aff) (ps : List PlaneClaim) :
    ((as.map Sum.inl ++ ps.map Sum.inr : List Claim).filter fun c => c.isRight) =
      ps.map Sum.inr := by
  rw [List.filter_append]
  have e1 : ((as.map Sum.inl : List Claim).filter fun c => c.isRight) = [] :=
    List.filter_eq_nil_iff.2 fun c hc => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
      simp
  have e2 : ((ps.map Sum.inr : List Claim).filter fun c => c.isRight) = ps.map Sum.inr :=
    List.filter_eq_self.2 fun c hc => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hc
      rfl
  rw [e1, e2, List.nil_append]

/-- **The layer's rows in the public table's order are the kind's own groupRows.** -/
theorem rowsByD_group (planesAt : Row → Tensor → Row) (F : Fork) (home : Array Slot)
    (front : List Aff) (bits : Aff) (a b c : PlaneClaim) (rows : List Row)
    (h : rowsInOrder planesAt (layerOrder (front ++ [bits]).length) F home
      ((front ++ [bits]).map Sum.inl ++ [a, b, c].map Sum.inr) = some rows) :
    groupRows planesAt F home (front ++ [bits]) [a, b, c] = some rows := by
  unfold rowsInOrder at h
  rw [filterL, filterR] at h
  dsimp only at h
  split at h
  · cases h
  · unfold layerOrder at h
    rw [List.mapM_append, mapM_map'] at h
    have hn : (front ++ [bits]).length - 1 = front.length := by simp
    rw [hn] at h
    have e0 : (List.range front.length).mapM (fun j =>
        ((if (false, j, true).1 = true then ([a, b, c].map Sum.inr : List Claim)
          else (front ++ [bits]).map Sum.inl)[(false, j, true).2.1]?).bind
            (rowOfClaim planesAt F home (false, j, true).2.2)) = front.mapM (rowOfAff F home) := by
      rw [show front.mapM (rowOfAff F home) =
          (front.map (Sum.inl : Aff → Claim)).mapM (rowOfClaim planesAt F home true) from
        (mapM_map' (Sum.inl : Aff → Claim) (rowOfClaim planesAt F home true) front).symm,
        ← mapM_range_bind (rowOfClaim planesAt F home true) (front.map Sum.inl), List.length_map]
      refine mapM_congr' _ fun j hj => ?_
      have hj' : j < front.length := List.mem_range.1 hj
      show (((front ++ [bits]).map Sum.inl : List Claim)[j]?).bind _ = _
      rw [List.map_append, List.getElem?_append_left (by simpa using hj')]
    rw [e0] at h
    unfold groupRows
    have hl : (front ++ [bits]).getLast? = some bits := by simp
    have hd : (front ++ [bits]).dropLast = front := by simp
    simp only [hl, hd]
    have eb : (((front ++ [bits]).map Sum.inl : List Claim)[front.length]?) = some (Sum.inl bits) :=
        by
      simp
    simp only [List.mapM_cons, List.mapM_nil, eb, if_true, Bool.false_eq_true, if_false,
      List.map_cons, List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.bind_some, rowOfClaim] at h
    cases e1 : front.mapM (rowOfAff F home) with
    | none => simp [e1] at h
    | some f1 =>
      cases e2 : rowOfPlane planesAt F home true a with
      | none => simp [e1, e2] at h
      | some r1 =>
        cases e3 : rowOfAff F home bits with
        | none => simp [e1, e2, e3] at h
        | some r2 =>
          cases e4 : rowOfPlane planesAt F home false b with
          | none => simp [e1, e2, e3, e4] at h
          | some r3 =>
            cases e5 : rowOfPlane planesAt F home true c with
            | none => simp [e1, e2, e3, e4, e5] at h
            | some r4 =>
              simp only [e1, e2, e3, e4, e5, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def] at h ⊢
              exact h

/-! ## The exchange -/

/-- **The exchange, at what the record holds.** K: the ledger at which the layer reads; homeA: the
record's table of homes; g: what was heard; pl: the three claims on the planes. The rows that the
layer writes and the claims on the keys that it writes say, of words and a matrix, just what the
typed out-relation says of the entries read off them. -/
theorem doneD_iff {one : OneTime} {i : ℕ} {K : Fork} {homeA : Array Slot} {g : HeardG}
    {pl : List PlaneClaim} {rows : List Row} {keys : List Lkp.Keys} (id : ℕ) (m : Wf.Matrix)
    (l : WfLookup)
    (hrows : rowsInOrder (Wf.planesAt one.ranges one.codes i) (layerOrder g.rows.toList.length) K
        homeA
      (g.rows.toList.map Sum.inl ++ pl.map Sum.inr) = some rows)
    (hkeys : keyClaims (Wf.lookupOf id m l) K homeA g = some keys)
    (h3 : ∃ a b c, pl = [a, b, c]) (hpairs : ∀ c ∈ pl, c.pairs.length = l.mu + l.d)
    (hth : g.theta = zeroE) (k1 : g.keys.length = l.parts.length)
    (k2 : ∀ q < l.parts.length, (g.keys.getD q (#[], {})).1.size =
      (l.parts.map fun p => p.logPlaces + m.kCol).getD q 0)
    (A : Dat GE) (sl : Slot → A.J) (st : A.St) (hP : A.toPub = pubOf (Wf.lookupOf id m l))
    (hadm : A.toPub.Adm Cb.Gl.p) (hlo : Wf.lookupOk Wf.fBits l = true)
    (hfm : Wf.fitsMatrix m l = true) (μ : A.J → GE) (w : Means.Words GE) (St : Statement)
    (M : ℕ → ℕ → GE) (hT : Tied A sl μ w one.ranges one.codes i homeA.toList)
    (hTab : TablesFit St one.ranges one.codes)
    (hIn : ∀ s ∈ homeA.toList, s.oracle < St.oracles.size ∧
      s.index < Means.tableSize St s.oracle .mask)
    (hi : one.ranges.lookups[i]? = some l)
    (hla : ((Wf.layout one.ranges.lookups (Planes.codeOf one.ranges one.codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf one.ranges one.codes).ell)) = true)
    (hK : KeysAre A st μ id m l M) :
    keys.length = l.parts.length ∧
      (A.Done μ (outOf A sl st K (fun n => homeA.getD n default) g pl) ↔
        Means.AllSay Reading.gl St rows w ∧
          ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p →
            (Leaves.readTRow (Wf.pendingRow m l p (keys.getD j default)
              (Wf.eqPlaces m (keys.getD j default).point))).Holds
                ⟨fun s => w s.oracle .mask s.index⟩ M m.rows m.kCol) := by
  obtain ⟨a, b, c, rfl⟩ := h3
  have hA := homeArr_getD homeA
  -- the objects are not none
  have hne : g.rows.toList ≠ [] := by
    intro h0
    rw [h0] at hrows
    unfold rowsInOrder at hrows
    simp [layerOrder] at hrows
  obtain ⟨front, bits, hfb⟩ : ∃ front bits, g.rows.toList = front ++ [bits] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  rw [hfb] at hrows
  have hgr := rowsByD_group _ K homeA front bits a b c rows hrows
  rw [← hfb] at hgr
  have e1 := groupRows_iff (A := A) (sl := sl) (μ := μ) (w := w) St hadm.room hT hTab l hi hlo hla
    (congrArg Lk6.Pub.mu hP).symm (congrArg Lk6.Pub.d hP).symm (congrArg Lk6.Pub.pl hP).symm hA
    (fun s hs => hs) hIn hpairs hgr
  obtain ⟨e0, e2⟩ := keys_iff_rec hA id m l hkeys hth k1 k2 A sl st hP hlo hfm μ
    ⟨fun s => w s.oracle .mask s.index⟩ M hT.mask hK
  refine ⟨e0, ?_⟩
  unfold Lk6.Dat.Done
  show ((∀ j : Fin A.m, (Lk6.Mid.rdCl A sl (readE g.alpha) (A.v j)
      (keyF K (fun n => homeA.getD n default) (g.keys.getD j (#[], {})))).Holds (A.v j)
        (A.key st μ j) μ) ∧
    Cb.LdLkp.RowsHold ((rowsF K (fun n => homeA.getD n default) g.rows.toList [a, b, c]).map
      (Lk6.Mid.rdRow A sl)) μ) ↔ _
  rw [e1, e2]
  exact And.comm

/-! ## The rows onto the ranges' group -/

/-- Rows added one by one: the statement behind them. -/
theorem addRowsFrom_st {L : Type} (g : ℕ) : ∀ (l : List Row) (d d' : _root_.Desc.Plain.DState L),
    addRowsFrom g l d = some d' → d'.st = withRows d.st g l
  | [], d, d', h => by
    cases h
    rfl
  | r :: l, d, d', h => by
    have h' : (addRowP d g r).bind (addRowsFrom g l) = some d' := h
    cases h1 : addRowP d g r with
    | none => rw [h1] at h'; cases h'
    | some d1 =>
      rw [h1] at h'
      unfold addRowP at h1
      split at h1
      · cases h1
        exact addRowsFrom_st g l _ d' h'
      · cases h1

/-- **The yes of the block that lays the rows**: all lookups have written their rows; the ranges'
group held no open row; behind it the group's open rows are all lookups' rows, in order, and nothing
else of the record has turned but the statement. -/
theorem rowsD_law {one : OneTime} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layRows one).decide s rs gs = .ok s') :
    s.base.rows.length = (lookupsOf one).length ∧ s'.base = s.base ∧ s'.grp = s.grp ∧
      ∃ G, s'.d.st.groups[s.grp]? = some G ∧ G.rows.toList = s.base.rows.flatten := by
  have h' : (do
      need "rng.0.rows: all lookups have laid their rows"
        (s.base.rows.length == (lookupsOf one).length)
      need "rng.0.rows: the ranges' group holds no open row and its test has not begun"
        ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun)
      let d ← named "rng.0.rows: a row does not fit the ranges' group"
        (addRowsP s.d s.grp s.base.rows.flatten)
      pure ({ s with d := d } : FirstState) : Except String FirstState) = .ok s' := h
  obtain ⟨_, h1, h'⟩ := bindX h'
  obtain ⟨_, h2, h'⟩ := bindX h'
  obtain ⟨d, h3, h'⟩ := bindX h'
  cases h'
  have e2 := needX h2
  have e3 := namedX h3
  cases hG : s.d.st.groups[s.grp]? with
  | none =>
    rw [hG] at e2
    cases e2
  | some G0 =>
    rw [hG] at e2
    have hemp : G0.rows = #[] := by
      have : G0.rows.isEmpty = true := by
        simp only [Option.any_some, Bool.and_eq_true] at e2
        exact e2.1
      simpa using this
    unfold addRowsP at e3
    split at e3
    · refine ⟨by simpa using needX h1, rfl, rfl,
        { G0 with rows := G0.rows ++ s.base.rows.flatten.toArray }, ?_, ?_⟩
      · show d.st.groups[s.grp]? = _
        rw [addRowsFrom_st _ _ _ _ e3]
        exact withRows_group _ _ _ _ hG
      · show (G0.rows ++ s.base.rows.flatten.toArray).toList = _
        rw [hemp]
        simp
    · cases e3

end Johnson.RunOne.Law.AtKeyD

#print axioms Johnson.RunOne.Law.AtKeyD.callerD_law
#print axioms Johnson.RunOne.Law.AtKeyD.claimsD_law
#print axioms Johnson.RunOne.Law.AtKeyD.layerD_law
#print axioms Johnson.RunOne.Law.AtKeyD.rowsByD_group
#print axioms Johnson.RunOne.Law.AtKeyD.doneD_iff
#print axioms Johnson.RunOne.Law.AtKeyD.rowsD_law
