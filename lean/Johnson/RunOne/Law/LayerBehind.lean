-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LayerBehind.lean: THE
TABLE'S PROMISE BEHIND THE LAYER, FROM THE PIECE'S YES: at the maker's own pieces 5 and 11 of the
key file's first chain: the table's promise with its history in front, and the piece's yes, give the
table's promise behind (borders 6 and 12): the third of the four implications that a tie by
Leads.conseq asks at the fields r1_5 and r1_11.

Main names:
  layPut: the state behind the layer: a ledger put; a list of rows and a list of claims on keys
    appended.
  done_step: doneB's step from d lookups done to d + 1.
  yes_layer: the layer's yes from s to s', where the record holds what the kind's block has left:
    s' is layPut of s; the ledger behind has the ledger in front's next and ns, is sized, and ALL
    ITS SLOTS BELOW next ARE FILLED (the layer's own last test, doneG); the rows are not none; there
    are as many claims on keys as the lookup has parts.
  on_behind_layer: On₁' … (2 + 6 l + 3) a, the piece's out a τ = some b ⊢ On₁ … (2 + 6 l + 4) b,
    l < 2.

Object: the layer at its places in Key.descriptionFromSource X N P; the promise on₁ (Johnson/RunOne/KeyRows1At.lean).
User: FieldsLayer.lean calls on_behind_layer; StepSide4.lean calls yes_layer and done_step.
Letters and premises: those of on_behind_k3 (Johnson/RunOne/Law/TieBehindK3.lean), none more.

Limits. The history behind is not added here. Nothing on the claims. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieBehindK3
import Johnson.RunOne.Law.PlanesInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.LayerBehind
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Model (Fork)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where lookupSeat pinned
  lookupsOf sentB groupB doneB core₁ shape₁ shape₁_step SamePins onAt_fwd strsStay_of_out layer
  caller lookupPlace rowsInOrder layerOrder)
open Johnson.RunOne.Sound (FK fk_link_at)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ ties₁ tiesA sizesB open₁ on₁ on₁_two
  free₁_step CollCell)
open Johnson.RunOne.Law.SeatsKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.WalkAtFK
open Johnson.RunOne.Law.RecOfHist
open Johnson.RunOne.Law.TieBehind
open Johnson.RunOne.Law.AtKeyD
open Johnson.RunOne.Law.PlanesInv
open LPFD (On₁')

/-- **The state behind the layer.** -/
def layPut (s : FirstState) (F' : Fork) (rows : List OnBytes.Row) (keys : List Lkp.Keys) :
    FirstState :=
  { s with base := { s.base with
      fork := some F'
      rows := s.base.rows ++ [rows]
      keys := s.base.keys ++ [keys] } }

variable (one : OneTime) (s : FirstState) (F' : Fork) (rows : List OnBytes.Row)
  (keys : List Lkp.Keys)

/-- **doneB's step**: d lookups have laid; the layer of lookup d lays rows that are not none and as
many claims on keys as the lookup has parts. -/
theorem done_step (d : ℕ) (L : WfLookup) (hL : one.ranges.lookups[d]? = some L)
    (hr : s.base.rows.length = d) (hk : s.base.keys.length = d) (hne : rows ≠ [])
    (hlen : keys.length = L.parts.length)
    (h : doneB (plan₁ one) (readers₁ one) 2 d s = true) :
    doneB (plan₁ one) (readers₁ one) 2 (d + 1) (layPut s F' rows keys) = true := by
  unfold doneB at h ⊢
  refine List.all_eq_true.2 fun l hl => ?_
  have h0 := List.all_eq_true.1 h l hl
  have eR : (readers₁ one).rowsAt (layPut s F' rows keys) l = (s.base.rows ++ [rows])[l]? := rfl
  have eK : (readers₁ one).keysAt (layPut s F' rows keys) l =
      ((s.base.keys ++ [keys])[l]?).bind (Johnson.RunOne.KeyReaders.pendingOf one l) := rfl
  have eR0 : (readers₁ one).rowsAt s l = s.base.rows[l]? := rfl
  have eK0 : (readers₁ one).keysAt s l =
      (s.base.keys[l]?).bind (Johnson.RunOne.KeyReaders.pendingOf one l) := rfl
  rcases Nat.lt_trichotomy l d with hlt | rfl | hgt
  · rw [if_pos hlt] at h0
    rw [if_pos (Nat.lt_succ_of_lt hlt), eR, eK, List.getElem?_append_left (by omega),
      List.getElem?_append_left (by omega), ← eR0, ← eK0]
    exact h0
  · rw [if_pos (Nat.lt_succ_self _), eR, eK,
      List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hr, hk,
      Nat.sub_self]
    have e : Johnson.RunOne.KeyReaders.pendingOf one l keys = some ((L.parts.zip keys).map
        fun x => Wf.pendingRow (Wf.matrixOf one.lin) L x.1 x.2
          (Wf.eqPlaces (Wf.matrixOf one.lin) x.2.point)) := by
      unfold Johnson.RunOne.KeyReaders.pendingOf
      rw [hL]
      rfl
    show ((some rows).any (fun r => !r.isEmpty) &&
      (match Johnson.RunOne.KeyReaders.pendingOf one l keys, one.ranges.lookups[l]? with
        | some ks, some L => ks.length == L.parts.length
        | _, _ => false)) = true
    rw [e, hL]
    have e1 : (some rows).any (fun r => !r.isEmpty) = true := by
      cases rows with
      | nil => exact absurd rfl hne
      | cons _ _ => rfl
    rw [e1]
    show (true && (((L.parts.zip keys).map _).length == L.parts.length)) = true
    rw [List.length_map, List.length_zip, hlen, Nat.min_self]
    simp
  · rw [if_neg (by omega), eR, eK, List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by simp; omega)]
    rfl

/-- core₁'s step across the layer of lookup 0: border 5 → 6. -/
theorem c_5_6 (G : Fork) (hG : s.base.fork = some G) (hn : F'.next = G.next) (hs : F'.ns = G.ns)
    (hz : PscRun.Sized F')
    (hfill : ∀ j, j < F'.next → F'.gotF.getD j false = true)
    (hd : doneB (plan₁ one) (readers₁ one) 2 0 s = true →
      doneB (plan₁ one) (readers₁ one) 2 1 (layPut s F' rows keys) = true)
    (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 5 s = true) :
    core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 6 (layPut s F' rows keys) =
      true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 0 s && ((readers₁ one).pile s).isNone) &&
      (s.base.heard.isSome && s.base.home.size == slots₁ one 0 && _)) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h'
  obtain ⟨h1a, h1p⟩ := Bool.and_eq_true_iff.1 h1
  obtain ⟨h1b, h1d⟩ := Bool.and_eq_true_iff.1 h1a
  have h3 := (Bool.and_eq_true_iff.1 h2).1
  have h4 : ((s.base.fork.map _).any _) = true := (Bool.and_eq_true_iff.1 h2).2
  rw [hG] at h4
  have h5 : (G.next == slots₁ one 0 && G.ns == slots₁ one 0 &&
      (G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns)) = true := h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  have hf : ((List.range F'.next).all fun j => F'.gotF.getD j false) = true :=
    List.all_eq_true.2 fun j hj => hfill j (List.mem_range.1 hj)
  show ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 1 (layPut s F' rows keys) &&
      ((readers₁ one).pile s).isNone) &&
      (s.base.heard.isSome && s.base.home.size == slots₁ one 0 &&
        (F'.next == slots₁ one 0 && F'.ns == slots₁ one 0 &&
          (F'.vp.size == F'.ns && F'.mf.size == F'.ns && F'.gotF.size == F'.ns) &&
          (List.range F'.next).all fun j => F'.gotF.getD j false))) = true
  rw [h1b, hd h1d, h1p, h3, hf]
  simp [hn, hs, h5.1.1, h5.1.2, hz.1, hz.2.1, hz.2.2]

/-- The ties' step across the layer of lookup 0. -/
theorem t_5_6 (h : ties₁ one 5 s = true) : ties₁ one 6 (layPut s F' rows keys) = true := by
  have h' : (tiesA one 5 s && (s.base.rows.length == 0 && s.base.keys.length == 0 && _ && _ && _ &&
      VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots) && sizesB one 5 s) = true := h
  obtain ⟨h1, h3⟩ := Bool.and_eq_true_iff.1 h'
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  show (tiesA one 5 s && ((s.base.rows ++ [rows]).length == 1 &&
      (s.base.keys ++ [keys]).length == 1 && true && true && true &&
      VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots) && sizesB one 5 s) = true
  rw [h1, h3]
  simp [h2.1.1.1.1.1, h2.1.1.1.1.2, h2.2]

theorem sh_5_6 (G : Fork) (hG : s.base.fork = some G) (hn : F'.next = G.next)
    (hs : F'.ns = G.ns) (hz : PscRun.Sized F')
    (hfill : ∀ j, j < F'.next → F'.gotF.getD j false = true)
    (hd : doneB (plan₁ one) (readers₁ one) 2 0 s = true →
      doneB (plan₁ one) (readers₁ one) 2 1 (layPut s F' rows keys) = true)
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 5 s = true) :
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 6 (layPut s F' rows keys) =
      true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 5 6 s _
    (t_5_6 one s F' rows keys) (c_5_6 one s F' rows keys G hG hn hs hz hfill hd) h

/-- core₁'s step across the layer of lookup 1: border 11 → 12. -/
theorem c_11_12 (G : Fork) (hG : s.base.fork = some G) (hn : F'.next = G.next) (hs : F'.ns = G.ns)
    (hz : PscRun.Sized F')
    (hfill : ∀ j, j < F'.next → F'.gotF.getD j false = true)
    (hd : doneB (plan₁ one) (readers₁ one) 2 1 s = true →
      doneB (plan₁ one) (readers₁ one) 2 2 (layPut s F' rows keys) = true)
    (h : core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 11 s = true) :
    core₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 12 (layPut s F' rows keys) =
      true := by
  have h' : ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 1 s && ((readers₁ one).pile s).isNone) &&
      (s.base.heard.isSome && s.base.home.size == slots₁ one 1 && _)) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h'
  obtain ⟨h1a, h1p⟩ := Bool.and_eq_true_iff.1 h1
  obtain ⟨h1b, h1d⟩ := Bool.and_eq_true_iff.1 h1a
  have h3 := (Bool.and_eq_true_iff.1 h2).1
  have h4 : ((s.base.fork.map _).any _) = true := (Bool.and_eq_true_iff.1 h2).2
  rw [hG] at h4
  have h5 : (G.next == slots₁ one 1 && G.ns == slots₁ one 1 &&
      (G.vp.size == G.ns && G.mf.size == G.ns && G.gotF.size == G.ns)) = true := h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h5
  have hf : ((List.range F'.next).all fun j => F'.gotF.getD j false) = true :=
    List.all_eq_true.2 fun j hj => hfill j (List.mem_range.1 hj)
  show ((sentB (plan₁ one) (readers₁ one) s 0 && sentB (plan₁ one) (readers₁ one) s 1 &&
      !sentB (plan₁ one) (readers₁ one) s 2 && groupB (readers₁ one) s false 0 &&
      doneB (plan₁ one) (readers₁ one) 2 2 (layPut s F' rows keys) &&
      ((readers₁ one).pile s).isNone) &&
      (s.base.heard.isSome && s.base.home.size == slots₁ one 1 &&
        (F'.next == slots₁ one 1 && F'.ns == slots₁ one 1 &&
          (F'.vp.size == F'.ns && F'.mf.size == F'.ns && F'.gotF.size == F'.ns) &&
          (List.range F'.next).all fun j => F'.gotF.getD j false))) = true
  rw [h1b, hd h1d, h1p, h3, hf]
  simp [hn, hs, h5.1.1, h5.1.2, hz.1, hz.2.1, hz.2.2]

/-- The ties' step across the layer of lookup 1. -/
theorem t_11_12 (h : ties₁ one 11 s = true) : ties₁ one 12 (layPut s F' rows keys) = true := by
  have h' : (tiesA one 11 s &&
      (s.base.rows.length == 1 && s.base.keys.length == 1 && _ && _ && _ &&
        VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots) &&
      sizesB one 11 s) = true := h
  obtain ⟨h1, h3⟩ := Bool.and_eq_true_iff.1 h'
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  show (tiesA one 11 s && ((s.base.rows ++ [rows]).length == 2 &&
      (s.base.keys ++ [keys]).length == 2 && true && true && true &&
      VerifiableInference.Desc.Sound.bookStepB 0 s.d.book s.d.roots) && sizesB one 11 s) = true
  rw [h1, h3]
  simp [h2.1.1.1.1.1, h2.1.1.1.1.2, h2.2]

theorem sh_11_12 (G : Fork) (hG : s.base.fork = some G) (hn : F'.next = G.next)
    (hs : F'.ns = G.ns) (hz : PscRun.Sized F')
    (hfill : ∀ j, j < F'.next → F'.gotF.getD j false = true)
    (hd : doneB (plan₁ one) (readers₁ one) 2 1 s = true →
      doneB (plan₁ one) (readers₁ one) 2 2 (layPut s F' rows keys) = true)
    (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 11 s = true) :
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 12 (layPut s F' rows keys) =
      true :=
  shape₁_step (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 11 12 s _
    (t_11_12 one s F' rows keys) (c_11_12 one s F' rows keys G hG hn hs hz hfill hd) h

section
variable {XI Cells Mm Smp Rec W : Type} {C : _root_.Run.PQ.CK} (F : FileDescription XI) (Fr : Frame)
  (Gr : Reading (Xi × FirstState) Cells Mm Smp Rec) (at_ : Where) (one : OneTime)
  (R : KRead Cells Mm) (coll : Strs → Rec → Prop)
  (hP : ∀ (p : Xi) (s : FirstState) (F' : Fork) (rows : List OnBytes.Row) (keys : List Lkp.Keys),
    SamePins Gr (p, s) (p, layPut s F' rows keys))

include hP

/-- **The table's promise behind the layer of lookup 0**: border 5 → 6. -/
theorem on_5_6 (pc : Piece C Fr (Xi × FirstState) Claim W)
    (hbase : ∀ j ∈ pinned (open₁ 2 5), (at_ j).1 < pc.base) (hcoll : CollCell coll)
    (a b : (Xi × FirstState) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds))
    (hout : pc.ior.red.out a τ = some b) (F' : Fork) (rows : List OnBytes.Row)
    (keys : List Lkp.Keys) (hb : b.1 = (a.1.1, layPut a.1.2 F' rows keys)) (G : Fork)
    (hG : a.1.2.base.fork = some G) (hn : F'.next = G.next) (hs : F'.ns = G.ns)
    (hz : PscRun.Sized F')
    (hfill : ∀ j, j < F'.next → F'.gotF.getD j false = true)
    (hd : doneB (plan₁ one) (readers₁ one) 2 0 a.1.2 = true →
      doneB (plan₁ one) (readers₁ one) 2 1 (layPut a.1.2 F' rows keys) = true)
    (h : on₁ F Fr Gr at_ one R coll 5 a) : on₁ F Fr Gr at_ one R coll 6 b := by
  have h2 := on₁_two F Fr Gr at_ one R coll 5 a h
  obtain ⟨⟨p, s⟩, y⟩ := a
  obtain ⟨b1, y'⟩ := b
  obtain rfl : b1 = (p, layPut s F' rows keys) := hb
  have Hy := strsStay_of_out F Fr at_ pc (open₁ 2 5) hbase _ _ τ hout
  unfold on₁ at h ⊢
  rw [h2] at h ⊢
  refine onAt_fwd F Gr at_ _ _ _ _ _ _ _ _ _ _ _ (open₁ 2 5) (open₁ 2 6) rfl p s _ _ _ rfl
    (hP p s F' rows keys) Hy
    (free₁_step F Gr at_ one R coll 5 6 p s _ _ _ (hP p s F' rows keys) hcoll Hy rfl rfl
      (by omega) (fun h18 => absurd h18 (by omega)) (fun _ h => h) fun h => h)
    (sh_5_6 one s F' rows keys G hG hn hs hz hfill hd) h

/-- **The table's promise behind the layer of lookup 1**: border 11 → 12. -/
theorem on_11_12 (pc : Piece C Fr (Xi × FirstState) Claim W)
    (hbase : ∀ j ∈ pinned (open₁ 2 11), (at_ j).1 < pc.base) (hcoll : CollCell coll)
    (a b : (Xi × FirstState) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds))
    (hout : pc.ior.red.out a τ = some b) (F' : Fork) (rows : List OnBytes.Row)
    (keys : List Lkp.Keys) (hb : b.1 = (a.1.1, layPut a.1.2 F' rows keys)) (G : Fork)
    (hG : a.1.2.base.fork = some G) (hn : F'.next = G.next) (hs : F'.ns = G.ns)
    (hz : PscRun.Sized F')
    (hfill : ∀ j, j < F'.next → F'.gotF.getD j false = true)
    (hd : doneB (plan₁ one) (readers₁ one) 2 1 a.1.2 = true →
      doneB (plan₁ one) (readers₁ one) 2 2 (layPut a.1.2 F' rows keys) = true)
    (h : on₁ F Fr Gr at_ one R coll 11 a) : on₁ F Fr Gr at_ one R coll 12 b := by
  have h2 := on₁_two F Fr Gr at_ one R coll 11 a h
  obtain ⟨⟨p, s⟩, y⟩ := a
  obtain ⟨b1, y'⟩ := b
  obtain rfl : b1 = (p, layPut s F' rows keys) := hb
  have Hy := strsStay_of_out F Fr at_ pc (open₁ 2 11) hbase _ _ τ hout
  unfold on₁ at h ⊢
  rw [h2] at h ⊢
  refine onAt_fwd F Gr at_ _ _ _ _ _ _ _ _ _ _ _ (open₁ 2 11) (open₁ 2 12) rfl p s _ _ _ rfl
    (hP p s F' rows keys) Hy
    (free₁_step F Gr at_ one R coll 11 12 p s _ _ _ (hP p s F' rows keys) hcoll Hy rfl rfl
      (by omega) (fun h18 => absurd h18 (by omega)) (fun _ h => h) fun h => h)
    (sh_11_12 one s F' rows keys G hG hn hs hz hfill hd) h

end

/-- The table's reading at the first chain does not read what the layer writes. -/
theorem samePins_lay {Cells Mm Smp Rec : Type} (B : BaseSt Cells Mm Smp Rec) (p : Xi)
    (s : FirstState) (F' : Fork) (rows : List OnBytes.Row) (keys : List Lkp.Keys) :
    SamePins B.h₁ (p, s) (p, layPut s F' rows keys) :=
  ⟨fun _ _ => rfl, rfl⟩

/-- rowsInOrder's list, at the layer's own order, is not none. -/
theorem rows_ne {planesAt : OnBytes.Row → Tensor → OnBytes.Row} {n : ℕ} {F : Fork}
    {home : Array Slot} {cls : List Claim} {rows : List OnBytes.Row}
    (h : rowsInOrder planesAt (layerOrder n) F home cls = some rows) : rows ≠ [] := by
  unfold rowsInOrder at h
  dsimp only at h
  split_ifs at h
  have e := (mapM_getD _ _ _ h).1
  rintro rfl
  unfold layerOrder at e
  simp at e

/-- **What the layer's yes says of the record behind**, where the record in front holds what the
kind's own block has left. -/
theorem yes_layer {one : OneTime} {set : Setting} {i : ℕ}
    {x : VerifiableInference.Desc.Key.Lookup} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hH : HeardOk lookupSeat (lookupPlace set i x) s)
    (hd : (layer one set i x
      (claimsIn [caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)]
        [(1, "objects"), (1, "planes"), (1, "guests")])).decide s rs gs = .ok s') :
    ∃ G F' rows keys, s.base.fork = some G ∧ s' = layPut s F' rows keys ∧ F'.next = G.next ∧
      F'.ns = G.ns ∧ PscRun.Sized F' ∧ (∀ j, j < F'.next → F'.gotF.getD j false = true) ∧
      rows ≠ [] ∧ keys.length = (faceOfLkp x).parts.length := by
  obtain ⟨G, g, hG, hg, hS, hnext, -, hk1, -⟩ := hH
  obtain ⟨cls, s1, F, g', rows, keys, hc, hF, hg', hrows, hkeys, hdone, rfl⟩ := layerD_done hd
  obtain ⟨pl, H', u, hpl, -, rfl⟩ := claimsD_law hG hg hc
  obtain rfl : H'.paid g.owedPlanes = F := Option.some.inj hF
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  obtain ⟨hrun, -, -⟩ := planes_inv hpl
  obtain ⟨n1, n2, -, n4, n5, n6⟩ := hideRun_same hrun
  obtain ⟨-, d2, -⟩ := doneG_parts hdone
  have e1 : H'.next = G.next := n1
  have e2 : H'.ns = G.ns := n2
  refine ⟨G, (H'.paid g.owedPlanes).paid g.owedJoin, rows, keys, hG, rfl, e1, e2,
    ⟨?_, ?_, ?_⟩, fun j hj => ?_, rows_ne hrows, ?_⟩
  · show H'.vp.size = H'.ns
    rw [e2]
    exact n4.trans hS.1
  · show H'.mf.size = H'.ns
    rw [e2]
    exact n5.trans hS.2.1
  · show H'.gotF.size = H'.ns
    rw [e2]
    exact n6.trans hS.2.2
  · have hj' : j < (faceOfLkp x).slots := by
      have e3 : H'.next = 0 + (faceOfLkp x).slots := e1.trans hnext
      have hj2 : j < H'.next := hj
      omega
    have := d2 j hj'
    rwa [show (lookupPlace set i x).first + j = j from Nat.zero_add j] at this
  · have e := (mapM_getD _ _ _ hkeys).1
    rw [e, List.length_zipIdx]
    exact hk1

variable {W Cells Mm Smp Rec : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD) (B : BaseSt Cells Mm Smp Rec)
  (at_ : Where) (R : KRead Cells Mm) (coll : Strs → Rec → Prop)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)

/-- **THE TABLE'S PROMISE BEHIND THE LAYER.** -/
theorem on_behind_layer (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0)
    (hn : X.Y.k.oneTime.ranges.lookups.length = 2) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hcoll : CollCell coll) (l : ℕ) (hl : l < 2) (p)
    (hq : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
        dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2 + 6 * l + 3]? = some p)
    (hbase : ∀ j ∈ [0, 1], (at_ j).1 < p.base) (a b : (Xi × FirstState) × (fr₁ D).E.Str)
    (τ : Iop.Tr (uLT (ckP .two) p.ds)) (hon : On₁' X N P D B at_ R coll (2 + 6 * l + 3) a)
    (hout : p.ior.red.out a τ = some b) : On₁ X N P D B at_ R coll (2 + 6 * l + 4) b := by
  have hl' : l < X.Y.k.oneTime.ranges.lookups.length := by rw [hn]; exact hl
  have hW := fk_admitted X N P hp
  obtain ⟨blk, hblk⟩ : ∃ blk, blk = layer X.Y.k.oneTime X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
        (Lof X.Y.k.oneTime l))
      (claimsIn [caller X.Y.k.oneTime l (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)),
        lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l
              (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
                (Lof X.Y.k.oneTime l)))]
        [(1, "objects"), (1, "planes"), (1, "guests")]) := ⟨_, rfl⟩
  have hpb : p.b = held blk := by
    have h1 := LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (2 + 6 * l + 3) p hq
    obtain ⟨c0, c4, c5, hF, -, -, -⟩ := link_flat X.Y.k.oneTime X.set l
      (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
        (Lof X.Y.k.oneTime l))
    have h2 := fk_link_at X N P l 3 (by omega) _ (look_at X.Y.k.oneTime l hl')
    rw [hF] at h2
    have h3 : (c₁ :: k₁)[2 + 6 * l + 3]? = some blk := by
      rw [← q₁, Nat.add_assoc, hblk]
      exact h2
    rw [List.getElem?_map, h3] at h1
    exact (Option.some.inj h1).symm
  have hrec := rec_of_hist D a.2 hp hR ha (2 + 6 * l + 3) (by rw [hn]; omega) a.1 hon.2
  rw [Nat.add_assoc] at hrec
  obtain ⟨⟨hI, hH⟩, -⟩ := (recAt_link X l 3 (by omega) a.1.2).1 hrec
  have hd := piece_decides_at p a τ b hout
  rw [hpb] at hd
  obtain ⟨e1, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  rw [hblk] at hd'
  obtain ⟨G, F', rows, keys, hG, e2, g1, g2, g3, g4, g5, g6⟩ := yes_layer hH hd'
  have hb1 : b.1 = (a.1.1, layPut a.1.2 F' rows keys) := Prod.ext e1 e2
  have hlen : keys.length = (Lof X.Y.k.oneTime l).parts.length := by
    rw [g6]
    exact List.length_map _
  have hstep := done_step X.Y.k.oneTime a.1.2 F' rows keys l (Lof X.Y.k.oneTime l)
    (tests_at hW hl').1 hI.2.2.1 hI.2.2.2.1 g5 hlen
  have c2 : l = 0 ∨ l = 1 := by omega
  rcases c2 with rfl | rfl
  · exact on_5_6 (Fk X N P) (fr₁ D) B.h₁ at_ X.Y.k.oneTime R coll (samePins_lay B) p hbase hcoll a b
      τ hout F' rows keys hb1 G hG g1 g2 g3 g4 hstep hon.1
  · exact on_11_12 (Fk X N P) (fr₁ D) B.h₁ at_ X.Y.k.oneTime R coll (samePins_lay B) p hbase hcoll a
      b τ hout F' rows keys hb1 G hG g1 g2 g3 g4 hstep hon.1

end Johnson.RunOne.Law.LayerBehind

#print axioms Johnson.RunOne.Law.LayerBehind.done_step
#print axioms Johnson.RunOne.Law.LayerBehind.c_5_6
#print axioms Johnson.RunOne.Law.LayerBehind.t_5_6
#print axioms Johnson.RunOne.Law.LayerBehind.c_11_12
#print axioms Johnson.RunOne.Law.LayerBehind.t_11_12
#print axioms Johnson.RunOne.Law.LayerBehind.sh_5_6
#print axioms Johnson.RunOne.Law.LayerBehind.sh_11_12
#print axioms Johnson.RunOne.Law.LayerBehind.on_5_6
#print axioms Johnson.RunOne.Law.LayerBehind.on_11_12
#print axioms Johnson.RunOne.Law.LayerBehind.samePins_lay
#print axioms Johnson.RunOne.Law.LayerBehind.rows_ne
#print axioms Johnson.RunOne.Law.LayerBehind.yes_layer
#print axioms Johnson.RunOne.Law.LayerBehind.on_behind_layer
