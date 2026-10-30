--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeLayer.lean: THE SUB-PROTOCOL BEHIND A LOOKUP'S ROUNDS (`layer`,
Johnson/Desc/Key/Link.lean) ON THE KEY FILE'S FIRST CHAIN'S SHAPE (E2E/KeyShapeFirst.lean).
Definitions, statements and proofs. NOTHING IS SHOWN OF ANY PROVER: no completeness.

What is defined.
  `slotsAt home l`: the homes of a list of hidden values.   `keyFormB`: the two tests on the form of
    a claim on keys.
  `blocksB one i`: a public test: the own message's main table has at most 63 index bits, and each
    block's term has just so many variables.
  `layerBlock Q i`; `gLayer Q i`: the sub-protocol; it, on the shape. It asks: a lookup number i ·
    an open ledger in front of the gathering · the mark on what was heard · i lookups have written ·
    the homes (`homesB`, a function of the shape's list of homes) · the marks plain and keysOk ·
    `blocksB` · each claim's point's length. It lays: «a ledger, its shape not held» · the mark on
    what was heard false · a count of rows (the forms and three) · of each new claim on keys the
    homes of the slots that its form names.
What is shown.
  `added_paid`, `unpaid_false`, `leftB_false`: behind the gathering the second debt is marked: so
    the reader's two tests on the open lookup say no.
  `layerOrder_length`, `mapM_length`, `rowsInOrder_length`, `mapM_map'`: counts.
  `fold_slots`, `maskSide_slots`, `scale_slots`: the slots that a claim's mask form names are the
    homes of the hidden values that its form names, in order.
  `keys_aux`, `zip_one`, `keysB_one`, `lookAt_of`: the claims on a lookup's parts' keys: as many as
    parts; each passes the two tests on form (no written-out variable: the library's
    `pendOkKeys_weights`); the mark keysOk is kept.
  **`layer_exact`**: where `gLayer` returns at a state's shape, the sub-protocol's decision returns
    a state of the shape that it returns. NO TEST ON VALUES. By E2E/KeyLookupAround.lean's
    `layer_decide` and E2E/KeyRowsFit.lean's `rows_plain`.

Limits.
- `gLayer` asks more than the sub-protocol does: sufficient, not necessary. That `blocksB` passes at
  the intended sizes is shown nowhere here.
- The third test on a claim on keys, which compares values, is not treated: it is asked where the
  rows on the table are made.
- FORM ALONE: that what is written holds of anything is not touched.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyShapeFirst
import OnBytes.Tie.Pv.Lookup.PendOkKeys

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyShape
open OnBytes
open OnBytes.Params (WfPart WfLookup)
open OnBytes.Model (Fork Aff)
open ProofFile.Honest (CarriesR ReturnsR)
open VerifiableInference.Desc (Block named need Key.quietAt)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.First.Shape (LedSh ledSh)
open _root_.Desc.Plain (DState)
open AtPublicFiles.KeyLookup AtPublicFiles.RowsFit
open AtPublicFiles.AtFiles (keysB keysSlots)

/-! ## 1. Behind the gathering the second debt is marked -/

theorem added_paid (F : Fork) (o i : ℕ) (h : (F.owed[i]?).map (·.added) = some true) :
    ((F.paid o).owed[i]?).map (·.added) = some true := by
  show ((F.owed.modify o fun x => { x with added := true })[i]?).map (·.added) = some true
  rw [Array.getElem?_modify]
  split
  · cases hx : F.owed[i]? with
    | none => rw [hx] at h; cases h
    | some x => rfl
  · exact h

theorem unpaid_false {p : PG} {g : HeardG} {F : Fork} (h : doneG p g F = true) :
    unpaidG (F.paid g.owedObjects) g.owedPlanes = false := by
  unfold doneG at h
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at h
  unfold unpaidG
  rw [added_paid F _ _ h.2.2.1]
  rfl

/-! ## 2. Counts -/

theorem layerOrder_length {n : ℕ} (h : 1 ≤ n) : (layerOrder n).length = n + 3 := by
  unfold layerOrder
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
    List.length_nil]
  omega

theorem mapM_length {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length
  | [], r, h => by
    have h' : some [] = some r := h
    obtain rfl := Option.some.inj h'
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; cases h
    | some b =>
      rw [ha] at h
      cases hl : l.mapM f with
      | none => rw [hl] at h; cases h
      | some t =>
        rw [hl] at h
        obtain rfl : b :: t = r := Option.some.inj h
        rw [List.length_cons, List.length_cons, mapM_length f l t hl]

theorem rowsInOrder_length {planesAt : OnBytes.Row → Tensor → OnBytes.Row}
    {tab : List (Bool × ℕ × Bool)} {F : Fork} {home : Array Slot} {cls : List Claim}
    {rows : List OnBytes.Row} (h : rowsInOrder planesAt tab F home cls = some rows) :
    rows.length = tab.length := by
  unfold rowsInOrder at h
  dsimp only at h
  split at h
  · cases h
  · exact mapM_length _ _ _ h

/-! ## 3. The slots that a claim's mask form names -/

/-- The homes of a list of hidden values. -/
def slotsAt (home : List Slot) (l : List ℕ) : Option (List Slot) := l.mapM fun t => home[t]?

theorem fold_slots {F : Fork} {home : Array Slot} : ∀ (l : List (ℕ × E)) (init y : MaskForm × E),
    l.foldlM (fun (y : MaskForm × E) (t : ℕ × E) =>
      match home[t.1]?, F.shown t.1 with
      | some s, some v => some (y.1 ++ [(s, mulE t.2 (F.mf.getD t.1 zeroE))], addE y.2 (mulE t.2 v))
      | _, _ => none) init = some y →
    ∃ r, slotsAt home.toList (l.map (·.1)) = some r ∧ y.1.map (·.1) = init.1.map (·.1) ++ r
  | [], init, y, h => by
    have h' : some init = some y := h
    obtain rfl := Option.some.inj h'
    exact ⟨[], rfl, (List.append_nil _).symm⟩
  | t :: l, init, y, h => by
    rw [List.foldlM_cons] at h
    cases hs : home[t.1]? with
    | none => rw [hs] at h; cases h
    | some s =>
      cases hv : F.shown t.1 with
      | none => rw [hs, hv] at h; cases h
      | some v =>
        rw [hs, hv] at h
        obtain ⟨r, hr, e⟩ := fold_slots l _ y h
        refine ⟨s :: r, ?_, ?_⟩
        · unfold slotsAt at hr ⊢
          rw [List.map_cons, List.mapM_cons, Array.getElem?_toList, hs, hr]
          rfl
        · rw [e]
          simp

theorem maskSide_slots {F : Fork} {home : Array Slot} {a : Aff} {y : MaskForm × E}
    (h : maskSide F home a = some y) :
    slotsAt home.toList (a.slots.toList.map (·.1)) = some (y.1.map (·.1)) := by
  unfold maskSide at h
  split at h
  · cases h
  · rw [← Array.foldlM_toList] at h
    obtain ⟨r, hr, e⟩ := fold_slots _ _ y h
    rw [hr, e]
    rfl

theorem scale_slots (c : E) (m : MaskForm) : (Psc.scaleForm c m).map (·.1) = m.map (·.1) := by
  unfold Psc.scaleForm
  rw [List.map_map]
  rfl

/-! ## 4. The claims on a lookup's parts' keys -/

/-- The two tests on a claim's form. -/
def keyFormB (m : Wf.Matrix) (y : WfPart × Lkp.Keys) : Bool :=
  y.2.point.length == m.kCol + y.1.logPlaces && y.2.weights.tensors.all (·.denseVars.isEmpty)

theorem keys_aux (msg : ℕ) (m : Wf.Matrix) (W : WfLookup) (F : Fork) (home : Array Slot)
    (θ α : E) : ∀ (l : List (Array E × Aff)) (ps : List WfPart) (n : ℕ) (keys : List Lkp.Keys),
    l.map (·.1.size) = ps.map (fun p => m.kCol + p.logPlaces) →
    (l.zipIdx n).mapM (fun k => (maskSide F home k.1.2).map fun y =>
      Lkp.keysOf (Wf.lookupOf msg m W) θ α k.2 ⟨k.1.1.toList.reverse, y.1, y.2⟩) = some keys →
    ps.length = keys.length ∧ ((ps.zip keys).all (keyFormB m)) = true ∧
      l.mapM (fun k => slotsAt home.toList (k.2.slots.toList.map (·.1))) =
        some (keys.map fun k => k.masks.map (·.1))
  | [], [], _, keys, _, h => by
    have h' : some [] = some keys := h
    obtain rfl := Option.some.inj h'
    exact ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, hs, _ => by cases hs
  | _ :: _, [], _, _, hs, _ => by cases hs
  | q :: l, p :: ps, n, keys, hs, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at hs
    rw [List.zipIdx_cons, List.mapM_cons] at h
    cases hy : maskSide F home q.2 with
    | none => rw [hy] at h; cases h
    | some y =>
      rw [hy] at h
      cases hl : (l.zipIdx (n + 1)).mapM (fun k => (maskSide F home k.1.2).map fun y =>
          Lkp.keysOf (Wf.lookupOf msg m W) θ α k.2 ⟨k.1.1.toList.reverse, y.1, y.2⟩) with
      | none => rw [hl] at h; cases h
      | some t =>
        rw [hl] at h
        obtain rfl : Lkp.keysOf (Wf.lookupOf msg m W) θ α n ⟨q.1.toList.reverse, y.1, y.2⟩ :: t =
          keys := Option.some.inj h
        obtain ⟨a, b, c⟩ := keys_aux msg m W F home θ α l ps (n + 1) t hs.2 hl
        refine ⟨by rw [List.length_cons, List.length_cons, a], ?_, ?_⟩
        · rw [List.zip_cons_cons, List.all_cons, b, Bool.and_true]
          unfold keyFormB
          rw [(Wf.Proved.pendOkKeys_weights (Wf.lookupOf msg m W) θ α n
            ⟨q.1.toList.reverse, y.1, y.2⟩ rfl).1, Bool.and_true, beq_iff_eq]
          show q.1.toList.reverse.length = _
          rw [List.length_reverse, Array.length_toList]
          exact hs.1
        · rw [List.mapM_cons, maskSide_slots hy, c]
          show some (y.1.map (·.1) :: _) = some ((Psc.scaleForm (negE oneE) y.1).map (·.1) :: _)
          rw [scale_slots]

theorem zip_one {α β : Type} : ∀ (as : List α) (bs : List β) (a : α) (b : β),
    as[bs.length]? = some a → as.zip (bs ++ [b]) = as.zip bs ++ [(a, b)]
  | [], _, _, _, h => by cases h
  | x :: as, [], a, b, h => by
    obtain rfl : x = a := Option.some.inj h
    cases as <;> rfl
  | x :: as, y :: bs, a, b, h => by
    show (x, y) :: as.zip (bs ++ [b]) = (x, y) :: (as.zip bs ++ [(a, b)])
    rw [zip_one as bs a b (by simpa using h)]

/-- The mark on the claims on keys, with one lookup's claims more. -/
theorem keysB_one (m : Wf.Matrix) (lookups : List WfLookup) (keys : List (List Lkp.Keys))
    (W : WfLookup) (new : List Lkp.Keys) (hW : lookups[keys.length]? = some W)
    (h : keysB m lookups keys = true) (hn : W.parts.length = new.length)
    (hf : ((W.parts.zip new).all (keyFormB m)) = true) :
    keysB m lookups (keys ++ [new]) = true := by
  unfold keysB at h ⊢
  rw [zipT_eq] at h ⊢
  rw [zip_one lookups keys W new hW, List.all_append, h, Bool.true_and, List.all_cons,
    List.all_nil, Bool.and_true, zipT_eq, Bool.and_eq_true, beq_iff_eq]
  exact ⟨hn, hf⟩

/-! ## 5. The sub-protocol behind a lookup's rounds -/

variable (Q : Pub1) {Bk : Type} (bk : BackOf → Bk)

/-- A public test: the own message's main table has at most 63 index bits, and each block's term has
just so many variables. -/
def blocksB (one : Params.OneTime) (i : ℕ) : Bool :=
  decide (bitsV one ≤ 63) && (blocksOf one.ranges one.codes i).all fun bl =>
    (termOf one.ranges one.codes i (canon ((faceOfLkp (lookAt one i)).mu +
      (faceOfLkp (lookAt one i)).d)) bl).pairs.length == bitsV one

/-- Lookup number i's sub-protocol behind its rounds. -/
abbrev layerBlock (i : ℕ) : Block FirstState Claim :=
  (lookupLink Q.one Q.set i (lookAt Q.one i)).batch (VerifiableInference.Desc.claimsInBy
    (lookupLink Q.one Q.set i (lookAt Q.one i)).each
    (lookupLink Q.one Q.set i (lookAt Q.one i)).hear
    (lookupLink Q.one Q.set i (lookAt Q.one i)).order)

/-- It, on the shape. -/
def gLayer (i : ℕ) (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  let f := faceOfLkp (lookAt Q.one i)
  match Q.one.ranges.lookups[i]?, a.2.look.led, a.2.look.heard with
  | some W, some (some _), some h =>
    if h.mark && a.2.look.keys.length == i && homesB Q.one f a.2.look.home &&
        (fromKeys f).length == f.slots && a.2.look.plain && a.2.look.keysOk && blocksB Q.one i &&
        h.keys.map (·.1) == W.parts.map fun p => (Wf.matrixOf Q.one.lin).kCol + p.logPlaces then
      match h.keys.mapM fun k => slotsAt a.2.look.home k.2 with
      | some sl =>
        .ok (a.1, { a.2 with look := { a.2.look with
          led := some none, heard := some { h with mark := false }
          rows := a.2.look.rows ++ [h.rows + 3], keys := a.2.look.keys ++ [sl] } })
      | none => .error "the layer: a form on keys names a hidden value without a home"
    else .error "the layer: a guard on the shape"
  | _, _, _ => .error "the layer: no lookup of that number, no open ledger, or nothing heard"

theorem lookAt_of {one : Params.OneTime} {i : ℕ} {W : WfLookup}
    (h : one.ranges.lookups[i]? = some W) :
    lookAt one i = Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin) W := by
  unfold lookAt lookupsOf Wf.lookupsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

theorem mapM_map' {α β γ : Type} (f : α → β) (g : β → Option γ) : ∀ l : List α,
    (l.map f).mapM g = l.mapM fun a => g (f a)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map' f g l]

theorem leftB_false {p : PG} {g : HeardG} {F : Fork}
    (h : unpaidG (F.paid g.owedObjects) g.owedPlanes = false) : leftB p g F = false := by
  unfold leftB
  rw [h]
  rfl

theorem layer_exact (i : ℕ) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (s : FirstState) (t : Sh₁ Bk) (hg : gLayer Q i (sh₁ Q bk s) = .ok t) :
    ∃ s', (layerBlock Q i).decide s rs gs = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gLayer at hg
  dsimp only at hg
  split at hg
  case h_2 => cases hg
  rename_i W L h hW hled hheard
  split at hg
  case isFalse => cases hg
  rename_i h0
  split at hg
  case h_2 => cases hg
  rename_i sl hsl
  obtain rfl := Except.ok.inj hg
  simp only [Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨⟨⟨⟨⟨⟨hm, hk⟩, hhome⟩, hfk⟩, hplain⟩, hkok⟩, hbl⟩, hsz⟩ := h0
  -- the ledger and what was heard
  have hled' : (s.base.fork.map fun F => if stageOpen s then some (ledSh F) else none) =
      some (some L) := hled
  obtain ⟨G, hF, -⟩ := Option.map_eq_some_iff.1 hled'
  have hheard' : s.base.heard.map (heardSh Q s) = some h := hheard
  obtain ⟨g, hgd, rfl⟩ := Option.map_eq_some_iff.1 hheard'
  have hk' : s.base.keys.length = i := by
    have : (keysSlots s.base.keys).length = i := hk
    unfold keysSlots at this
    rwa [List.length_map] at this
  subst hk'
  -- the mark
  have hm' : heardB Q s g = true := hm
  unfold heardB at hm'
  rw [hF] at hm'
  simp only [Bool.and_eq_true, curAt] at hm'
  obtain ⟨⟨hlB, hoff⟩, hoff'⟩ := hm'
  obtain ⟨cl, G₂, hL⟩ := left_of_B hlB
  obtain ⟨rest, hp⟩ := hL.planes
  have hp' : planesG (faceOfLkp (lookAt Q.one s.base.keys.length)) g (G.paid g.owedObjects) [] =
      some (cl, G₂, rest) := hp
  rw [hp] at hoff'
  simp only [List.all_eq_true] at hoff hoff'
  -- the homes
  have hhome' : homesB Q.one (faceOfLkp (lookAt Q.one s.base.keys.length)) s.base.home.toList =
      true := hhome
  unfold homesB at hhome'
  rw [Bool.and_eq_true, beq_iff_eq] at hhome'
  obtain ⟨hlen, hzip⟩ := hhome'
  obtain ⟨o, k, e, ho⟩ := homesFrom_split (ownOk Q.one)
    (fromKeys (faceOfLkp (lookAt Q.one s.base.keys.length))) s.base.home.toList
    (hlen.trans hfk.symm) hzip
  have hhm : s.base.home = homes (faceOfLkp (lookAt Q.one s.base.keys.length)) o k := by
    unfold homes
    rw [e]
  have hsize : s.base.home.size = (faceOfLkp (lookAt Q.one s.base.keys.length)).slots := by
    rw [← Array.length_toList]
    exact hlen
  obtain ⟨rows, keys, hrows, hkeys, hdec⟩ := layer_decide Q.one Q.set s.base.keys.length
    (lookAt Q.one s.base.keys.length) rs gs hF hgd hsize hL
  obtain ⟨s', hs'⟩ : ∃ s' : FirstState, s' = { s with base := { s.base with
      fork := some ((G₂.paid g.owedPlanes).paid g.owedJoin)
      rows := s.base.rows ++ [rows], keys := s.base.keys ++ [keys] } } := ⟨_, rfl⟩
  rw [← hs'] at hdec
  refine ⟨s', hdec, ?_⟩
  -- the new rows
  unfold blocksB at hbl
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hbl
  obtain ⟨hV, hT⟩ := hbl
  have ho' : ∀ y ∈ o, y.oracle = Q.one.ranges.messageId ∧ y.index < sizeB Q.one ∧
      y.index < padP Q.one := by
    intro y hy
    have := ho y hy
    unfold ownOk at this
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  rw [hhm] at hrows
  have hnew := rows_plain (x := Q.one.ranges) (codes := Q.one.codes) (i := s.base.keys.length)
    (y := lookAt Q.one s.base.keys.length) (B := sizeB Q.one) (P := padP Q.one) (V := bitsV Q.one)
    ho' (fun a ha => ownOnly_of (hL.rows a ha) (off_of_B (hoff a ha)))
    (fun c hc => ownOnly_of (hL.leads c hc) (off_of_B (hoff' c hc))) (planesG_pairs hp) hT hV hrows
  have hrl : rows.length = g.rows.size + 3 := by
    rw [rowsInOrder_length hrows, layerOrder_length hL.one, Array.length_toList]
  -- the new claims on keys
  have hsz' : g.keys.map (·.1.size) =
      W.parts.map fun p => (Wf.matrixOf Q.one.lin).kCol + p.logPlaces := by
    have e1 : (heardSh Q s g).keys.map (·.1) = g.keys.map (·.1.size) := by
      unfold heardSh
      rw [List.map_map]
      rfl
    rw [← e1]
    exact hsz
  unfold keyClaims at hkeys
  rw [lookAt_of hW] at hkeys
  obtain ⟨ka, kb, kc⟩ := keys_aux _ _ W _ _ _ _ g.keys W.parts 0 keys hsz' hkeys
  have hsl' : g.keys.mapM (fun q => slotsAt s.base.home.toList (q.2.slots.toList.map (·.1))) =
      some sl := by
    have e2 := mapM_map' (fun q : Array E × Aff => (q.1.size, q.2.slots.toList.map (·.1)))
      (fun q : ℕ × List ℕ => slotsAt s.base.home.toList q.2) g.keys
    rw [← e2]
    exact hsl
  rw [kc] at hsl'
  obtain rfl := Option.some.inj hsl'
  have hu := unpaid_false hL.done
  have f1 : s'.base.fork = some ((G₂.paid g.owedPlanes).paid g.owedJoin) := by rw [hs']
  have f2 : s'.base.heard = some g := by rw [hs']; exact hgd
  have f3 : s'.base.home = s.base.home := by rw [hs']
  have f4 : s'.base.rows = s.base.rows ++ [rows] := by rw [hs']
  have f5 : s'.base.keys = s.base.keys ++ [keys] := by rw [hs']
  have hst : stageOpen s' = false := by
    unfold stageOpen
    rw [f1, f2]
    exact hu
  have hB : heardB Q s' g = false := by
    unfold heardB
    rw [f1]
    simp only [leftB_false hu, Bool.false_and]
  have hpl : s.base.rows.flatten.all
      (plainRowB (msgOf Q.one) (sizeB Q.one) (padP Q.one) (bitsV Q.one)) = true := hplain
  have hko : keysB (Wf.matrixOf Q.one.lin) Q.one.ranges.lookups s.base.keys = true := hkok
  have hlk : lookSh Q s' =
      { lookSh Q s with
        led := some none, heard := some { heardSh Q s g with mark := false }
        rows := (lookSh Q s).rows ++ [(heardSh Q s g).rows + 3]
        keys := (lookSh Q s).keys ++ [keys.map fun q => q.masks.map (·.1)] } := by
    unfold lookSh
    rw [f1, f2, f3, f4, f5, hst]
    simp only [LookSh.mk.injEq, Option.map_some]
    refine ⟨rfl, ?_, trivial, ?_, ?_, ?_, ?_⟩
    · unfold heardSh
      rw [hB]
    · rw [List.map_append, List.map_cons, List.map_nil, hrl]
      rfl
    · rw [hpl, List.flatten_append, List.all_append, hpl, Bool.true_and]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.all_eq_true]
      exact fun r hr => plainRowB_iff.2 (hnew r hr)
    · unfold keysSlots
      rw [List.map_append]
      rfl
    · rw [hko]
      exact keysB_one _ _ _ W keys hW hko ka kb
  have hd : s'.d = s.d := by rw [hs']
  unfold sh₁ locSh
  rw [hlk, hd, hs']

end AtPublicFiles.KeyShape

#print axioms AtPublicFiles.KeyShape.layer_exact
#print axioms AtPublicFiles.KeyShape.keys_aux
#print axioms AtPublicFiles.KeyShape.keysB_one
#print axioms AtPublicFiles.KeyShape.unpaid_false
#print axioms AtPublicFiles.KeyShape.rowsInOrder_length
#print axioms AtPublicFiles.KeyShape.maskSide_slots
