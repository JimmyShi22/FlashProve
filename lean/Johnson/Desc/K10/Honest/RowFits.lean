-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/RowFits.lean: AT EVERY ELEMENT THAT "BAT" MAY DRAW THE BATCHING RETURNS A ROW,
AND THAT ROW PASSES THE FOLD's TEST ON ITS SIZES: from facts on the group's rows that do not name that
element. Theorems on the verifier's own text (`Own.batch`, Johnson/Desc/Own/Batch.lean;
`Own.foldRowFits`, Johnson/Desc/Own/Fold.lean). It names no frame of an honest side.

Why. Two of the facts in front of the closing of a segment read the element x that "BAT" draws
(`CloseFront.combine`, `CloseFront.rowfits`, Johnson/Desc/K10/Honest/Front.lean). Here both follow, at
every x, from facts that name no x.

What is asked. The group is in order (`GroupOk`) and the layout is the statement's; every row meets
what the adding of a row tests (`RowIn`, Johnson/Desc/Means/Says.lean; a member's sample rows, which
do not pass the adding, are asked the same); EVERY STRUCTURED VECTOR AMONG A ROW's TERMS ON A MAIN
TABLE IS IN ORDER (`Tensor.ok`: `RowIn` does not ask that of terms; of forms it does);
the group's main table has at most 63 index bits; the fold's shape has the layout's numbers and the
group's codes, and the mask code's message length is a power of two.

  `TOk`, `All`        a structured vector's slice lies in its vector and its written-out variables are
                     in order; a property of all structured vectors of a form
  `KQ`, `Inv`         what is kept along the laying: every structured vector of the form on the main
                     table is `TOk`; each separate form is on a kept member, has that member's
                     table's index bits, and is in order
  `onKept_inv`        a change of one kept member's form keeps a property of all separate forms
  `lays_inv`, `lays_dsize`, `combine_inv`   along the laying and the batching
  `batch_returns`     the batching returns a row at every x: `combine_means`
                     (Johnson/Desc/Means/Combine.lean), said of `Own.batch`
  `batch_rowfits`     THE ROW THAT IT RETURNS PASSES `Own.foldRowFits`

By: `combine_means`; `combine_cfits` (Johnson/Desc/Means/Shape.lean): the variables and indices of the
form on the main table; `inOrder_insertChoice` (OnBytes/Slice/BlkProxOrder.lean); `Tensor.addTo_size`
(OnBytes/Iop/SpreadLaws.lean); `batch_agrees` (Johnson/Desc/Own/BatchAgree.lean); `foldRowFits_iff`,
`formFits_iff`, `tensorInOrder_iff` (Johnson/Desc/Own/FoldMean.lean, ShapesMean.lean).

Limits. That the rows of a group which an honest run leaves meet what is asked is not shown here.
Nothing on the values of the row. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.Means.Shape
import OnBytes.Slice.BlkProxOrder
import OnBytes.Iop.SpreadLaws
import Johnson.Desc.Own.BatchAgree
import Johnson.Desc.Own.FoldMean
import Johnson.Desc.Own.ShapesMean
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.RowFit
open OnBytes OnBytes.Means VerifiableInference.Desc

/-! ## 1 Structured vectors and forms -/

/-- The slice lies in its vector, no written-out variable is named twice, and each has the pair
(1, 1): `Tensor.ok` without its bound on the number of variables. -/
def TOk (v : Tensor) : Prop :=
  (v.denseVars = [] ∨ v.first + 2 ^ v.denseVars.length ≤ v.values.size) ∧ v.InOrder

theorem scale_first (v : Tensor) (x : E) : (v.scale x).first = v.first := by
  unfold Tensor.scale
  rfl

theorem scale_values (v : Tensor) (x : E) : (v.scale x).values = v.values := by
  unfold Tensor.scale
  rfl

theorem TOk.scale {v : Tensor} (h : TOk v) (x : E) : TOk (v.scale x) := by
  unfold TOk
  rw [Tensor.denseVars_scale, scale_first, scale_values]
  exact ⟨h.1, h.2.scale x⟩

theorem TOk.insertChoice {v : Tensor} (h : TOk v) (pos count value : Nat) :
    TOk (v.insertChoice pos count value) := by
  refine ⟨?_, OnBytes.Slice.ProxRun.inOrder_insertChoice h.2 pos count value⟩
  rcases h.1 with h0 | h1
  · left
    show v.denseVars.map _ = []
    rw [h0]
    rfl
  · right
    show v.first + 2 ^ (v.denseVars.map _).length ≤ v.values.size
    rw [List.length_map]
    exact h1

theorem TOk.of_own {v : Tensor} (h : Own.InOrder v) : TOk v := ⟨h.2.1, h.2.2.2, h.2.2.1⟩

theorem TOk.own {v : Tensor} (h : TOk v) (hn : v.pairs.length ≤ 63) : Own.InOrder v :=
  ⟨hn, h.1, h.2.2, h.2.1⟩

theorem own_of_ok {v : Tensor} (h : v.ok = true) : Own.InOrder v :=
  (Own.tensorInOrder_iff v).1 ((Own.tensorInOrder_agrees v).symm.trans h)

theorem own_scale {v : Tensor} (h : Own.InOrder v) (x : E) : Own.InOrder (v.scale x) := by
  unfold Own.InOrder
  rw [Tensor.denseVars_scale, scale_first, scale_values, Tensor.pairs_scale]
  exact h

theorem own_scale' : ∀ (v : Tensor) (x : E), Own.InOrder v → Own.InOrder (v.scale x) :=
  fun _ x h => own_scale h x

theorem tok_scale' : ∀ (v : Tensor) (x : E), TOk v → TOk (v.scale x) := fun _ x h => h.scale x

/-- All structured vectors of the form have the property. -/
def All (P : Tensor → Prop) (f : Form) : Prop := ∀ v ∈ f.tensors, P v

section
variable {P : Tensor → Prop} {f g : Form}

theorem All.empty : All P {} := fun _ h => (List.not_mem_nil h).elim

theorem All.add (h : All P f) {v : Tensor} (hv : P v) : All P (f.add v) := fun w hw => by
  rcases List.mem_cons.1 hw with e | c
  · rw [e]
    exact hv
  · exact h w c

theorem All.addEntry (h : All P f) (i : Nat) (c : E) : All P (f.addEntry i c) := h

theorem All.scale (hs : ∀ v x, P v → P (v.scale x)) (h : All P g) (x : E) : All P (g.scale x) :=
  fun w hw => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact hs v x (h v hv)

theorem All.plus (h : All P f) (k : All P g) : All P (f.plus g) :=
  fun w hw => (List.mem_append.1 hw).elim (k w) (h w)

theorem All.addForm (hs : ∀ v x, P v → P (v.scale x)) (h : All P f) (k : All P g) (x : E) :
    All P (f.addForm g x) := h.plus (k.scale hs x)

theorem All.insertChoice (pos count value : Nat)
    (hi : ∀ v, P v → P (v.insertChoice pos count value)) (h : All P g) :
    All P (g.insertChoice pos count value) := fun w hw => by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  exact hi v (h v hv)

theorem All.mono {Q : Tensor → Prop} (hq : ∀ v, P v → Q v) (h : All P f) : All Q f :=
  fun v hv => hq v (h v hv)

end

/-- The library's test on a form gives that its structured vectors are in order. -/
theorem all_of_fits {f : Form} {n : Nat} (h : f.fits n = true) : All Own.InOrder f :=
  fun v hv => (((Own.formFits_iff f n).1 ((Own.formFits_agrees f n).symm.trans h)).1 v hv).2

/-- The verifier's test on a form, from its parts. -/
theorem formFits_of {f : Form} {n : Nat} (hc : CFits n f) (ho : All Own.InOrder f) :
    Own.formFits f n = true :=
  (Own.formFits_iff f n).2 ⟨fun v hv => ⟨hc.1 v hv, ho v hv⟩, hc.2⟩

/-! ## 2 What is kept along the laying -/

variable {S : Statement} {G : Group} {L : GroupLayout}

/-- A separate form: it is on a kept member of the layout, has the index bits of that member's own
main table, and is in order. -/
def KQ (S : Statement) (L : GroupLayout) (o : Nat) (c : Form) : Prop :=
  (∃ i, L.find o = some i ∧ L.kept.getD i false = true) ∧ CFits (S.tableBits o .main) c ∧
    All Own.InOrder c

/-- What is kept along the laying: every structured vector of the form on the main table is `TOk`, and
each separate form meets `KQ`. -/
def Inv (S : Statement) (L : GroupLayout) (acc : GroupRow) : Prop :=
  All TOk acc.c ∧ ∀ f ∈ acc.kept.toList, KQ S L f.oracle f.c

theorem forall_modify {α : Type} (P : α → Prop) (g : α → α) : ∀ (l : List α) (i : Nat),
    (∀ a ∈ l, P a) → (∀ a, l[i]? = some a → P (g a)) → ∀ a ∈ l.modify i g, P a
  | [], _, _, _, a, ha => by simp at ha
  | b :: l, 0, h, hg, a, ha => by
    rw [List.modify_zero_cons] at ha
    rcases List.mem_cons.1 ha with e | c
    · rw [e]
      exact hg b (by simp)
    · exact h a (List.mem_cons_of_mem _ c)
  | b :: l, i + 1, h, hg, a, ha => by
    rw [List.modify_succ_cons] at ha
    rcases List.mem_cons.1 ha with e | c
    · rw [e]
      exact h b List.mem_cons_self
    · exact forall_modify P g l i (fun x hx => h x (List.mem_cons_of_mem _ hx))
        (fun x hx => hg x (by simpa using hx)) a c

/-- **A change of one kept member's form keeps a property of all separate forms.** -/
theorem onKept_inv (Q : Nat → Form → Prop) (kept : Array KeptForm) (o : Nat) (φ : Form → Form)
    (h : ∀ f ∈ kept.toList, Q f.oracle f.c) (h0 : Q o {}) (hφ : ∀ c, Q o c → Q o (φ c)) :
    ∀ f ∈ (onKept kept o φ).toList, Q f.oracle f.c := by
  unfold onKept
  cases hx : kept.findIdx? (·.oracle == o) with
  | some i =>
    obtain ⟨hi, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx
    simp only [Array.toList_modify]
    refine forall_modify (fun f : KeptForm => Q f.oracle f.c) _ kept.toList i h fun a ha => ?_
    have ea : a = kept[i] := by
      have : kept.toList[i]? = some kept[i] := by simp [hi]
      rw [this] at ha
      exact (Option.some.inj ha).symm
    subst ea
    have ho : kept[i].oracle = o := by simpa using hp
    show Q kept[i].oracle (φ kept[i].c)
    have hq := h kept[i] (by simp)
    rw [ho] at hq ⊢
    exact hφ _ hq
  | none =>
    intro f hf
    rw [Array.toList_append, Array.toList_append, Array.toList_filter, Array.toList_filter] at hf
    rcases List.mem_append.1 hf with c | c
    · rcases List.mem_append.1 c with c | e
      · exact h f (List.mem_filter.1 c).1
      · rw [List.mem_singleton.1 e]
        exact hφ _ h0
    · exact h f (List.mem_filter.1 c).1

theorem kq_empty {o i : Nat} (hf : L.find o = some i) (hk : L.kept.getD i false = true) :
    KQ S L o {} := ⟨⟨i, hf, hk⟩, CFits.empty _, All.empty⟩

theorem addTermTo_inv (F : LayFacts S G L) (x : E) (acc acc' : GroupRow) (t : Term)
    (ht : Blk.placeOk S G t.oracle t.part t.v.vars 0 = true)
    (hok : t.part = .main → Own.InOrder t.v)
    (h : addTermTo S L x acc t = some acc') (hc : Inv S L acc) : Inv S L acc' := by
  obtain ⟨hm, hh, hv, _⟩ := (placeOk_iff _ _ _ _ _ _).1 ht
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addTermTo at h
  cases hp : t.part with
  | main =>
    rw [hp] at hh hv
    by_cases hk : L.kept.getD i false = true
    · simp only [hf, hp, hk, if_true] at h
      obtain rfl := Option.some.inj h
      exact ⟨hc.1, onKept_inv (KQ S L) _ _ _ hc.2 (kq_empty hf hk) fun c hq =>
        ⟨hq.1, hq.2.1.add (by rw [Tensor.vars_scale]; exact hv),
          hq.2.2.add (own_scale (hok hp) x)⟩⟩
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
      have hle := (F.main_block _ i first hf hmf).2.2.le
      have hlt : ¬ L.k < S.rowBits t.oracle .main := Nat.not_lt.2 hle
      simp only [hf, hp, hk', hmf, hlt, Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      exact ⟨hc.1.add (((TOk.of_own (hok hp)).scale x).insertChoice _ _ _), hc.2⟩
  | mask =>
    rw [hp] at hh
    obtain ⟨first, hmf⟩ := F.mask_block_of _ i hf hh
    have hlt : ¬ L.h < S.rowBits t.oracle .mask :=
      Nat.not_lt.2 (F.mask_block _ i first hf hmf).2.le
    simp only [hf, hp, hmf, hlt, if_false] at h
    obtain rfl := Option.some.inj h
    exact ⟨hc.1, hc.2⟩

theorem addEntryTo_inv (F : LayFacts S G L) (x : E) (acc acc' : GroupRow) (o : Nat) (part : Part)
    (index : Nat) (coeff : E) (hm : o ∈ G.members.toList) (hh : S.has o part = true)
    (hi : index < 2 ^ S.tableBits o part)
    (h : addEntryTo S L x acc o part index coeff = some acc') (hc : Inv S L acc) :
    Inv S L acc' := by
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addEntryTo at h
  cases part with
  | main =>
    by_cases hk : L.kept.getD i false = true
    · simp only [hf, hk, if_true] at h
      obtain rfl := Option.some.inj h
      exact ⟨hc.1, onKept_inv (KQ S L) _ _ _ hc.2 (kq_empty hf hk) fun c hq =>
        ⟨hq.1, hq.2.1.addEntry hi _, hq.2.2.addEntry _ _⟩⟩
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
      simp only [hf, hk', hmf, Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      exact ⟨hc.1.addEntry _ _, hc.2⟩
  | mask =>
    obtain ⟨first, hmf⟩ := F.mask_block_of _ i hf hh
    simp only [hf, hmf] at h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨hc.1, hc.2⟩
    · cases h

theorem addFormTo_inv (F : LayFacts S G L) (x : E) (acc acc' : GroupRow) (f : MainForm)
    (hm : f.oracle ∈ G.members.toList) (hh : S.has f.oracle .main = true)
    (hfit : f.c.fits (S.tableBits f.oracle .main) = true)
    (h : addFormTo S L x acc f = some acc') (hc : Inv S L acc) : Inv S L acc' := by
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addFormTo at h
  by_cases hk : L.kept.getD i false = true
  · simp only [hf, hk, if_true] at h
    obtain rfl := Option.some.inj h
    exact ⟨hc.1, onKept_inv (KQ S L) _ _ _ hc.2 (kq_empty hf hk) fun c hq =>
      ⟨hq.1, hq.2.1.addForm (CFits.of_fits hfit) x,
        hq.2.2.addForm own_scale' (all_of_fits hfit) x⟩⟩
  · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
    obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
    have hle := (F.main_block _ i first hf hmf).2.2.le
    have hlt : ¬ L.k < S.rowBits f.oracle .main := Nat.not_lt.2 hle
    simp only [hf, hk', hmf, hlt, Bool.false_eq_true, if_false] at h
    obtain rfl := Option.some.inj h
    exact ⟨hc.1.addForm tok_scale'
      (((all_of_fits hfit).mono fun _ => TOk.of_own).insertChoice _ _ _
        fun _ hv => TOk.insertChoice hv _ _ _) x, hc.2⟩

theorem ready_kept (acc : GroupRow) (L : GroupLayout) : (acc.ready L).kept = acc.kept := by
  unfold GroupRow.ready
  split <;> rfl

/-- **The laying keeps it.** -/
theorem lays_inv {row : Row} (F : LayFacts S G L) (hr : RowIn S G row)
    (ho : ∀ t ∈ row.terms.toList, t.part = .main → Own.InOrder t.v) (x : E) (acc acc' : GroupRow)
    (h : addToGroupRow S L row x acc = some acc') (hc : Inv S L acc) : Inv S L acc' := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  have c1 := foldlM_inv (Inv S L) (addTermTo S L x)
    row.terms.toList (fun t ht b b' hb => addTermTo_inv F x b b' t (hr.terms t ht) (ho t ht) hb) _
    a1 h1 (by
      show All TOk (acc.ready L).c ∧ ∀ f ∈ (acc.ready L).kept.toList, KQ S L f.oracle f.c
      rw [ready_c, ready_kept]
      exact hc)
  have c2 := foldlM_inv (Inv S L)
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff)
    row.units.toList (fun u hu b b' hb => by
      obtain ⟨hm, hh, _, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 (hr.units u hu)
      exact addEntryTo_inv F x b b' _ _ _ _ hm hh hi hb) _ a2 h2 c1
  have c3 := foldlM_inv (Inv S L) (addRunTo S L x)
    row.runs.toList (fun w hw b b' hb => by
      obtain ⟨_, _, hpl⟩ := hr.runs w hw
      obtain ⟨hm, hh, _, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 hpl
      exact foldlM_inv (Inv S L)
        (fun acc j => addEntryTo S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j))
        (List.range w.coeffs.size) (fun j hj c c' hc' => by
          have hj' : j ≤ w.coeffs.size - 1 := by
            have := List.mem_range.1 hj
            omega
          have hlt : w.first + w.step * j < 2 ^ S.tableBits w.oracle w.part :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _) hi
          exact addEntryTo_inv F x c c' _ _ _ _ hm hh hlt hc') b b' hb) _ a3 h3 c2
  have c4 := foldlM_inv (Inv S L) (addFormTo S L x)
    row.forms.toList (fun f hf b b' hb => by
      obtain ⟨hpl, hfit⟩ := hr.forms f hf
      obtain ⟨hm, hh, _, _⟩ := (placeOk_iff _ _ _ _ _ _).1 hpl
      exact addFormTo_inv F x b b' f hm hh hfit hb) _ a4 h4 c3
  exact ⟨c4.1, c4.2⟩

/-! ## 3 The mask table's length -/

theorem addEntryTo_dsize (x : E) (acc acc' : GroupRow) (o : Nat) (part : Part) (index : Nat)
    (coeff : E) (h : addEntryTo S L x acc o part index coeff = some acc') :
    acc'.d.size = acc.d.size := by
  unfold addEntryTo at h
  split at h
  · cases h
  · cases part with
    | main =>
      simp only at h
      split at h
      · obtain rfl := Option.some.inj h
        rfl
      · split at h
        · cases h
        · obtain rfl := Option.some.inj h
          rfl
    | mask =>
      simp only at h
      split at h
      · cases h
      · split at h
        · obtain rfl := Option.some.inj h
          simp only [Array.size_modify]
        · cases h

theorem addTermTo_dsize (x : E) (acc acc' : GroupRow) (t : Term)
    (h : addTermTo S L x acc t = some acc') : acc'.d.size = acc.d.size := by
  unfold addTermTo at h
  split at h
  · cases h
  · simp only at h
    split at h
    · split at h
      · obtain rfl := Option.some.inj h
        rfl
      · split at h
        · cases h
        · split at h
          · cases h
          · obtain rfl := Option.some.inj h
            rfl
    · split at h
      · cases h
      · split at h
        · cases h
        · obtain rfl := Option.some.inj h
          simp only [Tensor.addTo_size]

theorem addFormTo_dsize (x : E) (acc acc' : GroupRow) (f : MainForm)
    (h : addFormTo S L x acc f = some acc') : acc'.d.size = acc.d.size := by
  unfold addFormTo at h
  split at h
  · cases h
  · split at h
    · obtain rfl := Option.some.inj h
      rfl
    · simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · obtain rfl := Option.some.inj h
          rfl

theorem ready_size (acc : GroupRow) (h : MaskReady L acc) :
    (acc.ready L).d.size = 2 ^ (L.h + L.logEllZk) := by
  unfold GroupRow.ready
  rcases h with h | h
  · simp [h]
  · split
    · simp
    · exact h

/-- **Behind a laying the mask table has its full length.** -/
theorem lays_dsize {row : Row} (x : E) (acc acc' : GroupRow) (hp : MaskReady L acc)
    (h : addToGroupRow S L row x acc = some acc') : acc'.d.size = 2 ^ (L.h + L.logEllZk) := by
  unfold addToGroupRow at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := h
  let Q : GroupRow → Prop := fun g => g.d.size = 2 ^ (L.h + L.logEllZk)
  have c1 := foldlM_inv Q (addTermTo S L x) row.terms.toList
    (fun t _ b b' hb hq => (addTermTo_dsize x b b' t hb).trans hq) _ a1 h1 (ready_size acc hp)
  have c2 := foldlM_inv Q
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff)
    row.units.toList (fun u _ b b' hb hq => (addEntryTo_dsize x b b' _ _ _ _ hb).trans hq) _ a2 h2 c1
  have c3 := foldlM_inv Q (addRunTo S L x) row.runs.toList (fun w _ b b' hb hq =>
    foldlM_inv Q
      (fun acc j => addEntryTo S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j))
      (List.range w.coeffs.size)
      (fun j _ c c' hc' hq' => (addEntryTo_dsize x c c' _ _ _ _ hc').trans hq') b b' hb hq) _ a3 h3
    c2
  exact foldlM_inv Q (addFormTo S L x) row.forms.toList
    (fun f _ b b' hb hq => (addFormTo_dsize x b b' f hb).trans hq) _ a4 h4 c3

/-! ## 4 The batching -/

/-- **What the batching returns.** -/
theorem combine_inv {g : Nat} {rows : Array Row} {x : E} {out : GroupRow}
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r)
    (ho : ∀ r ∈ rows.toList, ∀ t ∈ r.terms.toList, t.part = .main → Own.InOrder t.v)
    (h : Bat.combine S g ⟨L, rows⟩ x = some out) :
    Inv S L out ∧ out.d.size = 2 ^ (L.h + L.logEllZk) := by
  have F := layFacts hG hL hOk
  have a0 : AsideIn S G {} := ⟨rfl, rfl, by simp, by simp, by simp, by simp⟩
  unfold Bat.combine at h
  simp only [← Array.foldlM_toList, Option.bind_eq_bind] at h
  obtain ⟨s, h1, h2⟩ := Option.bind_eq_some_iff.1 h
  have inv := foldlM_inv
    (fun s : GroupRow × Row × E => (Inv S L s.1 ∧ MaskReady L s.1) ∧ AsideIn S G s.2.1) _
    rows.toList
    (fun r hr' b b' hb hP => by
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
      obtain ⟨acc, ha, rfl⟩ := hb
      exact ⟨⟨lays_inv F (hr r hr').structured (ho r hr') b.2.2 b.1 acc ha hP.1.1,
        Or.inr (lays_dsize b.2.2 b.1 acc hP.1.2 ha)⟩, hP.2.addScaled (hr r hr') b.2.2⟩) _ s h1
    ⟨⟨⟨All.empty, fun _ hf => by simp at hf⟩, Or.inl rfl⟩, a0⟩
  exact ⟨lays_inv F inv.2.isIn (fun t ht => by rw [inv.2.terms] at ht; simp at ht) oneE s.1 out h2
    inv.1.1, lays_dsize oneE s.1 out inv.1.2 h2⟩

/-- **AT EVERY ELEMENT THE BATCHING RETURNS A ROW.** -/
theorem batch_returns (g : Nat) (rows : Array Row) (x : E) (hG : S.groups[g]? = some G)
    (hL : S.layout g = some L) (hOk : GroupOk S G) (hr : ∀ r ∈ rows.toList, RowIn S G r) :
    ∃ out, Own.batch S g ⟨L, rows⟩ x = some out := by
  obtain ⟨out, h, _⟩ := combine_means OnBytes.Slice.rdE S g G L rows x hG hL hOk hr
  exact ⟨out, (Own.batch_agrees S g ⟨L, rows⟩ x).symm.trans h⟩

/-- **THE ROW THAT THE BATCHING RETURNS PASSES THE FOLD's TEST ON ITS SIZES.** S': the statement at
which the test is asked (behind the spending of the mask): it has the codes of S and, at the group's
members, the tables' index bits of S. F: the fold's shape. -/
theorem batch_rowfits {g : Nat} {rows : Array Row} {x : E} {out : GroupRow}
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r)
    (ho : ∀ r ∈ rows.toList, ∀ t ∈ r.terms.toList, t.part = .main → t.v.ok = true)
    (h : Own.batch S g ⟨L, rows⟩ x = some out) (S' : Statement) (hc : S'.codes = S.codes)
    (hb : ∀ o ∈ G.members.toList, S'.tableBits o .main = S.tableBits o .main) (F : FoldShape)
    (f1 : F.layout.members = L.members) (f2 : F.layout.kept = L.kept) (f3 : F.layout.k = L.k)
    (f4 : F.layout.h = L.h) (e1 : ceilLog2 (S.codes.base.getD F.code default).ell = L.logEll)
    (e2 : (S.codes.mask.getD F.maskCode default).ell = 2 ^ L.logEllZk)
    (hv : L.k + L.logEll ≤ 63) : Own.foldRowFits S' F out = true := by
  have h' : Bat.combine S g ⟨L, rows⟩ x = some out := (Own.batch_agrees S g ⟨L, rows⟩ x).trans h
  obtain ⟨⟨i1, i2⟩, i3⟩ := combine_inv hG hL hOk hr
    (fun r hr' t ht hp => own_of_ok (ho r hr' t ht hp)) h'
  have cf := combine_cfits hG hL hOk hr h'
  rw [Own.foldRowFits_iff]
  refine ⟨?_, ?_, fun f hf => ?_⟩
  · rw [hc, f3, e1]
    exact formFits_of cf fun v hv' => (i1 v hv').own (by
      have := cf.1 v hv'
      unfold Tensor.vars at this
      omega)
  · rw [hc, e2, f4, i3, Nat.pow_add, Nat.mul_comm]
  · obtain ⟨⟨i, k1, k2⟩, k3, k4⟩ := i2 f (by simpa using hf)
    refine ⟨⟨i, ?_, ?_⟩, ?_⟩
    · rw [f1]
      exact k1
    · rw [f2]
      exact k2
    · rw [hb _ ((layFacts hG hL hOk).mem_of_find _ i k1)]
      exact formFits_of k3 k4

end ProofFile.Honest.K10.RowFit

#print axioms ProofFile.Honest.K10.RowFit.onKept_inv
#print axioms ProofFile.Honest.K10.RowFit.lays_inv
#print axioms ProofFile.Honest.K10.RowFit.lays_dsize
#print axioms ProofFile.Honest.K10.RowFit.combine_inv
#print axioms ProofFile.Honest.K10.RowFit.batch_returns
#print axioms ProofFile.Honest.K10.RowFit.batch_rowfits
