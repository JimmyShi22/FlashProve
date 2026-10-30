-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/BatWipe.lean: the verifier's text of the batching (`bat`,
Johnson/Desc/First/Close/Closing.lean) at a statement and at that statement with every row's target set to zero
(`wipeSt`, Honest/K10/StAtZero.lean). Six definitions with code; the rest are theorems.

What is proved. `bat_wipe`: at the two statements the batching refuses with one word, or returns at both; then the
two layouts are one, the statement behind at the wiped statement is the statement behind, wiped, and the two batched
rows are one but for their targets. On the way, one law for each function of the library that the batching or a reader
of its result calls:
  `rowBits_wipe`, `has_wipe`, `placeBits_wipe`, `tableBits_wipe`, `tableThere_wipe`, `realRows_wipe`, `tableSize_wipe`,
  `mainWeight_wipe`, `mainBack_wipe`, `maskWeight_wipe`, `maskBack_wipe`   each is one function at both statements
  `entryInto_st`, `termInto_st`, `runInto_st`, `formInto_st`, `rowInto_st`   so are the five steps of the batching
  `entryInto_acc`, `termInto_acc`, `runInto_acc`, `formInto_acc`, `ready_wipe`   four steps, and the writing out of the
                 mask table, go through the wiping of the row that is added to
  `rowInto_rel`, `addScaled_rel`, `batch_wipe`   rows that are one but for targets are batched to such rows
  `layoutOf_wipe`, `runRows_wipe`, `closeLedgers_wipe`, `begun_wipe`, `beginRunL_wipe`, `beginRunP_wipe`   the beginning
                 of the test

By what. Each body is unfolded and followed arm by arm. No arithmetic on a target is done: two rows are compared with
both targets set to zero (`wipeG`, `wipeRow`). The general laws in front (`ite_map` to `need_rel`) carry a comparison
through a choice, a bind, a fold and a change at one place of an array.

Limits. The laws speak of the functions' values at all arguments; they say nothing of what a statement or a row means.
Nothing is said of a statement that differs from another in more than targets. No job, part or lot is named here. No
property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.StAtZero
import Johnson.Desc.First.Close.Closing
import Johnson.Desc.Means.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE mulE Statement Oracle Row GroupRow GroupLayout RunInput)
open OnBytes.Slice (runRows begun closeLedgers)
open VerifiableInference.Desc.Own (entryInto termInto runInto formInto rowInto batch blockBits layoutOf tableThere)
open VerifiableInference.Desc.Ground (beginRunL beginRunP)
open VerifiableInference.Desc.First.Close (bat onSt got need)

/-! ## 1 General laws -/

/-- A map goes through a choice, arm by arm. -/
theorem ite_map {α β : Type} (φ : α → β) {c : Prop} [Decidable c] {p q : Option α} {p' q' : Option β}
    (hp : p.map φ = p') (hq : q.map φ = q') : (if c then p else q).map φ = if c then p' else q' := by
  subst hp hq
  exact apply_ite (Option.map φ) c p q

/-- Two binds are alike where their heads are alike and their tails are alike at alike values. -/
theorem bind_rel {β γ δ ε : Type} (φ : β → δ) (ψ : γ → ε) {p p' : Option β} {k k' : β → Option γ}
    (hp : p.map φ = p'.map φ) (h : ∀ b b', φ b = φ b' → (k b).map ψ = (k' b').map ψ) :
    (p >>= k).map ψ = (p' >>= k').map ψ := by
  cases p with
  | none =>
    cases p' with
    | none => rfl
    | some b' => cases hp
  | some b =>
    cases p' with
    | none => cases hp
    | some b' => exact h b b' (Option.some.inj hp)

/-- A fold whose step goes through a map goes through it. -/
theorem foldlM_hom {α β : Type} (φ : β → β) (f : β → α → Option β)
    (h : ∀ b a, (f b a).map φ = f (φ b) a) :
    ∀ (l : List α) (b : β), (l.foldlM f b).map φ = l.foldlM f (φ b)
  | [], _ => rfl
  | a :: l, b => by
    rw [List.foldlM_cons, List.foldlM_cons, ← h b a]
    cases f b a with
    | none => rfl
    | some c => exact foldlM_hom φ f h l c

/-- Such a fold over an array, from two alike values, ends alike. -/
theorem foldA_same {α β : Type} (φ : β → β) (f : β → α → Option β)
    (h : ∀ b a, (f b a).map φ = f (φ b) a) (as : Array α) {b b' : β} (hb : φ b = φ b') :
    (as.foldlM f b).map φ = (as.foldlM f b').map φ := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact (foldlM_hom φ f h as.toList b).trans
    ((congrArg (fun c => as.toList.foldlM f c) hb).trans (foldlM_hom φ f h as.toList b').symm)

/-- Two folds, one over a list and one over its image, end alike where their steps keep alike values alike. -/
theorem foldlM_rel {α β γ : Type} (φ : β → γ) (ψ : α → α) (f f' : β → α → Option β)
    (h : ∀ b b' a, φ b = φ b' → (f b a).map φ = (f' b' (ψ a)).map φ) :
    ∀ (l : List α) (b b' : β), φ b = φ b' → (l.foldlM f b).map φ = ((l.map ψ).foldlM f' b').map φ
  | [], _, _, hb => congrArg some hb
  | a :: l, b, b', hb => by
    rw [List.map_cons, List.foldlM_cons, List.foldlM_cons]
    exact bind_rel φ φ (h b b' a hb) fun c c' hc => foldlM_rel φ ψ f f' h l c c' hc

/-- The same over arrays. -/
theorem foldA_rel {α β γ : Type} (φ : β → γ) (ψ : α → α) (f f' : β → α → Option β)
    (h : ∀ b b' a, φ b = φ b' → (f b a).map φ = (f' b' (ψ a)).map φ) (as : Array α) {b b' : β}
    (hb : φ b = φ b') : (as.foldlM f b).map φ = ((as.map ψ).foldlM f' b').map φ := by
  rw [← Array.foldlM_toList, ← Array.foldlM_toList, Array.toList_map]
  exact foldlM_rel φ ψ f f' h as.toList b b' hb

/-- A change at one place of an array goes through a map that it goes through at each entry. -/
theorem map_modify_comm {α β : Type} (a : Array α) (i : Nat) (f : α → α) (h : α → β) (f' : β → β)
    (hc : ∀ x, h (f x) = f' (h x)) : (a.modify i f).map h = (a.map h).modify i f' := by
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map, Array.getElem?_modify, Array.getElem?_modify, Array.getElem?_map]
  split
  · cases a[j]? with
    | none => rfl
    | some x => exact congrArg some (hc x)
  · rfl

/-- Two binds with one head are alike where their tails are. -/
theorem ebind_same {ε β γ δ : Type} {ψ ψ' : γ → δ} {p : Except ε β} {k k' : β → Except ε γ}
    (h : ∀ b, (k b).map ψ = (k' b).map ψ') : (p >>= k).map ψ = (p >>= k').map ψ' := by
  cases p with
  | error _ => rfl
  | ok b => exact h b

/-- The like behind `got`, where the one value is the other's image. -/
theorem got_map {β γ δ : Type} {ψ ψ' : γ → δ} {n : String} (F : β → β) {o : Option β}
    {k k' : β → Except String γ} (h : ∀ b, (k (F b)).map ψ = (k' b).map ψ') :
    (got n (o.map F) >>= k).map ψ = (got n o >>= k').map ψ' := by
  cases o with
  | none => rfl
  | some b => exact h b

/-- The like behind `got`, where the two values are alike. -/
theorem got_rel {β γ δ ζ : Type} {ψ ψ' : γ → δ} {n : String} (φ : β → ζ) {o o' : Option β}
    {k k' : β → Except String γ} (ho : o.map φ = o'.map φ)
    (h : ∀ b b', φ b = φ b' → (k b).map ψ = (k' b').map ψ') :
    (got n o >>= k).map ψ = (got n o' >>= k').map ψ' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some b' => cases ho
  | some b =>
    cases o' with
    | none => cases ho
    | some b' => exact h b b' (Option.some.inj ho)

/-- The like behind `need`, at one test. -/
theorem need_rel {γ δ : Type} {ψ ψ' : γ → δ} {n : String} {b b' : Bool} {k k' : Unit → Except String γ}
    (hb : b = b') (h : (k ()).map ψ = (k' ()).map ψ') :
    (need n b >>= k).map ψ = (need n b' >>= k').map ψ' := by
  subst hb
  cases b with
  | false => rfl
  | true => exact h

/-! ## 2 The wiping, piece by piece -/

/-- An oracle message with each sample row's target set to zero. -/
def wipeOr (o : Oracle) : Oracle := { o with sampleRows := o.sampleRows.map wipeRow }

/-- A group with each open row's target set to zero. -/
def wipeGr (G : OnBytes.Group) : OnBytes.Group := { G with rows := G.rows.map wipeRow }

/-- A group's row with its target set to zero. -/
def wipeG (r : GroupRow) : GroupRow := { r with target := zeroE }

/-- What the batching's fold carries, with both rows' targets set to zero. -/
def wipe3 (s : GroupRow × Row × E) : GroupRow × Row × E := (wipeG s.1, wipeRow s.2.1, s.2.2)

/-- The wiping goes through a change of the coefficients on the mask table, whatever these are. -/
theorem some_d (acc : GroupRow) (D : Array E) :
    (some { acc with d := D }).map wipeG = some { wipeG acc with d := D } := rfl

/-- The wiping does not see what target a row had. -/
theorem wipeG_target (a : GroupRow) (t : E) : wipeG { a with target := t } = wipeG a := rfl

/-- An oracle message of the wiped statement is the statement's, wiped. -/
theorem wipeSt_oracle_at (S : Statement) (o : Nat) :
    (wipeSt S).oracles[o]? = (S.oracles[o]?).map wipeOr := by
  show (S.oracles.map wipeOr)[o]? = _
  rw [Array.getElem?_map]

/-- A group of the wiped statement is the statement's, wiped. -/
theorem wipeSt_group_at (S : Statement) (g : Nat) :
    (wipeSt S).groups[g]? = (S.groups[g]?).map wipeGr := by
  show (S.groups.map wipeGr)[g]? = _
  rw [Array.getElem?_map]

/-- The wiped statement has as many oracle messages. -/
theorem wipeSt_size (S : Statement) : (wipeSt S).oracles.size = S.oracles.size := by
  show (S.oracles.map wipeOr).size = _
  rw [Array.size_map]

/-- The wiped statement has the same shapes. -/
theorem shape_at_wipe (S : Statement) (o : Nat) :
    ((wipeSt S).oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape) := by
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-! ## 3 What reads shapes and codes alone -/

/-- The bits that index a row of a table are one at both statements. -/
theorem rowBits_wipe (S : Statement) : (wipeSt S).rowBits = S.rowBits := by
  funext o part
  unfold OnBytes.Statement.rowBits
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- Whether a table is there is one at both statements. -/
theorem has_wipe (S : Statement) : (wipeSt S).has = S.has := by
  funext o part
  unfold OnBytes.Statement.has
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- The bits that index a place in a row are one at both statements. -/
theorem placeBits_wipe (S : Statement) : (wipeSt S).placeBits = S.placeBits := by
  funext o part
  unfold OnBytes.Statement.placeBits
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- A table's index bits are one at both statements. -/
theorem tableBits_wipe (S : Statement) : (wipeSt S).tableBits = S.tableBits := by
  funext o part
  unfold OnBytes.Statement.tableBits
  rw [rowBits_wipe, placeBits_wipe]

/-- The description's own test whether a table is there is one at both statements. -/
theorem tableThere_wipe (S : Statement) : tableThere (wipeSt S) = tableThere S := by
  funext o part
  unfold VerifiableInference.Desc.Own.tableThere
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- The number of a table's real rows is one at both statements. -/
theorem realRows_wipe (S : Statement) : OnBytes.Means.realRows (wipeSt S) = OnBytes.Means.realRows S := by
  funext o part
  unfold OnBytes.Means.realRows
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? <;> rfl

/-- The number of a table's entries is one at both statements. -/
theorem tableSize_wipe (S : Statement) : OnBytes.Means.tableSize (wipeSt S) = OnBytes.Means.tableSize S := by
  funext o part
  unfold OnBytes.Means.tableSize
  rw [has_wipe, tableBits_wipe]

/-- The library's weight on the group's main table is one at both statements. -/
theorem mainWeight_wipe {K : Type} [CommRing K] (S : Statement) :
    OnBytes.mainWeight (K := K) (wipeSt S) = OnBytes.mainWeight (K := K) S := by
  funext L o J
  unfold OnBytes.mainWeight
  rw [rowBits_wipe]

/-- The index in a member's main table that belongs to an index of the group's is one at both statements. -/
theorem mainBack_wipe (S : Statement) : OnBytes.mainBack (wipeSt S) = OnBytes.mainBack S := by
  funext L o J
  unfold OnBytes.mainBack
  rw [rowBits_wipe]

/-- The library's weight on the group's mask table is one at both statements. -/
theorem maskWeight_wipe {K : Type} [CommRing K] (S : Statement) :
    OnBytes.maskWeight (K := K) (wipeSt S) = OnBytes.maskWeight (K := K) S := by
  funext L o J
  unfold OnBytes.maskWeight
  rw [rowBits_wipe]

/-- The index in a member's mask table that belongs to an index of the group's is one at both statements. -/
theorem maskBack_wipe (S : Statement) : OnBytes.maskBack (wipeSt S) = OnBytes.maskBack S := by
  funext L o J
  unfold OnBytes.maskBack
  rw [rowBits_wipe]

/-! ## 4 The batching's steps: of the statement they read the row bits alone -/

/-- The adding of one entry is one function at both statements. -/
theorem entryInto_st (S : Statement) : entryInto (wipeSt S) = entryInto S := by
  funext L x acc o part index coeff
  unfold VerifiableInference.Desc.Own.entryInto
  rw [rowBits_wipe]

/-- The adding of a vector of product form is one function at both statements. -/
theorem termInto_st (S : Statement) : termInto (wipeSt S) = termInto S := by
  funext L x acc t
  unfold VerifiableInference.Desc.Own.termInto
  rw [rowBits_wipe]

/-- The adding of a run is one function at both statements. -/
theorem runInto_st (S : Statement) : runInto (wipeSt S) = runInto S := by
  funext L x acc w
  unfold VerifiableInference.Desc.Own.runInto
  rw [entryInto_st]

/-- The adding of a whole form is one function at both statements. -/
theorem formInto_st (S : Statement) : formInto (wipeSt S) = formInto S := by
  funext L x acc f
  unfold VerifiableInference.Desc.Own.formInto
  rw [rowBits_wipe]

/-- The adding of a row is one function at both statements. -/
theorem rowInto_st (S : Statement) : rowInto (wipeSt S) = rowInto S := by
  funext L row x acc
  unfold VerifiableInference.Desc.Own.rowInto
  rw [termInto_st, entryInto_st, runInto_st, formInto_st]

/-! ## 5 The batching's steps: four neither read nor write the target of the row that they add to; `rowInto` adds a
row's target to that row's target, and to nothing else -/

/-- The adding of one entry goes through the wiping of the row that is added to. -/
theorem entryInto_acc (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (o : Nat)
    (part : OnBytes.Part) (index : Nat) (coeff : E) :
    (entryInto S L x acc o part index coeff).map wipeG = entryInto S L x (wipeG acc) o part index coeff := by
  unfold VerifiableInference.Desc.Own.entryInto
  cases L.members.idxOf? o with
  | none => rfl
  | some i =>
    cases part with
    | mask =>
      dsimp only
      cases L.maskFirst.getD i none with
      | none => rfl
      | some first => exact ite_map wipeG rfl rfl
    | main =>
      dsimp only
      refine ite_map wipeG rfl ?_
      cases L.mainFirst.getD i none with
      | none => rfl
      | some first => rfl

/-- The adding of a vector of product form goes through the wiping of the row that is added to. -/
theorem termInto_acc (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (t : OnBytes.Term) :
    (termInto S L x acc t).map wipeG = termInto S L x (wipeG acc) t := by
  unfold VerifiableInference.Desc.Own.termInto
  cases L.members.idxOf? t.oracle with
  | none => rfl
  | some i =>
    cases t.part with
    | main =>
      dsimp only
      refine ite_map wipeG rfl ?_
      cases L.mainFirst.getD i none with
      | none => rfl
      | some first => exact ite_map wipeG rfl rfl
    | mask =>
      dsimp only
      cases L.maskFirst.getD i none with
      | none => rfl
      | some first => exact ite_map wipeG rfl (some_d acc _)

/-- The adding of a run goes through the wiping of the row that is added to. -/
theorem runInto_acc (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (w : OnBytes.Run) :
    (runInto S L x acc w).map wipeG = runInto S L x (wipeG acc) w := by
  unfold VerifiableInference.Desc.Own.runInto
  exact foldlM_hom wipeG _
    (fun b j => entryInto_acc S L x b w.oracle w.part (w.first + w.step * j) (w.coeffs.get j)) _ acc

/-- The adding of a whole form goes through the wiping of the row that is added to. -/
theorem formInto_acc (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (f : OnBytes.MainForm) :
    (formInto S L x acc f).map wipeG = formInto S L x (wipeG acc) f := by
  unfold VerifiableInference.Desc.Own.formInto
  cases L.members.idxOf? f.oracle with
  | none => rfl
  | some i =>
    dsimp only
    refine ite_map wipeG rfl ?_
    cases L.mainFirst.getD i none with
    | none => rfl
    | some first => exact ite_map wipeG rfl rfl

/-- The writing out of the mask table goes through the wiping. -/
theorem ready_wipe (acc : GroupRow) (L : GroupLayout) : wipeG (acc.ready L) = (wipeG acc).ready L := by
  unfold OnBytes.GroupRow.ready
  exact apply_ite wipeG _ _ _

/-- **A row is added**: rows that are one but for their targets, added to rows that are one but for their targets,
both yield nothing or yield such rows. -/
theorem rowInto_rel (S : Statement) (L : GroupLayout) {x x' : E} {row row' : Row} {acc acc' : GroupRow}
    (hx : x = x') (ha : wipeG acc = wipeG acc') (hr : wipeRow row = wipeRow row') :
    (rowInto S L row x acc).map wipeG = (rowInto S L row' x' acc').map wipeG := by
  subst hx
  have ht : row.terms = row'.terms := (congrArg (fun r : Row => r.terms) hr :)
  have hu : row.units = row'.units := (congrArg (fun r : Row => r.units) hr :)
  have hn : row.runs = row'.runs := (congrArg (fun r : Row => r.runs) hr :)
  have hf : row.forms = row'.forms := (congrArg (fun r : Row => r.forms) hr :)
  have h0 : wipeG (acc.ready L) = wipeG (acc'.ready L) :=
    (ready_wipe acc L).trans ((congrArg (fun a : GroupRow => a.ready L) ha).trans (ready_wipe acc' L).symm)
  unfold VerifiableInference.Desc.Own.rowInto
  rw [ht, hu, hn, hf]
  refine bind_rel wipeG wipeG (foldA_same wipeG _ (termInto_acc S L x) _ h0) fun a1 b1 h1 => ?_
  refine bind_rel wipeG wipeG (foldA_same wipeG _
    (fun b u => entryInto_acc S L x b u.oracle u.part u.index u.coeff) _ h1) fun a2 b2 h2 => ?_
  refine bind_rel wipeG wipeG (foldA_same wipeG _ (runInto_acc S L x) _ h2) fun a3 b3 h3 => ?_
  refine bind_rel wipeG wipeG (foldA_same wipeG _ (formInto_acc S L x) _ h3) fun a4 b4 h4 => ?_
  have e4 : wipeG { a4 with target := OnBytes.maddE a4.target x row.target } =
      wipeG { b4 with target := OnBytes.maddE b4.target x row'.target } :=
    (wipeG_target a4 _).trans (h4.trans (wipeG_target b4 _).symm)
  exact congrArg some e4

/-- The sum of two rows reads of the first row's target nothing but for the sum's target. -/
theorem addScaled_wipe (a w : Row) (x : E) :
    wipeRow (a.addScaled w x) = wipeRow ((wipeRow a).addScaled w x) := by
  unfold wipeRow OnBytes.Row.addScaled OnBytes.Row.addRunsScaled
  rfl

/-- A row without its single entries and runs, wiped, does not see whether the row was wiped before. -/
theorem wipeRow_strip (r : Row) :
    wipeRow { r with units := #[], runs := #[] } = wipeRow { wipeRow r with units := #[], runs := #[] } := by
  unfold wipeRow
  rfl

/-- Sums of rows that are one but for their targets with one row are one but for their targets. -/
theorem addScaled_rel {a a' : Row} (h : wipeRow a = wipeRow a') (w : Row) (x : E) :
    wipeRow (a.addScaled w x) = wipeRow (a'.addScaled w x) :=
  (addScaled_wipe a w x).trans
    ((congrArg (fun t : Row => wipeRow (t.addScaled w x)) h).trans (addScaled_wipe a' w x).symm)

/-- **The batching**, at a statement and its rows and at both wiped: both yield nothing, or rows that are one but for
their targets. -/
theorem batch_wipe (S : Statement) (g : Nat) (input : RunInput) (x : E) :
    (batch S g input x).map wipeG =
      (batch (wipeSt S) g ⟨input.layout, input.rows.map wipeRow⟩ x).map wipeG := by
  unfold VerifiableInference.Desc.Own.batch
  rw [rowInto_st]
  refine bind_rel wipe3 wipeG (foldA_rel wipe3 wipeRow _ _ ?_ input.rows rfl) ?_
  · intro s s' r hs
    have h1 : wipeG s.1 = wipeG s'.1 := (congrArg (fun z : GroupRow × Row × E => z.1) hs :)
    have h2 : wipeRow s.2.1 = wipeRow s'.2.1 := (congrArg (fun z : GroupRow × Row × E => z.2.1) hs :)
    have h3 : s.2.2 = s'.2.2 := (congrArg (fun z : GroupRow × Row × E => z.2.2) hs :)
    refine bind_rel wipeG wipe3 (rowInto_rel S input.layout h3 h1 (wipeRow_strip r)) fun p p' hp => ?_
    show some (wipeG p, wipeRow (s.2.1.addScaled { units := r.units, runs := r.runs } s.2.2), mulE s.2.2 x) =
      some (wipeG p', wipeRow (s'.2.1.addScaled { units := r.units, runs := r.runs } s'.2.2), mulE s'.2.2 x)
    rw [hp, ← h3, addScaled_rel h2]
  · intro s s' hs
    have h1 : wipeG s.1 = wipeG s'.1 := (congrArg (fun z : GroupRow × Row × E => z.1) hs :)
    have h2 : wipeRow s.2.1 = wipeRow s'.2.1 := (congrArg (fun z : GroupRow × Row × E => z.2.1) hs :)
    exact rowInto_rel S input.layout rfl h1 h2

/-! ## 6 The beginning of the test -/

/-- The members' block sizes read no row. -/
theorem blockBits_wipe (S : Statement) (G : OnBytes.Group) (part : OnBytes.Part) :
    blockBits (wipeSt S) (wipeGr G) part = blockBits S G part := by
  unfold VerifiableInference.Desc.Own.blockBits
  rw [tableThere_wipe, rowBits_wipe]
  rfl

/-- The layout reads no row. -/
theorem layoutOf_wipe (S : Statement) (G : OnBytes.Group) : layoutOf (wipeSt S) (wipeGr G) = layoutOf S G := by
  unfold VerifiableInference.Desc.Own.layoutOf
  rw [blockBits_wipe, blockBits_wipe]
  rfl

/-- The choice of rows of one kind goes through the wiping. -/
theorem filter_wipe (A : Array Row) (k : OnBytes.RowKind) :
    (A.map wipeRow).filter (·.kind == k) = (A.filter (·.kind == k)).map wipeRow := by
  rw [Array.filter_map]
  rfl

/-- A member's sample rows at the wiped statement are its sample rows, wiped. -/
theorem sample_at (S : Statement) (o : Nat) :
    (((wipeSt S).oracles[o]?).map (·.sampleRows)).getD #[] =
      (((S.oracles[o]?).map (·.sampleRows)).getD #[]).map wipeRow := by
  rw [wipeSt_oracle_at]
  cases S.oracles[o]? with
  | none => exact Array.map_empty.symm
  | some x => rfl

/-- The members' sample rows, laid one behind the other, go through the wiping. -/
theorem samples_wipe (S : Statement) : ∀ (l : List Nat) (a : Array Row),
    l.foldl (fun a o => a ++ (((wipeSt S).oracles[o]?).map (·.sampleRows)).getD #[]) (a.map wipeRow) =
      (l.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) a).map wipeRow
  | [], _ => rfl
  | o :: l, a => by
    show l.foldl _ (a.map wipeRow ++ (((wipeSt S).oracles[o]?).map (·.sampleRows)).getD #[]) =
      (l.foldl _ (a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[])).map wipeRow
    rw [sample_at S o, ← Array.map_append]
    exact samples_wipe S l _

/-- **The rows that the test takes in**, at the wiped statement, are the rows that it takes in, wiped, in their
order. -/
theorem runRows_wipe (S : Statement) (G : OnBytes.Group) :
    runRows (wipeSt S) (wipeGr G) = (runRows S G).map wipeRow := by
  have h := samples_wipe S G.members.toList #[]
  rw [Array.map_empty, Array.foldl_toList, Array.foldl_toList] at h
  unfold OnBytes.Slice.runRows
  show (G.rows.map wipeRow).filter (·.kind == .plain) ++
      G.members.foldl (fun a o => a ++ (((wipeSt S).oracles[o]?).map (·.sampleRows)).getD #[]) #[] ++
      (G.rows.map wipeRow).filter (·.kind == .generator) = _
  rw [filter_wipe, filter_wipe, h, Array.map_append, Array.map_append]

/-- An oracle message with its ledger closed, as `closeLedgers` closes it. -/
def shutO (x : Oracle) : Oracle := { x with ledger := x.ledger.map fun l => { l with closed := true } }

/-- A group marked as in its test, without open rows, as `begun` marks it. -/
def markRun (G : OnBytes.Group) : OnBytes.Group := { G with inRun := true, rows := #[] }

/-- A change of one oracle message that goes through its wiping goes through the statement's. -/
theorem wipeSt_modify (S : Statement) (o : Nat) (f : Oracle → Oracle)
    (hf : ∀ x, wipeOr (f x) = f (wipeOr x)) :
    wipeSt { S with oracles := S.oracles.modify o f } =
      { wipeSt S with oracles := (wipeSt S).oracles.modify o f } := by
  show (⟨S.codes, (S.oracles.modify o f).map wipeOr, S.groups.map wipeGr⟩ : Statement) =
    ⟨S.codes, (S.oracles.map wipeOr).modify o f, S.groups.map wipeGr⟩
  rw [map_modify_comm S.oracles o f wipeOr f hf]

/-- The closing of ledgers goes through the wiping. -/
theorem closeLedgers_wipe : ∀ (l : List Nat) (S : Statement),
    closeLedgers (wipeSt S) l = wipeSt (closeLedgers S l)
  | [], _ => rfl
  | o :: l, S => by
    show closeLedgers { wipeSt S with oracles := (wipeSt S).oracles.modify o shutO } l =
      wipeSt (closeLedgers { S with oracles := S.oracles.modify o shutO } l)
    rw [← closeLedgers_wipe l, wipeSt_modify S o shutO fun _ => rfl]

/-- The marking of a group goes through the wiping. -/
theorem markRun_wipe (G : OnBytes.Group) : wipeGr (markRun G) = markRun (wipeGr G) := by
  show ({ G with inRun := true, rows := (#[] : Array Row).map wipeRow } : OnBytes.Group) =
    { G with inRun := true, rows := #[] }
  rw [Array.map_empty]

/-- **The statement behind the beginning of the test**, at the wiped statement, is the statement behind, wiped. -/
theorem begun_wipe (S : Statement) (g : Nat) (G : OnBytes.Group) :
    begun (wipeSt S) g (wipeGr G) = wipeSt (begun S g G) := by
  show ({ closeLedgers (wipeSt S) G.members.toList with
      groups := (closeLedgers (wipeSt S) G.members.toList).groups.modify g markRun } : Statement) =
    wipeSt { closeLedgers S G.members.toList with
      groups := (closeLedgers S G.members.toList).groups.modify g markRun }
  rw [closeLedgers_wipe]
  generalize closeLedgers S G.members.toList = C
  show (⟨C.codes, C.oracles.map wipeOr, (C.groups.map wipeGr).modify g markRun⟩ : Statement) =
    ⟨C.codes, C.oracles.map wipeOr, (C.groups.modify g markRun).map wipeGr⟩
  rw [map_modify_comm C.groups g markRun wipeGr markRun markRun_wipe]

/-- The test in front of the beginning reads no row. -/
theorem beginRunL_wipe (S : Statement) (g : Nat) : beginRunL (wipeSt S) g = beginRunL S g := by
  unfold VerifiableInference.Desc.Ground.beginRunL
  rw [wipeSt_group_at, wipeSt_size]
  cases S.groups[g]? <;> rfl

/-- **The beginning of the test**, at the wiped statement: nothing where it yields nothing; else the same layout, the
rows wiped, the statement behind wiped. -/
theorem beginRunP_wipe (S : Statement) (g : Nat) :
    beginRunP (onSt (wipeSt S)) g = (beginRunP (onSt S) g).map fun z =>
      (⟨z.1.layout, z.1.rows.map wipeRow⟩, onSt (wipeSt z.2.st)) := by
  have hg : (onSt (wipeSt S)).st.groups[g]? = ((onSt S).st.groups[g]?).map wipeGr := wipeSt_group_at S g
  have hL : beginRunL (onSt (wipeSt S)).st g = beginRunL (onSt S).st g := beginRunL_wipe S g
  unfold VerifiableInference.Desc.Ground.beginRunP
  rw [hL, hg]
  symm
  refine ite_map _ ?_ rfl
  cases (onSt S).st.groups[g]? with
  | none => rfl
  | some G =>
    show some ((⟨layoutOf S G, (runRows S G).map wipeRow⟩ : RunInput), onSt (wipeSt (begun S g G))) =
      some (⟨layoutOf (wipeSt S) (wipeGr G), runRows (wipeSt S) (wipeGr G)⟩,
        onSt (begun (wipeSt S) g (wipeGr G)))
    rw [layoutOf_wipe, runRows_wipe, begun_wipe]

/-! ## 7 The batching, whole -/

/-- **The verifier's text of the batching at a statement and at that statement wiped**: one refusal, or at both a
return: the rows are one but for their targets, the layout is one, and the statement behind at the wiped statement is
the statement behind, wiped. -/
theorem bat_wipe (S : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) :
    (bat (wipeSt S) g e r).map (fun z => (wipeG z.1, z.2)) =
      (bat S g e r).map fun z => (wipeG z.1, z.2.1, wipeSt z.2.2) := by
  unfold VerifiableInference.Desc.First.Close.bat
  rw [beginRunL_wipe, beginRunP_wipe]
  refine ebind_same fun _ => ?_
  refine got_map _ fun p => ?_
  obtain ⟨input, d⟩ := p
  refine ebind_same fun x => ?_
  have hs : (e.rows == (input.rows.map wipeRow).size) = (e.rows == input.rows.size) := by
    rw [Array.size_map]
  refine need_rel hs ?_
  refine got_rel wipeG (batch_wipe d.st g input x).symm fun a b hab => ?_
  exact congrArg (fun t : GroupRow => (Except.ok (t, input.layout, wipeSt d.st) :
    Except String (GroupRow × GroupLayout × Statement))) hab

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ite_map
#print axioms ProofFile.Honest.K10.bind_rel
#print axioms ProofFile.Honest.K10.foldlM_hom
#print axioms ProofFile.Honest.K10.foldA_same
#print axioms ProofFile.Honest.K10.foldlM_rel
#print axioms ProofFile.Honest.K10.foldA_rel
#print axioms ProofFile.Honest.K10.map_modify_comm
#print axioms ProofFile.Honest.K10.ebind_same
#print axioms ProofFile.Honest.K10.got_map
#print axioms ProofFile.Honest.K10.got_rel
#print axioms ProofFile.Honest.K10.need_rel
#print axioms ProofFile.Honest.K10.wipeOr
#print axioms ProofFile.Honest.K10.wipeGr
#print axioms ProofFile.Honest.K10.wipeG
#print axioms ProofFile.Honest.K10.wipe3
#print axioms ProofFile.Honest.K10.some_d
#print axioms ProofFile.Honest.K10.wipeG_target
#print axioms ProofFile.Honest.K10.wipeSt_oracle_at
#print axioms ProofFile.Honest.K10.wipeSt_group_at
#print axioms ProofFile.Honest.K10.wipeSt_size
#print axioms ProofFile.Honest.K10.shape_at_wipe
#print axioms ProofFile.Honest.K10.rowBits_wipe
#print axioms ProofFile.Honest.K10.has_wipe
#print axioms ProofFile.Honest.K10.placeBits_wipe
#print axioms ProofFile.Honest.K10.tableBits_wipe
#print axioms ProofFile.Honest.K10.tableThere_wipe
#print axioms ProofFile.Honest.K10.realRows_wipe
#print axioms ProofFile.Honest.K10.tableSize_wipe
#print axioms ProofFile.Honest.K10.mainWeight_wipe
#print axioms ProofFile.Honest.K10.mainBack_wipe
#print axioms ProofFile.Honest.K10.maskWeight_wipe
#print axioms ProofFile.Honest.K10.maskBack_wipe
#print axioms ProofFile.Honest.K10.entryInto_st
#print axioms ProofFile.Honest.K10.termInto_st
#print axioms ProofFile.Honest.K10.runInto_st
#print axioms ProofFile.Honest.K10.formInto_st
#print axioms ProofFile.Honest.K10.rowInto_st
#print axioms ProofFile.Honest.K10.entryInto_acc
#print axioms ProofFile.Honest.K10.termInto_acc
#print axioms ProofFile.Honest.K10.runInto_acc
#print axioms ProofFile.Honest.K10.formInto_acc
#print axioms ProofFile.Honest.K10.ready_wipe
#print axioms ProofFile.Honest.K10.rowInto_rel
#print axioms ProofFile.Honest.K10.addScaled_wipe
#print axioms ProofFile.Honest.K10.wipeRow_strip
#print axioms ProofFile.Honest.K10.addScaled_rel
#print axioms ProofFile.Honest.K10.batch_wipe
#print axioms ProofFile.Honest.K10.blockBits_wipe
#print axioms ProofFile.Honest.K10.layoutOf_wipe
#print axioms ProofFile.Honest.K10.filter_wipe
#print axioms ProofFile.Honest.K10.sample_at
#print axioms ProofFile.Honest.K10.samples_wipe
#print axioms ProofFile.Honest.K10.runRows_wipe
#print axioms ProofFile.Honest.K10.shutO
#print axioms ProofFile.Honest.K10.markRun
#print axioms ProofFile.Honest.K10.wipeSt_modify
#print axioms ProofFile.Honest.K10.closeLedgers_wipe
#print axioms ProofFile.Honest.K10.markRun_wipe
#print axioms ProofFile.Honest.K10.begun_wipe
#print axioms ProofFile.Honest.K10.beginRunL_wipe
#print axioms ProofFile.Honest.K10.beginRunP_wipe
#print axioms ProofFile.Honest.K10.bat_wipe
