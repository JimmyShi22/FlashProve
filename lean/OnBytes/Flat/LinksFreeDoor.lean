-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeDoor.lean: the end of a link's check gives the same from two states that are
alike: `DoorFree` (OnBytes/Flat/LinksFreeHead.lean), one of the seven pieces of `HeadFree`.

`doorH` (OnBytes/Model/Trees.lean) hands the chain the one equation in which a sub-proof ends. It
reads the state of the check itself. Of two states that are alike (`ForkAlike`,
OnBytes/Flat/LinksFreeFork.lean) the weights L on the virtual rows and the constant c0 differ, so
the two equations differ: in the weights that are written out on the arrays' columns and in the
target. What is shown: in a dry run nothing that is made of these outlives the call. By the
program's text: the tests before the loop read what the two states share, or are conditions on
values, which a dry run skips; `doorTerms` lays L into a term and reads its size alone;
`Fork.settle` makes the coefficients on the masks of what is shared and lays c0 into the constant
alone; `ReqRows.row` refuses by shapes (`addTerms_alike`, OnBytes/Flat/DoorTermsAlike.lean); and
`Blk.addRow` in a dry run reads the row's kind and keeps no row.

Main theorems: `addRow_rel`, `row_rel`, `close_rel` (blocks); `settle_alike`, `settle_rel`;
`forIn_rel` (a loop over two lists, member by member; `StepBoth`); `doorTerms_rel`; `subA_rel`,
`testAs_rel`, `call_rel` (the link's layer); `doorH_rel`; `doorFree_of`: `DoorFree` from
`AddTermsAlike` (OnBytes/Flat/DoorAlike.lean); `doorFree : DoorFree`.

Not claimed: anything on a run on a view: there the two equations are two rows. Nothing on the other
six pieces. For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksFreeHead
import OnBytes.Flat.DoorTermsAlike

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-! ## Blocks -/

/-- After the question whether the run is dry: the two continuations at "yes". -/
theorem relB_isDry {β : Type} {R : β → β → Prop} {f f' : Bool → Blk β}
    (h : relB R (f true) (f' true)) : relB R (Blk.isDry >>= f) (Blk.isDry >>= f') := by
  intro c hc
  have e : ∀ g : Bool → Blk β, (Blk.isDry >>= g) c = g true c := by
    intro g
    show (match Blk.isDry c with
      | .error e => .error e
      | .ok p => g p.1 p.2) = g true c
    unfold Blk.isDry
    simp only [hc.1]
  rw [e, e]
  exact h c hc

/-- Unwrapping two values that are both there, in R, or both not. -/
theorem relB_get {α : Type} {R : α → α → Prop} {x x' : Option α} (h : OptRel R x x')
    (name : String) : relB R (Blk.get x name) (Blk.get x' name) := by
  intro c _
  unfold Blk.get
  cases x <;> cases x'
  · trivial
  · exact h.elim
  · exact h.elim
  · exact ⟨h, rfl⟩

/-- **A dry run keeps no row**: of the row it reads the kind alone. -/
theorem addRow_rel (g : Nat) {row row' : Row} (h : row.kind = row'.kind) :
    relB Eq (Blk.addRow g row) (Blk.addRow g row') := by
  unfold Blk.addRow
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun S => ?_
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun G => ?_
  rw [h]
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_isDry ?_
  simp only [if_true]
  exact relB_pure rfl

/-- A link's equation as a row, at two equations that are alike. -/
theorem row_rel (hA : AddTermsAlike) (R : ReqRows) (f : ReqFrame) {e e' : ReqEquation}
    (h : EqnAlike e e') :
    relB (fun r r' => r.kind = r'.kind) (R.row f e) (R.row f e') := by
  unfold ReqRows.row
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun S => ?_
  refine relB_bind (S := fun r r' => r.kind = r'.kind) (by show Over.K (m := Blk) _; keeps)
    (relB_get (hA R f S _ _ {} {} h.1 rfl) _) fun row row' hk => ?_
  rw [← h.2]
  split
  · exact relB_pure hk
  · iterate 5 (refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_)
    exact relB_pure hk

/-- **The link's end on the chain**, at two equations that are alike: one state of the chain's calls
and one context are left. -/
theorem close_rel (hA : AddTermsAlike) (c : ChainCheck) {e e' : ReqEquation} (h : EqnAlike e e') :
    relB Eq (c.close e) (c.close e') := by
  unfold ChainCheck.close
  refine relB_same (by show Over.K (m := Blk) _; keeps) fun _ => ?_
  refine relB_bind (by show Over.K (m := Blk) _; keeps) (row_rel hA _ _ h) fun row row' hk => ?_
  refine relB_bind (by show Over.K (m := Blk) _; keeps) (addRow_rel _ hk) fun _ _ _ => ?_
  exact relB_refl _

/-! ## What is made of the state -/

/-- The fold of `Fork.settle` from two constants: it refuses both times, or returns one count and
one array of coefficients on the masks. -/
theorem settleFold_alike (F : Fork) : ∀ (l : List E) (j : Nat) (m : Array E) (c c' : E),
    OptRel (fun x x' => x.1 = x'.1 ∧ x.2.1 = x'.2.1)
      (l.foldlM (Fork.settleStep F) (j, m, c)) (l.foldlM (Fork.settleStep F) (j, m, c'))
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | y :: l, j, m, c, c' => by
      rw [List.foldlM_cons, List.foldlM_cons]
      unfold Fork.settleStep
      dsimp only
      split
      · exact settleFold_alike F l _ _ _ _
      · split
        · exact settleFold_alike F l _ _ _ _
        · trivial

/-- The coefficients on the masks are the same at two states that are alike; the constants are free.
-/
theorem settle_alike {F F' : Fork} (h : ForkAlike F F') (used : Nat) :
    OptRel (fun p p' => p.1 = p'.1) (F.settle used) (F'.settle used) := by
  obtain ⟨e, hT⟩ := h
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  unfold Fork.settle
  dsimp only
  split
  · have k := settleFold_alike F F.LS.toList 0 (Array.replicate F.ns zeroE) F.c0 c'
    have es : Fork.settleStep { F with trees := T', c0 := c' } = Fork.settleStep F := rfl
    rw [es, ← Array.foldlM_toList, ← Array.foldlM_toList]
    revert k
    cases List.foldlM (Fork.settleStep F) (0, Array.replicate F.ns zeroE, F.c0) F.LS.toList <;>
      cases List.foldlM (Fork.settleStep F) (0, Array.replicate F.ns zeroE, c') F.LS.toList <;>
      intro k
    · trivial
    · exact k.elim
    · exact k.elim
    · exact k.2
  · trivial

/-- `SubM.settle` from two states that are alike. -/
theorem settle_rel (used : Nat) :
    cmpA.Rel (fun p p' => p.1 = p'.1) (SubM.settle used) (SubM.settle used) :=
  ask_rel fun _ _ h => settle_alike h used

/-! ## Loops, two-sided -/

/-- Two steps of a loop: both end it, or both go on, with values in S. -/
def StepBoth {β : Type} (S : β → β → Prop) : ForInStep β → ForInStep β → Prop
  | .done a, .done b => S a b
  | .yield a, .yield b => S a b
  | _, _ => False

/-- A loop over two lists, member by member. -/
theorem forIn_rel {m : Type → Type} [Monad m] [Over m] (c : Cmp m) {α β : Type}
    {Q : α → α → Prop} {S : β → β → Prop} {f f' : α → β → m (ForInStep β)}
    (hk : ∀ a s, Over.K (f a s))
    (hf : ∀ a a' s s', Q a a' → S s s' → c.Rel (StepBoth S) (f a s) (f' a' s')) :
    ∀ {l l' : List α}, All2 Q l l' → ∀ {s s' : β}, S s s' →
      c.Rel S (forIn l s f) (forIn l' s' f')
  | _, _, .nil, _, _, hs => by
      rw [List.forIn_nil, List.forIn_nil]
      exact c.pure' hs
  | _, _, .cons ha hl, _, _, hs => by
      rw [List.forIn_cons, List.forIn_cons]
      refine c.bind' (hk _ _) (hf _ _ _ _ ha hs) fun r r' hr => ?_
      cases r <;> cases r'
      · exact c.pure' hr
      · exact hr.elim
      · exact hr.elim
      · exact forIn_rel c hk hf hl hr

/-- One member more at the end of both lists. -/
theorem All2.snoc {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β} {a : α} {b : β}
    (h : All2 R l l') (hab : R a b) : All2 R (l ++ [a]) (l' ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h0 _ ih => exact .cons h0 ih

/-- Two lists with one image under g, member by member. -/
theorem all2_of_map {α β : Type} {g : α → β} : ∀ {l l' : List α}, l.map g = l'.map g →
    All2 (fun a a' => g a = g a') l l'
  | [], [], _ => .nil
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | _ :: _, _ :: _, h => by
      rw [List.map_cons, List.map_cons, List.cons.injEq] at h
      exact .cons h.1 (all2_of_map h.2)

/-! ## The terms of the equation -/

/-- Two arrays of terms, member by member. -/
def TermsAlike (t t' : Array ReqTerm) : Prop := All2 TermAlike t.toList t'.toList

/-- One term more on both arrays. -/
theorem TermsAlike.push {t t' : Array ReqTerm} (h : TermsAlike t t') {x x' : ReqTerm}
    (hx : TermAlike x x') : TermsAlike (t.push x) (t'.push x') := by
  unfold TermsAlike
  rw [Array.toList_push, Array.toList_push]
  exact All2.snoc h hx

/-- Two arrays behind two arrays. -/
theorem TermsAlike.append {t t' u u' : Array ReqTerm} (h : TermsAlike t t')
    (hu : TermsAlike u u') : TermsAlike (t ++ u) (t' ++ u') := by
  unfold TermsAlike
  rw [Array.toList_append, Array.toList_append]
  exact All2.append h hu

/-- Two virtual rows that agree without the weights: all is equal but L, of one size. -/
theorem eraseRow_eq {r r' : HRow} (h : eraseRow r = eraseRow r') :
    r' = { r with L := r'.L } ∧ r.L.size = r'.L.size := by
  cases r
  cases r'
  simp only [eraseRow, HRow.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  subst h1 h3 h4 h5 h6 h7 h8 h9
  refine ⟨rfl, ?_⟩
  have k := congrArg Array.size h2
  simpa only [Array.size_replicate] using k

/-- Two arrays that agree without the weights: all is equal but the virtual rows, which agree
without the weights. -/
theorem eraseTree_eq {X X' : HTree} (h : eraseTree X = eraseTree X') :
    X' = { X with rows := X'.rows } ∧ X.rows.map eraseRow = X'.rows.map eraseRow := by
  cases X
  cases X'
  simp only [eraseTree, HTree.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  subst h1 h2 h3 h4 h5 h6
  exact ⟨rfl, h7⟩

/-- **The terms on one array**, at two arrays that agree without the weights on the columns. -/
theorem doorTerms_rel (born : Nat) (array : String) {X X' : HTree}
    (h : eraseTree X = eraseTree X') :
    cmpA.Rel TermsAlike (doorTerms born array X) (doorTerms born array X') := by
  obtain ⟨e, hr⟩ := eraseTree_eq h
  generalize X'.rows = rows' at e hr
  subst e
  have hl : All2 (fun r r' => eraseRow r = eraseRow r') X.rows.toList rows'.toList := by
    refine all2_of_map ?_
    rw [← Array.toList_map, ← Array.toList_map, hr]
  unfold doorTerms
  dsimp only
  refine cmpA.bind' (S := TermsAlike) (by keeps) ?_ fun t t' ht => cmpA.pure' ht
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  refine forIn_rel cmpA (by intro a s; keeps) ?_ hl .nil
  intro r r' s s' hrr hs
  obtain ⟨er, hsz⟩ := eraseRow_eq hrr
  generalize r'.L = L' at er hsz
  subst er
  dsimp only
  rw [← hsz]
  refine cmpA_same (by resp) fun _ => ?_
  have term : ∀ (sc : E) (w : IndexWeights),
      TermAlike
        { born := born, array := array, scale := sc, onRows := w,
          onColumns := { values := some r.L } }
        { born := born, array := array, scale := sc, onRows := w,
          onColumns := { values := some L' } } :=
    fun _ _ => ⟨rfl, r.L, L', rfl, rfl, hsz⟩
  refine cmpA.ite ?_ ?_
  · have ew : rowWeights { X with rows := rows' } { r with L := L' } = rowWeights X r := rfl
    rw [ew]
    refine cmpA_same (by resp) fun w => ?_
    refine cmpA_same (by resp) fun _ => ?_
    exact cmpA.pure' (hs.push (term oneE w))
  · refine cmpA.bind' (S := TermsAlike) (by keeps) ?_ fun t t' ht => ?_
    · refine forIn_rel cmpA (Q := Eq) (by intro a s; keeps) ?_ (All2.refl (fun _ => rfl) _) hs
      intro i i' u u' e hu
      subst e
      refine cmpA_same (by resp) fun _ => ?_
      exact cmpA.pure' (hu.push (term _ _))
    · refine cmpA_same (by resp) fun _ => ?_
      exact cmpA.pure' ht

/-! ## The link's layer -/

/-- A routine of the sub-proof's engine, used inside a link, from two states that are alike. -/
theorem subA_rel {α : Type} {R : α → α → Prop} {x x' : SubM α} (hk : Over.K x)
    (hx : cmpA.Rel R x x') : cmpLA.Rel R (LinkM.sub x) (LinkM.sub x') := by
  intro C C' hC
  subst hC
  exact cmpA.bind' hk hx fun _ _ h => cmpA.pure' ⟨h, rfl⟩

/-- The same in a link. -/
theorem testAs_rel (name : String) (b b' : Bool) :
    cmpLA.Rel Eq (LinkM.testAs name b) (LinkM.testAs name b') := by
  unfold LinkM.testAs
  exact subA_rel (by keeps)
    (Cmp.blk.lift ForkAlike (by show Over.K (m := Blk) _; keeps) (relB_testAs name b b'))

/-- A call of the chain, at two calls that leave one state of the chain's calls. -/
theorem call_rel {f f' : ChainCheck → Blk ChainCheck} (hk : ∀ c, Blk.Keeps (f c))
    (h : ∀ c, relB Eq (f c) (f' c)) : cmpLA.Rel Eq (LinkM.call f) (LinkM.call f') := by
  intro C C' hC
  subst hC
  unfold LinkM.call
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (S := Eq) (k_lift (m := Blk) (hk _)) (Cmp.blk.lift ForkAlike (hk _) (h _))
    fun a a' e => ?_
  subst e
  exact cmpA.pure' ⟨rfl, rfl⟩

/-- The arrays of one number in two lists that agree without the weights. -/
theorem getD_erase {T T' : Array HTree} (h : T.map eraseTree = T'.map eraseTree) (i : Nat) :
    eraseTree (T.getD i {}) = eraseTree (T'.getD i {}) := by
  have k := trees_read h (fun o => eraseTree (o.getD {}))
    (fun o => by
      cases o
      · rfl
      · show eraseTree (eraseTree _) = eraseTree _
        unfold eraseTree eraseRow
        simp [Function.comp_def]) i
  simpa only [Array.getD_eq_getD_getElem?] using k

/-- **The link's end**, from two states that are alike. -/
theorem doorH_rel (hA : AddTermsAlike) (n : Nat) : cmpLA.Rel Eq (doorH n) (doorH n) := by
  have h3 : Resp.K (SubM.change fun F => some { F with doorShutF := true }) :=
    ⟨by keeps, change_rel fun F F' h => by
      obtain ⟨e, hT⟩ := h
      generalize F'.trees = T' at e hT
      generalize F'.c0 = c' at e
      subst e
      exact ⟨rfl, hT⟩⟩
  unfold doorH
  refine cmpLA_same (by resp) fun L => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA.bind' (by keeps) fork_rel fun F F' hF => ?_
  obtain ⟨e, hT⟩ := hF
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  dsimp only
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA.bind' (by keeps) (testAs_rel _ _ _) fun _ _ _ => ?_
  refine cmpLA_same (by resp) fun _ => ?_
  rw [← trees_size hT]
  refine cmpLA_same (by resp) fun _ => ?_
  refine cmpLA.bind' (S := TermsAlike) (by keeps) ?_ fun t t' ht => ?_
  · refine forIn_rel cmpLA (Q := Eq) (by intro a s; keeps) ?_ (All2.refl (fun _ => rfl) _) .nil
    intro ti ti' u u' e hu
    subst e
    have hX := getD_erase hT ti
    have eR : (eraseTree (F.trees.getD ti {})).R = (eraseTree (T'.getD ti {})).R :=
      congrArg HTree.R hX
    have eK : (eraseTree (F.trees.getD ti {})).K = (eraseTree (T'.getD ti {})).K :=
      congrArg HTree.K hX
    change (F.trees.getD ti {}).R = (T'.getD ti {}).R at eR
    change (F.trees.getD ti {}).K = (T'.getD ti {}).K at eK
    rw [← eR, ← eK]
    refine cmpLA_same (by resp) fun _ => ?_
    refine cmpLA.bind' (S := TermsAlike) (by keeps)
      (subA_rel (by keeps) (doorTerms_rel _ _ hX)) fun w w' hw => ?_
    refine cmpLA_same (by resp) fun _ => ?_
    exact cmpLA.pure' (hu.append hw)
  · refine cmpLA.bind' (S := fun p p' => p.1 = p'.1) (by keeps)
      (subA_rel (by keeps) (settle_rel _)) fun p p' hp => ?_
    refine cmpLA_same (by resp) fun _ => ?_
    refine cmpLA.bind' (by keeps)
      (call_rel (fun c => by show Over.K (m := Blk) _; keeps) fun c => close_rel hA c ⟨ht, hp⟩)
      fun _ _ _ => ?_
    exact (resp_link (by resp)).2

/-- **Of the link's end**, from what is asked of `ReqRows.addTerms`. -/
theorem doorFree_of (hA : AddTermsAlike) : DoorFree := fun n C =>
  ⟨(by keeps : Over.K (doorH n)) C,
    cmpA.mono' (fun _ _ k => Prod.ext k.1 k.2) (doorH_rel hA n C C rfl)⟩

/-- **Of the link's end.** -/
theorem doorFree : DoorFree := doorFree_of addTerms_alike

end OnBytes.Flat
