-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHeadC.lean: the claims of the smallness test (`HTailF2.objectsF`,
OnBytes/Model/Tail.lean) at two lists of tables that differ in the tables' weights.

The head passes its tables of reads to the smallness test, and three of them have weights made of
the request. What `objectsF` does with a table's weights phi: it compares their number with the
table's length; it lays their sum into the constant of a read's form; and it passes them as the
weights of two runs on one virtual row (`linRead`). The rest reads a table's four public numbers.
The state of the test only carries the list: `linJoin9`, `linBits9` and `weightsF` return it as it
came.

The test `funsHeld` compares the list that is passed in with the list that the state holds, weights
and all, and it is no test that a dry run skips. It gives the same at both requests because in each
run the two lists are one list (`TailAlike` says so, `funsHeld_self`).

Main theorems: `get_relA`; `linJoin9_rel`, `linBits9_rel`, `foldSums_alike`, `weightsF_rel`;
`t2Lin_rel`, `readEnts_eq`, `markLoop_eq`, `markRead_eq`, `linRead_rel`; `Cmp.forIn_list2` (two
loops over two lists, member by member); `sameFun_self`, `funsHeld_self`, `funs_all`,
`tablesTile_eq`, `resp_cols`, `resp_size`, `resp_kinds`; `objectsF_rel`.

Not claimed: anything on a run on a view. For proofs only; no module of the program imports this
file.


-/
import OnBytes.Flat.LinksFreeHeadB

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-- `SubM.get` at two values that may be missing. -/
theorem get_relA {α : Type} {R : α → α → Prop} {x x' : Option α} (h : OptRel R x x') :
    cmpA.Rel R (SubM.get x) (SubM.get x') := by
  cases x with
  | none =>
    cases x' with
    | none => exact fun _ _ _ _ _ => trivial
    | some a' => exact h.elim
  | some a =>
    cases x' with
    | none => exact h.elim
    | some a' =>
      intro s s' hs c _
      exact ⟨⟨h, hs⟩, rfl⟩

/-! ## Routines that only carry the list of tables -/

theorem linJoin9_rel {f f' : Array HFun} {tl tl' : HTailF2} (h : TailAlike f f' tl tl') :
    cmpA.Rel (TailAlike f f') tl.linJoin9 tl'.linJoin9 := by
  obtain ⟨h1, rfl⟩ := h
  unfold HTailF2.linJoin9
  dsimp only
  repeat (refine cmpA_same (by resp) fun _ => ?_)
  exact cmpA.pure' ⟨h1, rfl⟩

theorem linBits9_rel {f f' : Array HFun} {tl tl' : HTailF2} (h : TailAlike f f' tl tl') :
    cmpA.Rel (TailAlike f f') tl.linBits9 tl'.linBits9 := by
  obtain ⟨h1, rfl⟩ := h
  unfold HTailF2.linBits9
  dsimp only
  repeat (refine cmpA_same (by resp) fun _ => ?_)
  exact cmpA.pure' ⟨h1, rfl⟩

theorem foldSums_alike {f f' : Array HFun} {tl tl' : HTailF2} (h : TailAlike f f' tl tl')
    (mu : Nat) : OptRel (TailAlike f f') (tl.foldSums mu) (tl'.foldSums mu) := by
  obtain ⟨h1, rfl⟩ := h
  unfold HTailF2.foldSums
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | exact ⟨h1, rfl⟩

theorem weightsF_rel {f f' : Array HFun} {tl tl' : HTailF2} (h : TailAlike f f' tl tl') :
    cmpA.Rel (TailAlike f f') tl.weightsF tl'.weightsF := by
  obtain ⟨h1, rfl⟩ := h
  unfold HTailF2.weightsF
  refine cmpA.bind' (S := TailAlike f f') (by keeps) (ask_rel ?_) fun t t' ht => ?_
  · intro F F' hF
    obtain ⟨e, -⟩ := hF
    generalize F'.trees = T' at e
    generalize F'.c0 = c' at e
    subst e
    unfold HTailF2.powersF
    dsimp only
    split
    · trivial
    · exact ⟨h1, rfl⟩
  · have key : ∀ (l : List Nat) (x x' : HTailF2), TailAlike f f' x x' →
        OptRel (TailAlike f f') (l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) x)
          (l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) x') := by
      intro l
      induction l with
      | nil => exact fun _ _ hx => hx
      | cons mu l ih =>
        intro x x' hx
        rw [List.foldlM_cons, List.foldlM_cons]
        exact optRel_bind (foldSums_alike hx mu) fun y y' hy => ih y y' hy
    obtain ⟨t1, rfl⟩ := ht
    have h0 := key (List.range t.NM)
      { t with gamX := Array.replicate t.NM #[], gamV := Array.replicate t.NM #[] }
      { t with funs := f', gamX := Array.replicate t.NM #[], gamV := Array.replicate t.NM #[] }
      ⟨t1, rfl⟩
    exact get_relA h0

/-! ## A read of a table, at two vectors of weights -/

theorem t2Lin_rel {a a' : Aff} (ha : AffAlike a a') {runs runs' : Array Run2}
    (hr : All2 Run2Alike runs.toList runs'.toList) :
    cmpA.Rel Eq (t2Lin a runs) (t2Lin a' runs') := by
  unfold t2Lin
  refine cmpA_same (by resp) fun k => ?_
  refine cmpA.bind' (by keeps) (change_rel fun _ _ h => push_alike h k ha) fun _ _ _ => ?_
  exact change_rel fun _ _ h => pushRuns_alike h k k hr

/-- The number of columns of an array. -/
theorem resp_cols (t : Nat) : Resp.K (SubM.ask fun F => some (((F.trees[t]?).map (·.K)).getD 0)) :=
  ask_same _ fun _ _ _ h => by
    show some _ = some _
    rw [trees_read h (fun o => (o.map (·.K)).getD 0) (fun o => by cases o <;> rfl) t]

theorem readEnts_eq (tl : HTailF2) (f' : Array HFun) (Fn : HFun) (phi' : Array E)
    (sg tU cols : Nat) (minus : E) (gc : Array E) :
    ∀ (count c : Nat) (ents : Array Ent) (b : Bool),
      HTailF2.readEnts { tl with funs := f' } { Fn with phi := phi' } sg tU cols minus gc count c
        ents b = tl.readEnts Fn sg tU cols minus gc count c ents b
  | 0, _, _, _ => rfl
  | count + 1, c, ents, b => by
      unfold HTailF2.readEnts
      show (match tl.tabAt Fn c sg with
        | none => none
        | some pos => _) = _
      cases tl.tabAt Fn c sg with
      | none => rfl
      | some pos => exact readEnts_eq tl f' Fn phi' sg tU cols minus gc count (c + 1) _ _

theorem markLoop_eq (tl : HTailF2) (f' : Array HFun) (Fn : HFun) (phi' : Array E) (sg t0 : Nat) :
    ∀ (count c : Nat) (marks : Array Bool),
      HTailF2.markLoop { tl with funs := f' } { Fn with phi := phi' } sg t0 count c marks =
        tl.markLoop Fn sg t0 count c marks
  | 0, _, _ => rfl
  | count + 1, c, marks => by
      unfold HTailF2.markLoop
      show (match tl.tabAt Fn c sg with
        | none => none
        | some pos => _) = _
      cases tl.tabAt Fn c sg with
      | none => rfl
      | some pos =>
        dsimp only
        split
        · exact markLoop_eq tl f' Fn phi' sg t0 count (c + 1) _
        · rfl

theorem markRead_eq (tl : HTailF2) (f' : Array HFun) (Fn : HFun) (phi' : Array E) (sg : Nat)
    (rd : Array (Array Bool)) :
    HTailF2.markRead { tl with funs := f' } { Fn with phi := phi' } sg rd =
      tl.markRead Fn sg rd := by
  unfold HTailF2.markRead
  dsimp only
  rw [markLoop_eq tl f' Fn phi']

theorem linRead_rel (tl : HTailF2) (f' : Array HFun) {Fn Fn' : HFun} (hF : FunAlike Fn Fn')
    (sg laid : Nat) (sums sums' : E) :
    cmpA.Rel Eq (tl.linRead Fn sg laid sums)
      (HTailF2.linRead { tl with funs := f' } Fn' sg laid sums') := by
  obtain ⟨e, hs⟩ := hF
  generalize Fn'.phi = phi' at e hs
  subst e
  unfold HTailF2.linRead
  dsimp only
  refine cmpA_same (by resp) fun tU => ?_
  refine cmpA_same (resp_leadF _) fun lead => ?_
  refine cmpA_same (resp_cols tU) fun cols => ?_
  refine cmpA_same (by resp) fun _ => ?_
  rw [readEnts_eq tl f' Fn phi']
  refine cmpA_same (by resp) fun x => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA_same (by resp) fun c0 => ?_
  refine cmpA_same (by resp) fun c1 => ?_
  have e : ∀ v : E, (HTailF2.lessBeta v).slots = #[] := fun _ => rfl
  rw [e, e]
  generalize (HTailF2.lessBeta (mulE lead sums)).const = k1
  generalize (HTailF2.lessBeta (mulE lead sums')).const = k2
  generalize HTailF2.highDigit lead = hd
  refine t2Lin_rel ?_ ?_
  · exact ⟨rfl, rfl⟩
  · rw [List.toList_toArray, List.toList_toArray]
    refine .cons ?_ (.cons ?_ .nil)
    · exact ⟨rfl, rfl, rfl, rfl, rfl, hs⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, hs⟩

/-! ## Loops over two lists -/

theorem Cmp.forIn_list2 {m : Type → Type} [Monad m] [Over m] (c : Cmp m) {α β : Type}
    {Q : α → α → Prop} {S : β → β → Prop} {f f' : α → β → m (ForInStep β)}
    (hk : ∀ a s, Over.K (f a s))
    (hf : ∀ a a' s s', Q a a' → S s s' → c.Rel (StepRel S) (f a s) (f' a' s')) {l l' : List α}
    (hl : All2 Q l l') :
    ∀ {init init' : β}, S init init' → c.Rel S (forIn l init f) (forIn l' init' f') := by
  induction hl with
  | nil =>
    intro init init' h
    rw [List.forIn_nil, List.forIn_nil]
    exact c.pure' h
  | cons h0 _ ih =>
    intro init init' h
    rw [List.forIn_cons, List.forIn_cons]
    refine c.bind' (hk _ init) (hf _ _ init init' h0 h) fun r r' hr => ?_
    cases r <;> cases r'
    · exact c.pure' hr
    · exact hr.elim
    · exact hr.elim
    · exact ih hr

/-! ## What is read of a list of tables beside the weights -/

theorem sameFun_self (a : HFun) : HTailF2.sameFun a a = true := by
  unfold HTailF2.sameFun
  simp only [beq_self_eq_true, Bool.and_self]

/-- A state of the smallness test holds its own list, if the list is closed. -/
theorem funsHeld_self (tl : HTailF2) : tl.funsHeld tl.funs = tl.funClosed := by
  unfold HTailF2.funsHeld
  have e : ((List.range tl.funs.size).all fun i =>
      HTailF2.sameFun (tl.funs.getD i {}) (tl.funs.getD i {})) = true := by
    rw [List.all_eq_true]
    exact fun _ _ => sameFun_self _
  rw [e]
  simp only [beq_self_eq_true, Bool.and_true]

theorem funs_all {f f' : Array HFun} (h : FunsAlike f f') (p : Nat → Nat → Bool) :
    (f.all fun Fn => p Fn.mat Fn.tree) = f'.all fun Fn => p Fn.mat Fn.tree := by
  rw [← Array.all_toList, ← Array.all_toList]
  exact all_alike (fun a b hab => by rw [hab.1]) h

theorem tablesTile_eq (tl : HTailF2) {f f' : Array HFun} (h : FunsAlike f f') (un : Nat) :
    HTailF2.tablesTile { tl with funs := f' } f' un = tl.tablesTile f un := by
  have e : ∀ {l l' : List HFun}, All2 FunAlike l l' →
      ((l'.filter fun Fn => Fn.tree == un).map fun Fn =>
        (Fn.start, (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len),
          (tl.mats.getD Fn.mat {}).m / Fn.len)) =
      ((l.filter fun Fn => Fn.tree == un).map fun Fn =>
        (Fn.start, (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len),
          (tl.mats.getD Fn.mat {}).m / Fn.len)) := by
    intro l l' hl
    induction hl with
    | nil => rfl
    | cons h0 _ ih =>
      obtain ⟨e0, -⟩ := h0
      rw [e0]
      simp only [List.filter_cons]
      split
      · simp only [List.map_cons, ih]
      · exact ih
  unfold HTailF2.tablesTile
  dsimp only
  rw [e h]

theorem resp_size : Resp.K (SubM.ask fun F => some F.trees.size) :=
  ask_same _ fun _ _ _ h => congrArg some (trees_size h).symm

theorem resp_kinds : Resp.K (SubM.ask fun F => some (F.trees.map (·.kind))) :=
  ask_same _ fun F T' _ h => by
    have h0 := congrArg (Array.map (·.kind)) h
    simp only [Array.map_map] at h0
    exact congrArg some h0.symm

theorem stepRel_refl {β : Type} (a : ForInStep β) : StepRel Eq a a := by
  cases a <;> rfl

/-! ## The claims of the smallness test -/

theorem objectsF_rel {f f' : Array HFun} (hf : FunsAlike f f') {tl tl' : HTailF2}
    (h : TailAlike f f' tl tl') : cmpA.Rel (TailAlike f f') (tl.objectsF f) (tl'.objectsF f') := by
  obtain ⟨h1, rfl⟩ := h
  subst h1
  unfold HTailF2.objectsF
  dsimp only
  have e2 : HTailF2.funsHeld { tl with funs := f' } f' = tl.funClosed :=
    funsHeld_self { tl with funs := f' }
  rw [funsHeld_self tl, e2]
  simp only [beq_self_eq_true]
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA_same (ask_same _ fun _ _ _ _ => rfl) fun _ => ?_
  iterate 7 (refine cmpA_same (by resp) fun _ => ?_)
  refine cmpA.bind' (by keeps) (linJoin9_rel ⟨rfl, rfl⟩) fun t t' ht => ?_
  refine cmpA.bind' (by keeps) (linBits9_rel ht) fun t t' ht => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA_same (by resp) fun _ => ?_
  refine cmpA.bind' (by keeps) (weightsF_rel ht) fun t t' ht => ?_
  obtain ⟨t1, rfl⟩ := ht
  dsimp only
  refine cmpA_same resp_size fun n => ?_
  refine cmpA_same (by resp) fun r => ?_
  refine cmpA.bind' (S := Eq) (by keeps)
    (cmpA.forIn_list (fun _ _ => by keeps) (fun mu s s' hs => ?_) _ rfl) fun r1 r1' e1 => ?_
  · subst hs
    refine cmpA.bind' (S := Eq) (by keeps)
      (cmpA.forIn_list (fun _ _ => by keeps) (fun un s2 s2' hs2 => ?_) _ rfl) fun q q' eq => ?_
    · subst hs2
      refine cmpA.bind' (S := Eq) (by keeps) ?_ fun q q' eq => ?_
      · rw [← Array.forIn_toList, ← Array.forIn_toList]
        refine cmpA.forIn_list2 (fun _ _ => by keeps) (fun Fn Fn' s3 s3' hFn hs3 => ?_) hf rfl
        subst hs3
        obtain ⟨eF, hsz⟩ := hFn
        generalize Fn'.phi = phi' at eF hsz
        subst eF
        dsimp only
        split
        · refine cmpA_same (by resp) fun _ => ?_
          rw [← hsz]
          refine cmpA_same (by resp) fun _ => ?_
          refine cmpA.bind' (S := Eq) (by keeps)
            (cmpA.forIn_list (fun _ _ => by keeps) (fun sg s4 s4' hs4 => ?_) _ rfl)
            fun q q' eq => ?_
          · subst hs4
            rw [markRead_eq t f' Fn phi']
            refine cmpA_same (by resp) fun rd => ?_
            refine cmpA.bind' (by keeps) (linRead_rel t f' ⟨rfl, hsz⟩ _ _ _ _) fun _ _ _ => ?_
            exact cmpA_refl stepRel_refl (by resp)
          · subst eq
            exact cmpA_refl stepRel_refl (by resp)
        · exact cmpA_refl stepRel_refl (by resp)
      · subst eq
        exact cmpA_refl stepRel_refl (by resp)
    · subst eq
      exact cmpA_refl stepRel_refl (by resp)
  subst e1
  have ea := funs_all hf fun m tr => decide (m < t.NM) && (tr == 0 || tr == 2)
  rw [← ea, tablesTile_eq t hf 0, tablesTile_eq t hf 2]
  iterate 4 (refine cmpA_same (by resp) fun _ => ?_)
  refine cmpA_same resp_kinds fun _ => ?_
  iterate 3 (refine cmpA_same (by resp) fun _ => ?_)
  refine cmpA_same (ask_same _ fun _ _ _ _ => rfl) fun _ => ?_
  exact cmpA.pure' ⟨t1, rfl⟩

end OnBytes.Flat
