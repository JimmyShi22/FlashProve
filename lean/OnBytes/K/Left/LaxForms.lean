-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxForms.lean: the forms and the roots of the openings of an entry file, as the lax
verifier's clause on the walks asks them: two of the six conjuncts of the field `walks` of
`LaxDebts` (Lax.lean of this folder), `FormsOn` and `RtsL`; and, for two more, the side premises on
forms and roots of the two lemmas that make the records of an opening from the reader's yes
(`ownOkE_of_read`, `stoOkE_of_read`, OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean).

The field binds two relations by "there is". They are picked here:
  `FmOf D n s`: the n-th tree of D's rounds, counted through the rounds, has the form s.
  `RtOf o n c`: the n-th root that was sent, counted through the rounds as read, is c.

One hypothesis on the file: the strict reader's equation
`Fmt.readChainX h (specOf D st) seen b i = some (o, j)`, at any hash h and any statement st.
One on the description: `PQ.ok D.base = true`.

Main names:
  `forms_on`: `FormsOn (FmOf D) 0 D.ds`.
  `rts_on`: `RtsL (RtOf o) D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList)`.
  `own_facts`: an opening of a tree of the chain's own has a number m at which its form stands
    under `FmOf` and its root under `RtOf`, and its tree's number names that form alone.
  `own_form`, `own_root`: the premises `hform`, `hroot` of `ownOkE_of_read`.
  `own_tree`: that form is among the trees of one of D's rounds.
  `sto_root`: the premise `hr` of `stoOkE_of_read`, if the statement's items hold the two roots.
  `rts_on_at`, `own_form_at`, `own_root_at`, `own_tree_at`, `sto_root_at`: the same at the entry's
    description `entryXD G c` (OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean).
  `opens_at`: every opening of the file by its place in the file: the k-th opening of a round is of
    the k-th stored table that the description lists there, or of a tree that the round opens.

How. A tree of the chain's own has the number `firstTree` + n, by the format's conditions on a
description; so has the form that stands in for a tree that is opened nowhere. So a tree's number
names its place n in the order of sending. The reader has compared each opening's root with the
n-th root sent so far, or with the root in the statement's item.

Limits: values alone. Nothing on soundness; no probability. The lengths of columns and salts and the
depth of the stored tables are in LaxLens.lean; the leaves' laws in LaxPagesOwn.lean and
LaxPages.lean.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxReadAs
import OnBytes.TypedOracleCompiler.Slice.EntryWhole
import OnBytes.TypedOracleCompiler.Run.RootsByRound

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Run (bytesToDig HId)
open _root_.Run.PQ (TraceL ownNo allOpens shapeOfOwn bareShape)

/-- "Tree n, counted through the rounds, has the form s." -/
def FmOf (D : XD) (n : ℕ) (s : Fmt.Shape) : Prop := (allT D.ds)[n]? = some s

/-- "The n-th root that was sent, counted through the rounds, is c." -/
def RtOf (o : Fmt.ChainOut) (n : ℕ) (c : _root_.Iop.Dig 256) : Prop :=
  (TypedOracleCompiler.Run.PQ.rootsD o.rounds.toList)[n]? = some c

/-- The rounds' trees have their forms. -/
theorem forms_on (D : XD) : FormsOn (FmOf D) 0 D.ds :=
  formsOn_all (allT D.ds) D.ds 0 fun k s hk => by rwa [Nat.zero_add]

/-! ## Of the description -/

/-- An opening of a tree of the chain's own has the number of its tree, and is no stored table's. -/
theorem own_of_roundsOk (P : Fmt.Plan) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : ℕ), Fmt.roundsOk P nr ft after sent rs = true →
      ∀ r ∈ rs, ∀ x ∈ r.opens, ∀ n, x.2 = .own n → x.1.tree = ft + n ∧ x.1.stored = false
  | [], _, _, _, r, hr, _, _, _, _ => absurd hr List.not_mem_nil
  | r0 :: rs, after, sent, h, r, hr, x, hx, n, hn => by
    unfold Fmt.roundsOk at h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    rcases List.mem_cons.1 hr with rfl | hr
    · unfold Fmt.Round.ok at h1
      have h3 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 h1).2 x hx
      rw [hn] at h3
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at h3
      exact ⟨h3.2.1.1.2, h3.2.1.2⟩
    · exact own_of_roundsOk P nr ft rs _ _ h2 r hr x hx n hn

/-- The same from the format's conditions on a description. -/
theorem own_of_ok (S : Fmt.Spec) (h : S.ok = true) :
    ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∀ n, x.2 = .own n →
      x.1.tree = S.firstTree + n ∧ x.1.stored = false := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true] at h
  exact own_of_roundsOk _ _ _ _ _ _ h.1.1.2

/-- The forms of the rounds' trees, by number. -/
theorem allT_rdsFrom (S : Fmt.Spec) :
    ∀ (rs : List Fmt.Round) (sent k : ℕ) (s : Fmt.Shape),
      (allT (TypedOracleCompiler.Run.PQ.rdsFrom S sent rs))[k]? = some s →
      s = (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k))
  | [], _, _, _, h => by simp [TypedOracleCompiler.Run.PQ.rdsFrom, allT] at h
  | r :: rs, sent, k, s, h => by
    have e : allT (TypedOracleCompiler.Run.PQ.rdsFrom S sent (r :: rs)) =
        ((List.range r.entry.roots).map fun k =>
          (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k))) ++
        allT (TypedOracleCompiler.Run.PQ.rdsFrom S (sent + r.entry.roots) rs) := rfl
    rw [e] at h
    by_cases hk : k < r.entry.roots
    · rw [List.getElem?_append_left (by simpa using hk), List.getElem?_map,
        List.getElem?_range hk] at h
      exact (Option.some.inj h).symm
    · rw [List.getElem?_append_right (by simpa using hk)] at h
      simp only [List.length_map, List.length_range] at h
      have := allT_rdsFrom S rs _ _ s h
      rwa [show sent + r.entry.roots + (k - r.entry.roots) = sent + k by omega] at this

/-- What the search for the opening of own tree n finds. -/
theorem find_own (S : Fmt.Spec) {n : ℕ} {y : Fmt.Shape × Fmt.Src}
    (hf : ((allOpens S).find? fun o => ownNo o == some n) = some y) :
    ∃ r ∈ S.rounds, y ∈ r.opens ∧ y.2 = .own n := by
  have hy := List.find?_some hf
  obtain ⟨r, hr, hy'⟩ := List.mem_flatMap.1 (List.mem_of_find?_eq_some hf)
  refine ⟨r, hr, hy', ?_⟩
  unfold ownNo at hy
  cases e : y.2 with
  | own m =>
    rw [e] at hy
    simp only [beq_iff_eq, Option.some.injEq] at hy
    rw [hy]
  | given a b =>
    rw [e] at hy
    simp at hy

/-- The tree that stands for own tree n has the number of that tree. -/
theorem tree_at (S : Fmt.Spec) (h : S.ok = true) (n : ℕ) :
    ((shapeOfOwn S n).getD (bareShape S.firstTree n)).tree = S.firstTree + n := by
  cases hs : shapeOfOwn S n with
  | none => rfl
  | some sh =>
    unfold shapeOfOwn at hs
    obtain ⟨y, hf, rfl⟩ := Option.map_eq_some_iff.1 hs
    obtain ⟨r, hr, hy, hn⟩ := find_own S hf
    exact (own_of_ok S h r hr y hy n hn).1

/-- An opening of a tree of the chain's own stands in the description's list of such trees. -/
theorem mem_ownShapes (S : Fmt.Spec) {r : Fmt.Round} (hr : r ∈ S.rounds)
    {x : Fmt.Shape × Fmt.Src} (hx : x ∈ r.opens) {n : ℕ} (hn : x.2 = .own n) :
    (n, x.1) ∈ S.ownShapes := by
  unfold Fmt.Spec.ownShapes
  exact List.mem_flatMap.2 ⟨r, hr, List.mem_filterMap.2 ⟨x, hx, by rw [hn]⟩⟩

/-- Two openings of one tree of the chain's own have one form. -/
theorem shape_unique (S : Fmt.Spec) (h : S.ok = true) {r r' : Fmt.Round} (hr : r ∈ S.rounds)
    (hr' : r' ∈ S.rounds) {x x' : Fmt.Shape × Fmt.Src} (hx : x ∈ r.opens) (hx' : x' ∈ r'.opens)
    {n : ℕ} (hn : x.2 = .own n) (hn' : x'.2 = .own n) : x.1 = x'.1 := by
  have hall : (S.ownShapes.all fun x => S.shapeOf x.1 == some x.2) = true := by
    unfold Fmt.Spec.ok at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1.2
  have a := beq_iff_eq.1 (List.all_eq_true.1 hall _ (mem_ownShapes S hr hx hn))
  have b := beq_iff_eq.1 (List.all_eq_true.1 hall _ (mem_ownShapes S hr' hx' hn'))
  exact Option.some.inj (a.symm.trans b)

/-- The form under which own tree n is opened. -/
theorem shapeOfOwn_eq (S : Fmt.Spec) (h : S.ok = true) {r : Fmt.Round} (hr : r ∈ S.rounds)
    {x : Fmt.Shape × Fmt.Src} (hx : x ∈ r.opens) {n : ℕ} (hn : x.2 = .own n) :
    shapeOfOwn S n = some x.1 := by
  have hm : x ∈ allOpens S := List.mem_flatMap.2 ⟨r, hr, hx⟩
  have hp : (ownNo x == some n) = true := by
    unfold ownNo
    rw [hn]
    exact beq_self_eq_true _
  unfold shapeOfOwn
  cases hf : (allOpens S).find? fun o => ownNo o == some n with
  | none => exact absurd hp (by simpa using List.find?_eq_none.1 hf x hm)
  | some y =>
    obtain ⟨r', hr', hy, hyn⟩ := find_own S hf
    show some y.1 = some x.1
    rw [shape_unique S h hr' hr hy hx hyn hn]

/-- A form under `FmOf` with the number of an opened tree of the chain's own is that tree's, at
that tree's place in the order of sending. -/
theorem form_of_own (D : XD) (hok : D.base.ok = true) {r : Fmt.Round} (hr : r ∈ D.base.rounds)
    {x : Fmt.Shape × Fmt.Src} (hx : x ∈ r.opens) {m : ℕ} (hm : x.2 = .own m) (n : ℕ)
    (s : Fmt.Shape) (hF : FmOf D n s) (ht : s.tree = x.1.tree) : n = m ∧ s = x.1 := by
  have e := allT_rdsFrom D.base D.base.rounds 0 n s hF
  rw [Nat.zero_add] at e
  have t1 : s.tree = D.base.firstTree + n := by
    rw [e]
    exact tree_at _ hok n
  have t2 := (own_of_ok _ hok r hr x hx m hm).1
  obtain rfl : n = m := by omega
  exact ⟨rfl, by rw [e, shapeOfOwn_eq _ hok hr hx hm]; rfl⟩

/-! ## Of what was read -/

/-- The root to which an opened tree must lead, the roots sent being a list. -/
def rootAtL (L : List ByteArray) : Fmt.Src → Option ByteArray
  | .own n => L[n]?
  | .given r _ => some r

/-- It is the reader's `rootAt` at the list of an array. -/
theorem rootAtL_of (roots : Array ByteArray) (z : Fmt.Src) :
    rootAt roots z = rootAtL roots.toList z := by
  cases z <;> simp [rootAt, rootAtL]

/-- More roots behind the list change nothing. -/
theorem rootAtL_mono {L : List ByteArray} (M : List ByteArray) {z : Fmt.Src} {r : ByteArray}
    (h : rootAtL L z = some r) : rootAtL (L ++ M) z = some r := by
  cases z with
  | own n =>
    show (L ++ M)[n]? = some r
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
    exact h
  | given a b => exact h

/-- What holds along two lists holds at each place. -/
theorem forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ (k : ℕ) (y : β), l'[k]? = some y →
      ∃ x, l[k]? = some x ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons (a := a) r _, 0, y, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨a, rfl, r⟩
  | _, _, .cons _ rs, k + 1, y, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact forall₂_get rs k y h

/-- An opening of the typing's list, by its round's number and its own. -/
theorem opsOf_at {c : ℕ} {o : Fmt.ChainOut} {op : OpAt} (hop : op ∈ opsOf c o) :
    ∃ ro, o.rounds.toList[op.round]? = some ro ∧ ro.opens[op.k]? = some (op.sh, op.xs, op.out) := by
  unfold opsOf at hop
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.1 hop
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  exact ⟨r.1, List.mem_zipIdx_iff_getElem?.1 hr, List.mem_zipIdx_iff_getElem?.1 hx⟩

/-- Round by round, by the round's number: each stored table's opening has its facts; each
opening of another tree has the description's form and leads to its root among all roots sent. -/
theorem trace_all (h : HId) (cfg st : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored))
      (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut))) (c : Fmt.Chain)
      (roots : Array ByteArray),
      TraceL h P (rs.map (·.1)) (rc.map fun p => _root_.Run.PQ.stripR p.1) c roots →
      List.Forall₂ (fun x p => p.1.drawn.poss.length = x.1.entry.poss ∧
        List.Forall₂ (OwnRead h cfg P run b) x.1.opens p.1.opens ∧
        List.Forall₂ (fun t y => StoredFact h cfg st p.1.drawn.poss t y ∧
          StoredReadAt h cfg P b t y) x.2 p.2) rs rc →
      ∀ (k : ℕ) (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)), rc[k]? = some p →
        ∃ x, rs[k]? = some x ∧
          List.Forall₂ (fun t y => StoredFact h cfg st p.1.drawn.poss t y) x.2 p.2 ∧
          List.Forall₂ (fun z y => y.1 = z.1 ∧
            rootAtL (roots.toList ++ rc.flatMap fun q => Fmt.rootsOf q.1.vals) z.2 =
              some y.2.2.root) x.1.opens p.1.opens
  | [], [], _, _, _, _, k, p, hk => by simp at hk
  | [], _ :: _, _, _, _, f, _, _, _ => by cases f
  | _ :: _, [], _, _, _, f, _, _, _ => by cases f
  | x :: rs, q :: rc, c, roots, t, f, k, p, hk => by
    obtain ⟨-, -, -, -, t5, t6⟩ := t
    cases f with
    | cons f1 f2 =>
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        refine ⟨x, rfl, f1.2.2.imp fun _ _ w => w.1, ?_⟩
        have r5 := openFacts_roots P _ _ _ _ t5
        have s5 : List.Forall₂ (fun z y => y.1 = z.1) x.1.opens q.1.opens :=
          (List.forall₂_map_right_iff.1 t5).imp fun _ _ w => w.sh
        refine (forall₂_and s5 r5).imp fun z y w => ⟨w.1, ?_⟩
        have w2 := w.2
        rw [rootAtL_of, Array.toList_append] at w2
        rw [List.flatMap_cons, ← List.append_assoc]
        exact rootAtL_mono _ w2
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨x', h1, h2, h3⟩ := trace_all h cfg st P run b rs rc _ _ t6 f2 k p hk
        refine ⟨x', by simpa using h1, h2, h3.imp fun z y w => ⟨w.1, ?_⟩⟩
        have w2 := w.2
        rw [Array.toList_append] at w2
        rw [List.flatMap_cons, ← List.append_assoc]
        exact w2

/-- As many roots were read as a round has trees: that looks at a round's values alone. -/
theorem rootsFit_vals : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (l l' : List Fmt.RoundOut),
    List.Forall₂ (fun a a' => a.vals = a'.vals) l l' → TypedOracleCompiler.Run.PQ.RootsFitR ds l →
      TypedOracleCompiler.Run.PQ.RootsFitR ds l'
  | [], _, _, .nil, _ => trivial
  | [], _, _, .cons _ _, h => h.elim
  | _ :: _, _, _, .nil, h => h.elim
  | _ :: ds, _, _, .cons e es, h => ⟨by rw [← e]; exact h.1, rootsFit_vals ds _ _ es h.2⟩

section
variable {h : HId} {S : Fmt.SpecX} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut}
  {j : ℕ} (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))

include e in
/-- Every opening of the file, by its place in the file: the k-th opening of a round is of the
k-th stored table that the description lists for that round, has its form, and its root is the one
in the statement's item; or it is of a tree that the round's description opens, has its form, and
leads to its root among all roots that the chain has sent. -/
theorem opens_at : ∀ op ∈ opsOf 1 o,
    (∃ ts t, S.stored[op.round]? = some ts ∧ ts[op.k]? = some t ∧ op.sh = t.sh ∧
      Fmt.itemRoot S.base.statement t.item = some op.out.root) ∨
    ∃ r ∈ S.base.rounds, ∃ x ∈ r.opens, op.sh = x.1 ∧
      rootAtL (o.rounds.toList.flatMap fun q => Fmt.rootsOf q.vals) x.2 = some op.out.root := by
  intro op hop
  obtain ⟨hok, -, rc, g1, g2, -, g5⟩ := readX_trace h S seen b i o j e
  have hlen : S.stored.length = S.base.rounds.length := by
    have := hok
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have hz : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (by omega)
  obtain ⟨ro, h1, h2⟩ := opsOf_at hop
  rw [g1, List.getElem?_map] at h1
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨x, hx, hs, ho⟩ := trace_all h _ _ _ _ b (S.base.rounds.zip S.stored) rc _ #[]
    (by rw [hz]; exact g2) g5 _ p hp
  have hroots : (#[] : Array ByteArray).toList ++ (rc.flatMap fun q => Fmt.rootsOf q.1.vals) =
      o.rounds.toList.flatMap fun q => Fmt.rootsOf q.vals := by
    rw [g1, List.flatMap_map]
    rfl
  obtain ⟨hx1, hx2⟩ := List.getElem?_zip_eq_some.1 hx
  have h2' : (p.2 ++ p.1.opens)[op.k]? = some (op.sh, op.xs, op.out) := h2
  by_cases hk : op.k < p.2.length
  · rw [List.getElem?_append_left hk] at h2'
    obtain ⟨t, ht, hf⟩ := forall₂_get hs _ _ h2'
    exact Or.inl ⟨x.2, t, hx2, ht, hf.sh, hf.root⟩
  · rw [List.getElem?_append_right (by omega)] at h2'
    obtain ⟨z, hz', hf⟩ := forall₂_get ho _ _ h2'
    exact Or.inr ⟨x.1, List.mem_of_getElem? hx1, z, List.mem_of_getElem? hz', hf.1,
      by rw [← hroots]; exact hf.2⟩

include e in
/-- As many roots were read as each round has trees. ds: rounds' data that fit the description's
rounds. -/
theorem rootsFit_of_read (ds : List TypedOracleCompiler.Run.PQ.RD) (hfit : TypedOracleCompiler.Run.PQ.FitL ds S.base.rounds) :
    TypedOracleCompiler.Run.PQ.RootsFitR ds o.rounds.toList := by
  obtain ⟨-, -, rc, g1, g2, -, -⟩ := readX_trace h S seen b i o j e
  have f := TypedOracleCompiler.Run.PQ.rootsFit_of_trace h S.base.plan _ _ _ _ _ hfit g2
  rw [g1]
  exact rootsFit_vals ds (rc.map fun p => _root_.Run.PQ.stripR p.1) (rc.map roundWithStoredOpenings)
    (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun _ _ => rfl))) f

end

/-! ## At a description with stored tables -/

/-- The description that the reader takes: D's, with the statement st. -/
abbrev specOf (D : XD) (st : ByteArray) : Fmt.SpecX := ⟨{ D.base with statement := st }, D.stored⟩

/-- The road's limits hold the format's conditions. -/
theorem base_ok {S₀ : Fmt.Spec} (hok : TypedOracleCompiler.Run.PQ.ok S₀ = true) : S₀.ok = true := by
  unfold TypedOracleCompiler.Run.PQ.ok at hok
  simp only [Bool.and_eq_true] at hok
  exact hok.1.1.1.1

section
variable {h : HId} (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) {st : ByteArray} {seen : Fmt.Seen}
  {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut} {j : ℕ}
  (e : Fmt.readChainX (m := Id) h (specOf D st) seen b i = some (o, j))

include hok e in
/-- The roots that the chain's record holds, round by round, stand under `RtOf`. -/
theorem rts_on : RtsL (RtOf o) D.C 0 D.ds (TypedOracleCompiler.Run.PQ.rtSL D.C D.ds o.rounds.toList) :=
  TypedOracleCompiler.Run.PQ.rtsL_rtSL (TypedOracleCompiler.Run.PQ.rootsD o.rounds.toList) D.C [] D.ds o.rounds.toList 0
    (rootsFit_of_read e D.ds (TypedOracleCompiler.Run.PQ.fit_rds D.base hok))
    (by rw [List.drop_zero, List.append_nil])

include hok e in
/-- An opening of a tree of the chain's own: at some number m its form stands under `FmOf` and
the root in which its walk ended under `RtOf`; and whatever stands under `FmOf` with its tree's
number is that form, at m. -/
theorem own_facts : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∃ m, FmOf D m op.sh ∧ RtOf o m (bytesToDig op.out.root) ∧
      ∀ n s, FmOf D n s → s.tree = op.sh.tree → n = m ∧ s = op.sh := by
  intro op hop
  obtain ⟨hop1, hst⟩ := List.mem_filter.1 hop
  have hS : (specOf D st).ok = true := (readX_trace h _ seen b i o j e).1
  have hb := base_ok hok
  rcases opens_at e op hop1 with ⟨ts, t, hts, ht, hsh, -⟩ | ⟨r, hr, x, hx, hsh, hroot⟩
  · have := (stored_flags _ hS).1 t
      (List.mem_flatten.2 ⟨ts, List.mem_of_getElem? hts, List.mem_of_getElem? ht⟩)
    rw [hsh, this] at hst
    cases hst
  · obtain ⟨m, hm⟩ := opens_own hok r hr x hx
    rw [hm] at hroot
    have hroot' : (o.rounds.toList.flatMap fun q => Fmt.rootsOf q.vals)[m]? = some op.out.root :=
      hroot
    have hR : RtOf o m (bytesToDig op.out.root) := by
      unfold RtOf TypedOracleCompiler.Run.PQ.rootsD
      rw [List.getElem?_map, hroot']
      rfl
    have hlen : (TypedOracleCompiler.Run.PQ.rootsD o.rounds.toList).length = (allT D.ds).length := by
      rw [TypedOracleCompiler.Run.PQ.length_rootsD _ _ (rootsFit_of_read e D.ds (TypedOracleCompiler.Run.PQ.fit_rds D.base hok)),
        length_allT]
    have hlt : m < (allT D.ds).length := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.1 hR).1
    have hs : FmOf D m (allT D.ds)[m] := List.getElem?_eq_getElem hlt
    have e1 := allT_rdsFrom D.base D.base.rounds 0 m _ hs
    rw [Nat.zero_add, shapeOfOwn_eq _ hb hr hx hm] at e1
    have e2 : (allT D.ds)[m] = x.1 := e1
    rw [e2, ← hsh] at hs
    refine ⟨m, hs, hR, fun n s hF ht => ?_⟩
    rw [hsh] at ht ⊢
    exact form_of_own D hb hr hx hm n s hF ht

include hok e in
/-- The first side premise of `ownOkE_of_read` (OnBytes/TypedOracleCompiler/Slice/EntryWhole.lean). -/
theorem own_form : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∀ n s, FmOf D n s → s.tree = op.sh.tree → s = op.sh := fun op hop n s hF ht => by
  obtain ⟨_, -, -, hu⟩ := own_facts D hok e op hop
  exact (hu n s hF ht).2

include hok e in
/-- The second. -/
theorem own_root : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∀ n s c, FmOf D n s → s.tree = op.sh.tree → RtOf o n c → c = bytesToDig op.out.root :=
  fun op hop n s c hF ht hR => by
    obtain ⟨m, -, hm, hu⟩ := own_facts D hok e op hop
    obtain rfl := (hu n s hF ht).1
    exact Option.some.inj (hR.symm.trans hm)

include hok e in
/-- The form of an opening of a tree of the chain's own is among the trees of one of D's rounds. -/
theorem own_tree : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∃ d ∈ D.ds, op.sh ∈ d.trees := fun op hop => by
  obtain ⟨m, hm, -, -⟩ := own_facts D hok e op hop
  exact List.mem_flatMap.1 (List.mem_of_getElem? hm)

include hok e in
/-- An opening of a stored table: the outer root of its table is the root in which its walk
ended (the premise `hr` of `stoOkE_of_read`). r0, r1: the two roots that the statement's items
hold. -/
theorem sto_root (r0 r1 : ByteArray)
    (hit : ∀ t ∈ D.stored.flatten,
      Fmt.itemRoot st t.item = some (if t.item == 1 then r1 else r0)) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      [bytesToDig r0, bytesToDig r1].getD (whichOf D op) default = bytesToDig op.out.root := by
  intro op hop
  obtain ⟨hop1, hst⟩ := List.mem_filter.1 hop
  have hS : (specOf D st).ok = true := (readX_trace h _ seen b i o j e).1
  rcases opens_at e op hop1 with ⟨ts, t, hts, ht, -, hroot⟩ | ⟨r, hr, x, hx, hsh, -⟩
  · have hts' : D.stored[op.round]? = some ts := hts
    have hroot' : Fmt.itemRoot st t.item = some op.out.root := hroot
    have hi := hit t (List.mem_flatten.2 ⟨ts, List.mem_of_getElem? hts', List.mem_of_getElem? ht⟩)
    have er : op.out.root = if t.item == 1 then r1 else r0 :=
      Option.some.inj (hroot'.symm.trans hi)
    have ew : whichOf D op = if t.item == 1 then 1 else 0 := by
      unfold whichOf
      rw [hts', Option.bind_some, ht]
    rw [ew, er]
    cases t.item == 1 <;> rfl
  · have := (stored_flags _ hS).2 r hr x hx (opens_own hok r hr x hx)
    rw [hsh, this] at hst
    cases hst

end

/-! ## At the entry's description -/

section
variable (G : EntryGround) (c : ByteArray) (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
  {h : HId} {st : ByteArray} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut} {j : ℕ}
  (e : Fmt.readChainX (m := Id) h
    (TypedOracleCompiler.Run.PQ.withStatement (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) st)
    seen b i = some (o, j))

include hok e in
/-- `rts_on` at the entry's description. -/
theorem rts_on_at : RtsL (RtOf o) (entryXD G c).C 0 (entryXD G c).ds
    (TypedOracleCompiler.Run.PQ.rtSL (entryXD G c).C (entryXD G c).ds o.rounds.toList) :=
  rts_on (entryXD G c) hok (st := st) e

include hok e in
/-- `own_form` at the entry's description. -/
theorem own_form_at : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∀ n s, FmOf (entryXD G c) n s → s.tree = op.sh.tree → s = op.sh :=
  own_form (entryXD G c) hok (st := st) e

include hok e in
/-- `own_root` at the entry's description. -/
theorem own_root_at : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∀ n s d, FmOf (entryXD G c) n s → s.tree = op.sh.tree → RtOf o n d →
      d = bytesToDig op.out.root :=
  own_root (entryXD G c) hok (st := st) e

include hok e in
/-- `own_tree` at the entry's description. -/
theorem own_tree_at : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
    ∃ d ∈ (entryXD G c).ds, op.sh ∈ d.trees :=
  own_tree (entryXD G c) hok (st := st) e

include hok e in
/-- `sto_root` at the entry's description. -/
theorem sto_root_at (r0 r1 : ByteArray)
    (hit : ∀ t ∈ (entryXD G c).stored.flatten,
      Fmt.itemRoot st t.item = some (if t.item == 1 then r1 else r0)) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored),
      [bytesToDig r0, bytesToDig r1].getD (whichOf (entryXD G c) op) default =
        bytesToDig op.out.root :=
  sto_root (entryXD G c) hok (st := st) e r0 r1 hit

end

end OnBytes.K.Left
