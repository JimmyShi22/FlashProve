-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/NamedOfBuilt.lean: WHAT THE MAKING OF THE LINKS SAYS OF A BUILT LINK's
LIST OF NAMES: a law of a text that the verifier runs: a return of `buildLinksH`
(OnBytes/Model/StagesLinks.lean: the public tests on the links of a request's chain, on the first
chain's parameters as read back). Definitions, theorems and their proofs. No text already in the library turns.

Why. Two named tests on the three public files that stand in front of the top theorem (`namedThere`,
`seatsNamedC`) ask that the array which a label names lies in the layout, with its sizes, in an
oracle message that is a member of the reader's own group. The maker asks the like, at its own
letters: a link's arrays by their number in the link's ledger, and `LinkH.arrayOf`: for each the
link
that committed to it and its name there.

  `NamedHeld p l X τ born name`: born ≤ l; the layout of link born has an array A of that name; it
    lies in a message m of link born's; m is kept for at least l - born links; where born < l, m is
    of moment 0; where born = l, A has the rows and columns of X's planned array number τ.
  `named_of_buildLinks`: **buildLinksH links0 NGr p4 wsLay p = .ok B ⊢ at every entry (born, name)
  of
    every built link's arrayOf: NamedHeld.** General in the links that the maker is handed.
  `named_of_made`: **the same where the proof file's public part Z is made**
    (ProofFile.pureRoad.pub o pol lay KL = .ok Z), at Z.p.built.links and Z.first.
  How: `own` lays (l, name) and declares the array with the planned rows and columns; `foreign`
    refuses unless born < l, lays (born, name) and raises the owner's declared life to l - born;
    `declareLinks` refuses a list with an empty name; `heldAgainst` holds every declared array
    against the layout and the shape (`arrayHeld`). The loops by `forIn_done`
    (OnBytes/Tie/Pv/Lookup/Ends/FoDeclMoments.lean).
Limits. WHICH array of a link's ledger bears WHICH name is not said. At an entry of another link's
(born < l) no sizes are said. That two arrays of one link bear different names is not said. Nothing
on soundness.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoDeclMoments
import OnBytes.Tie.Pv.Lookup.Ends.FoBuiltCut
import Johnson.Desc.LaidAt
import Johnson.Desc.ProofFile.Law.PlainIsPlanned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done getD_set)

/-- **What the making of the links says of entry τ of a built link's list of names.** -/
def NamedHeld (p : Params.First) (l : Nat) (X : LinkH) (τ born : Nat) (name : String) : Prop :=
  born ≤ l ∧ ∃ (A : ReqArray) (L : ReqLink) (m : ReqMessage),
    VerifiableInference.Desc.arrayOf p.layout born name = some A ∧
    p.shape.link[born]? = some L ∧ L.messages[A.message]? = some m ∧
    l - born ≤ m.life ∧ (born < l → m.moment = 0) ∧
    (born = l → ∃ tr : HTree, X.Fp.trees[τ]? = some tr ∧ A.sizeI = tr.R ∧ A.sizeC = tr.K)

/-! ## 1 On the declared moments -/

abbrev Moments : Type := Array (Array FrameArray)

/-- Some moment declares an array of this name, rows and columns. -/
def HasSz (M : Moments) (name : String) (R K : Nat) : Prop :=
  ∃ t, ∃ a ∈ (M.getD t #[]).toList, a.name = name ∧ a.rows = R ∧ a.columns = K

/-- The first moment declares an array of this name that is kept for at least n links. -/
def HasLife (M : Moments) (name : String) (n : Nat) : Prop :=
  ∃ a ∈ (M.getD 0 #[]).toList, a.name = name ∧ n ≤ a.life

/-- Every declared array of M is declared at the same moment of M'. -/
def Sub (M M' : Moments) : Prop := ∀ t a, a ∈ (M.getD t #[]).toList → a ∈ (M'.getD t #[]).toList

theorem hasSz_sub {M M' : Moments} (h : Sub M M') {name : String} {R K : Nat}
    (x : HasSz M name R K) : HasSz M' name R K := by
  obtain ⟨t, a, ha, e⟩ := x
  exact ⟨t, a, h t a ha, e⟩

theorem sub_modify (M : Moments) (i : Nat) (b : FrameArray) : Sub M (M.modify i (·.push b)) := by
  intro t a ha
  rw [Fo.getD_modify]
  split
  · rw [Array.toList_push]
    exact List.mem_append_left _ ha
  · exact ha

theorem sub_push (M : Moments) : Sub M (M.push #[]) := by
  intro t a ha
  by_cases ht : t < M.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt ht, ← Array.getElem?_eq_getElem ht,
      ← Array.getD_eq_getD_getElem?]
    exact ha
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at ha
    exact nomatch ha

/-! ## 2 The link's own arrays -/

theorem get_set {α : Type} (arr : Array α) (i j : Nat) (v : α) (hi : i < arr.size) :
    (arr.setIfInBounds i v)[j]? = if i = j then some v else arr[j]? := by
  rw [Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h
    simp [hi]
  · simp [h]

theorem namesH_cut {arrayOf arrayOf' : Array (Nat × String)} {tree born : Nat} {name : String}
    (h : namesH arrayOf tree born name = .ok arrayOf') :
    arrayOf' = arrayOf.setIfInBounds tree (born, name) ∧ tree < arrayOf.size ∧
      ∀ x, arrayOf[tree]? = some x → x.2.isEmpty = true := by
  unfold namesH at h
  split at h
  · rename_i a ha
    split at h
    · rename_i he
      refine ⟨(Except.ok.inj h).symm, (Array.getElem?_eq_some_iff.1 ha).1, fun x hx => ?_⟩
      obtain rfl : a = x := Option.some.inj (ha.symm.trans hx)
      exact he
    · cases h
  · cases h

theorem own_cut2 {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') :
    ∃ tr b, X.Fp.trees[tree]? = some tr ∧ b.name = name ∧ b.rows = tr.R ∧ b.columns = tr.K ∧
      d'.arrayOf = d.arrayOf.setIfInBounds tree (l, name) ∧ tree < d.arrayOf.size ∧
      d'.moment = d.moment.modify (d.moment.size - 1) (·.push b) := by
  unfold own at h
  obtain ⟨arrayOf, hn, h⟩ := exc_bind h
  obtain ⟨e, hlt, _⟩ := namesH_cut hn
  split at h
  · rename_i t n ht _
    obtain rfl := Except.ok.inj h
    exact ⟨t, _, ht, rfl, rfl, rfl, e, hlt, rfl⟩
  · cases h

/-- While a link's own arrays are declared: there is a moment; every entry with a name is the
link's own, and some moment declares it with the planned rows and columns. -/
def OwnOK (X : LinkH) (l : Nat) (d : Declaring) : Prop :=
  1 ≤ d.moment.size ∧ ∀ (τ born : Nat) (name : String), d.arrayOf[τ]? = some (born, name) →
    name.isEmpty = false →
    born = l ∧ ∃ tr : HTree, X.Fp.trees[τ]? = some tr ∧ HasSz d.moment name tr.R tr.K

theorem own_ok {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (I : OwnOK X l d) (h : own X l d tree name = .ok d') : OwnOK X l d' := by
  obtain ⟨tr, b, htr, b1, b2, b3, ea, hlt, em⟩ := own_cut2 h
  refine ⟨by rw [em, Array.size_modify]; exact I.1, fun τ born nm hx hne => ?_⟩
  rw [ea, get_set _ _ _ _ hlt] at hx
  split at hx
  · rename_i hτ
    subst hτ
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hx)
    refine ⟨rfl, tr, htr, d.moment.size - 1, b, ?_, b1, b2, b3⟩
    rw [em, Fo.getD_modify, if_pos ⟨rfl, by have := I.1; omega⟩, Array.toList_push]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  · obtain ⟨e, tr', h1, h2⟩ := I.2 τ born nm hx hne
    exact ⟨e, tr', h1, by rw [em]; exact hasSz_sub (sub_modify _ _ _) h2⟩

theorem next_ok {X : LinkH} {l : Nat} {d : Declaring} (I : OwnOK X l d) :
    OwnOK X l d.nextMoment := by
  refine ⟨by show 1 ≤ (d.moment.push #[]).size; rw [Array.size_push]; omega,
    fun τ born nm hx hne => ?_⟩
  obtain ⟨e, tr', h1, h2⟩ := I.2 τ born nm hx hne
  exact ⟨e, tr', h1, hasSz_sub (sub_push _) h2⟩

theorem declareOwn_ok {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    OwnOK X l d := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have I0 : OwnOK X l { arrayOf := Array.replicate X.Tp.nt.size (noLink, ""), moment := #[#[]] } :=
    ⟨Nat.le_refl 1, fun τ born nm hx hne => by
      obtain ⟨_, e⟩ := Array.getElem?_eq_some_iff.1 hx
      rw [Array.getElem_replicate] at e
      obtain ⟨_, rfl⟩ := Prod.mk.inj e
      exact absurd hne (by decide)⟩
  have stepOwn : ∀ (done : List (Nat × Nat)) (a : Nat × Nat) (s : Declaring)
      (s' : ForInStep Declaring), OwnOK X l s →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ OwnOK X l t := by
    intro _ a s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    exact ⟨r, (Except.ok.inj e).symm, own_ok I e1⟩
  have I1 : OwnOK X l d1 := forIn_done _ (fun _ s => OwnOK X l s) stepOwn _ [] _ _ I0 h1
  have I2 : OwnOK X l d2 := forIn_done _ (fun _ s => OwnOK X l s) stepOwn _ [] _ _ I1 h2
  have I3 : OwnOK X l d3 := forIn_done _
    (fun (_ : List (Option Nat × Nat)) s => OwnOK X l s)
    (fun done a s s' I e => by
      split at e
      · obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨r, (Except.ok.inj e).symm, own_ok (next_ok I) e1⟩
      · obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨s, (Except.ok.inj e).symm, I⟩)
    _ [] _ _ I2 h3
  exact own_ok (own_ok (next_ok I3) h4) h5

/-! ## 3 Another link's arrays -/

theorem mem_lt {M : Moments} {t : Nat} {a : FrameArray} (h : a ∈ (M.getD t #[]).toList) :
    t < M.size := by
  by_contra hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)] at h
  exact nomatch h

/-- What `keptUpTo` does to one declared array. -/
def raise (name : String) (life : Nat) (a : FrameArray) : FrameArray :=
  if a.name == name then { a with life := max a.life life } else a

theorem raise_says (name : String) (life : Nat) (a : FrameArray) :
    (raise name life a).name = a.name ∧ (raise name life a).rows = a.rows ∧
      (raise name life a).columns = a.columns ∧ a.life ≤ (raise name life a).life ∧
      (a.name = name → life ≤ (raise name life a).life) := by
  unfold raise
  split
  · exact ⟨rfl, rfl, rfl, Nat.le_max_left _ _, fun _ => Nat.le_max_right _ _⟩
  · rename_i hn
    exact ⟨rfl, rfl, rfl, Nat.le_refl _, fun e => absurd (by simp [e]) hn⟩

theorem kept_cut {D D' : FrameLink} {name : String} {life : Nat}
    (h : keptUpTo D name life = .ok D') :
    (∀ nm R K, HasSz D.moment nm R K → HasSz D'.moment nm R K) ∧
      (∀ nm n, HasLife D.moment nm n → HasLife D'.moment nm n) ∧ HasLife D'.moment name life := by
  unfold keptUpTo at h
  dsimp only at h
  split at h
  · rename_i hany
    obtain rfl := Except.ok.inj h
    have e0 : ∀ a, a ∈ (D.moment.getD 0 #[]).toList → raise name life a ∈
        ((D.moment.setIfInBounds 0 ((D.moment.getD 0 #[]).map (raise name life))).getD 0
          #[]).toList := by
      intro a ha
      rw [getD_set, if_pos ⟨rfl, mem_lt ha⟩, Array.toList_map]
      exact List.mem_map_of_mem ha
    have et : ∀ t, t ≠ 0 →
        (D.moment.setIfInBounds 0 ((D.moment.getD 0 #[]).map (raise name life))).getD t #[] =
          D.moment.getD t #[] := by
      intro t ht
      rw [getD_set, if_neg (by omega)]
    refine ⟨fun nm R K x => ?_, fun nm n x => ?_, ?_⟩
    · obtain ⟨t, a, ha, a1, a2, a3⟩ := x
      obtain ⟨r1, r2, r3, _, _⟩ := raise_says name life a
      by_cases ht : t = 0
      · subst ht
        exact ⟨0, _, e0 a ha, r1.trans a1, r2.trans a2, r3.trans a3⟩
      · refine ⟨t, a, ?_, a1, a2, a3⟩
        show a ∈ ((D.moment.setIfInBounds 0 ((D.moment.getD 0 #[]).map (raise name life))).getD t
          #[]).toList
        rw [et t ht]
        exact ha
    · obtain ⟨a, ha, a1, a2⟩ := x
      obtain ⟨r1, _, _, r4, _⟩ := raise_says name life a
      exact ⟨_, e0 a ha, r1.trans a1, Nat.le_trans a2 r4⟩
    · rw [← Array.any_toList, List.any_eq_true] at hany
      obtain ⟨a, ha, hn⟩ := hany
      obtain ⟨r1, _, _, _, r5⟩ := raise_says name life a
      have en : a.name = name := by simpa using hn
      exact ⟨_, e0 a ha, r1.trans en, r5 en⟩
  · cases h

theorem foreign_cut2 {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    ∃ born D D' name, born < l ∧ namesH s.1 tree born name = .ok s'.1 ∧ s.2[born]? = some D ∧
      keptUpTo D name (l - born) = .ok D' ∧ s'.2 = s.2.setIfInBounds born D' := by
  unfold foreign at h
  dsimp only at h
  split at h
  · have hg := exc_guard_not h
    replace h := exc_guard h
    split at h
    · split at h
      · replace h := exc_guard h
        split at h
        · split at h
          · split at h
            · replace h := exc_guard h
              obtain ⟨arrayOf, hn, h⟩ := exc_bind h
              split at h
              · rename_i D hD
                obtain ⟨D', hk, h⟩ := exc_bind h
                obtain rfl := Except.ok.inj h
                refine ⟨_, D, D', _, ?_, hn, hD, hk, rfl⟩
                simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_le, ge_iff_le] at hg
                exact hg.2
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- An entry of a link's list of names, held against the declarations. -/
def EntryOK (declared : Array FrameLink) (l : Nat) (X : LinkH) (τ born : Nat) (name : String) :
    Prop :=
  ∃ D, declared[born]? = some D ∧
    ((born = l ∧ ∃ tr : HTree, X.Fp.trees[τ]? = some tr ∧ HasSz D.moment name tr.R tr.K) ∨
      (born < l ∧ HasLife D.moment name (l - born)))

def AllOK (named : Array LinkH) (declared : Array FrameLink) : Prop :=
  ∀ (l : Nat) (X : LinkH) (τ born : Nat) (name : String), named[l]? = some X →
    X.arrayOf[τ]? = some (born, name) → EntryOK declared l X τ born name

theorem entry_set {declared : Array FrameLink} {l : Nat} {X : LinkH} {τ born : Nat}
    {name : String} (I : EntryOK declared l X τ born name) {b : Nat} {D0 D0' : FrameLink}
    {nm : String} {life : Nat} (h0 : declared[b]? = some D0)
    (hk : keptUpTo D0 nm life = .ok D0') :
    EntryOK (declared.setIfInBounds b D0') l X τ born name := by
  obtain ⟨D, hD, c⟩ := I
  obtain ⟨k1, k2, _⟩ := kept_cut hk
  by_cases hb : b = born
  · subst hb
    obtain rfl : D0 = D := Option.some.inj (h0.symm.trans hD)
    refine ⟨D0', by rw [get_set _ _ _ _ (Array.getElem?_eq_some_iff.1 h0).1, if_pos rfl], ?_⟩
    rcases c with ⟨e, tr, h1, h2⟩ | ⟨e, h2⟩
    · exact .inl ⟨e, tr, h1, k1 _ _ _ h2⟩
    · exact .inr ⟨e, k2 _ _ h2⟩
  · exact ⟨D, by
      rw [get_set _ _ _ _ (Array.getElem?_eq_some_iff.1 h0).1, if_neg hb]
      exact hD, c⟩

/-- While link l's reads of earlier links' arrays are declared. dm: the link's own moments. -/
def CurOK (X : LinkH) (l : Nat) (dm : Moments) (q : Array (Nat × String) × Array FrameLink) :
    Prop :=
  ∀ (τ born : Nat) (name : String), q.1[τ]? = some (born, name) → name.isEmpty = false →
    (born = l ∧ ∃ tr : HTree, X.Fp.trees[τ]? = some tr ∧ HasSz dm name tr.R tr.K) ∨
      (born < l ∧ ∃ D, q.2[born]? = some D ∧ HasLife D.moment name (l - born))

theorem foreign_ok {links named : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {dm : Moments} {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (I : s.2.size = l ∧ AllOK named s.2 ∧ CurOK X l dm s)
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    s'.2.size = l ∧ AllOK named s'.2 ∧ CurOK X l dm s' := by
  obtain ⟨born, D, D', name, hlt, hn, hD, hk, e⟩ := foreign_cut2 h
  obtain ⟨ea, hin, _⟩ := namesH_cut hn
  obtain ⟨_, k2, k3⟩ := kept_cut hk
  have hsz : born < s.2.size := (Array.getElem?_eq_some_iff.1 hD).1
  refine ⟨by rw [e, Array.size_setIfInBounds]; exact I.1,
    fun j Y τ b nm hY hx => by rw [e]; exact entry_set (I.2.1 j Y τ b nm hY hx) hD hk,
    fun τ b nm hx hne => ?_⟩
  rw [ea, get_set _ _ _ _ hin] at hx
  split at hx
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hx)
    exact .inr ⟨hlt, D', by rw [e, get_set _ _ _ _ hsz, if_pos rfl], k3⟩
  · rcases I.2.2 τ b nm hx hne with c | ⟨c, D1, h1, h2⟩
    · exact .inl c
    · refine .inr ⟨c, ?_⟩
      by_cases hb : born = b
      · subst hb
        obtain rfl : D = D1 := Option.some.inj (hD.symm.trans h1)
        exact ⟨D', by rw [e, get_set _ _ _ _ hsz, if_pos rfl], k2 _ _ h2⟩
      · exact ⟨D1, by rw [e, get_set _ _ _ _ hsz, if_neg hb]; exact h1, h2⟩

/-! ## 4 All links -/

theorem declareLinks_ok {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) :
    AllOK named declared := by
  unfold declareLinks at h
  dsimp only at h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain ⟨rfl, rfl⟩ : r.snd = named ∧ r.fst = declared :=
    ⟨congrArg Prod.fst (Except.ok.inj h), congrArg Prod.snd (Except.ok.inj h)⟩
  have key := forIn_done _
    (fun (done : List (LinkH × Nat)) (s : MProd (Array FrameLink) (Array LinkH)) =>
      (∀ (j : Nat) (x : LinkH × Nat), done[j]? = some x → x.2 = j) →
        s.fst.size = done.length ∧ s.snd.size = done.length ∧ AllOK s.snd s.fst)
    (fun done x s s' I e => by
      obtain ⟨d, hd, e⟩ := exc_bind e
      obtain ⟨s1, h1, e⟩ := exc_bind e
      have hne := exc_guard_not e
      replace e := exc_guard e
      obtain ⟨_, _, e⟩ := exc_bind e
      refine ⟨_, (Except.ok.inj e).symm, fun hidx => ?_⟩
      have hx2 : x.2 = done.length := hidx done.length x (by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl)
      obtain ⟨z1, z2, z3⟩ := I fun j y hy => hidx j y (by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hy).1]
        exact hy)
      have O := declareOwn_ok hd
      have J : s1.2.size = x.2 ∧ AllOK s.snd s1.2 ∧ CurOK x.1 x.2 d.moment s1 :=
        forIn_done _
          (fun (_ : List (Nat × PlaceF)) (q : Array (Nat × String) × Array FrameLink) =>
            q.2.size = x.2 ∧ AllOK s.snd q.2 ∧ CurOK x.1 x.2 d.moment q)
          (fun _ y q q' Iq eq => by
            obtain ⟨q1, e1, eq⟩ := exc_bind eq
            obtain ⟨_, _, eq⟩ := exc_bind eq
            exact ⟨q1, (Except.ok.inj eq).symm, foreign_ok Iq e1⟩)
          _ [] _ _
          ⟨by rw [hx2]; exact z1, z3, fun τ b nm hx hn => .inl (O.2 τ b nm hx hn)⟩ h1
      obtain ⟨j1, j2, j3⟩ := J
      refine ⟨by
          show (s1.2.push _).size = (done ++ [x]).length
          rw [Array.size_push, j1, hx2, List.length_append]
          rfl, by
          show (s.snd.push _).size = (done ++ [x]).length
          rw [Array.size_push, z2, List.length_append]
          rfl, ?_⟩
      intro j Y τ b nm hY hx
      have hY' : (s.snd.push { x.1 with arrayOf := s1.1 })[j]? = some Y := hY
      show EntryOK (s1.2.push { name := x.1.name, moment := d.moment }) j Y τ b nm
      by_cases hj : j < s.snd.size
      · rw [Array.getElem?_push_lt hj, ← Array.getElem?_eq_getElem hj] at hY'
        obtain ⟨D, hD, c⟩ := j2 j Y τ b nm hY' hx
        have hb : b < s1.2.size := (Array.getElem?_eq_some_iff.1 hD).1
        exact ⟨D, by rw [Array.getElem?_push_lt hb, ← Array.getElem?_eq_getElem hb]; exact hD, c⟩
      · have hj' : j = s.snd.size := by
          have := (Array.getElem?_eq_some_iff.1 hY').1
          rw [Array.size_push] at this
          omega
        subst hj'
        rw [Array.getElem?_push_size] at hY'
        obtain rfl := Option.some.inj hY'
        have hl : s.snd.size = x.2 := by rw [z2, hx2]
        have hnm : nm.isEmpty = false := by
          have hall : ¬ (s1.1.any fun a => a.2.isEmpty) = true := hne
          rw [← Array.any_toList, List.any_eq_true] at hall
          cases hc : nm.isEmpty with
          | false => rfl
          | true =>
            exact absurd ⟨(b, nm), Array.mem_toList_iff.2 (Array.mem_of_getElem? hx), hc⟩ hall
        rw [hl]
        rcases j3 τ b nm hx hnm with ⟨c, tr, t1, t2⟩ | ⟨c, D, hD, t2⟩
        · refine ⟨{ name := x.1.name, moment := d.moment }, by
            rw [c, ← j1, Array.getElem?_push_size], .inl ⟨c, tr, t1, t2⟩⟩
        · have hb : b < s1.2.size := (Array.getElem?_eq_some_iff.1 hD).1
          exact ⟨D, by rw [Array.getElem?_push_lt hb, ← Array.getElem?_eq_getElem hb]; exact hD,
            .inr ⟨c, t2⟩⟩)
    links.toList.zipIdx [] ⟨#[], #[]⟩ r
    (fun _ => ⟨rfl, rfl, fun l X τ b nm hX _ => by simp at hX⟩) hr
  exact (key fun j x hx => by
    rw [List.nil_append, List.getElem?_zipIdx] at hx
    obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    simp).2.2

/-! ## 5 Held against the layout and the shape -/

theorem arrayHeld_cut {messages : List ReqMessage} {arrays : List ReqArray} {t : Nat}
    {a : FrameArray} (h : arrayHeld messages arrays t a = true) :
    ∃ A m, arrays.find? (fun A => A.name == a.name) = some A ∧ A.sizeI = a.rows ∧
      A.sizeC = a.columns ∧ messages[A.message]? = some m ∧ m.moment = t ∧ a.life ≤ m.life := by
  unfold arrayHeld at h
  split at h
  · cases h
  · rename_i A hA
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨s1, s2⟩, _⟩, _⟩, h⟩ := h
    split at h
    · cases h
    · rename_i m hm
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨A, m, hA, s1, s2, hm, h.1.1, h.2⟩

theorem linkHeld_at {D : FrameLink} {L : ReqLink} {arrays : List ReqArray}
    (h : linkHeld D L arrays = true) {t : Nat} {a : FrameArray}
    (ha : a ∈ (D.moment.getD t #[]).toList) : arrayHeld L.messages arrays t a = true := by
  unfold linkHeld at h
  simp only [Bool.and_eq_true] at h
  have h3 := h.1.1.2
  rw [List.all_eq_true] at h3
  have ht := mem_lt ha
  have hm : (D.moment[t], t) ∈ D.moment.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (by
      rw [Array.getElem?_toList]
      exact Array.getElem?_eq_getElem ht)
  have h4 := h3 _ hm
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht] at ha
  rw [← Array.all_toList, List.all_eq_true] at h4
  exact h4 a ha

/-- **(Q), AT THE MAKER's OWN TEXT.** -/
theorem named_of_buildLinks {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH) (τ born : Nat) (name : String), B.links[l]? = some X →
      X.arrayOf[τ]? = some (born, name) → NamedHeld p l X τ born name := by
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨named, declared⟩, h3, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨⟨⟩, h4, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  obtain ⟨e1, e2, hall⟩ := Fo.heldAgainst_cut h4
  intro l X τ born name hX hx
  obtain ⟨D, hD, c⟩ := declareLinks_ok h3 l X τ born name hX hx
  have hb : born < declared.size := (Array.getElem?_eq_some_iff.1 hD).1
  have hL := List.getElem?_eq_getElem (l := p.shape.link) (i := born) (by omega)
  have hA := List.getElem?_eq_getElem (l := p.layout.link) (i := born) (by omega)
  have hh := hall born D _ _ hD hL hA
  have lay : ∀ A, (p.layout.link[born]'(by omega)).find? (fun A => A.name == name) = some A →
      VerifiableInference.Desc.arrayOf p.layout born name = some A := fun A hf => by
    unfold VerifiableInference.Desc.arrayOf
    rw [hA]
    exact hf
  rcases c with ⟨rfl, tr, t1, t, a, ha, a1, a2, a3⟩ | ⟨hlt, a, ha, a1, a2⟩
  · obtain ⟨A, m, f1, f2, f3, f4, _, _⟩ := arrayHeld_cut (linkHeld_at hh ha)
    rw [a1] at f1
    exact ⟨Nat.le_refl _, A, _, m, lay A f1, hL, f4, by omega, fun hc => absurd hc (by omega),
      fun _ => ⟨tr, t1, f2.trans a2, f3.trans a3⟩⟩
  · obtain ⟨A, m, f1, _, _, f4, f5, f6⟩ := arrayHeld_cut (linkHeld_at hh ha)
    rw [a1] at f1
    exact ⟨Nat.le_of_lt hlt, A, _, m, lay A f1, hL, f4, Nat.le_trans a2 f6, fun _ => f5,
      fun hc => absurd hc (by omega)⟩

/-- **(Q), WHERE THE PROOF FILE's PUBLIC PART IS MADE.** -/
theorem named_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH) (τ born : Nat) (name : String), Z.p.built.links[l]? = some X →
      X.arrayOf[τ]? = some (born, name) → NamedHeld Z.first l X τ born name := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  unfold Verify.builtOf at hb
  obtain ⟨l0, _, hb⟩ := exc_bind hb
  intro l X τ born name hX hx
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact named_of_buildLinks hb l Y τ born name hY hx

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.declareOwn_ok
#print axioms VerifiableInference.Desc.LinkJoin.declareLinks_ok
#print axioms VerifiableInference.Desc.LinkJoin.named_of_buildLinks
#print axioms VerifiableInference.Desc.LinkJoin.named_of_made
