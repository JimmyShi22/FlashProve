-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesLaid.lean: the tables of a layer sub-proof lie one behind the other in the
vector of reads, at every layout.

Layer.layTables (OnBytes/Model/LayerForms.lean) places the families of tables one after the other,
and each family's parts one after the other; Layer.funsOf (OnBytes/Model/Layer.lean) makes one table
of each part. So no entry of the vector of reads lies in two tables, and all lie below the number of
entries that layTables returns.

Main names (namespace `Meaning.Planes`).
  `Seq l p q`: the stretches of l (first entry, number of entries) lie one behind the other from p
      to q, without a gap. `Seq.mem`, `Seq.before`, `Seq.append`.
  `layParts_seq`, `layTables_seq`, `funs_seq`: what these functions lay is such a row of stretches.
  `laid_public`: every table ends at or below n, and no entry lies in two tables.
  `hear_tables_n`: in a run of the layers' plain hearing, n is the plan's number hp.nU[2].
  `k4_tables_apart`: both at the tables that such a run leaves.

Limits. Numbers of entries alone: nothing on what an entry is worth. Nothing on soundness.

-/
import Johnson.Meaning.PlanesHost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open OnBytes OnBytes.Model Fo
open OnBytes.Model.Layer (TableAsk TableAt Lay layParts layTables funsOf phiOf Pub Own HPlan2
  tableAsks)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (engFl hearFl hear)
open Meaning.HKT (bind_some pure_some)

/-- Stretches (first entry, number of entries) that lie one behind the other, from p to q. -/
inductive Seq : List (ℕ × ℕ) → ℕ → ℕ → Prop
  | nil (p : ℕ) : Seq [] p p
  | cons {l : List (ℕ × ℕ)} {p q : ℕ} (n : ℕ) : Seq l (p + n) q → Seq ((p, n) :: l) p q

theorem Seq.le {l : List (ℕ × ℕ)} {p q : ℕ} (h : Seq l p q) : p ≤ q := by
  induction h with
  | nil p => exact Nat.le_refl p
  | cons n _ ih => omega

theorem Seq.append {l l' : List (ℕ × ℕ)} {p q r : ℕ} (h : Seq l p q) (h' : Seq l' q r) :
    Seq (l ++ l') p r := by
  induction h with
  | nil p => exact h'
  | cons n _ ih => exact Seq.cons n (ih h')

/-- Every stretch lies between p and q. -/
theorem Seq.mem {l : List (ℕ × ℕ)} {p q : ℕ} (h : Seq l p q) {x : ℕ × ℕ} (hx : x ∈ l) :
    p ≤ x.1 ∧ x.1 + x.2 ≤ q := by
  induction h with
  | nil p => cases hx
  | @cons l p q n h' ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨Nat.le_refl _, h'.le⟩
    · have := ih hx
      omega

/-- An earlier stretch ends before a later one begins. -/
theorem Seq.before {l : List (ℕ × ℕ)} {p q : ℕ} (h : Seq l p q) {i j : ℕ} (hij : i < j)
    {x y : ℕ × ℕ} (hx : l[i]? = some x) (hy : l[j]? = some y) : x.1 + x.2 ≤ y.1 := by
  induction h generalizing i j with
  | nil p => simp at hx
  | @cons l p q n h' ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hy' : l[j]? = some y := by simpa using hy
      cases i with
      | zero =>
        have e : (p, n) = x := by simpa using hx
        rw [← e]
        exact (h'.mem (List.mem_of_getElem? hy')).1
      | succ i =>
        have hx' : l[i]? = some x := by simpa using hx
        exact ih (by omega) hx' hy'

/-- The parts of one family lie one behind the other. -/
theorem layParts_seq (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ (n p : ℕ),
    Seq ((layParts mats a n p).1.map fun m =>
      (m.2, (mats.getD m.1 (0, 0)).2 * ((mats.getD m.1 (0, 0)).1 / a.L))) p (layParts mats a n p).2
  | 0, p => Seq.nil p
  | n + 1, p => by
    unfold layParts
    exact Seq.cons _ (layParts_seq mats a n _)

/-- All tables that layTables lays, as stretches, in their order. -/
def stretchesOf (mats : Array (ℕ × ℕ)) (laid : List (TableAsk × List (ℕ × ℕ))) : List (ℕ × ℕ) :=
  (laid.map fun x => x.2.map fun m =>
    (m.2, (mats.getD m.1 (0, 0)).2 * ((mats.getD m.1 (0, 0)).1 / x.1.L))).flatten

theorem layTables_seq (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (tab : List TableAt) (laid : List (TableAsk × List (ℕ × ℕ))) (n : ℕ),
    layTables mats asks p = some (tab, laid, n) → Seq (stretchesOf mats laid) p n
  | [], p, tab, laid, n, h => by
    unfold layTables at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, rfl⟩ := h
    exact Seq.nil p
  | a :: rest, p, tab, laid, n, h => by
    unfold layTables at h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨_, rfl, rfl⟩ := e
      exact (layParts_seq mats a a.parts p).append
        (layTables_seq mats rest _ r.1 r.2.1 r.2.2 hr)

/-- A table as a stretch, at the matrices' sizes as pairs. -/
def stretchOf (matsP : Array (ℕ × ℕ)) (f : HFun) : ℕ × ℕ :=
  (f.start, (matsP.getD f.mat (0, 0)).2 * ((matsP.getD f.mat (0, 0)).1 / f.len))

theorem flat_stretches (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (matsP : Array (ℕ × ℕ)) : ∀ (laid : List (TableAsk × List (ℕ × ℕ))) (l : List (List HFun)),
    laid.mapM (famFuns y fo pt) = some l →
      l.flatten.map (stretchOf matsP) = stretchesOf matsP laid
  | [], l, h => by
    have e : [] = l := by simpa using h
    rw [← e]
    rfl
  | x :: rest, l, h => by
    rw [List.mapM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨zs, hzs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : z :: zs = l := Option.some.inj h
    unfold famFuns at hz
    obtain ⟨phi, _, hz⟩ := Option.bind_eq_some_iff.mp hz
    obtain rfl := Option.some.inj hz
    have ih := flat_stretches y fo pt matsP rest zs hzs
    unfold stretchesOf at ih ⊢
    rw [List.flatten_cons, List.map_append, ih, List.map_cons, List.flatten_cons, List.map_map]
    rfl

/-- **The tables that funsOf makes of what layTables has laid lie one behind the other**, from 0 to
the number of entries that layTables returns. -/
theorem funs_seq {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {matsP : Array (ℕ × ℕ)} {asks : List TableAsk} {tab : List TableAt}
    {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {funs : Array HFun}
    (hl : layTables matsP asks 0 = some (tab, laid, n)) (hf : funsOf y fo pt laid = some funs) :
    Seq (funs.toList.map (stretchOf matsP)) 0 n := by
  have h' : (laid.mapM (famFuns y fo pt)).bind (fun l => some l.flatten.toArray) = some funs := hf
  obtain ⟨l, hl', e⟩ := Option.bind_eq_some_iff.mp h'
  obtain rfl := Option.some.inj e
  rw [List.toList_toArray, flat_stretches y fo pt matsP laid l hl']
  exact layTables_seq matsP asks 0 tab laid n hl

/-- The sizes as pairs and the matrices' records give one number of entries. -/
theorem stretchOf_entries (mats : Array TMat) (f : HFun) :
    stretchOf (mats.map fun M => (M.m, M.k)) f = (f.start, entriesOf mats f) := by
  unfold stretchOf entriesOf stretches
  have e : (mats.map fun M => (M.m, M.k)).getD f.mat (0, 0) =
      ((mats.getD f.mat {}).m, (mats.getD f.mat {}).k) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases mats[f.mat]? <;> rfl
  rw [e]

/-- **Two fields of Laid at whatever layTables and funsOf make**: every table's stretch ends at or
below n, and no entry lies in two tables. -/
theorem laid_public {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array TMat} {asks : List TableAsk} {tab : List TableAt}
    {laid : List (TableAsk × List (ℕ × ℕ))} {n : ℕ} {funs : Array HFun}
    (hl : layTables (mats.map fun M => (M.m, M.k)) asks 0 = some (tab, laid, n))
    (hf : funsOf y fo pt laid = some funs) :
    (∀ f ∈ funs.toList, f.start + entriesOf mats f ≤ n) ∧
      ∀ f ∈ funs.toList, ∀ f' ∈ funs.toList, ∀ col < entriesOf mats f,
        ∀ col' < entriesOf mats f', f.start + col = f'.start + col' → f = f' := by
  have S := funs_seq hl hf
  refine ⟨fun f hf' => ?_, fun f hf1 f' hf2 col hc col' hc' e => ?_⟩
  · have := (S.mem (List.mem_map_of_mem hf')).2
    rw [stretchOf_entries] at this
    exact this
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf1
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf2
    have mi : (funs.toList.map (stretchOf (mats.map fun M => (M.m, M.k))))[i]? =
        some (f.start, entriesOf mats f) := by
      rw [List.getElem?_map, hi, Option.map_some, stretchOf_entries]
    have mj : (funs.toList.map (stretchOf (mats.map fun M => (M.m, M.k))))[j]? =
        some (f'.start, entriesOf mats f') := by
      rw [List.getElem?_map, hj, Option.map_some, stretchOf_entries]
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := S.before h mi mj
      simp only at this
      omega
    · rw [h, hj] at hi
      exact (Option.some.inj hi).symm
    · have := S.before h mj mi
      simp only at this
      omega

/-- What a run of the layers' plain hearing leaves on the tables, with the number of entries: it is
the plan's. -/
theorem hear_tables_n {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, F', t')) :
    ∃ laid pt,
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (o.v.tab, laid, hp.nU.getD 2 0) ∧
      funsOf P.y fo pt laid = some o.funs := by
  unfold hearFl hear at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨iU3, _, _, _, h⟩ := bind_some h
  obtain ⟨H0, _, _, _, h⟩ := bind_some h
  obtain ⟨H, _, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨⟨tab, laid, nU3⟩, _, _, hl, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, _, _, hn, h⟩ := bind_some h
  have en : nU3 = hp.nU.getD 2 0 := by
    have := (Desc.First.K4.must_some hn).1
    exact beq_iff_eq.mp this
  obtain ⟨K, _, _, _, h⟩ := bind_some h
  obtain ⟨⟨hd, hd2⟩, _, _, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨claimsP, _, _, _, h⟩ := bind_some h
  split at h <;>
  · obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨pt, _, _, _, h⟩ := bind_some h
    obtain ⟨funs, _, _, hf, h⟩ := bind_some h
    rw [pure_some h, ← en]
    exact ⟨laid, pt, need_val hl, need_val hf⟩

/-- **No entry of the vector of reads lies in two of the tables that a run of the layers' plain
hearing leaves**, and every table ends at or below the plan's number of reads. -/
theorem k4_tables_apart {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : hearFl P hp g fo F t = some (o, F', t')) :
    (∀ f ∈ o.funs.toList, f.start + entriesOf (P.tails.getD g {}).mats f ≤ hp.nU.getD 2 0) ∧
      ∀ f ∈ o.funs.toList, ∀ f' ∈ o.funs.toList,
        ∀ col < entriesOf (P.tails.getD g {}).mats f,
        ∀ col' < entriesOf (P.tails.getD g {}).mats f',
          f.start + col = f'.start + col' → f = f' := by
  obtain ⟨laid, pt, hl, hf⟩ := hear_tables_n hh
  exact laid_public hl hf

#print axioms hear_tables_n
#print axioms k4_tables_apart
#print axioms layTables_seq
#print axioms funs_seq
#print axioms laid_public

end Meaning.Planes
