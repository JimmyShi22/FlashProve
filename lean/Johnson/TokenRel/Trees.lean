-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Trees.lean: HASH TREES AS TOKEN PROGRAMS: they keep the rules, and what they add to
the list of evaluations.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

A leaf (leafT, Johnson/TokenSide/Tree.lean): a new token, one marked evaluation at the leaf oracle
that is charged to it and may hold further tokens us. From then on the new token depends on the
answer's tail and on us alone, and nothing is charged to the tail (PairOK); just one evaluation is
charged to the new token, at the leaf's input, and its answer is the leaf's digest (LeafEv). Both
stay so along any run that charges neither token. Inner nodes are ordinary queries.
  safe_treeT, safe_treesT   one tree; the trees of one component of one round: the rules, the
      counts, TreeOKT, TreeNewT (Johnson/TokenRules/Spec.lean), LeafAt
      (Johnson/TokenRules/ReleaseSpec.lean), and that every evaluation that was added is a leaf,
      charged to a new token.
Follows the pattern of Compile/Batch/DisciplineE.lean; there a leaf's digest is a token that is
shown at once, here it is a value and nothing is shown.

-/
import Johnson.TokenRel.Inv

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {bl bf : ℕ}
  {sd : (t : Tag) → FbIn lam L t → Prop}

/-! ## The two tokens of a leaf -/

/-- The two tokens of a leaf: numbers from n on, which exist; the first depends on the second and on
us alone; nothing is charged to the second. -/
def PairOK (d : DSt (typedOracleFamily lam K L)) (us : List Tok) (n : ℕ) (a : Tok × Tok) : Prop :=
  n ≤ a.1 ∧ n ≤ a.2 ∧ a.1 < d.vals.length ∧ a.2 < d.vals.length ∧ Deps d a.1 (a.2 :: us) ∧
    Deps d a.2 []

theorem PairOK.keeps {d d' : DSt (typedOracleFamily lam K L)} {us : List Tok} {n : ℕ} {a : Tok × Tok}
    {Cc : Tok → Prop} (h : PairOK d us n a) (hc : Charges Cc d d') (h1 : ¬ Cc a.1)
    (h2 : ¬ Cc a.2) : PairOK d' us n a :=
  ⟨h.1, h.2.1, lt_of_lt_of_le h.2.2.1 hc.vals.length_le,
    lt_of_lt_of_le h.2.2.2.1 hc.vals.length_le, h.2.2.2.2.1.keeps h.2.2.1 hc h1,
    h.2.2.2.2.2.keeps h.2.2.2.1 hc h2⟩

/-- a leaf as an entry of a log -/
def leafEn (b : Body L) (salt : Bits) (dg : Dig lam) : QA (typedOracleFamily lam K L) :=
  ⟨OracleName.leaf, (⟨b, salt⟩ : LeafIn L), dg⟩

/-- Just one evaluation is charged to the first token of the leaf: at (body b, start pv then the
token's value), with the answer dg. None is charged to the second. -/
def LeafEv (d : DSt (typedOracleFamily lam K L)) (a : Tok × Tok) (b : Body L) (pv : Bits) (dg : Dig lam) :
    Prop :=
  (d.evs.filter fun e => e.charged == a.1).map qa = [leafEn b (pv ++ d.val a.1) dg] ∧
    (d.evs.filter fun e => e.charged == a.2) = []

theorem LeafEv.adds {d d' : DSt (typedOracleFamily lam K L)} {a : Tok × Tok} {b : Body L} {pv : Bits}
    {dg : Dig lam} {P : Ev (typedOracleFamily lam K L) → Prop} (h : LeafEv d a b pv dg)
    (hlt : a.1 < d.vals.length) (hv : d.vals <+: d'.vals) (ha : Adds P d d')
    (h1 : ∀ e, P e → e.charged ≠ a.1) (h2 : ∀ e, P e → e.charged ≠ a.2) : LeafEv d' a b pv dg :=
  ⟨by rw [filter_adds ha h1, val_of_prefix hv hlt]; exact h.1, by rw [filter_adds ha h2]; exact h.2⟩

/-- what the leaf programs add: leaves, charged to tokens from n on -/
def NewLeaf (n : ℕ) (e : Ev (typedOracleFamily lam K L)) : Prop := e.o = OracleName.leaf ∧ n ≤ e.charged

theorem map_val_prefix {d d' : DSt (typedOracleFamily lam K L)} (hv : d.vals <+: d'.vals) {us : List Tok}
    (hus : ∀ u ∈ us, u < d.vals.length) : us.map d'.val = us.map d.val :=
  List.map_congr_left fun u hu => val_of_prefix hv (hus u hu)

theorem safe_leafT {ℓ : ℕ} (hbl : bl ≤ ℓ) (us : List Tok) (pre : List Bits → Bits) (b : Body L)
    {d : DSt (typedOracleFamily lam K L)} (hd : TidyO (rulesT K L lam bl bf sd) d)
    (hus : ∀ u ∈ us, u < d.vals.length) :
    SafeO (rulesT K L lam bl bf sd) (leafT (K := K) ℓ us pre b) d fun x d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO noTok (fun u => u ∈ us) noTok zr (cnt1 OracleName.leaf 1) d d' ∧
      KeepsFree (fun o => o = OracleName.leaf) d d' ∧ PairOK d' us d.vals.length x.2 ∧
      Adds (NewLeaf d.vals.length) d d' ∧ LeafEv d' x.2 b (pre (us.map d.val)) x.1 := by
  unfold leafT
  intro u
  have h1 := hd.fresh (List.ofFn u)
  have hu := Untouched.of_fresh hd (List.ofFn u)
  have hl := Len.of_fresh d u
  have hus' : ∀ v ∈ us, v < (afterFresh d (List.ofFn u)).vals.length := fun v hv => by
    rw [length_afterFresh]
    exact Nat.lt_succ_of_lt (hus v hv)
  have htu : d.vals.length ∉ us := fun h => absurd (hus _ h) (lt_irrefl _)
  refine SafeO.mono ?_ _ _ (safe_mark h1 hus' htu (hu.freeAt OracleName.leaf)
    (le_trans hbl (le_of_eq hl.2.symm)) (fun _ => by trivial) _ _ _)
  rintro x d₁ ⟨r, e, rfl, hm, hev⟩
  have he : e = d.vals.length + 1 := by rw [hm.eq, length_afterFresh]
  have hold : ∀ s, d.vals.length ≤ s → (d.evs.filter fun e₀ => e₀.charged == s) = [] := fun s hs =>
    List.filter_eq_nil_iff.mpr fun e₀ he₀ => by
      simpa using Nat.ne_of_lt (lt_of_lt_of_le (hd.charged_lt e₀ he₀) hs)
  rw [map_val_prefix (d := d) (List.prefix_append _ _) hus,
    ← val_of_prefix hm.run.grows.vals hu.lt] at hev
  refine ⟨hm.tidy, ?_, (KeepsFree.ofFresh _ d _).trans hm.free,
    ⟨le_rfl, ?_, lt_of_lt_of_le hu.lt hm.run.length_le, hm.unt.lt, ?_, hm.unt.deps []⟩,
    ⟨_, hev, fun y hy => by rw [List.mem_singleton.mp hy]; exact ⟨rfl, le_rfl⟩⟩, ?_, ?_⟩
  · exact (Run.ofFresh (Cc := noTok) (Ch := fun u => u ∈ us) (R := noTok) (e := zr) (M := zr) d
      (List.ofFn u)).trans hm.run (fun _ h => Or.inr (le_of_eq h.symm))
      (fun _ h => h.elim (fun h => Or.inr (le_of_eq h.symm)) Or.inl) (fun _ h => Or.inl h)
      (fun _ => le_rfl) (fun _ => (Nat.zero_add _).le)
  · show d.vals.length ≤ e
    rw [he]
    exact Nat.le_succ _
  · exact (hm.deps [] (hu.deps [])).mono fun v hv => by simpa using hv
  · rw [hev]
    show ((d.evs ++ [_]).filter
      fun e₀ : Ev (typedOracleFamily lam K L) => e₀.charged == d.vals.length).map qa = _
    rw [List.filter_append, hold _ le_rfl, List.nil_append,
      List.filter_cons_of_pos (by simp), List.filter_nil]
    rfl
  · rw [hev]
    show ((d.evs ++ [_]).filter fun e₀ : Ev (typedOracleFamily lam K L) => e₀.charged == e) = []
    rw [List.filter_append, hold _ (by rw [he]; exact Nat.le_succ _), List.nil_append,
      List.filter_cons_of_neg (by simp [he]), List.filter_nil]

theorem safe_leavesT {ℓ : ℕ} (hbl : bl ≤ ℓ) (us : List Tok) (pre : List Bits → Bits) (pv : Bits) :
    ∀ (bs : List (Body L)) (d : DSt (typedOracleFamily lam K L)), TidyO (rulesT K L lam bl bf sd) d →
      (∀ u ∈ us, u < d.vals.length) → pre (us.map d.val) = pv →
    SafeO (rulesT K L lam bl bf sd) (TokenSide.leavesT (K := K) ℓ us pre bs) d fun r d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO noTok (fun u => u ∈ us) noTok zr (cnt1 OracleName.leaf bs.length) d d' ∧
      KeepsFree (fun o => o = OracleName.leaf) d d' ∧ r.1.length = bs.length ∧ r.2.length = bs.length ∧
      (∀ a ∈ r.2, PairOK d' us d.vals.length a) ∧ Adds (NewLeaf d.vals.length) d d' ∧
      ∀ (j : ℕ) (a : Tok × Tok), r.2[j]? = some a →
        ∃ b dg, bs[j]? = some b ∧ r.1[j]? = some dg ∧ LeafEv d' a b pv dg
  | [], d, hd, _, _ =>
      ⟨hd, Run.refl d, KeepsFree.refl _ d, rfl, rfl, fun _ h => absurd h List.not_mem_nil,
        Adds.refl _ d, fun _ _ h => nomatch h⟩
  | b :: bs, d, hd, hus, hpv => by
      rw [TokenSide.leavesT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_leafT hbl us pre b hd hus))
      rintro x d₁ ⟨hd₁, hr₁, hk₁, hp₁, ha₁, hl₁⟩
      have hus₁ : ∀ u ∈ us, u < d₁.vals.length := fun u hu =>
        lt_of_lt_of_le (hus u hu) hr₁.length_le
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_leavesT hbl us pre pv bs d₁ hd₁ hus₁
        (by rw [map_val_prefix hr₁.grows.vals hus]; exact hpv)))
      rintro r d₂ ⟨hd₂, hr₂, hk₂, hlen, hlen', hp₂, ha₂, hl₂⟩
      refine ⟨hd₂, hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        (fun _ => le_rfl) ?_, hk₁.trans hk₂, by simp [hlen], by simp [hlen'], ?_,
        ha₁.trans (ha₂.mono fun e _ h => ⟨h.1, le_trans hr₁.length_le h.2⟩), ?_⟩
      · intro o
        simp only [cnt1, List.length_cons]
        split <;> omega
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hp₁.keeps hr₂.charges (fun h => h) (fun h => h)
        · obtain ⟨a1, a2, rest⟩ := hp₂ a ha
          exact ⟨le_trans hr₁.length_le a1, le_trans hr₁.length_le a2, rest⟩
      · intro j a hj
        cases j with
        | zero =>
            have e : x.2 = a := by simpa using hj
            subst e
            refine ⟨b, x.1, rfl, rfl, ?_⟩
            rw [hpv] at hl₁
            exact hl₁.adds hp₁.2.2.1 hr₂.grows.vals ha₂
              (fun e h => Nat.ne_of_gt (lt_of_lt_of_le hp₁.2.2.1 h.2))
              (fun e h => Nat.ne_of_gt (lt_of_lt_of_le hp₁.2.2.2.1 h.2))
        | succ j => exact hl₂ j a (by simpa using hj)

section Nodes
variable {Ch : Tok → Prop} {P : OracleName → Prop} {Pe : Ev (typedOracleFamily lam K L) → Prop}

theorem safe_nodeT (a b : Dig lam) {d : DSt (typedOracleFamily lam K L)}
    (hd : TidyO (rulesT K L lam bl bf sd) d) :
    SafeO (rulesT K L lam bl bf sd) (nodeT (K := K) (L := L) a b) d fun _ d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧ RunO noTok Ch noTok (cnt1 OracleName.node 1) zr d d' ∧
      KeepsFree P d d' ∧ Adds Pe d d' :=
  ⟨trivial, fun _ T => ⟨hd.plain OracleName.node T, run_ofPlain d OracleName.node T, KeepsFree.ofPlain _ d _ T,
    Adds.ofPlain _ d _ T⟩⟩

theorem safe_pairUp : ∀ (l : List (Dig lam)) (d : DSt (typedOracleFamily lam K L)),
    TidyO (rulesT K L lam bl bf sd) d →
    SafeO (rulesT K L lam bl bf sd) (pairUp (nodeT (K := K) (L := L)) l) d fun a d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO noTok Ch noTok (cnt1 OracleName.node (l.length / 2)) zr d d' ∧ KeepsFree P d d' ∧
      Adds Pe d d' ∧ a.length = l.length - l.length / 2
  | [], d, hd => ⟨hd, Run.refl d, KeepsFree.refl _ d, Adds.refl _ d, by simp⟩
  | [_], d, hd => ⟨hd, Run.refl d, KeepsFree.refl _ d, Adds.refl _ d, by simp⟩
  | a :: b :: t, d, hd => by
      show SafeO _ ((nodeT a b).bind fun c => (pairUp nodeT t).bind fun r => Step.pure (c :: r)) d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
        (safe_nodeT (Ch := Ch) (P := P) (Pe := Pe) a b hd))
      rintro c d₁ ⟨hd₁, hr₁, hk₁, ha₁⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_pairUp t d₁ hd₁))
      rintro r d₂ ⟨hd₂, hr₂, hk₂, ha₂, hlen⟩
      refine ⟨hd₂, hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        ?_ (fun _ => le_rfl), hk₁.trans hk₂, ha₁.trans ha₂, ?_⟩
      · intro o
        simp only [cnt1, List.length_cons]
        split
        · omega
        · exact le_rfl
      · simp only [List.length_cons, hlen]
        omega

theorem safe_levelsM : ∀ (n : ℕ) (l : List (Dig lam)) (d : DSt (typedOracleFamily lam K L)),
    TidyO (rulesT K L lam bl bf sd) d →
    SafeO (rulesT K L lam bl bf sd) (levelsM (nodeT (K := K) (L := L)) n l) d fun lv d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧ RunO noTok Ch noTok (cnt1 OracleName.node l.length) zr d d' ∧
      KeepsFree P d d' ∧ Adds Pe d d' ∧ lv.headD [] = l
  | 0, _, d, hd => ⟨hd, Run.refl d, KeepsFree.refl _ d, Adds.refl _ d, rfl⟩
  | n + 1, l, d, hd => by
      show SafeO _
        ((pairUp nodeT l).bind fun u => (levelsM nodeT n u).bind fun r => Step.pure (l :: r)) d _
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d
        (safe_pairUp (Ch := Ch) (P := P) (Pe := Pe) l d hd))
      rintro u d₁ ⟨hd₁, hr₁, hk₁, ha₁, hlen⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_levelsM n u d₁ hd₁))
      rintro r d₂ ⟨hd₂, hr₂, hk₂, ha₂, _⟩
      refine ⟨hd₂, hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        ?_ (fun _ => le_rfl), hk₁.trans hk₂, ha₁.trans ha₂, rfl⟩
      intro o
      simp only [cnt1, hlen]
      split
      · omega
      · exact le_rfl

end Nodes

/-! ## Trees -/

theorem toK_inp_some {T : TreeT lam L} {j : ℕ} {a : Tok × Tok} (h : T.tok[j]? = some a)
    (val : Tok → Bits) (pre : Bits) : (T.toK val pre).inp j = ⟨T.body j, pre ++ val a.1⟩ := by
  simp [TreeT.toK, h]

theorem _root_.OnBytes.TokenRules.TreeOKT.keeps {d d' : DSt (typedOracleFamily lam K L)} {us : List Tok}
    {T : TreeT lam L}
    {Cc : Tok → Prop} (h : TreeOKT d us T) (hc : Charges Cc d d')
    (hn : ∀ u, TreeTokT T u → ¬ Cc u) : TreeOKT d' us T := fun a ha =>
  ⟨lt_of_lt_of_le (h a ha).1 hc.vals.length_le, lt_of_lt_of_le (h a ha).2.1 hc.vals.length_le,
    (h a ha).2.2.1.keeps (h a ha).1 hc (hn _ ⟨a, ha, Or.inl rfl⟩),
    (h a ha).2.2.2.keeps (h a ha).2.1 hc (hn _ ⟨a, ha, Or.inr rfl⟩)⟩

theorem _root_.OnBytes.TokenRules.TreeOKT.lt {d : DSt (typedOracleFamily lam K L)} {us : List Tok}
    {T : TreeT lam L}
    (h : TreeOKT d us T) {u : Tok} (hu : TreeTokT T u) : u < d.vals.length := by
  obtain ⟨a, ha, rfl | rfl⟩ := hu
  · exact (h a ha).1
  · exact (h a ha).2.1

/-- LeafAt stays along a run that reveals nothing and charges none of the tree's tokens. -/
theorem LeafAt.adds {d d' : DSt (typedOracleFamily lam K L)} {T : TreeT lam L} {pv : Bits}
    {P : Ev (typedOracleFamily lam K L) → Prop} (h : LeafAt d T pv) (hlt : ∀ u, TreeTokT T u → u < d.vals.length)
    (hv : d.vals <+: d'.vals) (ha : Adds P d d') (hP : ∀ e, P e → ¬ TreeTokT T e.charged) :
    LeafAt d' T pv := by
  refine ⟨h.1, fun j a hj => ?_⟩
  have hm : a ∈ T.tok := List.mem_of_getElem? hj
  have e1 : entryK (K := K) (T.toK d'.val pv) j = entryK (T.toK d.val pv) j := by
    unfold entryK
    rw [toK_inp_some hj, toK_inp_some hj, val_of_prefix hv (hlt _ ⟨a, hm, Or.inl rfl⟩)]
    rfl
  rw [filter_adds ha fun e he hc => hP e he ⟨a, hm, Or.inl hc⟩,
    filter_adds ha fun e he hc => hP e he ⟨a, hm, Or.inr hc⟩, e1]
  exact h.2 j a hj

/-- **One tree.** -/
theorem safe_treeT {ℓ : ℕ} (hbl : bl ≤ ℓ) (us : List Tok) (pre : List Bits → Bits) (dp : ℕ)
    (body : ℕ → Body L) {d : DSt (typedOracleFamily lam K L)} (hd : TidyO (rulesT K L lam bl bf sd) d)
    (hus : ∀ u ∈ us, u < d.vals.length) :
    SafeO (rulesT K L lam bl bf sd) (treeT (K := K) ℓ us pre dp body) d fun T d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO noTok (fun u => u ∈ us) noTok (cnt1 OracleName.node (2 ^ dp)) (cnt1 OracleName.leaf (2 ^ dp)) d d' ∧
      KeepsFree (fun o => o = OracleName.leaf) d d' ∧ TreeOKT d' us T ∧ TreeNewT d.vals.length T ∧
      Adds (NewLeaf d.vals.length) d d' ∧ LeafAt d' T (pre (us.map d.val)) ∧
      T.tok.length = 2 ^ dp := by
  unfold treeT
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_leavesT hbl us pre _ _ d hd hus rfl))
  rintro l d₁ ⟨hd₁, hr₁, hk₁, hlen, hlen', hp₁, ha₁, hl₁⟩
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁
    (safe_levelsM (Ch := fun u => u ∈ us) (P := fun o => o = OracleName.leaf)
      (Pe := NewLeaf d₁.vals.length) dp l.1 d₁ hd₁))
  rintro lv d₂ ⟨hd₂, hr₂, hk₂, ha₂, hlv⟩
  rw [List.length_map, List.length_range] at hlen hlen' hr₁
  rw [hlen] at hr₂
  have hp₂ : ∀ a ∈ l.2, PairOK d₂ us d.vals.length a := fun a ha =>
    (hp₁ a ha).keeps hr₂.charges (fun h => h) (fun h => h)
  refine ⟨hd₂, hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
    (fun _ => (Nat.zero_add _).le) (fun _ => le_rfl), hk₁.trans hk₂, ?_, ?_,
    ha₁.trans (ha₂.mono fun e _ h => ⟨h.1, le_trans hr₁.length_le h.2⟩), ⟨?_, ?_⟩, hlen'⟩
  · exact fun a ha => (hp₂ a ha).2.2
  · rintro u ⟨a, ha, rfl | rfl⟩
    · exact (hp₂ a ha).1
    · exact (hp₂ a ha).2.1
  · show l.2.length = (lv.headD []).length
    rw [hlv, hlen, hlen']
  · intro j a hj
    have hj' : l.2[j]? = some a := hj
    obtain ⟨b, dg, hb, hdg, hev⟩ := hl₁ j a hj'
    have hm : a ∈ l.2 := List.mem_of_getElem? hj'
    have hev₂ := hev.adds (hp₁ a hm).2.2.1 hr₂.grows.vals ha₂
      (fun e h => Nat.ne_of_gt (lt_of_lt_of_le (hp₁ a hm).2.2.1 h.2))
      (fun e h => Nat.ne_of_gt (lt_of_lt_of_le (hp₁ a hm).2.2.2.1 h.2))
    have hbj : b = body j := by
      rw [List.getElem?_map] at hb
      cases hr : (List.range (2 ^ dp))[j]? with
      | none => rw [hr] at hb; exact nomatch hb
      | some i =>
          rw [hr] at hb
          have hi : i = j := by
            have := List.getElem?_range (n := 2 ^ dp) (i := j)
            rcases Nat.lt_or_ge j (2 ^ dp) with hlt | hge
            · rw [List.getElem?_range hlt] at hr
              exact (Option.some.inj hr).symm
            · rw [List.getElem?_eq_none (by simpa using hge)] at hr
              exact nomatch hr
          rw [← hi]
          exact (Option.some.inj hb).symm
    have hen : entryK (K := K) (TreeT.toK d₂.val (pre (us.map d.val)) ⟨body, l.2, lv⟩) j =
        leafEn b (pre (us.map d.val) ++ d₂.val a.1) dg := by
      unfold entryK leafEn
      rw [toK_inp_some hj, hbj]
      show (⟨OracleName.leaf, _, (lv.headD []).getD j default⟩ : QA (typedOracleFamily lam K L)) = _
      rw [hlv, List.getD_eq_getElem?_getD, hdg]
      rfl
    rw [hen]
    exact hev₂

/-- **The trees of one component of one round.** -/
theorem safe_treesT {r : Round} {ℓ : ℕ} (hbl : bl ≤ ℓ) (us : List Tok) (pre : List Bits → Bits)
    (pad : Body L) (posAt : ℕ → ℕ → Option r.Pos) (emb : (p : r.Pos) → r.Sym p → Body L)
    (o : r.Orc) (pv : Bits) : ∀ (ds : List ℕ) (k : ℕ) (d : DSt (typedOracleFamily lam K L)),
      TidyO (rulesT K L lam bl bf sd) d → (∀ u ∈ us, u < d.vals.length) →
      pre (us.map d.val) = pv →
    SafeO (rulesT K L lam bl bf sd) (treesT (K := K) ℓ us pre pad posAt emb o k ds) d fun Ts d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO noTok (fun u => u ∈ us) noTok (cnt1 OracleName.node (nLv ds)) (cnt1 OracleName.leaf (nLv ds)) d d' ∧
      KeepsFree (fun o => o = OracleName.leaf) d d' ∧ Adds (NewLeaf d.vals.length) d d' ∧
      ∀ T ∈ Ts, TreeOKT d' us T ∧ TreeNewT d.vals.length T ∧ LeafAt d' T pv
  | [], _, d, hd, _, _ =>
      ⟨hd, Run.refl d, KeepsFree.refl _ d, Adds.refl _ d, fun _ h => absurd h List.not_mem_nil⟩
  | dp :: ds, k, d, hd, hus, hpv => by
      rw [treesT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_treeT hbl us pre dp _ hd hus))
      rintro T d₁ ⟨hd₁, hr₁, hk₁, hT, hN, ha₁, hL, _⟩
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_treesT hbl us pre pad posAt emb o pv ds
        (k + 1) d₁ hd₁ (fun u hu => lt_of_lt_of_le (hus u hu) hr₁.length_le)
        (by rw [map_val_prefix hr₁.grows.vals hus]; exact hpv)))
      rintro Ts d₂ ⟨hd₂, hr₂, hk₂, ha₂, hTs⟩
      refine ⟨hd₂, hr₁.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        ?_ ?_, hk₁.trans hk₂,
        ha₁.trans (ha₂.mono fun e _ h => ⟨h.1, le_trans hr₁.length_le h.2⟩), ?_⟩
      · intro o'
        simp only [cnt1, nLv, List.map_cons, List.sum_cons]
        split <;> simp
      · intro o'
        simp only [cnt1, nLv, List.map_cons, List.sum_cons]
        split <;> simp
      · intro T' hT'
        rcases List.mem_cons.mp hT' with rfl | hT'
        · rw [hpv] at hL
          exact ⟨TreeOKT.keeps hT hr₂.charges fun _ _ h => h, hN,
            LeafAt.adds hL (fun u hu => TreeOKT.lt hT hu) hr₂.grows.vals ha₂ fun e he hc =>
              absurd (TreeOKT.lt hT hc) (Nat.not_lt.mpr he.2)⟩
        · exact ⟨(hTs T' hT').1, fun u hu => le_trans hr₁.length_le ((hTs T' hT').2.1 u hu),
            (hTs T' hT').2.2⟩

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.safe_treeT
#print axioms OnBytes.TokenRel.safe_treesT
