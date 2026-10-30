-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/StableLeaf.lean: what lies under a root in a first algorithm's log stays as the
log grows, over the sibling's types.

OnBytes/Slice/StableLeaf.lean and one theorem of OnBytes/Slice/OneMaker.lean (`stableLeaf_maker`)
said again over the sibling of the library's soundness road (OnBytes/TypedOracleCompiler/: a list of roots a query;
a leaf's body a type of the interface's choosing). The text is cut by program from these two files:
the opened namespaces are the sibling's, and `Batch.` is written `TypedOracleCompiler.Compile.Batch.`. No
statement and no proof turns otherwise. Three declarations of StableLeaf.lean that are general in
the family of oracles (`bothExp`, `bothExp_glue`, `withTrace_withTrace`) are not said again: they
are opened from OnBytes.Slice.

Main theorems: `stableLeaf_typed`, `stableLeaf_one`, `stableLeaf_log`, `stableLeaf_maker`: with
probability at most 2 (t1 + 1 + t2)^2 / 2^lam a leaf that is read off the first log under the root
that `rt` names differs from the leaf read off the whole log.

What is not claimed. What the heads of the two files do not claim. The compiler under OnBytes/TypedOracleCompiler/
is the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.
Nothing on any protocol, checker or hash function.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Local
import OnBytes.TypedOracleCompiler.Compile.Batch.Hash
import OnBytes.Slice.OneMaker
import Rom.StateFirstCB

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal
open OnBytes.Slice (noCoin_of_detBound fst_of_mem_support twoExp twoExpOne_glue
    fst_down_of_mem_support
  bothExp bothExp_glue withTrace_withTrace twoExp_withTrace)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {β δ : Type}

/-! ## Entries of the marker oracle -/

/-- The entry that an announcement of c leaves. -/
def annK (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (c : Dig lam) : QA
    (typedOracleFamily lam K L) := ⟨TypedOracleCompiler.Compile.Batch.OracleName.ann, c, ()⟩

/-- The test "not an entry of the marker oracle". -/
def notAnnK (e : QA (typedOracleFamily lam K L)) : Bool := decide (e.1 ≠ TypedOracleCompiler.Compile.Batch.OracleName.ann)

/-- Entries of the marker oracle can be left out of a trace: the leaf query found at any place under
any digest stays. -/
theorem extLeaf_notAnn (tr : Trace (typedOracleFamily lam K L)) (d : ℕ) (c : Dig lam) (j : ℕ) :
    TypedOracleCompiler.Compile.Batch.extLeaf (tr.filter notAnnK) d c j = TypedOracleCompiler.Compile.Batch.extLeaf tr d c j := by
  have hp : ∀ e : QA (typedOracleFamily lam K L), notAnnK e = false → e.1 = TypedOracleCompiler.Compile.Batch.OracleName.ann := fun e he
      => by
    simpa [notAnnK] using he
  unfold TypedOracleCompiler.Compile.Batch.extLeaf
  refine Local.preimage_filter (pairM lam K L) notAnnK ?_ ?_ tr _ c
  · rintro ⟨o, q, r⟩ ho
    have h1 : o = TypedOracleCompiler.Compile.Batch.OracleName.ann := hp _ ho
    subst h1
    rfl
  · rintro ⟨o, q, r⟩ ho
    have h1 : o = TypedOracleCompiler.Compile.Batch.OracleName.ann := hp _ ho
    subst h1
    rfl

/-- An announcement in the middle of a trace changes nothing that is found in it. -/
theorem extLeaf_mid_ann (a b : Trace (typedOracleFamily lam K L)) (c : Dig lam) (d : ℕ) (cm : Dig lam) (j : ℕ) :
    TypedOracleCompiler.Compile.Batch.extLeaf (a ++ (annK lam K L c :: b)) d cm j = TypedOracleCompiler.Compile.Batch.extLeaf
        (a ++ b) d cm j := by
  rw [← extLeaf_notAnn (a ++ (annK lam K L c :: b)), ← extLeaf_notAnn (a ++ b)]
  congr 1
  have ha : notAnnK (annK lam K L c) = false := by
    unfold notAnnK
    exact decide_eq_false (fun h => h rfl)
  rw [List.filter_append, List.filter_append,
    List.filter_cons_of_neg (by rw [ha]; exact Bool.false_ne_true)]

/-! ## Under the typed oracles -/

/-- The event: `rt` reads a root off the first output, and at some depth and place the leaf
query found in the first trace under it differs from the one found in both traces, one behind the
other. -/
def movedLeaf (rt : β → Option (Dig lam)) :
    Set ((β × Trace (typedOracleFamily lam K L)) × (δ × Trace (typedOracleFamily lam K L))) :=
  {z | ∃ cm, rt z.1.1 = some cm ∧
    ∃ d j, TypedOracleCompiler.Compile.Batch.extLeaf z.1.2 d cm j ≠ TypedOracleCompiler.Compile.Batch.extLeaf
        (z.1.2 ++ z.2.2) d cm j}

/-- One announcement, or none. -/
def announceK (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Option (Dig lam) → TypedOracleComputation lam K L Unit
  | none => OComp.pure ()
  | some c => OComp.query (S := typedOracleFamily lam K L) TypedOracleCompiler.Compile.Batch.OracleName.ann c fun _ => OComp.pure ()

/-- The entry that `announceK` leaves in a trace; none where there is no root. -/
def annTrK (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) : Option (Dig lam) → Trace (typedOracleFamily lam K L)
  | none => []
  | some c => [annK lam K L c]

/-- The run of `announceK` under fixed oracles, with its trace. -/
theorem announceK_run (F : Fam (typedOracleFamily lam K L)) :
    ∀ y : Option (Dig lam),
      (announceK lam K L y).withTrace.runEager F = PMF.pure ((), annTrK lam K L y)
  | none => rfl
  | some _ => rfl

/-- `announceK` asks at most once. -/
theorem announceK_queryBound : ∀ y : Option (Dig lam), (announceK lam K L y).QueryBound 1
  | none => trivial
  | some _ => fun _ => trivial

/-- The algorithm of the proof: the first, the announcement of the root, the second. It stands in no
statement. -/
def joinedK (B1 : TypedOracleComputation lam K L β) (rt : β → Option (Dig lam)) (B2 : β → TypedOracleComputation lam K L δ) :
    TypedOracleComputation lam K L Unit :=
  B1.bind fun b => (announceK lam K L (rt b)).bind fun _ => (B2 b).bind fun _ => OComp.pure ()

/-- The algorithm of the proof asks at most t1 + 1 + t2 queries. -/
theorem joinedK_queryBound {B1 : TypedOracleComputation lam K L β} (rt : β → Option (Dig lam))
    {B2 : β → TypedOracleComputation lam K L δ} {t1 t2 : ℕ} (h1 : B1.QueryBound t1)
    (h2 : ∀ b, (B2 b).QueryBound t2) : (joinedK B1 rt B2).QueryBound (t1 + 1 + t2) := by
  have h : (joinedK B1 rt B2).QueryBound (t1 + (1 + (t2 + 0))) :=
    h1.bind fun b => (announceK_queryBound (rt b)).bind fun _ => (h2 b).bind fun _ => trivial
  exact h.mono (by omega)

/-- Under the typed random oracles, the leaf queries found under a root that the first algorithm
names do not change when a second algorithm asks on, at any depth and place, except with
probability at most 2 (t1 + 1 + t2)^2 / 2^lam. The 1 stands for one query to the marker oracle in
the proof. -/
theorem stableLeaf_typed (B1 : TypedOracleComputation lam K L β) (rt : β → Option (Dig lam))
    (B2 : β → TypedOracleComputation lam K L δ) (t1 t2 : ℕ) (h1 : B1.QueryBound t1)
    (h2 : ∀ b, (B2 b).QueryBound t2) :
    Rom.Pr (bothExp B1 B2) (fun _ => movedLeaf rt) ≤
      2 * ((t1 + 1 + t2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans ?_ (TypedOracleCompiler.Compile.Batch.hashEvents (joinedK B1 rt B2) _
      (joinedK_queryBound rt h1 h2))
  rw [← Pr_eq_law]
  refine MeasureTheory.lintegral_mono fun F => ?_
  unfold PrCoins
  simp only [bothExp, joinedK, Compile.withTrace_bind, OComp.bind_assoc, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, announceK_run, PMF.pure_bind]
  refine pr_bind_le_bind _ _ _ _ _ fun x _ => pr_bind_le_bind _ _ _ _ _ fun y _ =>
    pr_pure_le_pure ?_
  rintro ⟨cm, hr, d, j, hne⟩
  have hr' : rt x.1 = some cm := hr
  show TypedOracleCompiler.Compile.Batch.EM (x.2 ++ (annTrK lam K L (rt x.1) ++ (y.2 ++ []))) ∨
    TypedOracleCompiler.Compile.Batch.EF (x.2 ++ (annTrK lam K L (rt x.1) ++ (y.2 ++ [])))
  by_contra hnb
  have hEM : ¬ TypedOracleCompiler.Compile.Batch.EM (x.2 ++ (annTrK lam K L (rt x.1) ++ (y.2 ++ []))) :=
    fun h => hnb (Or.inl h)
  rw [hr', List.append_nil] at hEM
  have e1 : x.2 ++ (annTrK lam K L (some cm) ++ y.2) = (x.2 ++ [annK lam K L cm]) ++ y.2 := by
    simp [annTrK]
  rw [e1] at hEM
  have ho : (evM lam K L).OccursIn (x.2 ++ [annK lam K L cm]) cm :=
    ⟨_, List.mem_append_right _ List.mem_cons_self, List.mem_cons_self⟩
  have hs := TypedOracleCompiler.Compile.Batch.extLeaf_stable hEM (List.prefix_append _ _) ho d j
  have e2 : (x.2 ++ [annK lam K L cm]) ++ y.2 = x.2 ++ (annK lam K L cm :: y.2) := by simp
  rw [e2, extLeaf_mid_ann, extLeaf_mid_ann, List.append_nil] at hs
  exact hne hs

/-! ## Over one oracle -/

/-- The event over one oracle: `rt` reads a root off the first output, and at some depth and
place the leaf query found among the one-block entries of the first log under it differs from the
one found among those of both logs, one behind the other. -/
def movedLeafOne (m : OracleCoding (typedOracleFamily lam K L) lam) (rt : β → Option (Dig lam)) :
    Set ((β × Trace (rom lam)) × (δ × Trace (rom lam))) :=
  {z | ∃ cm, rt z.1.1 = some cm ∧ ∃ d j, TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m z.1.2) d cm j ≠
    TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m (z.1.2 ++ z.2.2)) d cm j}

/-- Whether a leaf query has moved is read off the one-block entries of the typed traces alone.
Asked of m: a leaf's and a vertex's answer is one block. -/
theorem movedLeaf_single (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.leaf = 1)
    (hn : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.node = 1) (rt : β → Option (Dig lam)) :
    (movedLeaf rt : Set ((β × Trace (typedOracleFamily lam K L)) × (δ × Trace (typedOracleFamily lam K L)))) =
      (fun z : (β × Trace (typedOracleFamily lam K L)) × (δ × Trace (typedOracleFamily lam K L)) =>
        ((z.1.1, single m z.1.2), (z.2.1, single m z.2.2))) ⁻¹' movedLeaf rt := by
  ext z
  have e : single m z.1.2 ++ single m z.2.2 = single m (z.1.2 ++ z.2.2) :=
    (List.filter_append _ _).symm
  simp only [movedLeaf, Set.mem_setOf_eq, Set.mem_preimage, e, extLeaf_single m hl hn]

/-- Over one random oracle on bit strings, the leaf queries found under a root that the first
algorithm names do not change when a second algorithm asks on, at any depth and place, except with
probability at most 2 (t1 + 1 + t2)^2 / 2^lam. The oracle is a function from all bit strings to
strings of lam bits, each value drawn uniformly and independently. t1 and t2 count strings, a
repeated one again; both algorithms may toss coins; the second sees the first's output. The leaf
queries are found among the one-block entries of the logs through m, any implementation in which a
leaf's and a vertex's answer is one block; a digest in an entry is the oracle's answer read through
`m.rng`. The 1 stands for a query to the marker oracle in the proof. Nothing on any protocol,
language or hash function. The bound says nothing once it reaches 1. -/
theorem stableLeaf_one (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.leaf = 1)
    (hn : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.node = 1) (B1 : OComp (rom lam) β) (rt : β → Option
                                (Dig lam))
    (B2 : β → OComp (rom lam) δ) (t1 t2 : ℕ) (h1 : B1.QueryBound t1)
    (h2 : ∀ b, (B2 b).QueryBound t2) :
    Rom.Pr (bothExp B1 B2) (fun _ => movedLeafOne m rt) ≤
      2 * ((t1 + 1 + t2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have e1 : (movedLeafOne m rt : Set ((β × Trace (rom lam)) × (δ × Trace (rom lam)))) =
      (fun z : (β × Trace (rom lam)) × (δ × Trace (rom lam)) =>
        ((z.1.1, singleTr m z.1.2), (z.2.1, singleTr m z.2.2))) ⁻¹' movedLeaf rt := by
    ext z
    simp only [movedLeafOne, movedLeaf, Set.mem_setOf_eq, Set.mem_preimage, singleTr_append]
  have hF : ∀ F : Fam (typedOracleFamily lam K L),
      PrCoins (glue m F) (bothExp B1 B2) (movedLeafOne m rt) =
        PrCoins F (bothExp (down m B1) fun b => down m (B2 b)) (movedLeaf rt) := fun F => by
    unfold PrCoins
    rw [e1, ← pr_map, bothExp_glue, pr_map, ← movedLeaf_single m hl hn rt]
  have hP : Rom.Pr (bothExp B1 B2) (fun _ => movedLeafOne m rt) =
      Rom.Pr (bothExp (down m B1) fun b => down m (B2 b)) (fun _ => movedLeaf rt) := by
    unfold Rom.Pr
    rw [lintegral_glue m (fun g => PrCoins g (bothExp B1 B2) (movedLeafOne m rt))]
    · simp only [hF]
    · simp only [hF]
      exact measurable_PrCoins _ _
  rw [hP]
  exact stableLeaf_typed (down m B1) rt (fun b => down m (B2 b)) t1 t2
    (queryBound_down m B1 t1 h1) fun b => queryBound_down m (B2 b) t2 (h2 b)

/-! ## The root read off the log too -/

/-- The same with the root read off the first algorithm's output and log. Over one random oracle
on bit strings: C asks at most t1 strings; P, which sees C's output and not its log, asks at most
t2. Except with probability at most 2 (t1 + 1 + t2)^2 / 2^lam, under the digest that `rt` reads off
C's output and log, the leaf query found at every depth and place is the same in C's log as in both
logs, one behind the other. Conditions and limits as in `stableLeaf_one`. -/
theorem stableLeaf_log (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.leaf = 1)
    (hn : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.node = 1) (C : OComp (rom lam) β)
    (rt : β × Trace (rom lam) → Option (Dig lam)) (P : β → OComp (rom lam) δ) (t1 t2 : ℕ)
    (h1 : C.QueryBound t1) (h2 : ∀ b, (P b).QueryBound t2) :
    Rom.Pr (bothExp C P) (fun _ => {z | ∃ cm, rt z.1 = some cm ∧
        ∃ d j, TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m z.1.2) d cm j ≠
          TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m (z.1.2 ++ z.2.2)) d cm j}) ≤
      2 * ((t1 + 1 + t2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := stableLeaf_one m hl hn C.withTrace rt (fun x => P x.1) t1 t2
    (queryBound_withTrace C t1 h1) fun x => h2 x.1
  have e : bothExp C.withTrace (fun x => P x.1) =
      (bothExp C P).bind fun z => OComp.pure ((z.1, z.1.2), z.2) := by
    unfold bothExp
    simp only [withTrace_withTrace, OComp.bind_assoc, OComp.bind]
  rw [e, Rom.Pr_bind_pure] at h
  exact h

/-- What lies under a root in the first algorithm's log stays as the log grows, as an event on the
one experiment. The oracle is drawn; C asks it at most t1 strings; `rt` reads a root off C's
output and log; P, on C's output, asks at most t2. With probability at most 2 (t1 + 1 + t2)^2 /
2^lam there are a depth and a place at which the leaf that is read off C's log under that root
differs from the leaf that is read off the whole log of C and P. The logs are read through m, in
which a leaf's and a vertex's answer is one block. This is `stableLeaf_log` in another form of the
experiment. Conditions and limits as in `stableLeaf_one`. One root: for several, one use for each.
-/
theorem stableLeaf_maker (m : OracleCoding (typedOracleFamily lam K L) lam) (hl : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.leaf = 1)
    (hn : m.blocks TypedOracleCompiler.Compile.Batch.OracleName.node = 1) (C : OComp (rom lam) β)
    (rt : β × Trace (rom lam) → Option (Dig lam)) (P : β → OComp (rom lam) δ) (t1 t2 : ℕ)
    (h1 : C.QueryBound t1) (h2 : ∀ b, (P b).QueryBound t2) :
    Rom.Pr (twoExp C P).withTrace (fun _ => {w | ∃ cm, rt w.1.1 = some cm ∧
        ∃ d j, TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m w.1.1.2) d cm j ≠
          TypedOracleCompiler.Compile.Batch.extLeaf (singleTr m w.2) d cm j}) ≤
      2 * ((t1 + 1 + t2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  rw [twoExp_withTrace, Rom.Pr_bind_pure]
  exact stableLeaf_log m hl hn C rt P t1 t2 h1 h2

end TypedOracleCompiler.Slice
