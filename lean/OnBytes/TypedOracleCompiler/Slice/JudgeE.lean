-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/JudgeE.lean: the judge of OnBytes/TypedOracleCompiler/Slice/JudgeOff.lean for a written batch
protocol under one or two outer roots: it recomputes, for EACH outer root, the part of the instance
that stands in no query, by a second protocol's chain under that root alone; and the analysis'
conclusion on it, for traces that ask first.

`judgeOff` has one root, one chain of the second protocol, one value. The entry has two stored
tables, each with a record whose seeds hang on that table's name, and a name holds one root. So the
second protocol's chain is run once for each outer root, each time under a list of that ONE root;
the instance's second part is k values as one (`Pack`).

Main definitions.
 `Pack k S Sd`, `pack1`, `pack2`   k values of a type S as one value of a type Sd; one value; a
                        pair.
 `chainsT`, `preE`      the second protocol's chain at the fixed string, once for each root of a
                        list; WHAT IS TO BE ASKED FIRST: before a first query under Z's tag, these
                        chains for its first k outer roots. With `preFbE`, `preOnE`.
 `extS1`, `extSE`       the value read off a trace under one root; the k values as one.
 `OutE`, `cmpT`, `judgeRunE`, `judgeE`   what a checker hands to the judge (a LIST of outer roots,
                        the instance, the string); the comparisons; the judge's run; the judge. Its
                        language, of k strings: Lg of the instance and the external string made of
                        them, and `bad₁` false of EACH string and the value of the same number.
 `judgeRunEL`, `judgeEL`   the same with the compiled verifier WITHOUT the test of the strict
                        format.
Main theorems.
 `preE_noCoin`, `preE_queries`, `preE_blind`   THE THREE FIELDS ON `pre` OF `Part.OKAsk`
                        (OnBytes/TypedOracleCompiler/Slice/PartAsk.lean), in their form, at n := k times the second
                        protocol's rounds. From `preE_bound`, `preE_tag`; with `preE_cases`,
                        `preE_f1`, `chainsT_bound`, `chainsT_tag`, `chainsT_sub`, `log_bind`.
 `preE_idle`            it asks nothing for its own queries, if the tags differ.
 `chainsT_ran`, `seedFirstE_of_asksFirst`   `SeedFirstE` from `AsksFirst`.
 `cmpT_bound`, `cmpT_true`   a yes of the comparisons: under each root the chain has run and has
                        yielded the value of the same number.
 `judgeAtAsk_E`         `JudgeAtAsk` (OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean) FOR `judgeE` AT `preE`.
                        With `judgeRunE_bound`, `keepsE_withPaths`.
 `judgeAtAsk_EL`        the same for `judgeEL`, under the same hypotheses.

Asked by `judgeAtAsk_E`: every count of ε and of εT is at most εs; the state function obeys `JointE`
and has the laws `StLawsE` at e; `Z.OK`; as many slots as the request tree at Z's tag has leaves;
k ≤ 2; the first query holds (e x.1, the fixed values) of an instance x AND NO LATER QUERY HOLDS THE
INSTANCE; the two tags differ; the second protocol has a round and what it writes of a plain part is
read back; the lane whose state is "bad₁ y (seedOf ρ)" obeys the laws of a lane, at as many slots as
the request tree at the second protocol's tag has leaves.

So it serves a file only if that file's interface takes the instance in at the first query alone.
What e erases is bound by no query: it is paid by the state function's laws over all instances with
one early part.

THE PRICE. Where `JudgeAtAsk` is used the whole count, the judge's own count among it, which has
grown by k times the second protocol's rounds, is multiplied by 1 + k times these rounds, in both
terms: at a second protocol of two rounds by 3 for one root and BY 5 FOR TWO. The number stands in
`preE_queries`; the product in `Part.boundAsk` (PartAsk.lean), which no declaration here names. ONE
lane of the second protocol serves all roots: it judges every chain under its tag at the string
under that chain's first outer root. So `bad₁` comes out false at every root, also where a caller
needs it at one alone.

Not claimed. NO SOUNDNESS IS PROVED: the laws of the state function and of the second lane are
hypotheses. That they are met together by a language other than "true" and a test other than "false"
is shown by nothing. No protocol, no second protocol, no `seedOf`, no `bad₁`, no fixed string:
nothing speaks of a record, of a file, or of the program. At a fixed string with too few roots the
second protocol's chain refuses, and the judge refuses everything. The second lane's count is over
the second protocol's verifier's messages, through `seedOf`. No part is made. That `judgeOff` is
`judgeE` at one root: by reading; `OutE` has a list of roots where `BatchOut` has one. That the
judge ever says yes. The form has "there is a set": it is for use in one world (see `JudgeAt`). What
the heads of WrittenE.lean, JudgeOff.lean, SeedFirstAsk.lean and SeedLane.lean do not claim. The
compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.WrittenE
import OnBytes.TypedOracleCompiler.Slice.JudgeOff

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (AsksFirst asksFirst_before lenB)
open scoped ENNReal

/-! ## k values as one -/

/-- k values of a type S as one value of a type Sd. -/
structure Pack (k : ℕ) (S Sd : Type) where
  /-- the one value, from the values number 0, 1, .. -/
  asm : (ℕ → S) → Sd
  /-- value number i of the one -/
  get : Sd → ℕ → S
  /-- the values come back (no proof in this file uses it) -/
  get_asm : ∀ f i, i < k → get (asm f) i = f i
  /-- the one value is made of its values -/
  asm_get : ∀ s, asm (get s) = s
  /-- it hangs on the first k values alone -/
  asm_congr : ∀ f g, (∀ i, i < k → f i = g i) → asm f = asm g

/-- One value. -/
def pack1 (S : Type) : Pack 1 S S where
  asm := fun f => f 0
  get := fun s _ => s
  get_asm := fun _ i hi => by
    obtain rfl : i = 0 := by omega
    rfl
  asm_get := fun _ => rfl
  asm_congr := fun _ _ h => h 0 Nat.one_pos

/-- Two values as a pair. -/
def pack2 (S : Type) : Pack 2 S (S × S) where
  asm := fun f => (f 0, f 1)
  get := fun s i => if i = 0 then s.1 else s.2
  get_asm := fun _ i hi => by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rfl
    · rfl
  asm_get := fun _ => rfl
  asm_congr := fun _ _ h => Prod.ext (h 0 (by decide)) (h 1 (by decide))

/-! ## A law on logs -/

/-- The log of two algorithms, one after the other. -/
theorem log_bind {S : OSpec} {α β : Type} (g : Fam S) (c : OComp S α) (k : α → OComp S β) :
    ((c.bind k).withTrace.det g).2 =
      (c.withTrace.det g).2 ++ ((k (c.withTrace.det g).1).withTrace.det g).2 := by
  rw [Rom.withTrace_bind, OComp.det_bind, OComp.det_bind]
  rfl

variable {I A Sd S : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L} {Ex : ExtRd L}

/-! ## The second protocol's chain, once for each outer root -/

section
variable (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
  (plainsT : Plains ZT.P.shape)

/-- The second protocol's chain at the fixed string, once for each root of a list, each time under
that root alone. -/
def chainsT : List (Dig lam) → TypedOracleComputation lam W.K L Unit
  | [] => OComp.pure ()
  | c :: l => (ZT.chainT saltT rtT rootsT plainsT [c]).bind fun _ => chainsT l

/-- It tosses no coin and asks at most as many queries as the list has roots, times the second
protocol's rounds. -/
theorem chainsT_bound : ∀ l : List (Dig lam),
    DetBound (chainsT ZT saltT rtT rootsT plainsT l) (l.length * ZT.P.shape.length)
  | [] => detBound_pure _ _
  | c :: l => by
    have h := DetBound.bind (chainB_lo ZT.t [c] none saltT rtT ZT.P.shape
      (RoundSplits.allLocal ZT.P.shape) ZT.wq.sh ZT.embP 0 .first rootsT plainsT (allLoA_allLocal _)).1
      fun _ => chainsT_bound l
    refine DetBound.mono h ?_
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- Every entry of its log stands at the challenge oracle of the second protocol's tag. -/
theorem chainsT_tag (g : Fam (typedOracleFamily lam W.K L)) : ∀ l : List (Dig lam),
    ∀ x ∈ ((chainsT ZT saltT rtT rootsT plainsT l).withTrace.det g).2,
      x.1 = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t
  | [], x, hx => by cases hx
  | c :: l, x, hx => by
    have hx' : x ∈ (((ZT.chainT saltT rtT rootsT plainsT [c]).bind fun _ =>
      chainsT ZT saltT rtT rootsT plainsT l).withTrace.det g).2 := hx
    rw [log_bind] at hx'
    rcases List.mem_append.1 hx' with h | h
    · exact chainAt_log ZT.t _ ZT.wq ZT.embP none saltT rtT rootsT plainsT [c]
        (allLoA_allLocal _) g x h
    · exact chainsT_tag g l x h

/-- The log of the chain under a root of the list is part of its log. -/
theorem chainsT_sub (g : Fam (typedOracleFamily lam W.K L)) : ∀ (l : List (Dig lam)) (c : Dig lam), c ∈ l →
    ((ZT.chainT saltT rtT rootsT plainsT [c]).withTrace.det g).2 ⊆
      ((chainsT ZT saltT rtT rootsT plainsT l).withTrace.det g).2
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, c, h => by
    show _ ⊆ (((ZT.chainT saltT rtT rootsT plainsT [a]).bind fun _ =>
      chainsT ZT saltT rtT rootsT plainsT l).withTrace.det g).2
    rw [log_bind]
    rcases List.mem_cons.1 h with rfl | h2
    · exact List.subset_append_left _ _
    · exact (chainsT_sub g l c h2).trans (List.subset_append_right _ _)

variable (Z : WrittenE W Ex)

/-- What is to be asked before a challenge query under the tag t. -/
def preFbE (t : Tag) (q : FbIn lam L t) : TypedOracleComputation lam W.K L Unit :=
  if t = Z.t then
    match f1Roots q.head with
    | some cms => chainsT ZT saltT rtT rootsT plainsT (cms.take Ex.k)
    | none => OComp.pure ()
  else OComp.pure ()

/-- `preE`, by the oracle's name. -/
def preOnE : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf lam L o → TypedOracleComputation lam W.K L Unit
  | .fb t, q => preFbE ZT saltT rtT rootsT plainsT Z t q
  | _, _ => OComp.pure ()

/-- What is to be asked first: before a first query under Z's tag: the second protocol's chain
at the fixed string, once for each of the first k outer roots of that query, each time under that
root alone. Before any other query: nothing. -/
def preE (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) : TypedOracleComputation lam W.K L Unit :=
  preOnE ZT saltT rtT rootsT plainsT Z o q

/-- What it is: the chains for a list of at most k roots. -/
theorem preE_cases (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    ∃ l : List (Dig lam), l.length ≤ Ex.k ∧
      preE ZT saltT rtT rootsT plainsT Z o q = chainsT ZT saltT rtT rootsT plainsT l := by
  cases o with
  | fb t =>
    show ∃ l : List (Dig lam), l.length ≤ Ex.k ∧ preFbE ZT saltT rtT rootsT plainsT Z t q = _
    unfold preFbE
    by_cases ht : t = Z.t
    · rw [if_pos ht]
      cases f1Roots (FbIn.head q) with
      | none => exact ⟨[], Nat.zero_le _, rfl⟩
      | some cms => exact ⟨cms.take Ex.k, by rw [List.length_take]; exact Nat.min_le_left _ _, rfl⟩
    · rw [if_neg ht]
      exact ⟨[], Nat.zero_le _, rfl⟩
  | _ => exact ⟨[], Nat.zero_le _, rfl⟩

/-- At a first query under Z's tag. -/
theorem preE_f1 (q : FbIn lam L Z.t) (cms : List (Dig lam)) (x : Option (A × Sd)) (s : Bits)
    (h : q.head = .f1 cms x s) :
    preE ZT saltT rtT rootsT plainsT Z (.fb Z.t) q =
      chainsT ZT saltT rtT rootsT plainsT (cms.take Ex.k) := by
  show preFbE ZT saltT rtT rootsT plainsT Z Z.t q = _
  unfold preFbE
  rw [if_pos rfl, h]
  rfl

/-- It tosses no coin and asks at most k times the second protocol's rounds. -/
theorem preE_bound (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    DetBound (preE ZT saltT rtT rootsT plainsT Z o q) (Ex.k * ZT.P.shape.length) := by
  obtain ⟨l, hl, e⟩ := preE_cases ZT saltT rtT rootsT plainsT Z o q
  rw [e]
  exact (chainsT_bound ZT saltT rtT rootsT plainsT l).mono (Nat.mul_le_mul_right _ hl)

/-- It tosses no coin: in the form of the field `preNoCoin` of `Part.OKAsk`
(OnBytes/TypedOracleCompiler/Slice/PartAsk.lean). -/
theorem preE_noCoin (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    (preE ZT saltT rtT rootsT plainsT Z o q).NoCoin :=
  noCoin_of_detBound (preE_bound ZT saltT rtT rootsT plainsT Z o q)

/-- It asks at most k times the second protocol's rounds: in the form of the field `preQueries`,
at n := that number. -/
theorem preE_queries (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    (preE ZT saltT rtT rootsT plainsT Z o q).QueryBound (Ex.k * ZT.P.shape.length) :=
  (preE_bound ZT saltT rtT rootsT plainsT Z o q).queryBound

/-- Every entry of its log stands at the challenge oracle of the second protocol's tag. -/
theorem preE_tag (g : Fam (typedOracleFamily lam W.K L)) (o : (typedOracleFamily lam W.K L).ι)
    (q : (typedOracleFamily lam W.K L).Dom o) :
    ∀ x ∈ ((preE ZT saltT rtT rootsT plainsT Z o q).withTrace.det g).2,
      x.1 = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t := by
  obtain ⟨l, -, e⟩ := preE_cases ZT saltT rtT rootsT plainsT Z o q
  rw [e]
  exact chainsT_tag ZT saltT rtT rootsT plainsT g l

/-- If the two tags differ it asks nothing for its own queries. -/
theorem preE_idle (hne : ZT.t ≠ Z.t) (g : Fam (typedOracleFamily lam W.K L)) (o : (typedOracleFamily lam W.K L).ι)
    (q : (typedOracleFamily lam W.K L).Dom o) :
    ∀ x ∈ ((preE ZT saltT rtT rootsT plainsT Z o q).withTrace.det g).2,
      ((preE ZT saltT rtT rootsT plainsT Z x.1 x.2.1).withTrace.det g).2 = [] := by
  intro x hx
  obtain ⟨xo, xq, xr⟩ := x
  have h : xo = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t :=
    preE_tag ZT saltT rtT rootsT plainsT Z g o q _ hx
  subst h
  have e : preE ZT saltT rtT rootsT plainsT Z (.fb ZT.t) xq = OComp.pure () := by
    show preFbE ZT saltT rtT rootsT plainsT Z ZT.t xq = _
    unfold preFbE
    rw [if_neg hne]
  show ((preE ZT saltT rtT rootsT plainsT Z (.fb ZT.t) xq).withTrace.det g).2 = []
  rw [e]
  rfl

/-- If the two tags differ: in a trace that asks first, before a first query under Z's tag the chain
under each of that query's first k outer roots has run to its end (which may be a refusal). -/
theorem chainsT_ran (hne : ZT.t ≠ Z.t) (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W)
    (hA : AsksFirst (preE ZT saltT rtT rootsT plainsT Z) F tr) (a b : Tc W)
    (q : FbIn lam L Z.t) (r : FsAns lam W.K) (cms : List (Dig lam)) (x : Option (A × Sd))
    (s : Bits) (hq : q.head = .f1 cms x s) (htr : tr = a ++ fbE Z.t q r :: b) (c : Dig lam)
    (hc : c ∈ cms.take Ex.k) : ∃ z, RunsIn a (ZT.chainT saltT rtT rootsT plainsT [c]) z := by
  have h1 := asksFirst_before (preE ZT saltT rtT rootsT plainsT Z) F tr hA
    (preE_idle ZT saltT rtT rootsT plainsT Z hne F) a (fbE Z.t q r) b htr
  have e : ((preE ZT saltT rtT rootsT plainsT Z (fbE Z.t q r).1
      (fbE Z.t q r).2.1).withTrace.det F).2 =
      ((chainsT ZT saltT rtT rootsT plainsT (cms.take Ex.k)).withTrace.det F).2 := by
    show ((preE ZT saltT rtT rootsT plainsT Z (.fb Z.t) q).withTrace.det F).2 = _
    rw [preE_f1 ZT saltT rtT rootsT plainsT Z q cms x s hq]
  rw [e] at h1
  exact ⟨_, (runsIn_det_log F _ (chainAt_noCoin ZT.t _ ZT.wq ZT.embP none saltT rtT rootsT plainsT
    [c] (allLoA_allLocal _))).mono
      ((chainsT_sub ZT saltT rtT rootsT plainsT F _ c hc).trans h1)⟩

/-! ## The value read off a trace -/

variable (seedOf : Rho ZT.P.shape → S) (d₁ : S) (Pk : Pack Ex.k S Sd)

/-- The value read off a trace under one root: `seedOf` of the verifier's messages that the chain at
the fixed string yields in the trace; d₁ where it has not run or refuses. -/
def extS1 : Tc W → List (Dig lam) → S :=
  extSOf ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT seedOf d₁

/-- The values read off a trace under the outer roots, as one: value number i is read under root
number i alone. -/
def extSE (tr : Tc W) (cms : List (Dig lam)) : Sd :=
  Pk.asm fun i => extS1 ZT saltT rtT rootsT plainsT seedOf d₁ tr [cms.getD i default]

/-- `SeedFirstE` from `AsksFirst`: if the two tags differ, each query of the trace has one
answer, and the trace asks first at `preE`. Asked: there are k outer roots. -/
theorem seedFirstE_of_asksFirst (hne : ZT.t ≠ Z.t) (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W)
    (h1 : OneAns tr) (hA : AsksFirst (preE ZT saltT rtT rootsT plainsT Z) F tr)
    (cms : List (Dig lam)) (hlen : cms.length = Ex.k) (x : A × Sd) (π : OneProtocolProof lam Z.Q) :
    SeedFirstE Z (extSE ZT saltT rtT rootsT plainsT seedOf d₁ Pk) tr cms x π := by
  intro pre q a post l cur htr ho
  have hs : pre ⊆ tr := by
    rw [htr]
    exact List.subset_append_left _ _
  refine Pk.asm_congr _ _ fun i hi => ?_
  have hm : cms.getD i default ∈ cms.take Ex.k :=
    getD_mem_take default cms i Ex.k (hlen ▸ hi) hi
  have hran : ∃ z, RunsIn pre (ZT.chainT saltT rtT rootsT plainsT [cms.getD i default]) z := by
    rcases ours_first _ ho with ⟨s, hq⟩ | ⟨q1, a1, s, hm1, hq⟩
    · exact chainsT_ran ZT saltT rtT rootsT plainsT Z hne F tr hA pre post q a cms _ s hq htr _ hm
    · obtain ⟨u, v, rfl⟩ := List.append_of_mem hm1
      obtain ⟨z, hz⟩ := chainsT_ran ZT saltT rtT rootsT plainsT Z hne F tr hA u
        (v ++ fbE Z.t q a :: post) q1 a1 cms _ s hq (by rw [htr]; simp) _ hm
      exact ⟨z, hz.mono (List.subset_append_left _ _)⟩
  obtain ⟨z, hz⟩ := hran
  exact extSOf_stable ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT
    seedOf d₁ h1 hs [cms.getD i default] hz

end

/-! ## The judge -/

section
variable [DecidableEq S] (Z : WrittenE W Ex) (ZT : Written W) (saltT : Bits) (rtT : Dig lam)
  (rootsT : List (Dig lam)) (plainsT : Plains ZT.P.shape) (seedOf : Rho ZT.P.shape → S)
  (Pk : Pack Ex.k S Sd) (sMT sFS : ℕ)

/-- For each root of a list: the second protocol's chain at the fixed string under that root alone;
a no if it refuses, or if the value that it yields is not the value of the same number in s (counted
from i). -/
def cmpT : List (Dig lam) → ℕ → Sd → TypedOracleComputation lam W.K L Bool
  | [], _, _ => OComp.pure true
  | c :: l, i, s => (ZT.chainT saltT rtT rootsT plainsT [c]).bind fun z =>
      match z with
      | some y => if seedOf y.1 = Pk.get s i then cmpT l (i + 1) s else OComp.pure false
      | none => OComp.pure false

/-- It tosses no coin and asks at most as many queries as the list has roots, times the second
protocol's rounds. -/
theorem cmpT_bound : ∀ (l : List (Dig lam)) (i : ℕ) (s : Sd),
    DetBound (cmpT ZT saltT rtT rootsT plainsT seedOf Pk l i s) (l.length * ZT.P.shape.length)
  | [], _, _ => detBound_pure _ _
  | c :: l, i, s => by
    have h := DetBound.bind (t := l.length * ZT.P.shape.length)
      (g := fun z : Option (Rho ZT.P.shape × RootsOfChain lam ZT.P.shape × Phase lam) =>
        match z with
        | some y => if seedOf y.1 = Pk.get s i then
            cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false
        | none => OComp.pure false)
      (chainB_lo ZT.t [c] none saltT rtT ZT.P.shape
        (RoundSplits.allLocal ZT.P.shape) ZT.wq.sh ZT.embP 0 .first rootsT plainsT (allLoA_allLocal _)).1
      fun z => by
        cases z with
        | none => exact detBound_pure _ _
        | some y =>
          show DetBound (if seedOf y.1 = Pk.get s i then
            cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false) _
          split
          · exact cmpT_bound l (i + 1) s
          · exact detBound_pure _ _
    refine DetBound.mono h ?_
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- If it says yes in a trace, then under each root of the list the chain has run in the trace,
and has yielded the value of the same number in s. -/
theorem cmpT_true {tr : Tc W} : ∀ (l : List (Dig lam)) (i : ℕ) (s : Sd),
    RunsIn tr (cmpT ZT saltT rtT rootsT plainsT seedOf Pk l i s) true →
    ∀ j, j < l.length → ∃ ρ rts ph,
      RunsIn tr (ZT.chainT saltT rtT rootsT plainsT [l.getD j default]) (some (ρ, rts, ph)) ∧
        seedOf ρ = Pk.get s (i + j)
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: l, i, s, h, j, hj => by
    obtain ⟨z, hz, h2⟩ := (runsIn_bind_iff _ _ _).1 h
    cases z with
    | none => cases runsIn_pure_iff.1 h2
    | some y0 =>
      obtain ⟨ρ, rts, ph⟩ := y0
      have h3 : RunsIn tr (if seedOf ρ = Pk.get s i then
          cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false) true := h2
      by_cases hs : seedOf ρ = Pk.get s i
      · rw [if_pos hs] at h3
        cases j with
        | zero => exact ⟨ρ, rts, ph, hz, hs⟩
        | succ j =>
          obtain ⟨ρ', rts', ph', h4, h5⟩ := cmpT_true l (i + 1) s h3 j (Nat.lt_of_succ_lt_succ hj)
          exact ⟨ρ', rts', ph', h4, by rw [h5]; congr 1; omega⟩
      · rw [if_neg hs] at h3
        cases runsIn_pure_iff.1 h3

/-- What a checker hands to the judge: the outer roots, the instance, the string. -/
abbrev OutE : Type := List (Dig lam) × (A × Sd) × OneProtocolProof lam Z.Q

/-- The judge's run: for each of the first k outer roots the second protocol's chain under that
root alone, compared with the value of the same number in the instance's second part; then the
compiled verifier with the strict format, under all outer roots. -/
def judgeRunE (o : OutE Z) : TypedOracleComputation lam W.K L Bool :=
  (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).bind fun b =>
    if b then Z.verifierS sMT sFS o.1 o.2.1 o.2.2 else OComp.pure false

/-- It tosses no coin and asks at most k times the second protocol's rounds, and what the compiled
verifier asks. -/
theorem judgeRunE_bound (o : OutE Z) :
    DetBound (judgeRunE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS o)
      (Ex.k * ZT.P.shape.length + tVQB Z.wq (W.dReq Z.t)) := by
  refine DetBound.bind ((cmpT_bound ZT saltT rtT rootsT plainsT seedOf Pk _ 0 _).mono
    (Nat.mul_le_mul_right _ (by rw [List.length_take]; exact Nat.min_le_left _ _))) fun b => ?_
  cases b with
  | false => exact detBound_pure _ _
  | true => exact detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

variable (R : Reading L W.embE) (Lg : A × Sd → Ex.Str → Prop)
  (bad₁ : (Fin L.wordLength → L.Symbol) → S → Bool)

/-- That run as a judge. Its language, of k strings: Lg holds of the instance and the external
string made of them, and `bad₁` is false of EACH string and the value of the same number in the
instance's second part. On a list of fewer than k strings the language holds for free; `ok` asks k
roots. What a checker owes beside the run's yes: k outer roots, and external openings that R keeps.
-/
def judgeE : Judge W (OutE Z) where
  run := judgeRunE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS
  tV := Ex.k * ZT.P.shape.length + tVQB Z.wq (W.dReq Z.t)
  bound := judgeRunE_bound Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS
  roots := fun o => o.1
  R := R
  Lang := fun o ys => ∀ f : ℕ → Fin L.wordLength → L.Symbol, (∀ i, i < Ex.k → ys[i]? = some (f i)) →
    Lg o.2.1 (Ex.asm f) ∧ ∀ i, i < Ex.k → bad₁ (f i) (Pk.get o.2.1.2 i) = false
  ok := fun o => o.1.length = Ex.k ∧ KeepsE Z R o.2.2

/-- A string with other paths in its openings has the same symbols and salts there. -/
theorem keepsE_withPaths (π : OneProtocolProof lam Z.Q) (P1 : OPos Z.Q.loc.shape → List (Dig lam))
    (P2 : Ex.Pos → List (Dig lam)) (hk : KeepsE Z R π) : KeepsE Z R (π.withPaths P1 P2) := by
  intro p op h
  have h' : (π.ext p).map (fun o => (⟨o.sym, o.salt, P2 p⟩ : Opening lam L.Symbol)) = some op := h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact hk p o ho

/-- THE ANALYSIS' CONCLUSION ON THAT JUDGE, FOR TRACES THAT ASK FIRST AT `preE`. What is asked:
see the file's head. -/
theorem judgeAtAsk_E (e : A → A) (d₁ : S) (ε : Err Z.Q.loc.shape)
    (State : Ex.Str → A × Sd → PTr Z.Q.loc.shape → Bool) (εT : Err ZT.P.shape) (εs : ℝ≥0∞)
    (hb : Err.Below ε εs) (hJ : JointE Z ε State) (hS : StLawsE Z e State Lg) (hZ : Z.OK)
    (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) {NT : ℕ} (hNT : NT = 2 ^ (W.dReq ZT.t)) (hk2 : Ex.k ≤ 2)
    (hE : ∀ x, L.early x = (e x.1, Pk.asm fun _ => d₁)) (hl : L.late = none) (hne : ZT.t ≠ Z.t)
    (hneT : ZT.P.shape ≠ []) (hP : ∀ z, ZT.prjP (ZT.embP z) = some z)
    (oT : (ZT.laneBad R εT fun y ρ => bad₁ y (seedOf ρ)).OK NT) (bT : Err.Below εT εs) :
    JudgeAtAsk W (judgeE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS R Lg bad₁) εs
      (preE ZT saltT rtT rootsT plainsT Z) := by
  refine ⟨badE Z R (extSE ZT saltT rtT rootsT plainsT seedOf d₁ Pk) (Pk.asm fun _ => d₁) ε State
      (ZT.laneBad R εT fun y ρ => bad₁ y (seedOf ρ)),
    fun β Alg t hA => badE_rare Z R _ _ ε State _ εs hb hJ hZ hN hNT hne.symm oT bT β Alg t hA,
    badE_mono Z R _ _ ε State _, fun F tr o hB hA _ hok hrun f hf => ?_,
    fun tr tr' cm hB hann => badE_stable Z R _ _ ε State _ tr tr' cm hB hann⟩
  obtain ⟨hlen, hkeep⟩ := hok
  have hlen' : o.1.length = Ex.k := hlen
  obtain ⟨hM, hF, -, hS2, h1⟩ := not_bad3 hB
  have hfi : ∀ i, i < Ex.k → f i = R.at W tr (o.1.getD i default) := fun i hi => by
    have h2 := hf i hi
    have h3 : ((o.1.map (R.at W tr))[i]? : Option _) = some (f i) := h2
    rw [List.getElem?_map] at h3
    have hi' : i < o.1.length := hlen' ▸ hi
    rw [List.getElem?_eq_getElem hi'] at h3
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    exact (Option.some.inj h3).symm
  have hasm : Ex.asm f = Ex.read R tr o.1 := Ex.asm_congr _ _ hfi
  obtain ⟨b, hb1, hb2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  cases b with
  | false => cases runsIn_pure_iff.1 hb2
  | true =>
    have h3 : RunsIn tr (Z.verifierS sMT sFS o.1 o.2.1 o.2.2) true := hb2
    have hall := cmpT_true ZT saltT rtT rootsT plainsT seedOf Pk _ 0 _ hb1
    have htake : o.1.take Ex.k = o.1 := by rw [← hlen', List.take_length]
    rw [htake] at hall
    obtain ⟨P1, P2, h4⟩ := runsIn_verifyB_of_strict hZ.wire h3
    have he : extSE ZT saltT rtT rootsT plainsT seedOf d₁ Pk tr o.1 = o.2.1.2 := by
      rw [← Pk.asm_get o.2.1.2]
      refine Pk.asm_congr _ _ fun i hi => ?_
      obtain ⟨ρ, rts, ph, hz, hs⟩ := hall i (hlen' ▸ hi)
      rw [Nat.zero_add] at hs
      rw [← hs]
      exact extSOf_run ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT
        seedOf d₁ h1 [o.1.getD i default] hz
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hasm]
      exact (badE_lang Z R _ _ ε State _ e Lg hS hZ hE hl tr o.1 hlen' hk2 o.2.1
        (o.2.2.withPaths P1 P2) hB (keepsE_withPaths Z R o.2.2 P1 P2 hkeep) h4
        (seedFirstE_of_asksFirst ZT saltT rtT rootsT plainsT Z seedOf d₁ Pk hne F tr h1 hA o.1
          hlen' o.2.1 _)).resolve_left fun h => h he
    · obtain ⟨ρ, rts, ph, hz, hs⟩ := hall i (hlen' ▸ hi)
      rw [Nat.zero_add] at hs
      rw [hfi i hi, ← hs]
      exact no_coll ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) hneT ZT.wq ZT.embP (fun _ => none)
        (fun y ρ => bad₁ y (seedOf ρ)) ZT.prjS ZT.prjP hP (fun _ => some ())
        (fun tr cms => R.at W tr (cms.getD 0 default)) εT hM hF hS2
        [o.1.getD i default] () saltT rtT 0 rootsT plainsT (fun _ => ()) (fun _ => rfl)
        (fun _ _ h => absurd rfl h) hz
        (fun c hc => by
          rw [slotVal_none_local ZT.P.shape ZT.wq.sh ZT.embP 0 .first ph rootsT plainsT ρ rts rfl
            hz] at hc
          cases hc)
        (fun pre q a post l cur htr ho => R.at_before htr hM (ours_cms _ a ho _ (by simp)))

/-! ### The same with the verifier without the strict format -/

/-- The judge's run with the compiled verifier WITHOUT the test of the strict format (whole paths).
-/
def judgeRunEL (o : OutE Z) : TypedOracleComputation lam W.K L Bool :=
  (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).bind fun b =>
    if b then Z.verifier o.1 o.2.1 o.2.2 else OComp.pure false

/-- It tosses no coin and asks at most k times the second protocol's rounds, and what the compiled
verifier asks. -/
theorem judgeRunEL_bound (o : OutE Z) :
    DetBound (judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk o)
      (Ex.k * ZT.P.shape.length + tVQB Z.wq (W.dReq Z.t)) := by
  refine DetBound.bind ((cmpT_bound ZT saltT rtT rootsT plainsT seedOf Pk _ 0 _).mono
    (Nat.mul_le_mul_right _ (by rw [List.length_take]; exact Nat.min_le_left _ _))) fun b => ?_
  cases b with
  | false => exact detBound_pure _ _
  | true => exact detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

/-- That run as a judge: `judgeE` but for the run. -/
def judgeEL : Judge W (OutE Z) :=
  { judgeE Z ZT saltT rtT rootsT plainsT seedOf Pk 0 0 R Lg bad₁ with
    run := judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk
    bound := judgeRunEL_bound Z ZT saltT rtT rootsT plainsT seedOf Pk }

/-- THE ANALYSIS' CONCLUSION ON THAT JUDGE: under the hypotheses of `judgeAtAsk_E`. -/
theorem judgeAtAsk_EL (e : A → A) (d₁ : S) (ε : Err Z.Q.loc.shape)
    (State : Ex.Str → A × Sd → PTr Z.Q.loc.shape → Bool) (εT : Err ZT.P.shape) (εs : ℝ≥0∞)
    (hb : Err.Below ε εs) (hJ : JointE Z ε State) (hS : StLawsE Z e State Lg) (hZ : Z.OK)
    (hN : L.maxBatchSize = 2 ^ (W.dReq Z.t)) {NT : ℕ} (hNT : NT = 2 ^ (W.dReq ZT.t)) (hk2 : Ex.k ≤ 2)
    (hE : ∀ x, L.early x = (e x.1, Pk.asm fun _ => d₁)) (hl : L.late = none) (hne : ZT.t ≠ Z.t)
    (hneT : ZT.P.shape ≠ []) (hP : ∀ z, ZT.prjP (ZT.embP z) = some z)
    (oT : (ZT.laneBad R εT fun y ρ => bad₁ y (seedOf ρ)).OK NT) (bT : Err.Below εT εs) :
    JudgeAtAsk W (judgeEL Z ZT saltT rtT rootsT plainsT seedOf Pk R Lg bad₁) εs
      (preE ZT saltT rtT rootsT plainsT Z) := by
  refine ⟨badE Z R (extSE ZT saltT rtT rootsT plainsT seedOf d₁ Pk) (Pk.asm fun _ => d₁) ε State
      (ZT.laneBad R εT fun y ρ => bad₁ y (seedOf ρ)),
    fun β Alg t hA => badE_rare Z R _ _ ε State _ εs hb hJ hZ hN hNT hne.symm oT bT β Alg t hA,
    badE_mono Z R _ _ ε State _, fun F tr o hB hA _ hok hrun f hf => ?_,
    fun tr tr' cm hB hann => badE_stable Z R _ _ ε State _ tr tr' cm hB hann⟩
  obtain ⟨hlen, hkeep⟩ := hok
  have hlen' : o.1.length = Ex.k := hlen
  obtain ⟨hM, hF, -, hS2, h1⟩ := not_bad3 hB
  have hfi : ∀ i, i < Ex.k → f i = R.at W tr (o.1.getD i default) := fun i hi => by
    have h2 := hf i hi
    have h3 : ((o.1.map (R.at W tr))[i]? : Option _) = some (f i) := h2
    rw [List.getElem?_map] at h3
    have hi' : i < o.1.length := hlen' ▸ hi
    rw [List.getElem?_eq_getElem hi'] at h3
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    exact (Option.some.inj h3).symm
  have hasm : Ex.asm f = Ex.read R tr o.1 := Ex.asm_congr _ _ hfi
  obtain ⟨b, hb1, hb2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  cases b with
  | false => cases runsIn_pure_iff.1 hb2
  | true =>
    have h4 : RunsIn tr (Z.verifier o.1 o.2.1 o.2.2) true := hb2
    have hall := cmpT_true ZT saltT rtT rootsT plainsT seedOf Pk _ 0 _ hb1
    have htake : o.1.take Ex.k = o.1 := by rw [← hlen', List.take_length]
    rw [htake] at hall
    have he : extSE ZT saltT rtT rootsT plainsT seedOf d₁ Pk tr o.1 = o.2.1.2 := by
      rw [← Pk.asm_get o.2.1.2]
      refine Pk.asm_congr _ _ fun i hi => ?_
      obtain ⟨ρ, rts, ph, hz, hs⟩ := hall i (hlen' ▸ hi)
      rw [Nat.zero_add] at hs
      rw [← hs]
      exact extSOf_run ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT
        seedOf d₁ h1 [o.1.getD i default] hz
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hasm]
      exact (badE_lang Z R _ _ ε State _ e Lg hS hZ hE hl tr o.1 hlen' hk2 o.2.1 o.2.2 hB hkeep h4
        (seedFirstE_of_asksFirst ZT saltT rtT rootsT plainsT Z seedOf d₁ Pk hne F tr h1 hA o.1
          hlen' o.2.1 _)).resolve_left fun h => h he
    · obtain ⟨ρ, rts, ph, hz, hs⟩ := hall i (hlen' ▸ hi)
      rw [Nat.zero_add] at hs
      rw [hfi i hi, ← hs]
      exact no_coll ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) hneT ZT.wq ZT.embP (fun _ => none)
        (fun y ρ => bad₁ y (seedOf ρ)) ZT.prjS ZT.prjP hP (fun _ => some ())
        (fun tr cms => R.at W tr (cms.getD 0 default)) εT hM hF hS2
        [o.1.getD i default] () saltT rtT 0 rootsT plainsT (fun _ => ()) (fun _ => rfl)
        (fun _ _ h => absurd rfl h) hz
        (fun c hc => by
          rw [slotVal_none_local ZT.P.shape ZT.wq.sh ZT.embP 0 .first ph rootsT plainsT ρ rts rfl
            hz] at hc
          cases hc)
        (fun pre q a post l cur htr ho => R.at_before htr hM (ours_cms _ a ho _ (by simp)))

omit [DecidableEq S] in
/-- Every reading is blind to what `preE` asks: in the form of the field `blind` of `Part.OKAsk`
(OnBytes/TypedOracleCompiler/Slice/PartAsk.lean). -/
theorem preE_blind (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W) (cm : Dig lam) :
    R.at W (lenB (preE ZT saltT rtT rootsT plainsT Z) F tr) cm = R.at W tr cm :=
  R.at_lenB W _ F (fun o q x hx => by
    obtain ⟨xo, xq, xr⟩ := x
    have h : xo = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t :=
      preE_tag ZT saltT rtT rootsT plainsT Z F o q _ hx
    subst h
    rfl) tr cm

end

end TypedOracleCompiler.Slice
