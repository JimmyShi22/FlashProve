-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/SeedFirstAsk.lean: in a trace that asks first, if the two protocols stand under
different tags and each query of the trace has one answer, the value that a second protocol's chain
draws from an outer root is read the same before and after every query of a chain that begins with
that root: `SeedFirst` (OnBytes/TypedOracleCompiler/Slice/BatchClauseOff.lean) from `AsksFirst`
(OnBytes/Slice/WrapBetween.lean).

`batBadOff_lang` has a hypothesis on the trace, `SeedFirst`, which a maker can break at no cost.
OnBytes/TypedOracleCompiler/Slice/OneWorldAsk.lean wraps the whole algorithm of its proof, so that before each typed
query stands what a given `pre` asks for it; its clause on accepted strings is then asked only of
traces that ask first. This file gives the `pre` and draws `SeedFirst` from that.
 - `runsIn_det_log`: an algorithm without coins runs in its own log; `log_bind_unit`: dropping the
   value does not change the log;
 - `Written.chainT`, `Written.extSW`: a written second protocol's chain at one fixed string (no
   instance; salt, request root, roots and plain parts fixed), under given outer roots; the value
   read off a trace: `seedOf` of the verifier's messages that this chain yields in the trace, d
   where it has not run (the sibling's `extSOf`);
 - `preSeed` (through `f1Roots`, `preSeedFb`, `preSeedOn`): before a first query under Z's tag (head
   `.f1 cms _ _`): that chain under cms; before any other query: nothing; `preSeed_cases`,
   `preSeed_f1`;
 - `preSeed_noCoin`, `preSeed_queries`, `preSeed_tag`, `preSeed_idle`: it tosses no coin, asks at
   most as many queries as ZT has rounds, asks under ZT's tag alone, and, if the two tags differ,
   asks nothing for its own queries;
 - `seedFirst_of_asksFirst`: IF the two tags differ, each query of the trace has one answer, and the
   trace asks first at `preSeed`: `SeedFirst` holds for every root, instance and string;
 - `batBadOff_lang_ask`: so, under the conditions of `batBadOff_lang`, if the two tags differ:
   outside the named set, in a trace that asks first, an accepted string whose external openings the
   reading keeps means: the value read off the trace is not the instance's, or the language holds.

Main definitions: `Written.chainT`, `Written.extSW`, `preSeed`.
Main theorems: `runsIn_det_log`, `preSeed_idle`, `seedFirst_of_asksFirst`, `batBadOff_lang_ask`.

Not claimed. Nothing shuts out the first way out, "the value read off the trace is not the
instance's": that is for a checker which recomputes the value. No second protocol, no `seedOf` and
no fixed string are given. That the reading of the external string is blind to what `preSeed` asks
is not said here (OnBytes/TypedOracleCompiler/Slice/ReadingBlind.lean has the law to use). `preSeed` asks its chain
again at every first query under Z's tag, whatever its roots and whether or not it was asked before:
where a trace is made to ask first, the count is multiplied by 1 + the number of the second
protocol's rounds. The verifier is the one without the test of the strict format. What the heads of
BatchClauseOff.lean and WrapBetween.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one
that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.SeedLane
import OnBytes.TypedOracleCompiler.Compile.Batch.OursFirst
import OnBytes.Slice.WrapBetween

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice (AsksFirst asksFirst_before lenB)
open scoped ENNReal

/-! ## Two laws on logs -/

section
variable {S : OSpec} {α : Type}

/-- An algorithm without coins runs in its own log, under a family g of oracle functions, with
the value that it has under g. -/
theorem runsIn_det_log (g : Fam S) (c : OComp S α) (hc : c.NoCoin) :
    RunsIn (c.withTrace.det g).2 c (c.withTrace.det g).1 := by
  induction c with
  | pure a => exact RunsIn.pure a
  | query o q k ih =>
    have e : ((OComp.query o q k).withTrace.det g) =
        (((k (g o q)).withTrace.det g).1,
          (⟨o, q, g o q⟩ : QA S) :: ((k (g o q)).withTrace.det g).2) := by
      show (((k (g o q)).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).det g) = _
      rw [OComp.det_bind]
      rfl
    rw [e]
    exact RunsIn.query o q k (g o q) _ List.mem_cons_self
      ((ih (g o q) (hc (g o q))).mono (List.subset_cons_self _ _))
  | sample n k _ => exact hc.elim

/-- Dropping an algorithm's value does not change its log. -/
theorem log_bind_unit (g : Fam S) (c : OComp S α) :
    ((c.bind fun _ => (OComp.pure () : OComp S Unit)).withTrace.det g).2 =
      (c.withTrace.det g).2 := by
  rw [Rom.withTrace_bind, OComp.det_bind]
  show (c.withTrace.det g).2 ++ [] = _
  rw [List.append_nil]

end

variable {I A Sd : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L}

/-! ## The second protocol's chain at one fixed string, and the value read off a trace -/

section
variable (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
  (plainsT : Plains ZT.P.shape)

/-- A written protocol's chain at one fixed string, under the outer roots cms. -/
def Written.chainT (cms : List (Dig lam)) :
    TypedOracleComputation lam W.K L (Option (Rho ZT.P.shape × RootsOfChain lam ZT.P.shape × Phase lam)) :=
  chainAt ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT cms

variable (seedOf : Rho ZT.P.shape → Sd) (d : Sd)

/-- The value read off a trace under the outer roots: `seedOf` of the verifier's messages that the
chain at the fixed string yields in the trace; d where it has not run or refuses. -/
def Written.extSW : Tc W → List (Dig lam) → Sd :=
  extSOf ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT seedOf d

variable (Z : WrittenB W)

/-- The outer roots of a first query's head; nothing at another head. -/
def f1Roots {X : Type} : Head lam X → Option (List (Dig lam))
  | .f1 cms _ _ => some cms
  | _ => none

/-- What is to be asked before a challenge query under the tag t. -/
def preSeedFb (t : Tag) (q : FbIn lam L t) : TypedOracleComputation lam W.K L Unit :=
  if t = Z.t then
    match f1Roots q.head with
    | some cms => (ZT.chainT saltT rtT rootsT plainsT cms).bind fun _ => OComp.pure ()
    | none => OComp.pure ()
  else OComp.pure ()

/-- `preSeed`, by the oracle's name. -/
def preSeedOn : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf lam L o → TypedOracleComputation lam W.K L Unit
  | .fb t, q => preSeedFb ZT saltT rtT rootsT plainsT Z t q
  | _, _ => OComp.pure ()

/-- What is to be asked first: before a first query under Z's tag, with the outer roots cms: the
second protocol's chain at the fixed string under cms. Before any other query: nothing. -/
def preSeed (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) : TypedOracleComputation lam W.K L Unit :=
  preSeedOn ZT saltT rtT rootsT plainsT Z o q

/-- What it is: nothing, or the chain under some outer roots. -/
theorem preSeed_cases (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    preSeed ZT saltT rtT rootsT plainsT Z o q = OComp.pure () ∨
      ∃ cms, preSeed ZT saltT rtT rootsT plainsT Z o q =
        (ZT.chainT saltT rtT rootsT plainsT cms).bind fun _ => OComp.pure () := by
  cases o with
  | fb t =>
    show preSeedFb ZT saltT rtT rootsT plainsT Z t q = _ ∨
      ∃ cms, preSeedFb ZT saltT rtT rootsT plainsT Z t q = _
    unfold preSeedFb
    by_cases ht : t = Z.t
    · rw [if_pos ht]
      cases f1Roots (FbIn.head q) with
      | none => exact Or.inl rfl
      | some cms => exact Or.inr ⟨cms, rfl⟩
    · rw [if_neg ht]
      exact Or.inl rfl
  | _ => exact Or.inl rfl

/-- At a first query under Z's tag it is the chain under that query's outer roots. -/
theorem preSeed_f1 (q : FbIn lam L Z.t) (cms : List (Dig lam)) (x : Option (A × Sd)) (s : Bits)
    (h : q.head = .f1 cms x s) :
    preSeed ZT saltT rtT rootsT plainsT Z (.fb Z.t) q =
      (ZT.chainT saltT rtT rootsT plainsT cms).bind fun _ => OComp.pure () := by
  show preSeedFb ZT saltT rtT rootsT plainsT Z Z.t q = _
  unfold preSeedFb
  rw [if_pos rfl, h]
  rfl

/-- It tosses no coin. -/
theorem preSeed_noCoin (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    (preSeed ZT saltT rtT rootsT plainsT Z o q).NoCoin := by
  rcases preSeed_cases ZT saltT rtT rootsT plainsT Z o q with h | ⟨cms, h⟩
  · rw [h]; trivial
  · rw [h]
    exact OComp.NoCoin.bind (chainAt_noCoin ZT.t _ ZT.wq ZT.embP none saltT rtT rootsT plainsT cms
      (allLoA_allLocal _)) fun _ => trivial

/-- It asks at most as many queries as the second protocol has rounds. -/
theorem preSeed_queries (o : (typedOracleFamily lam W.K L).ι) (q : (typedOracleFamily lam W.K L).Dom o) :
    (preSeed ZT saltT rtT rootsT plainsT Z o q).QueryBound ZT.P.shape.length := by
  rcases preSeed_cases ZT saltT rtT rootsT plainsT Z o q with h | ⟨cms, h⟩
  · rw [h]; trivial
  · rw [h]
    exact OComp.QueryBound.bind (t := 0) (chainAt_queryBound ZT.t _ ZT.wq ZT.embP none saltT rtT
      rootsT plainsT cms (allLoA_allLocal _)) fun _ => trivial

/-- Every entry of its log stands at the challenge oracle of the second protocol's tag. -/
theorem preSeed_tag (g : Fam (typedOracleFamily lam W.K L)) (o : (typedOracleFamily lam W.K L).ι)
    (q : (typedOracleFamily lam W.K L).Dom o) :
    ∀ x ∈ ((preSeed ZT saltT rtT rootsT plainsT Z o q).withTrace.det g).2,
      x.1 = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t := by
  rcases preSeed_cases ZT saltT rtT rootsT plainsT Z o q with h | ⟨cms, h⟩
  · rw [h]
    intro x hx
    cases hx
  · rw [h, log_bind_unit]
    exact chainAt_log ZT.t _ ZT.wq ZT.embP none saltT rtT rootsT plainsT cms (allLoA_allLocal _) g

/-- If the two tags differ it asks nothing for its own queries. -/
theorem preSeed_idle (hne : ZT.t ≠ Z.t) (g : Fam (typedOracleFamily lam W.K L)) (o : (typedOracleFamily lam W.K L).ι)
    (q : (typedOracleFamily lam W.K L).Dom o) :
    ∀ x ∈ ((preSeed ZT saltT rtT rootsT plainsT Z o q).withTrace.det g).2,
      ((preSeed ZT saltT rtT rootsT plainsT Z x.1 x.2.1).withTrace.det g).2 = [] := by
  intro x hx
  obtain ⟨xo, xq, xr⟩ := x
  have h : xo = TypedOracleCompiler.Compile.Batch.OracleName.fb ZT.t :=
    preSeed_tag ZT saltT rtT rootsT plainsT Z g o q _ hx
  subst h
  have e : preSeed ZT saltT rtT rootsT plainsT Z (.fb ZT.t) xq = OComp.pure () := by
    show preSeedFb ZT saltT rtT rootsT plainsT Z ZT.t xq = _
    unfold preSeedFb
    rw [if_neg hne]
  show ((preSeed ZT saltT rtT rootsT plainsT Z (.fb ZT.t) xq).withTrace.det g).2 = []
  rw [e]
  rfl

/-- If the two tags differ: in a trace that asks first, before a first query under Z's tag the chain
under that query's outer roots has run to its end (which may be a refusal). -/
theorem chainT_ran (hne : ZT.t ≠ Z.t) (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W)
    (hA : AsksFirst (preSeed ZT saltT rtT rootsT plainsT Z) F tr) (a b : Tc W)
    (q : FbIn lam L Z.t) (r : FsAns lam W.K) (cms : List (Dig lam)) (x : Option (A × Sd))
    (s : Bits) (hq : q.head = .f1 cms x s) (htr : tr = a ++ fbE Z.t q r :: b) :
    ∃ z, RunsIn a (ZT.chainT saltT rtT rootsT plainsT cms) z := by
  have h1 := asksFirst_before (preSeed ZT saltT rtT rootsT plainsT Z) F tr hA
    (preSeed_idle ZT saltT rtT rootsT plainsT Z hne F) a (fbE Z.t q r) b htr
  have e : ((preSeed ZT saltT rtT rootsT plainsT Z (fbE Z.t q r).1
      (fbE Z.t q r).2.1).withTrace.det F).2 =
      ((ZT.chainT saltT rtT rootsT plainsT cms).withTrace.det F).2 := by
    show ((preSeed ZT saltT rtT rootsT plainsT Z (.fb Z.t) q).withTrace.det F).2 = _
    rw [preSeed_f1 ZT saltT rtT rootsT plainsT Z q cms x s hq, log_bind_unit]
  rw [e] at h1
  exact ⟨_, (runsIn_det_log F _ (chainAt_noCoin ZT.t _ ZT.wq ZT.embP none saltT rtT rootsT plainsT
    cms (allLoA_allLocal _))).mono h1⟩

/-- `SeedFirst` from `AsksFirst`: if the two tags differ, each query of the trace has one
answer, and the trace asks first at `preSeed`, then for every root, instance and string: at every
query whose chain begins with the root and with what the first query holds of the instance, the
value read off the trace before it is the value read off the whole trace. -/
theorem seedFirst_of_asksFirst (hne : ZT.t ≠ Z.t) (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W)
    (h1 : OneAns tr) (hA : AsksFirst (preSeed ZT saltT rtT rootsT plainsT Z) F tr) (cm : Dig lam)
    (x : A × Sd) (π : OneProtocolProof lam Z.Q) :
    SeedFirst Z (ZT.extSW saltT rtT rootsT plainsT seedOf d) tr cm x π := by
  intro pre q a post l cur htr ho
  have hs : pre ⊆ tr := by
    rw [htr]
    exact List.subset_append_left _ _
  have hran : ∃ z, RunsIn pre (ZT.chainT saltT rtT rootsT plainsT [cm]) z := by
    rcases ours_first _ ho with ⟨s, hq⟩ | ⟨q1, a1, s, hm, hq⟩
    · exact chainT_ran ZT saltT rtT rootsT plainsT Z hne F tr hA pre post q a [cm] _ s hq htr
    · obtain ⟨u, v, rfl⟩ := List.append_of_mem hm
      obtain ⟨z, hz⟩ := chainT_ran ZT saltT rtT rootsT plainsT Z hne F tr hA u
        (v ++ fbE Z.t q a :: post) q1 a1 [cm] _ s hq (by rw [htr]; simp)
      exact ⟨z, hz.mono (List.subset_append_left _ _)⟩
  obtain ⟨z, hz⟩ := hran
  exact extSOf_stable ZT.t (BatchInteractiveOracleProof.ofProto ZT.P) ZT.wq ZT.embP none saltT rtT rootsT plainsT
    seedOf d h1 hs [cm] hz

/-- Outside the named set, in a trace that asks first, an accepted string whose external openings
R keeps means: the value read off the trace is not the instance's, or the language holds. Asked
beside what `batBadOff_lang` asks: the two tags differ. -/
theorem batBadOff_lang_ask (R : Reading L W.embE) (ε : Err Z.Q.loc.shape)
    (State : (Fin L.wordLength → L.Symbol) → A × Sd → PTr Z.Q.loc.shape → Bool) (ℓ : Lane W)
    (Lg : A × Sd → (oneExternalString L.wordLength L.Symbol).Str → Prop) (hS : StLawsOwn Z State Lg) (hZ : Z.OK)
    (hE : ∀ x, L.early x = (x.1, d)) (hl : L.late = none) (hne : ZT.t ≠ Z.t)
    (F : Fam (typedOracleFamily lam W.K L)) (tr : Tc W) (cm : Dig lam) (x : A × Sd) (π : OneProtocolProof lam Z.Q)
    (hB : ¬ batBadOff Z R (ZT.extSW saltT rtT rootsT plainsT seedOf d) d ε State ℓ tr)
    (hA : AsksFirst (preSeed ZT saltT rtT rootsT plainsT Z) F tr)
    (hk : ∀ p op, π.ext p = some op → R.keeps p op.sym op.salt)
    (hrun : RunsIn tr (Z.verifier cm x π) true) :
    ZT.extSW saltT rtT rootsT plainsT seedOf d tr [cm] ≠ x.2 ∨ Lg x (R.at W tr cm) :=
  batBadOff_lang Z R _ d ε State ℓ Lg hS hZ hE hl tr cm x π hB hk hrun
    (seedFirst_of_asksFirst ZT saltT rtT rootsT plainsT seedOf d Z hne F tr
      (batBadOff_second Z R _ d ε State ℓ tr hB).2 hA cm x π)

end

end TypedOracleCompiler.Slice
