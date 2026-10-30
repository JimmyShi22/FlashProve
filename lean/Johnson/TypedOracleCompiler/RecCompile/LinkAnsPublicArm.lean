-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsPublicArm.lean: the two arms of the entry's check ask no point of the
spare oracle: what `arm_pr_pub` (LinkAnsPublic.lean) asks of an arm, paid.

`arm_pr_pub` asks of a set Pt of public strings that the arm, over the hash function, asks none of
them, and that none codes a leaf or a node. Here Pt is "the string codes a point of the spare oracle
`OracleName.other`" under the coding m. The arm with the lax Link and the arm with the strict Link ask the
Fiat-Shamir oracle of the seeds' tag and what a compiled verifier at the tag link asks
(OnBytes/TypedOracleCompiler/Compile/Batch/NoOther.lean): never `OracleName.other`.

  `asksIn_askAll`, `asksIn_overOne`   a property of the typed queries, over the hash function
  `asksIn_seedIs`, `asksIn_armL`, `asksIn_armS`   the arms ask no point of `OracleName.other`
  `IsOther`         the string codes a point of `OracleName.other`
  `hno_armL`, `hno_armS`, `isOther_tree`   the premises of `arm_pr_pub` at `IsOther`
  `ansOK_cons`      a digest laid in front of the code of the answers keeps its laws

Limits: nothing on which strings the programs hash.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublic
import OnBytes.TypedOracleCompiler.Compile.Batch.NoOther

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

/-! ## A property of the typed queries, over the hash function -/

section
variable {Sp : OSpec} {lam : ℕ} {α : Type}

/-- The calls for the blocks of an answer ask the given strings alone. -/
theorem asksIn_askAll (P : List Bool → Prop) :
    ∀ (n : ℕ) (f : Fin n → List Bool), (∀ j, P (f j)) →
      (askAll lam n f).AsksIn fun _ s => P s
  | 0, _, _ => trivial
  | n + 1, f, h => by
    refine ⟨h 0, fun r => ?_⟩
    refine OComp.AsksIn.bind ?_ (asksIn_askAll P n (fun i => f i.succ) fun j => h j.succ)
    intro _
    trivial

/-- If every typed query of an algorithm has the property P, every string that it asks over the hash
function codes a typed point with P. -/
theorem asksIn_overOne (m : OracleCoding Sp lam) (P : (o : Sp.ι) → Sp.Dom o → Prop) :
    ∀ c : OComp Sp α, c.AsksIn P →
      (c.overOne m).AsksIn fun _ s => P (m.dec s).1 (m.dec s).2.1 := by
  intro c
  induction c with
  | pure a => intro _; trivial
  | sample n k ih => intro h x; exact ih x (h x)
  | query o q k ih =>
    intro h
    refine OComp.AsksIn.bind (fun bs => ih _ (h.2 _))
      (asksIn_askAll (fun s => P (m.dec s).1 (m.dec s).2.1) _ _ fun j => ?_)
    have hx : ∀ x : m.Pt, x = ⟨o, (q, j)⟩ → P x.1 x.2.1 := by
      rintro _ rfl
      exact h.1
    exact hx _ (m.dec_code o q j)

end

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-! ## The arms ask no point of the spare oracle -/

/-- the property: the query does not go to the spare oracle -/
abbrev NotOther {I' X' : Type} (lam : ℕ) (Lc : BatchProtocolWithLeafBody I' X') : (o : OracleName) → domOf lam Lc o → Prop :=
  fun o _ => o ≠ OracleName.other

/-- The test of a seed asks the Fiat-Shamir oracle of the seeds' tag alone. -/
theorem asksIn_seedIs (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (c : Dig lam) (s : L.OutOfDomainSeed) :
    (outOfDomainSeedIs W S c s).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) :=
  ⟨fun e => OracleName.noConfusion e, fun _ => ⟨fun e => OracleName.noConfusion e, fun _ => trivial⟩⟩

/-- The arm with the lax Link asks no point of the spare oracle. -/
theorem asksIn_armL (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam))
    (z : OutLA lam L aL) : (armL W S cA z).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  show (VLA' W S cA z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).AsksIn (NotOther lam (typedOracleCarrier L Bd aT
      aL))
  unfold VLA'
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_
    (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyB _ _ _ _ _ _ _ _ _ _ _))
  intro _
  trivial

/-- The arm with the strict Link asks no point of the spare oracle. -/
theorem asksIn_armS (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params)
    (z : OutLA lam L aL) : (armS W S cA p z).AsksIn (NotOther lam (typedOracleCarrier L Bd aT aL)) := by
  show (VLA W S cA p z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2).AsksIn (NotOther lam (typedOracleCarrier L Bd aT
      aL))
  unfold VLA
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_ (asksIn_seedIs S _ _)
  intro _
  refine OComp.AsksIn.bind ?_
    (OComp.AsksIn.mono (fun _ _ h => (vNames_ne h).1) (asksIn_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _))
  intro _
  trivial

/-! ## The premises of `arm_pr_pub` -/

/-- The string codes a point of the spare oracle. -/
def IsOther (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s : List Bool) : Prop :=
  (m.dec s).1 = OracleName.other

/-- Such a string codes no leaf and no node. -/
theorem isOther_tree (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (s : List Bool)
    (h : IsOther m s) : (m.dec s).1 ≠ OracleName.leaf ∧ (m.dec s).1 ≠ OracleName.node := by
  unfold IsOther at h
  rw [h]
  exact ⟨fun e => OracleName.noConfusion e, fun e => OracleName.noConfusion e⟩

/-- Over the hash function the arm with the lax Link asks no such string. -/
theorem hno_armL (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (z : OutLA lam L aL) :
    ((armL W S cA z).overOne m).AsksIn fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _ (asksIn_armL S cA z)

/-- Over the hash function the arm with the strict Link asks no such string. -/
theorem hno_armS (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : Params)
    (z : OutLA lam L aL) : ((armS W S cA p z).overOne m).AsksIn fun _ s => ¬ IsOther m s :=
  asksIn_overOne m (NotOther lam (typedOracleCarrier L Bd aT aL)) _ (asksIn_armS S cA p z)

/-- A digest laid in front of the code of the answers keeps its laws. -/
theorem ansOK_cons {cA : L.OutOfDomainAnswer → List (Dig lam)} (h : AnsOK cA) (d : Dig lam) :
    AnsOK fun a => d :: cA a :=
  ⟨fun a a' e => h.inj (List.cons.inj e).2, fun a a' => by
    simp only [List.length_cons, h.len a a']⟩

end TypedOracleCompiler.Compile.Batch.Cms
