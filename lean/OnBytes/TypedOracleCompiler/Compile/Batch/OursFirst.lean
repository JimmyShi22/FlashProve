-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/OursFirst.lean: every query of the verifier's own chain is, or has before
it, a first query with the same external roots; and a chain of local rounds asks its own Fiat-Shamir
oracle alone.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Why. By `extSOf_stable` (ReadRun.lean) the stability of a value that is read off a chain apart, at
the queries of the verifier's own chain, comes to this: at each of these queries the chain apart, at
its fixed string, has run in the prefix. If every maker of queries asks that chain before each first
query with the roots [cm], two facts on this folder's text are wanted, and they are here.

  `first_of_startsWith`, `ours_first`
      Every query that is ours (`Ours`, Chain.lean) is, or has before it in the prefix, a first
      query (F1) with our external roots and our early instance, at our tag (with some salt). It is
      the case split of `ours_cms`, kept one step earlier; the shared case too.
  `AllLoA`, `allLoA_allLocal`
      All rounds of an annotation are local.
  `chainB_lo`
      A chain of local rounds alone has no coin, asks at most as many queries as it has rounds, and
      asks the Fiat-Shamir oracle of its own tag alone (no query to g: it never joins).
  `noCoin_of_detBound`, `mem_trace_of_asksIn`
      Generic: `DetBound` has no coin; every entry of an algorithm's own log at oracle functions is
      a query that it may ask.
  `chainAt_noCoin`, `chainAt_queryBound`, `chainAt_log`
      The three for `chainAt` (ReadRun.lean) at local rounds alone: `NoCoin`; `QueryBound` (the
      number of rounds); every entry x of `((chainAt …).withTrace.det g).2` has `x.1 = OracleName.fb t`.

Limits. `ours_first` fixes the external roots, the early instance and the tag of that first query,
not its salt. Nothing on probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ReadRun
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools
import Rom.AsksIn
import Rom.Cache

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem first_of_startsWith {K : ℕ} {t : Tag} {pre : Trace (typedOracleFamily lam K L)} {cms : List (Dig lam)}
    {x : Option X}
    {l : List (Rec lam K L t)} (h : StartsWith cms x l) (hin : ∀ rc ∈ l, RecIn pre rc) :
    ∃ q1 a1 salt, fbE t q1 a1 ∈ pre ∧ q1.head = Head.f1 cms x salt := by
  obtain ⟨q1, a1, rest, salt, rfl, hq⟩ := h
  exact ⟨q1, a1, salt, hin _ List.mem_cons_self, hq⟩

/-- Every query that is ours is, or has before it, a first query with our external roots and our
early instance. -/
theorem ours_first {W : QueryLayout lam L} (C : Ctx W) {pre : Tc W} {q : FbIn lam L C.t}
    {l : List (Rec lam W.K L C.t)}
    {cur : Item lam L C.t} (h : Ours C pre q l cur) :
    (∃ salt, q.head = Head.f1 C.cms C.xo salt) ∨
      ∃ q1 a1 salt, fbE C.t q1 a1 ∈ pre ∧ q1.head = Head.f1 C.cms C.xo salt := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨slot, sh, c', sd, hr, -, hs, hx, -⟩
  · obtain ⟨-, -, h3, h4⟩ := rooted_good pre _ _ _ h1
    rcases h4 with ⟨-, salt, hq⟩ | h4
    · exact Or.inl ⟨salt, hq⟩
    · exact Or.inr (first_of_startsWith h4 h3)
  · obtain ⟨h3, h4⟩ := rooted_good pre _ _ _ h1
    exact Or.inr (first_of_startsWith h4 h3)
  · obtain ⟨-, iJ, -, hslot⟩ := rooted_good pre _ _ _ hr
    obtain ⟨-, -, h6, -, h8⟩ := hslot c' sd hs
    rw [hx] at h8
    exact Or.inr (first_of_startsWith h8 h6)

/-! ## A chain of local rounds alone -/

/-- all rounds are local -/
def AllLoA : (s : Shape) → RoundSplits s → Prop
  | [], _ => True
  | _ :: s, (a, A) => a.kind = Kind.lo ∧ AllLoA s A

theorem allLoA_allLocal : ∀ s : Shape, AllLoA s (RoundSplits.allLocal s)
  | [] => trivial
  | _ :: s => ⟨rfl, allLoA_allLocal s⟩

theorem asksIn_askV {K : ℕ} {P : (o : OracleName) → domOf lam L o → Prop} (o : OracleName)
    (q : domOf lam L o) (h : P o q) :
    (askTypedOracle (L := L) (K := K) o q).AsksIn P := ⟨h, fun _ => trivial⟩

/-- A chain of local rounds alone: no coin, at most as many queries as rounds, at its own tag's
Fiat-Shamir oracle alone. -/
theorem chainB_lo {K : ℕ} (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s), AllLoA s A →
      DetBound (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls) s.length ∧
      (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).AsksIn fun o _ => o = OracleName.fb t
  | [], _, _, _, _, _, _, _, _ => ⟨detBound_pure _ _, trivial⟩
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls), hA => by
      simp only [recomputeChain]
      split
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine ⟨((detBound_askV (L := L) (K := K) _ _).bind (t := s.length + 0) fun ans =>
            ((chainB_lo t cms x salt rtreq s A W _ _ _ rts' pls hA.2).1.bind (t := 0) fun _ =>
                detBound_pure _ _)).mono
              (by simp only [List.length_cons]; omega), ?_⟩
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ rfl)
          intro ans
          refine OComp.AsksIn.bind ?_ (chainB_lo t cms x salt rtreq s A W _ _ _ rts' pls hA.2).2
          intro _
          exact trivial
        · exact ⟨detBound_pure _ _, trivial⟩
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine ⟨((detBound_askV (L := L) (K := K) _ _).bind (t := s.length + 0) fun ans =>
            ((chainB_lo t cms x salt rtreq s A W _ _ _ rts' pls hA.2).1.bind (t := 0) fun _ =>
                detBound_pure _ _)).mono
              (by simp only [List.length_cons]; omega), ?_⟩
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ rfl)
          intro ans
          refine OComp.AsksIn.bind ?_ (chainB_lo t cms x salt rtreq s A W _ _ _ rts' pls hA.2).2
          intro _
          exact trivial
        · exact ⟨detBound_pure _ _, trivial⟩
      · rename_i ρ e
        rw [hA.1] at e
        cases ph <;> simp only [actOf, Option.some.injEq, reduceCtorEq] at e
      · exact ⟨detBound_pure _ _, trivial⟩

theorem noCoin_of_detBound {S : OSpec} {α : Type} : ∀ {c : OComp S α} {t : ℕ},
    DetBound c t → c.NoCoin
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, h => h.elim
  | .query _ _ _, _ + 1, h => fun r => noCoin_of_detBound (h r)
  | .sample _ _, _, h => h.elim

/-- every entry of an algorithm's own log at oracle functions is a query that it may ask -/
theorem mem_trace_of_asksIn {S : OSpec} {α : Type} {P : (o : S.ι) → S.Dom o → Prop} (g : Fam S) :
    ∀ {c : OComp S α}, c.AsksIn P → ∀ x ∈ (c.withTrace.det g).2, P x.1 x.2.1
  | .pure _, _, x, hx => by cases hx
  | .sample _ k, hc, x, hx => mem_trace_of_asksIn g (hc 0) x hx
  | .query o q k, hc, x, hx => by
      have e : (OComp.query o q k).withTrace.det g =
          (((k (g o q)).withTrace.det g).1, (⟨o, q, g o q⟩ : QA S) ::
              ((k (g o q)).withTrace.det g).2) := by
        show ((k (g o q)).withTrace.bind fun out =>
            OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).det g = _
        rw [OComp.det_bind]
        rfl
      rw [e] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hc.1
      · exact mem_trace_of_asksIn g (hc.2 _) x hx

variable {W : QueryLayout lam L}

section
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xo : Option X) (salt : Bits)
      (rtreq : Dig lam)
  (roots : List (Dig lam)) (plains : Plains Q.loc.shape) (cms : List (Dig lam))
      (hA : AllLoA Q.loc.shape Q.ann)
include hA

theorem chainAt_noCoin : (chainAt t Q wq embP xo salt rtreq roots plains cms).NoCoin :=
  noCoin_of_detBound (chainB_lo t cms xo salt rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
      roots plains hA).1

theorem chainAt_queryBound : (chainAt t Q wq embP xo salt rtreq roots plains cms).QueryBound
    Q.loc.shape.length :=
  (chainB_lo t cms xo salt rtreq Q.loc.shape Q.ann wq.sh embP 0 .first roots plains hA).1.queryBound

theorem chainAt_log (g : Fam (typedOracleFamily lam W.K L)) :
    ∀ x ∈ ((chainAt t Q wq embP xo salt rtreq roots plains cms).withTrace.det g).2, x.1 = OracleName.fb t :=
  mem_trace_of_asksIn g (chainB_lo t cms xo salt rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
      roots plains hA).2

end

end TypedOracleCompiler.Compile.Batch
