-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/SeedsApart.lean: when a query of a seed (`seedQ0`, `seedQ1`,
Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) can be a query of a verifier's own chain; on typed queries, and
on the format's strings.

Definitions, statements and proofs. A seed's two queries go to the Fiat-Shamir oracle of one tag. If
that is the tag of a compiled verifier, they share that oracle with the verifier's chain (`recomputeChain`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean). An encoding of typed queries as strings is one to one. So
an encoding that writes the format's strings for both wants two things: a chain's typed query is no
seed's typed query; and a chain's string is no seed's string. "The chain asks" is `OComp.AsksIn`
(Rom/SigmaExits.lean): on every path, whatever the answers. The typed forms are stated at any tag
and any plain parts; a seed's queries are these forms by definition.
Main names:
  `PlainPart.depth`: the number of the round of which a plain part is a plain part.
  `chainB_round`: every query of a chain to its Fiat-Shamir oracle holds a plain part of the round
    whose number it holds.
  `chainB_f1`: a query of a chain with a head (F1) is in the chain's first round, and the chain
    begins in the phase `first`.
  `chainB_tag`: a chain asks the two oracles of its own tag alone.
  `chain_ne_q0`: no query of a chain from round 0 has round 1 and a head (F1). No premise.
  `chain_ne_q1`: no query of a chain from round 0 is ⟨2, (F2), no root, p1⟩, if p1 is no plain part
    of round 2.
  `chain_meets_q1`: that premise cannot be dropped: with three local rounds of which the third
    sends no tree, and that round's own plain part as p1, the chain asks such a query.
  `seedQ0_apart`, `seedQ1_apart`: the two at a seeds' wire, for a chain at its tag;
    `seed_apart_tag`: for a chain at another tag.
  `testChain_ne_q0`, `testChain_ne_q1`: the two at the chain of the compiled verifier of Test
    (Johnson/TypedOracleCompiler/RecCompile/Cms.lean), for every list of digests that it is handed.
  `PlainPart.depth_inl`: a plain part of round 0 serves as p1.
  `Fmt.seedRound_ne`, `Fmt.seedFirst_ne`: on the format's strings: a call of a round, and the call
    for the first value, under the label of the seeds' chain (`Fmt.recordLabel`) are no such calls
    under a label below 2^32. `Fmt.oStr_ne_number`: calls under different numbers have different
    strings: so a seed's two calls (160, 162) are apart from a chain's calls under other numbers.
    `Fmt.startChainW_label`: a chain that is started from parameters and a statement has a label
    below 2^32, or is refused.
  `OnBytes.Slice.blockStr_ne_round`, `OnBytes.Slice.seedFirst_ne_first`: the two at the seeds' own
    written strings (`blockStr`, `seedFirst`, OnBytes/Slice/SeedRow.lean), whose data are in the
    hash's domain.
Limits: the chain alone: what a compiled verifier asks behind its chain goes to other oracles by its
text; no statement here says so. Nothing on what a prover asks. No encoding is built or named here:
the two halves are what an encoding of both needs, not that there is one. That a description's seeds
have their second plain part off round 2 is not shown here. The statements on strings ask that the
other call's data are in the hash's domain (`Fmt.hDom`); that every chain of a file is started by
`Fmt.startChainW` is not shown here (OnBytes/Chain/Engine.lean calls it). They are on Lean's text of
the format, with that text's own limits (Fmt/Rules4.lean). Nothing on an honest prover or on hiding.

-/
import Johnson.TypedOracleCompiler.RecCompile.Cms
import OnBytes.TypedOracleCompiler.Compile.Batch.OursFirst
import OnBytes.Slice.SeedStrings

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The number of the round of which a plain part is a plain part. -/
def PlainPart.depth : (s : Shape) → (A : RoundSplits s) → PlainPart s A → ℕ
  | [], _, z => z.elim
  | _ :: _, (_, _), .inl _ => 0
  | _ :: s, (_, A), .inr z => PlainPart.depth s A z + 1

/-- A plain part of round 0. -/
theorem PlainPart.depth_inl {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (u : a.P0 ⊕ a.Pj) :
    PlainPart.depth (r :: s) (a, A) (.inl u) = 0 := rfl

/-- What `chainB_round` says of a query. -/
def RoundAt (t : Tag) (s : Shape) (A : RoundSplits s) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (o : OracleName) (q : domOf lam L o) : Prop :=
  ∀ q' : FbIn lam L t, (⟨o, q⟩ : Σ o, domOf lam L o) = ⟨OracleName.fb t, q'⟩ →
    ∃ z, q'.plain = embP z ∧ q'.round = i + PlainPart.depth s A z

/-- From the later rounds to the whole. -/
theorem roundAt_next {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} (o : OracleName)
    (q : domOf lam L o) (h : RoundAt t s A (fun z => embP (.inr z)) (i + 1) o q) :
    RoundAt t (r :: s) (a, A) embP i o q := fun q' e => by
  obtain ⟨z, h1, h2⟩ := h q' e
  exact ⟨.inr z, h1, by rw [h2]; show i + 1 + _ = i + (_ + 1); omega⟩

/-- The query of the first of the rounds that are left. -/
theorem roundAt_fb {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} (h : Head lam X)
    (rt : List (Dig lam)) (u : a.P0 ⊕ a.Pj) :
    RoundAt t (r :: s) (a, A) embP i (OracleName.fb t) (⟨i, h, rt, embP (.inl u)⟩ : FbIn lam L t) :=
  fun q' e => by
    obtain rfl := eq_of_heq (Sigma.mk.inj e).2
    exact ⟨.inl u, rfl, rfl⟩

/-- A query to the oracle g is none to the Fiat-Shamir oracle. -/
theorem roundAt_g {t : Tag} {s : Shape} {A : RoundSplits s}
    {embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} (q : JoiningRoundQuery lam L t) :
    RoundAt t s A embP i (OracleName.g t) q := fun _ e => by
  have := (Sigma.mk.inj e).1
  cases this

/-- **Every query of a chain to its Fiat-Shamir oracle holds a plain part of the round whose number
it holds.** -/
theorem chainB_round {K : ℕ} (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).AsksIn (RoundAt t s A embP i)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (roundAt_fb _ _ _))
          intro ans
          refine OComp.AsksIn.bind ?_ ((chainB_round t cms x salt rtreq s A W _ _ _ rts' pls).mono
            roundAt_next)
          intro _
          exact trivial
        · exact trivial
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (roundAt_fb _ _ _))
          intro ans
          refine OComp.AsksIn.bind ?_ ((chainB_round t cms x salt rtreq s A W _ _ _ rts' pls).mono
            roundAt_next)
          intro _
          exact trivial
        · exact trivial
      · split
        · split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (roundAt_g _))
            intro c
            refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (roundAt_fb _ _ _))
            intro ans
            refine OComp.AsksIn.bind ?_
              ((chainB_round t cms x salt rtreq s A W _ _ _ rts' pls).mono roundAt_next)
            intro _
            exact trivial
          · exact trivial
        · exact trivial
      · exact trivial

/-! ## A head (F1) -/

/-- The field for the late instance turns no other head into a head (F1). -/
theorem withLate_f1 {h : Head lam X} {xl : Option X} {c : List (Dig lam)} {y : Option X}
    {sl : Bits} (e : h.withLate xl = .f1 c y sl) : h = .f1 c y sl := by
  cases h <;> simp_all [Head.withLate]

/-- Of an act with one query: a head (F1) stands in the phase `first` alone; no act leads back to
that phase. -/
theorem actOf_one {cms : List (Dig lam)} {x : Option X} {salt : Bits} {k : Kind} {ph : Phase lam}
    {h : Head lam X} {own : Bool} {next : Bits → Phase lam}
    (e : actOf cms x salt k ph = some (.one h own next)) :
    (∀ c y sl, h = .f1 c y sl → ph = .first) ∧ ∀ v, next v ≠ .first := by
  cases k <;> cases ph <;> simp only [actOf, Option.some.injEq, Act.one.injEq, reduceCtorEq] at e
  all_goals
    obtain ⟨rfl, -, rfl⟩ := e
    exact ⟨fun _ _ _ h => (by first | rfl | cases h), fun _ h => (by cases h)⟩

/-- What `chainB_f1` says of a query. -/
def F1At (t : Tag) (i : ℕ) (ph : Phase lam) (o : OracleName) (q : domOf lam L o) : Prop :=
  ∀ q' : FbIn lam L t, (⟨o, q⟩ : Σ o, domOf lam L o) = ⟨OracleName.fb t, q'⟩ →
    ∀ c y sl, q'.head = .f1 c y sl → ph = .first ∧ q'.round = i

/-- From the later rounds, which begin in another phase than `first`, to the whole. -/
theorem f1At_next {t : Tag} {i : ℕ} {ph ph' : Phase lam} (hp : ph' ≠ .first) (o : OracleName)
    (q : domOf lam L o) (h : F1At t (i + 1) ph' o q) : F1At t i ph o q :=
  fun q' e c y sl hq => absurd (h q' e c y sl hq).1 hp

/-- The query of the first of the rounds that are left. -/
theorem f1At_fb {t : Tag} {i : ℕ} {ph : Phase lam} (h : Head lam X) (rt : List (Dig lam))
    (p : PlainPart (shapeOf L t) (annOf L t)) (hh : ∀ c y sl, h = .f1 c y sl → ph = .first) :
    F1At t i ph (OracleName.fb t) (⟨i, h, rt, p⟩ : FbIn lam L t) := fun q' e c y sl hq => by
  obtain rfl := eq_of_heq (Sigma.mk.inj e).2
  exact ⟨hh c y sl hq, rfl⟩

/-- A query to the oracle g is none to the Fiat-Shamir oracle. -/
theorem f1At_g {t : Tag} {i : ℕ} {ph : Phase lam} (q : JoiningRoundQuery lam L t) :
    F1At t i ph (OracleName.g t) q := fun _ e => by
  have := (Sigma.mk.inj e).1
  cases this

/-- **A query of a chain with a head (F1) is in the chain's first round, and the chain begins in the
phase `first`.** -/
theorem chainB_f1 {K : ℕ} (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).AsksIn (F1At t i ph)
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _
            (f1At_fb _ _ _ fun c y sl hq => (actOf_one e).1 c y sl (withLate_f1 hq)))
          intro ans
          refine OComp.AsksIn.bind ?_ ((chainB_f1 t cms x salt rtreq s A W _ _ _ rts' pls).mono
            (f1At_next ((actOf_one e).2 _)))
          intro _
          exact trivial
        · exact trivial
      · rename_i h next e
        split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (f1At_fb _ _ _ (actOf_one e).1))
          intro ans
          refine OComp.AsksIn.bind ?_ ((chainB_f1 t cms x salt rtreq s A W _ _ _ rts' pls).mono
            (f1At_next ((actOf_one e).2 _)))
          intro _
          exact trivial
        · exact trivial
      · split
        · split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (f1At_g _))
            intro c
            refine OComp.AsksIn.bind ?_ (asksIn_askV _ _
              (f1At_fb _ _ _ fun _ _ _ hq => by cases hq))
            intro ans
            refine OComp.AsksIn.bind ?_ ((chainB_f1 t cms x salt rtreq s A W _ _ _ rts' pls).mono
              (f1At_next (by intro hq; cases hq)))
            intro _
            exact trivial
          · exact trivial
        · exact trivial
      · exact trivial

/-- A chain asks the two oracles of its own tag alone. -/
theorem chainB_tag {K : ℕ} (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls).AsksIn
        fun o _ => o = OracleName.fb t ∨ o = OracleName.g t
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain]
      split
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (Or.inl rfl))
          intro ans
          refine OComp.AsksIn.bind ?_ (chainB_tag t cms x salt rtreq s A W _ _ _ rts' pls)
          intro _
          exact trivial
        · exact trivial
      · split
        · rename_i rt rts' _
          simp only [bind_eq]
          refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (Or.inl rfl))
          intro ans
          refine OComp.AsksIn.bind ?_ (chainB_tag t cms x salt rtreq s A W _ _ _ rts' pls)
          intro _
          exact trivial
        · exact trivial
      · split
        · split
          · rename_i rt0 rts' _
            simp only [bind_eq]
            refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (Or.inr rfl))
            intro c
            refine OComp.AsksIn.bind ?_ (asksIn_askV _ _ (Or.inl rfl))
            intro ans
            refine OComp.AsksIn.bind ?_ (chainB_tag t cms x salt rtreq s A W _ _ _ rts' pls)
            intro _
            exact trivial
          · exact trivial
        · exact trivial
      · exact trivial

/-! ## The two typed forms -/

section
variable {K : ℕ} (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)

/-- **No query of a chain from round 0 has round 1 and a head (F1).** -/
theorem chain_ne_q0 :
    (recomputeChainOfProof (L := L) t Q wq embP xin cms x π).AsksIn fun o q =>
      ∀ c y sl rt p, (⟨o, q⟩ : Σ o, domOf lam L o) ≠
        ⟨OracleName.fb t, (⟨1, .f1 c y sl, rt, p⟩ : FbIn lam L t)⟩ :=
  (chainB_f1 t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots
    π.plains).mono fun _ _ h c y sl _ _ e => absurd (h _ e c y sl rfl).2 Nat.one_ne_zero

/-- **No query of a chain from round 0 has round 2 and the plain part p1, if p1 is no plain part of
round 2.** -/
theorem chain_ne_q1 (p1 : PlainPart (shapeOf L t) (annOf L t))
    (h1 : ∀ z, PlainPart.depth Q.loc.shape Q.ann z = 2 → embP z ≠ p1) :
    (recomputeChainOfProof (L := L) t Q wq embP xin cms x π).AsksIn fun o q =>
      ∀ hd rt, (⟨o, q⟩ : Σ o, domOf lam L o) ≠ ⟨OracleName.fb t, (⟨2, hd, rt, p1⟩ : FbIn lam L t)⟩ :=
  (chainB_round t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots
    π.plains).mono fun _ _ h _ _ e => by
      obtain ⟨z, hz, hr⟩ := h _ e
      exact h1 z (by have : (2 : ℕ) = 0 + PlainPart.depth Q.loc.shape Q.ann z := hr
                     omega) hz.symm

/-- A chain asks no Fiat-Shamir oracle of another tag. -/
theorem chain_ne_tag {t' : Tag} (ht : t' ≠ t) :
    (recomputeChainOfProof (L := L) t Q wq embP xin cms x π).AsksIn fun o q =>
      ∀ q' : FbIn lam L t', (⟨o, q⟩ : Σ o, domOf lam L o) ≠ ⟨OracleName.fb t', q'⟩ :=
  (chainB_tag t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots
    π.plains).mono fun _ _ h _ e => by
      have e1 := (Sigma.mk.inj e).1
      rcases h with h | h
      · exact ht (OracleName.fb.inj (e1.symm.trans h))
      · rw [h] at e1
        cases e1

end

/-- **The premise of `chain_ne_q1` cannot be dropped.** Three local rounds, of which the third sends
no tree; roots enough for the first two: the chain asks a query with round 2, a head (F2) without an
instance, no root, and the third round's own plain part. -/
theorem chain_meets_q1 {K : ℕ} (t : Tag) (cms : List (Dig lam)) (salt : Bits) (rtreq : Dig lam)
    {r0 r1 r2 : Round} {s : Shape} (a0 : RAnn r0) (a1 : RAnn r1) (a2 : RAnn r2) (A : RoundSplits s)
    (w0 : WireRB lam K r0 a0) (w1 : WireRB lam K r1 a1) (w2 : WireRB lam K r2 a2)
    (W : RoundsQueryLayout lam K s A)
    (embP : PlainPart (r0 :: r1 :: r2 :: s) (a0, a1, a2, A) → PlainPart (shapeOf L t) (annOf L t))
    (rts : List (Dig lam)) (m0 : r0.Plain) (m1 : r1.Plain) (m2 : r2.Plain) (ms : Plains s)
    (k0 : a0.kind = Kind.lo) (k1 : a1.kind = Kind.lo) (k2 : a2.kind = Kind.lo)
    (h2 : w2.depthJ = []) (n0 : w0.depthJ.length ≤ TypedOracleCompiler.Iop.maxRt)
    (n1 : w1.depthJ.length ≤ TypedOracleCompiler.Iop.maxRt)
    (hr : w0.depthJ.length + w1.depthJ.length ≤ rts.length) :
    ¬ (recomputeChain (L := L) t cms none salt rtreq (r0 :: r1 :: r2 :: s) (a0, a1, a2, A) (w0, w1, w2, W)
        embP 0 .first rts (m0, m1, m2, ms)).AsksIn fun o q =>
      ∀ v, (⟨o, q⟩ : Σ o, domOf lam L o) ≠
        ⟨OracleName.fb t, (⟨2, .f2 none v, [], embP (.inr (.inr (.inl (.inr (a2.plain m2).2))))⟩ :
                  FbIn lam L t)⟩ := by
  intro h
  have t0 : takeRt w0.depthJ.length rts =
      some (rts.take w0.depthJ.length, rts.drop w0.depthJ.length) :=
    if_pos ⟨n0, by omega⟩
  have t1 : takeRt w1.depthJ.length (rts.drop w0.depthJ.length) =
      some ((rts.drop w0.depthJ.length).take w1.depthJ.length,
        (rts.drop w0.depthJ.length).drop w1.depthJ.length) :=
    if_pos ⟨n1, by rw [List.length_drop]; omega⟩
  have t2 : ∀ l : List (Dig lam), takeRt w2.depthJ.length l = some ([], l) := fun l => by
    rw [h2]
    exact if_pos ⟨Nat.zero_le _, Nat.zero_le _⟩
  simp only [recomputeChain, k0, k1, k2, actOf, Option.map_none, t0, t1, t2, bind_eq] at h
  have d : FsAns lam K := (fun _ _ => false, fun _ => false)
  have hl : lateInstancePart L (0 + 1 + 1) none = none := by
    unfold lateInstancePart
    split <;> rfl
  exact (((h.2 d).2 d).1 (List.ofFn d.2)) (by rw [hl]; rfl)

end TypedOracleCompiler.Compile.Batch

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-! ## At a seeds' wire -/

section
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam W.K Q)
  (xin : Y → Option L.XC) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)

/-- **No query of a chain at the seeds' tag is the first query of a seed.** -/
theorem seedQ0_apart
    (embP : PlainPart Q.loc.shape Q.ann →
      PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) S.t) (annOf (typedOracleCarrier L Bd aT aL) S.t)) :
    (recomputeChainOfProof (L := typedOracleCarrier L Bd aT aL) S.t Q wq embP xin cms x π).AsksIn fun o q =>
      ∀ cm, (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) ≠ ⟨OracleName.fb S.t, seedQ0 W S cm⟩ :=
  (chain_ne_q0 S.t Q wq embP xin cms x π).mono fun _ _ h _ => h _ _ _ _ _

/-- **None is the second query of a seed, if the seeds' second plain part is no plain part of
round 2.** -/
theorem seedQ1_apart
    (embP : PlainPart Q.loc.shape Q.ann →
      PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) S.t) (annOf (typedOracleCarrier L Bd aT aL) S.t))
    (h1 : ∀ z, PlainPart.depth Q.loc.shape Q.ann z = 2 → embP z ≠ S.pl1) :
    (recomputeChainOfProof (L := typedOracleCarrier L Bd aT aL) S.t Q wq embP xin cms x π).AsksIn fun o q =>
      ∀ v, (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) ≠ ⟨OracleName.fb S.t, seedQ1 W S v⟩ :=
  (chain_ne_q1 S.t Q wq embP xin cms x π S.pl1 h1).mono fun _ _ h _ => h _ _

/-- A chain at another tag asks no query of the seeds' oracle. -/
theorem seed_apart_tag {t : Tag} (ht : S.t ≠ t)
    (embP : PlainPart Q.loc.shape Q.ann →
      PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t)) :
    (recomputeChainOfProof (L := typedOracleCarrier L Bd aT aL) t Q wq embP xin cms x π).AsksIn fun o q =>
      ∀ q' : FbIn lam (typedOracleCarrier L Bd aT aL) S.t,
        (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) ≠ ⟨OracleName.fb S.t, q'⟩ :=
  chain_ne_tag t Q wq embP xin cms x π ht

end

/-! ## At the chain of the compiled verifier of Test -/

/-- The chain of Test asks no query with round 1 and a head (F1), whatever list it is handed. -/
theorem testChain_ne_q0 (cms : List (Dig lam)) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    (recomputeChainOfProof (L := typedOracleCarrier L Bd aT aL) Tag.test (batTC L aT) (wTC W) id (fun _ => none) cms rec
      π).AsksIn fun o q => ∀ c y sl rt p, (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) ≠
        ⟨OracleName.fb Tag.test, (⟨1, .f1 c y sl, rt, p⟩ : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.test)⟩ :=
  chain_ne_q0 (L := typedOracleCarrier L Bd aT aL) Tag.test (batTC L aT) (wTC W) id (fun _ => none) cms rec π

/-- The chain of Test asks no query with round 2 and the plain part p1, if p1 is no plain part of
round 2 of Test. -/
theorem testChain_ne_q1 (cms : List (Dig lam)) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT))
    (p1 : PlainPart L.offline.shape aT) (h : PlainPart.depth L.offline.shape aT p1 ≠ 2) :
    (recomputeChainOfProof (L := typedOracleCarrier L Bd aT aL) Tag.test (batTC L aT) (wTC W) id (fun _ => none) cms rec
      π).AsksIn fun o q => ∀ hd rt, (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) ≠
        ⟨OracleName.fb Tag.test, (⟨2, hd, rt, p1⟩ : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.test)⟩ :=
  chain_ne_q1 (L := typedOracleCarrier L Bd aT aL) Tag.test (batTC L aT) (wTC W) id (fun _ => none) cms rec π
    p1
    fun z hz e => h (by rw [← show z = p1 from e]; exact hz)

end TypedOracleCompiler.Compile.Batch.Cms

/-! ## On the format's strings -/

namespace Fmt

/-- Two calls under different numbers have different strings. -/
theorem oStr_ne_number (h h' : UInt8) (hh : h = 0 ∨ h = 1) (hh' : h' = 0 ∨ h' = 1)
    (n n' t t' i i' : Nat) (s s' b b' : ByteArray) (hn : n ≠ n') (hd : hDom n t i s b = true)
    (hd' : hDom n' t' i' s' b' = true) : oStr h n t i s b ≠ oStr h' n' t' i' s' b' := fun e =>
  hn (oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ hh hh' hd hd' e).2.1

/-- A call of a round under the label of the seeds' chain is no call of a round under a label below
2^32. -/
theorem seedRound_ne (h h' : UInt8) (hh : h = 0 ∨ h = 1) (hh' : h' = 0 ∨ h' = 1) (l i i' : Nat)
    (ρ ρ' b b' : ByteArray) (hl : l < 2 ^ 32) (hd : hDom 162 recordLabel i ρ b = true)
    (hd' : hDom 162 l i' ρ' b' = true) :
    oStr h 162 recordLabel i ρ b ≠ oStr h' 162 l i' ρ' b' := fun e => by
  have e1 : recordLabel = l := (oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ hh hh' hd hd' e).2.2.1
  unfold recordLabel at e1
  omega

/-- The call for the first value under the label of the seeds' chain is no such call under a label
below 2^32. -/
theorem seedFirst_ne (h h' : UInt8) (hh : h = 0 ∨ h = 1) (hh' : h' = 0 ∨ h' = 1) (l : Nat)
    (s s' b b' : ByteArray) (hl : l < 2 ^ 32) (hd : hDom 160 0 recordLabel s b = true)
    (hd' : hDom 160 0 l s' b' = true) :
    oStr h 160 0 recordLabel s b ≠ oStr h' 160 0 l s' b' := fun e => by
  have e1 : recordLabel = l := (oStr_inj _ _ _ _ _ _ _ _ _ _ _ _ hh hh' hd hd' e).2.2.2.1
  unfold recordLabel at e1
  omega

/-- A chain that is started from parameters and a statement under a label that is not below 2^32 is
refused. -/
theorem startChainW_label {m : Type → Type} [Monad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (lab : Nat)
    (pd statement : ByteArray) (rnd : Option ByteArray) (hl : ¬ lab < 2 ^ 32) :
    startChainW h lab pd statement rnd = pure none := by
  unfold startChainW
  rw [if_neg hl]

end Fmt

namespace OnBytes.Slice
open _root_.Run

/-- **The string of a block of the seeds' round is no string of a call of a round under a label
below 2^32**: at a start of 32 bytes, whatever the other call's half, round, start and bytes. -/
theorem blockStr_ne_round (ρ0 : ByteArray) (h0 : ρ0.size = 32) (j : ℕ) (h' : UInt8)
    (hh' : h' = 0 ∨ h' = 1) (l i' : ℕ) (ρ' b' : ByteArray) (hl : l < 2 ^ 32)
    (hd' : Fmt.hDom 162 l i' ρ' b' = true) : blockStr ρ0 j ≠ Fmt.oStr h' 162 l i' ρ' b' :=
  Fmt.seedRound_ne _ h'
    (by
      rcases Nat.mod_two_eq_zero_or_one j with e | e <;> rw [e]
      · exact Or.inl rfl
      · exact Or.inr rfl)
    hh' l 1 i' ρ0 ρ' _ b' hl (blockStr_dom ρ0 h0 (j / 2)) hd'

/-- **The string of a table's name is no string of a call for a first value under a label below
2^32**: for names of at most 2^31 bytes. -/
theorem seedFirst_ne_first (name : ByteArray) (hn : name.size ≤ 2 ^ 31) (h' : UInt8)
    (hh' : h' = 0 ∨ h' = 1) (l : ℕ) (s' b' : ByteArray) (hl : l < 2 ^ 32)
    (hd' : Fmt.hDom 160 0 l s' b' = true) : seedFirst name ≠ Fmt.oStr h' 160 0 l s' b' :=
  Fmt.seedFirst_ne 0 h' (Or.inl rfl) hh' l Fmt.zero32 s' _ b' hl
    (dom0 160 Fmt.recordLabel _ (by decide) (by decide) (by decide) (by
      rw [size_seedBytes]
      omega)) hd'

end OnBytes.Slice

#print axioms TypedOracleCompiler.Compile.Batch.chainB_round
#print axioms TypedOracleCompiler.Compile.Batch.chainB_f1
#print axioms TypedOracleCompiler.Compile.Batch.chainB_tag
#print axioms TypedOracleCompiler.Compile.Batch.chain_ne_q0
#print axioms TypedOracleCompiler.Compile.Batch.chain_ne_q1
#print axioms TypedOracleCompiler.Compile.Batch.chain_ne_tag
#print axioms TypedOracleCompiler.Compile.Batch.chain_meets_q1
#print axioms TypedOracleCompiler.Compile.Batch.Cms.seedQ0_apart
#print axioms TypedOracleCompiler.Compile.Batch.Cms.seedQ1_apart
#print axioms TypedOracleCompiler.Compile.Batch.Cms.seed_apart_tag
#print axioms TypedOracleCompiler.Compile.Batch.Cms.testChain_ne_q0
#print axioms TypedOracleCompiler.Compile.Batch.Cms.testChain_ne_q1
#print axioms Fmt.oStr_ne_number
#print axioms Fmt.seedRound_ne
#print axioms Fmt.seedFirst_ne
#print axioms Fmt.startChainW_label
#print axioms OnBytes.Slice.blockStr_ne_round
#print axioms OnBytes.Slice.seedFirst_ne_first
