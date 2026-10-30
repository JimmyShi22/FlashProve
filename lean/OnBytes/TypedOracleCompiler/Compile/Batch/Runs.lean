-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Runs.lean: a second form of Compile/Batch/Runs.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/Runs.lean, comments apart: definitions: `VStep`,
`RtFlags`, `z0Of`, `zJOf`; statements: `isSome_of_takeRt`, `extSyms_congr`, `msgStar_congr`,
`sym_eq_of_checksOpt`; proofs alone: `runsIn_chainB_cons_flags`, `read_mkTr_eq`; new here:
`mem_checksTrees`. Every other declaration has that file's text.

Where the head below explains `RtC`: here it is `Option (List (Dig lam))`: none: the component is
not sent; some []: it is sent and has no tree (only its plain part is sent); some rts: it is sent,
and rts are the roots of its trees. Where it explains `mkTr`: here an opened symbol counts where the
tree of its position has a root (`rootAt`).

The rest of this head is the head of Compile/Batch/Runs.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Runs.lean: what an accepting run of the compiled verifier of a slot leaves in the
trace; the transcript τ∗ (`trStar`); outside the hash event `EM` and under the hypotheses there,
opened symbols are extracted symbols (`read_mkTr_eq`). (Words of this library: lean/GLOSSARY.md.)

`RunsIn` (Compile/Spec.lean): a coin-free algorithm returns a value when a trace answers its
queries.

Notation:
  the cases of `VStep`: `f1`, `f2`, `f3`, `f5`: a Fiat-Shamir query in the format (F1), (F2), (F3),
    (F5); `join`: the joining round: the query (G) to g and the query (F4); `f2'`: (F2) from the
    phase `.aft` (`Head`, `JoiningRoundQuery`: Compile/Batch/Oracles.lean)
  `Phase`: how far the chain of a slot has come: `.first`, `.loc ρ`, `.shr ρ0 c`, `.aft ρ c`; c: the
    slot value, once the chain has passed the joining round (Compile/Batch/Verifier.lean)
  `cms`: List (Dig lam), the external roots; `salt`, `rtreq`: the fields of the proof string `OneProtocolProof`:
    the salt, the request root; `pl`, `pls`: the plain parts; `embP`: a map of the protocol's plain
    parts into those of protocol t
  `RtC`: what the chain yields for one component of one round: none: the component is not sent; some
    none: it is sent and has no tree; some (some rt): it is sent, and rt is the root of its tree;
    `RootsOfChain`: for each round: what the chain yields for the shared component, and for the slot's
    component
  `effPlain`: the plain part of a round: of each component what the proof string holds, if the
    component is sent, and else that of the fixed message; `mkTr`: a transcript from the proof
    string: opened symbols where there are any and their component has a root, the fixed symbol 0
    elsewhere (all: Compile/Batch/Verifier.lean)

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Facts

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Part 1. The chain, round by round -/

/-- the Fiat-Shamir query of an item -/
def Item.q {t : Tag} : Item lam L t → FbIn lam L t
  | .lo q => q
  | .jn _ q => q
  | .sh q => q

section VStep
variable {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}

/-- One round of the verifier's chain: from the phase ph, with the item cur and the answer ans of
its Fiat-Shamir query, to the next phase; rt holds the roots of the round. -/
inductive VStep (tr : Trace (typedOracleFamily lam K L)) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (pl : r.Plain) :
    Phase lam → Item lam L t → FsAns lam K → Phase lam → RtC lam × RtC lam → Prop
  | f1 (root : List (Dig lam)) (ans : FsAns lam K) :
      a.kind = .lo →
      VStep tr cms x salt rtreq embP i pl .first
        (.lo ⟨i, .f1 cms (x.map L.early) salt, root, embP (.inl (.inr (a.plain pl).2))⟩) ans
        (.loc (link ans)) (none, some root)
  | f2 (ρ : Bits) (root : List (Dig lam)) (ans : FsAns lam K) :
      a.kind = .lo →
      VStep tr cms x salt rtreq embP i pl (.loc ρ)
        (.lo ⟨i, .f2 (lateInstancePart L i x) ρ, root, embP (.inl (.inr (a.plain pl).2))⟩) ans
        (.loc (link ans)) (none, some root)
  | join (ρ : Bits) (rtj rt0 : List (Dig lam)) (c : Dig lam) (ans : FsAns lam K) :
      a.kind = .sh → gE t (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t) c ∈ tr →
      VStep tr cms x salt rtreq embP i pl (.loc ρ)
        (.jn ⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩
          ⟨i, .f4 cms (List.ofFn rtreq), rt0, embP (.inl (.inl (a.plain pl).1))⟩)
        ans (.shr (link ans) c) (some rt0, some rtj)
  | f5 (ρ0 : Bits) (c : Dig lam) (root : List (Dig lam)) (ans : FsAns lam K) :
      a.kind = .sh →
      VStep tr cms x salt rtreq embP i pl (.shr ρ0 c)
        (.sh ⟨i, .f5 ρ0, root, embP (.inl (.inl (a.plain pl).1))⟩) ans
        (.shr (link ans) c) (some root, none)
  | f3 (ρ0 : Bits) (c : Dig lam) (root : List (Dig lam)) (ans : FsAns lam K) :
      a.kind = .lo →
      VStep tr cms x salt rtreq embP i pl (.shr ρ0 c)
        (.lo ⟨i, .f3 ρ0 (List.ofFn c), root, embP (.inl (.inr (a.plain pl).2))⟩) ans
        (.aft (link ans) c) (none, some root)
  | f2' (ρ : Bits) (c : Dig lam) (root : List (Dig lam)) (ans : FsAns lam K) :
      a.kind = .lo →
      VStep tr cms x salt rtreq embP i pl (.aft ρ c)
        (.lo ⟨i, .f2 (lateInstancePart L i x) ρ, root, embP (.inl (.inr (a.plain pl).2))⟩) ans
        (.aft (link ans) c) (none, some root)

variable {tr : Trace (typedOracleFamily lam K L)} {cms : List (Dig lam)} {x : Option X} {salt : Bits}
  {rtreq : Dig lam} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
  {pl : r.Plain} {ph ph₁ : Phase lam} {cur : Item lam L t} {ans : FsAns lam K}
  {rt : RtC lam × RtC lam}

/-- The kind of the item is that of the round; its fields are the roots of the round with the plain
parts of the proof string; its query has the number of the round. -/
theorem VStep.fields (h : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt) :
    cur.kind = a.kind ∧ cur.q.round = i ∧
    cur.shd = rt.1.map (fun c => (c, embP (.inl (.inl (a.plain pl).1)))) ∧
    cur.own = rt.2.map (fun c => (c, embP (.inl (.inr (a.plain pl).2)))) := by
  cases h with
  | f1 root ans hk => exact ⟨hk.symm, rfl, rfl, rfl⟩
  | f2 ρ root ans hk => exact ⟨hk.symm, rfl, rfl, rfl⟩
  | join ρ rtj rt0 c ans hk hg => exact ⟨hk.symm, rfl, rfl, rfl⟩
  | f5 ρ0 c root ans hk => exact ⟨hk.symm, rfl, rfl, rfl⟩
  | f3 ρ0 c root ans hk => exact ⟨hk.symm, rfl, rfl, rfl⟩
  | f2' ρ c root ans hk => exact ⟨hk.symm, rfl, rfl, rfl⟩

/-- Once the chain has joined, a round keeps the slot value. -/
theorem VStep.slotVal (h : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt)
    {c : Dig lam} (hc : ph.slotVal = some c) : ph₁.slotVal = some c := by
  cases h <;> first | exact hc | cases hc

end VStep

/-- as many roots are taken from the list as the component has trees, and at most maxRt -/
theorem isSome_of_takeRt {n : ℕ} {rts rts' : List (Dig lam)} {root : List (Dig lam)}
    (h : takeRt n rts = some (root, rts')) : root.length = n ∧ n ≤ maxRt := by
  unfold takeRt at h
  split at h
  · rename_i hn
    cases h
    exact ⟨List.length_take_of_le hn.2, hn.1⟩
  · cases h

/-- What the wire says of the roots of a round: a component that is sent has as many roots as it has
trees, and at most maxRt. -/
def RtFlags {r : Round} {a : RAnn r} (w : WireRB lam K r a) (rt : RtC lam × RtC lam) : Prop :=
  (∀ x, rt.1 = some x → x.length = w.depth0.length ∧ w.depth0.length ≤ maxRt) ∧
    ∀ x, rt.2 = some x → x.length = w.depthJ.length ∧ w.depthJ.length ≤ maxRt

/-- The chain, one round, with the flags (`RtFlags`): if `recomputeChain` on the rounds r :: s runs in the
trace to some ((c, ρ), (rt, RTs), ph'), then there are an item cur, an answer ans, a phase ph₁ and
a list of roots rts' with: a `VStep` of cur, ans and rt from ph to ph₁; the query of cur with the
answer ans is in the trace; c = w.chal ans.1; `recomputeChain` on s, from round i + 1, ph₁ and rts', runs
in the trace to some (ρ, RTs, ph'); and `RtFlags w rt`. -/
theorem runsIn_chainB_cons_flags {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {w : WireRB lam K r a} {ws : RoundsQueryLayout lam K s A}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} {ph ph' : Phase lam}
    {rts : List (Dig lam)} {pl : r.Plain} {pls : Plains s} {c : r.Chal} {ρ : Rho s}
    {rt : RtC lam × RtC lam} {RTs : RootsOfChain lam s}
    (h : RunsIn tr
      (recomputeChain (K := K) t cms x salt rtreq (r :: s) (a, A) (w, ws) embP i ph rts (pl, pls))
      (some ((c, ρ), (rt, RTs), ph'))) :
    ∃ (cur : Item lam L t) (ans : FsAns lam K) (ph₁ : Phase lam) (rts' : List (Dig lam)),
      VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt ∧
      fbE t cur.q ans ∈ tr ∧
      c = w.chal ans.1 ∧
      RunsIn tr
        (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1) ph₁ rts' pls)
        (some (ρ, RTs, ph')) ∧
      RtFlags w rt := by
  -- one query, with the slot's component or with the shared one
  have one : ∀ (hd : Head lam X) (next : Bits → Phase lam) (root : List (Dig lam))
        (rts' : List (Dig lam)) (α : PlainPart (shapeOf L t) (annOf L t)) (rt' : RtC lam × RtC lam),
      RunsIn tr ((askTypedOracle (L := L) (K := K) (OracleName.fb t)
          (⟨i, hd, root, α⟩ : FbIn lam L t)).bind fun ans =>
            (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1)
              (next (List.ofFn ans.2)) rts' pls).bind fun r' =>
                OComp.pure
                  (r'.map fun z =>
                    (((w.chal ans.1, z.1), (rt', z.2.1), z.2.2) :
                      Rho (r :: s) × RootsOfChain lam (r :: s) × Phase lam)))
        (some ((c, ρ), (rt, RTs), ph')) →
      ∃ ans : FsAns lam K,
        fbE t (⟨i, hd, root, α⟩ : FbIn lam L t) ans ∈ tr ∧ c = w.chal ans.1 ∧ rt = rt' ∧
        RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1)
            (next (link ans)) rts' pls)
          (some (ρ, RTs, ph')) := by
    intro hd next root rts' α rt' h'
    obtain ⟨ans, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
    obtain ⟨r', hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
    have h4 := runsIn_pure_iff.1 h3
    cases r' with
    | none => cases h4
    | some z =>
      obtain ⟨ρ', RTs', ph''⟩ := z
      have h5 : (((w.chal ans.1, ρ'), (rt', RTs'), ph'') :
            (r.Chal × Rho s) × ((RtC lam × RtC lam) × RootsOfChain lam s) × Phase lam) =
          ((c, ρ), (rt, RTs), ph') :=
        Option.some.inj h4
      simp only [Prod.mk.injEq] at h5
      obtain ⟨⟨h6, rfl⟩, ⟨h7, rfl⟩, rfl⟩ := h5
      exact ⟨ans, runsIn_ask_iff.1 ha, h6.symm, h7.symm, hr'⟩
  unfold recomputeChain at h
  cases hk : a.kind with
  | lo =>
    cases ph with
    | first =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.depthJ.length rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ _ _ _ _ _ h
        exact ⟨_, ans, _, rts', VStep.f1 root ans hk, h1, h2, h4,
          ⟨fun _ e => (nomatch e), fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt⟩⟩
    | loc ρ' =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.depthJ.length rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ _ _ _ _ _ h
        exact ⟨_, ans, _, rts', VStep.f2 ρ' root ans hk, h1, h2, h4,
          ⟨fun _ e => (nomatch e), fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt⟩⟩
    | shr ρ0 cv =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.depthJ.length rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ (fun v => Phase.aft v cv) _ _ _ _ h
        exact ⟨_, ans, _, rts', VStep.f3 ρ0 cv root ans hk, h1, h2, h4,
          ⟨fun _ e => (nomatch e), fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt⟩⟩
    | aft ρ' cv =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.depthJ.length rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ (fun v => Phase.aft v cv) _ _ _ _ h
        exact ⟨_, ans, _, rts', VStep.f2' ρ' cv root ans hk, h1, h2, h4,
          ⟨fun _ e => (nomatch e), fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt⟩⟩
  | sh =>
    cases ph with
    | first => simp only [hk, actOf] at h; cases runsIn_pure_iff.1 h
    | aft ρ' cv => simp only [hk, actOf] at h; cases runsIn_pure_iff.1 h
    | shr ρ0 cv =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.depth0.length rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨root, rts'⟩ := z
        simp only [hrt] at h
        obtain ⟨ans, h1, h2, rfl, h4⟩ := one _ (fun v => Phase.shr v cv) _ _ _ _ h
        exact ⟨_, ans, _, rts', VStep.f5 ρ0 cv root ans hk, h1, h2, h4,
          ⟨fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt, fun _ e => nomatch e⟩⟩
    | loc ρ' =>
      simp only [hk, actOf] at h
      cases hrt : takeRt w.depthJ.length rts with
      | none => simp only [hrt] at h; cases runsIn_pure_iff.1 h
      | some z =>
        obtain ⟨rtj, rts1⟩ := z
        simp only [hrt] at h
        cases hrt0 : takeRt w.depth0.length rts1 with
        | none => simp only [hrt0] at h; cases runsIn_pure_iff.1 h
        | some z0 =>
          obtain ⟨rt0, rts'⟩ := z0
          simp only [hrt0] at h
          rw [bind_eq] at h
          obtain ⟨cv, hc, h2⟩ := (runsIn_bind_iff _ _ _).1 h
          obtain ⟨ans, h1, h3, rfl, h4⟩ := one _ (fun v => Phase.shr v cv) _ _ _ _ h2
          exact ⟨_, ans, _, rts', VStep.join ρ' rtj rt0 cv ans hk (runsIn_ask_iff.1 hc), h1, h3, h4,
            ⟨fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt0,
              fun _ e => Option.some.inj e ▸ isSome_of_takeRt hrt⟩⟩

/-- `runsIn_chainB_cons_flags` without the clause `RtFlags`. -/
theorem runsIn_chainB_cons {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {w : WireRB lam K r a} {ws : RoundsQueryLayout lam K s A}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ} {ph ph' : Phase lam}
    {rts : List (Dig lam)} {pl : r.Plain} {pls : Plains s} {c : r.Chal} {ρ : Rho s}
    {rt : RtC lam × RtC lam} {RTs : RootsOfChain lam s}
    (h : RunsIn tr
      (recomputeChain (K := K) t cms x salt rtreq (r :: s) (a, A) (w, ws) embP i ph rts (pl, pls))
      (some ((c, ρ), (rt, RTs), ph'))) :
    ∃ (cur : Item lam L t) (ans : FsAns lam K) (ph₁ : Phase lam) (rts' : List (Dig lam)),
      VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt ∧
      fbE t cur.q ans ∈ tr ∧
      c = w.chal ans.1 ∧
      RunsIn tr
        (recomputeChain (K := K) t cms x salt rtreq s A ws (fun z => embP (.inr z)) (i + 1) ph₁ rts' pls)
        (some (ρ, RTs, ph')) := by
  obtain ⟨cur, ans, ph₁, rts', h1, h2, h3, h4, -⟩ := runsIn_chainB_cons_flags h
  exact ⟨cur, ans, ph₁, rts', h1, h2, h3, h4⟩

/-- Once the chain has joined, the slot value is kept to the end. -/
theorem slotVal_of_chainB {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s) (c : Dig lam),
      ph.slotVal = some c →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      ph'.slotVal = some c
  | [], _, _, _, _, ph, ph', _, _, _, _, c, hc, h => by
      have h1 : some (((), (), ph) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact hc
  | _ :: s, (_, A), (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (_, RTs), c, hc, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      exact slotVal_of_chainB s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs c (hv.slotVal hc) hr

/-! ## Part 2. The transcript τ∗ -/

section Star
variable {r : Round} {a : RAnn r}

/-- Here: the roots and the plain part of the shared component of a round, as the proof string gives
them; nothing if the component is not sent -/
def z0Of (a : RAnn r) (rt : RtC lam × RtC lam) (pl : r.Plain) : List (Dig lam) × Option a.P0 :=
  (rt.1.getD [], rt.1.map fun _ => (a.plain pl).1)
def zJOf (a : RAnn r) (rt : RtC lam × RtC lam) (pl : r.Plain) : List (Dig lam) × Option a.Pj :=
  (rt.2.getD [], rt.2.map fun _ => (a.plain pl).2)

/-- the prover message of a round with the oracles that the trace determines under the roots of the
proof string -/
def msgStar (tr : Trace (typedOracleFamily lam K L)) (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (rt : RtC lam × RtC lam) (pl : r.Plain) :
    r.Msg :=
  a.join (m0Of tr w prj (z0Of a rt pl)) (mJOf tr w prj (zJOf a rt pl))

theorem msgStar_plain (h : a.Coherent) (tr : Trace (typedOracleFamily lam K L)) (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (rt : RtC lam × RtC lam) (pl : r.Plain) :
    (msgStar tr w prj rt pl).2 = effPlain a rt pl := by
  unfold msgStar m0Of mJOf
  rw [plain_join w.pt h]
  obtain ⟨r0, rJ⟩ := rt
  cases r0 <;> cases rJ <;> rfl

theorem extSyms_congr {tr tr' : Trace (typedOracleFamily lam K L)} (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (depth : List ℕ) {rt : List (Dig lam)}
    (h : ∀ c ∈ rt, ∀ d j, extLeaf tr d c j = extLeaf tr' d c j) :
    extSyms tr w prj depth rt = extSyms tr' w prj depth rt := by
  funext p
  unfold extSyms
  cases hd : depth[w.tree p]? with
  | none => rfl
  | some d =>
    cases hc : rt[w.tree p]? with
    | none => rfl
    | some c =>
      show (match extLeaf tr d c (w.place p) with | some x => _ | none => _) =
        (match extLeaf tr' d c (w.place p) with | some x => _ | none => _)
      rw [h c (List.mem_of_getElem? hc)]

/-- The message depends on the trace only through what stands under its roots. -/
theorem msgStar_congr {tr tr' : Trace (typedOracleFamily lam K L)} (w : WireRB lam K r a)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) {rt : RtC lam × RtC lam} (pl : r.Plain)
    (h : ∀ c,
      c ∈ rt.1.getD [] ∨ c ∈ rt.2.getD [] → ∀ d j, extLeaf tr d c j = extLeaf tr' d c j) :
    msgStar tr w prj rt pl = msgStar tr' w prj rt pl := by
  unfold msgStar m0Of mJOf
  rw [show extSyms tr w prj w.depth0 (z0Of a rt pl).1 = extSyms tr' w prj w.depth0 (z0Of a rt pl).1
        from extSyms_congr w prj _ fun c hc => h c (Or.inl hc),
    show extSyms tr w prj w.depthJ (zJOf a rt pl).1 = extSyms tr' w prj w.depthJ (zJOf a rt pl).1
      from extSyms_congr w prj _ fun c hc => h c (Or.inr hc)]

/-- Under the hypotheses below: the item of a round of the verifier's chain gives the message with
the roots and plain parts of the proof string. -/
theorem msgOf_of_fields {t : Tag} {s : Shape} {A : RoundSplits s} (tr : Trace (typedOracleFamily lam K L))
    (w : WireRB lam K r a) (prj : (p : r.Pos) → Body L → Option (r.Sym p))
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart (r :: s) (a, A))}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} (hprj : ∀ z, prjP (embP z) = some z)
    {cur : Item lam L t} {rt : RtC lam × RtC lam} {pl : r.Plain} (hk : cur.kind = a.kind)
    (h0 : cur.shd = rt.1.map (fun c => (c, embP (.inl (.inl (a.plain pl).1)))))
    (hJ : cur.own = rt.2.map (fun c => (c, embP (.inl (.inr (a.plain pl).2))))) :
    msgOf tr w prj prjP cur = some (msgStar tr w prj rt pl) := by
  have e0 : rd0 prjP cur.shd = some (z0Of a rt pl) := by
    rw [h0]
    obtain ⟨r0, rJ⟩ := rt
    cases r0 with
    | none => rfl
    | some c =>
      show ((prjP (embP _)).bind PlainPart.head0?).map _ = _
      rw [hprj]
      rfl
  have eJ : rdJ prjP cur.own = some (zJOf a rt pl) := by
    rw [hJ]
    obtain ⟨r0, rJ⟩ := rt
    cases rJ with
    | none => rfl
    | some c =>
      show ((prjP (embP _)).bind PlainPart.headJ?).map _ = _
      rw [hprj]
      rfl
  unfold msgOf
  rw [if_pos hk, e0, eJ]
  rfl

end Star

/-- τ∗: the slot's transcript whose prover messages have the oracles that the whole trace determines
under the roots of the proof string, with its plain parts, and the verifier messages of the
chain. -/
def trStar (tr : Trace (typedOracleFamily lam K L)) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → Body L → Option (OSym s p)) →
    RootsOfChain lam s → Plains s → Rho s → Tr s
  | [], _, _, _, _, _, _ => ()
  | _ :: s, (_, A), (w, ws), prjS, (rt, rts), (pl, pls), (c, ρ) =>
      (msgStar tr w (fun p => prjS (.inl p)) rt pl,
        c,
        trStar tr s A ws (fun p => prjS (.inr p)) rts pls ρ)

theorem trStar_rho (tr : Trace (typedOracleFamily lam K L)) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s)
        (pls : Plains s) (ρ : Rho s),
      (trStar tr s A ws prjS rts pls ρ).rho = ρ
  | [], _, _, _, _, _, () => rfl
  | _ :: s, (_, A), (_, ws), prjS, (_, rts), (_, pls), (c, ρ) =>
      congrArg (Prod.mk c) (trStar_rho tr s A ws (fun p => prjS (.inr p)) rts pls ρ)

theorem trStar_plains (tr : Trace (typedOracleFamily lam K L)) :
    ∀ (s : Shape) (A : RoundSplits s), A.Coherent →
      ∀ (ws : RoundsQueryLayout lam K s A) (prjS : (p : OPos s) → Body L → Option (OSym s p)) (rts : RootsOfChain lam s)
          (pls : Plains s) (ρ : Rho s),
        (trStar tr s A ws prjS rts pls ρ).plains = effPlains s A rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), h, (w, ws), prjS, (rt, rts), (pl, pls), (_, ρ) => by
      show ((msgStar tr w _ rt pl).2, (trStar tr s A ws _ rts pls ρ).plains) = (_, _)
      rw [msgStar_plain h.1, trStar_plains tr s A h.2]

theorem mkTr_rho :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (pls : Plains s) (ρ : Rho s)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))),
      (mkTr s A ws rts pls ρ f).rho = ρ
  | [], _, _, _, _, (), _ => rfl
  | _ :: s, (_, A), (_, ws), (_, rts), (_, pls), (c, ρ), f =>
    congrArg (Prod.mk c) (mkTr_rho s A ws rts pls ρ fun p => f (.inr p))

theorem mkTr_plains :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (pls : Plains s) (ρ : Rho s)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))),
      (mkTr s A ws rts pls ρ f).plains = effPlains s A rts pls
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (_, ws), (rt, rts), (pl, pls), (_, ρ), f =>
      congrArg (Prod.mk (effPlain a rt pl)) (mkTr_plains s A ws rts pls ρ fun p => f (.inr p))

/-! ## Part 3. Checks -/

section Checks
variable {tr : Trace (typedOracleFamily lam K L)}

/-- If all checks together pass, each of them passes. -/
theorem runsIn_runCheck_of_runChecks :
    ∀ (cs : List (Check lam L)),
      RunsIn tr (runChecks (K := K) cs) true → ∀ c ∈ cs, RunsIn tr (runCheck (K := K) c) true
  | [], _, _, hc => by cases hc
  | c0 :: cs, h, c, hc => by
      have h' : RunsIn tr
          ((runCheck (K := K) c0).bind fun a =>
            (runChecks (K := K) cs).bind fun b => OComp.pure (a && b)) true := h
      obtain ⟨a, ha, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨b, hb, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      have h4 : (a && b) = true := runsIn_pure_iff.1 h3
      obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.1 h4
      rcases List.mem_cons.1 hc with rfl | hc'
      · exact ha
      · exact runsIn_runCheck_of_runChecks cs hb c hc'

/-- If `checksComp` returns checks for js: every read position at a leaf of js has an opening, and
its check is among them. -/
theorem mem_checksComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) (cs : List (Check lam L)), checksComp posAt depth emb rt isRead f js = some cs →
      ∀ j ∈ js, ∀ p, posAt j = some p → isRead p = true →
        ∃ op, f p = some op ∧ (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ : Check lam L) ∈ cs
  | [], _, _, _, hj, _, _, _ => by cases hj
  | j0 :: js, cs, h, j, hj, p, hp, hr => by
      simp only [checksComp] at h
      cases h0 : posAt j0 with
      | none =>
        rw [h0] at h
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [h0] at hp; cases hp
        · exact mem_checksComp posAt depth emb rt isRead f js cs h j hj' p hp hr
      | some p0 =>
        rw [h0] at h
        by_cases hr0 : isRead p0 = true
        · simp only [hr0, if_true] at h
          cases hf : f p0 with
          | none => rw [hf] at h; cases h
          | some op =>
            cases hc : checksComp posAt depth emb rt isRead f js with
            | none => rw [hf, hc] at h; cases h
            | some cs' =>
              rw [hf, hc] at h
              cases h
              rcases List.mem_cons.1 hj with rfl | hj'
              · rw [h0] at hp; cases hp
                exact ⟨op, hf, List.mem_cons_self⟩
              · obtain ⟨op', h1, h2⟩ :=
                  mem_checksComp posAt depth emb rt isRead f js cs' hc j hj' p hp hr
                exact ⟨op', h1, List.mem_cons_of_mem _ h2⟩
        · simp only [hr0] at h
          rcases List.mem_cons.1 hj with rfl | hj'
          · rw [h0] at hp; cases hp
            exact absurd hr hr0
          · exact mem_checksComp posAt depth emb rt isRead f js cs h j hj' p hp hr

/-- Here: the checks of a tree that has a depth and a root are among what checksTrees yields. -/
theorem mem_checksTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (rt : List (Dig lam)) (l : List (ℕ × Dig lam × List (Check lam L))),
      checksTrees posAt emb isRead f k ds rt = some l →
      ∀ (i d : ℕ) (c : Dig lam), ds[i]? = some d → rt[i]? = some c →
        ∃ cs, checksComp (posAt (k + i)) d emb c isRead f (List.range (2 ^ d)) = some cs ∧
          (d, c, cs) ∈ l
  | _, [], _, _, _, _, _, _, hd, _ => by simp at hd
  | _, _ :: _, [], _, _, _, _, _, _, hc => by simp at hc
  | k, d0 :: ds, c0 :: rt, l, h, i, d, c, hd, hc => by
      simp only [checksTrees] at h
      cases h1 : checksComp (posAt k) d0 emb c0 isRead f (List.range (2 ^ d0)) with
      | none => rw [h1] at h; cases h
      | some a =>
        cases h2 : checksTrees posAt emb isRead f (k + 1) ds rt with
        | none => rw [h1, h2] at h; cases h
        | some b =>
          rw [h1, h2] at h
          cases h
          cases i with
          | zero =>
            cases Option.some.inj hd
            cases Option.some.inj hc
            exact ⟨a, h1, List.mem_cons_self⟩
          | succ i =>
            obtain ⟨cs', h3, h4⟩ := mem_checksTrees posAt emb isRead f (k + 1) ds rt b h2 i d c
              (by simpa using hd) (by simpa using hc)
            exact ⟨cs', by rwa [show k + (i + 1) = k + 1 + i by omega], List.mem_cons_of_mem _ h4⟩

/-- The same for the external strings (`checksExt`). -/
theorem mem_checksExt {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ (ps : List E.Pos) (cs : List (Check lam L)), checksExt we emb cms isRead g ps = some cs →
      ∀ p ∈ ps, isRead p = true →
        ∃ op,
          g p = some op ∧
          (⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
              cms.getD (we.which p) default, we.depth⟩ : Check lam L) ∈ cs
  | [], _, _, _, hp, _ => by cases hp
  | p0 :: ps, cs, h, p, hp, hr => by
      simp only [checksExt] at h
      by_cases hr0 : isRead p0 = true
      · simp only [hr0, if_true] at h
        cases hf : g p0 with
        | none => rw [hf] at h; cases h
        | some op =>
          cases hc : checksExt we emb cms isRead g ps with
          | none => rw [hf, hc] at h; cases h
          | some cs' =>
            rw [hf, hc] at h
            cases h
            rcases List.mem_cons.1 hp with rfl | hp'
            · exact ⟨op, hf, List.mem_cons_self⟩
            · obtain ⟨op', h1, h2⟩ := mem_checksExt we emb cms isRead g ps cs' hc p hp' hr
              exact ⟨op', h1, List.mem_cons_of_mem _ h2⟩
      · simp only [hr0] at h
        rcases List.mem_cons.1 hp with rfl | hp'
        · exact absurd hr hr0
        · exact mem_checksExt we emb cms isRead g ps cs h p hp' hr

/-- One component of one round: at a read position, the opened symbol is the extracted one; if the
component is not sent, both are 0. -/
theorem sym_eq_of_checksOpt (hM : ¬ EM tr) {r : Round} {a : RAnn r} (w : WireRB lam K r a)
    (posAt : ℕ → ℕ → Option r.Pos) (depth : List ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (prj : (p : r.Pos) → Body L → Option (r.Sym p)) (hprj : ∀ p x, prj p (emb p x) = some x)
    (rt : List (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (cs : List (Check lam L))
    (hcs : checksOpt posAt depth emb rt isRead f = some cs)
    (hall : ∀ c ∈ cs, c.wellFormed = true ∧ RunsIn tr (runCheck (K := K) c) true)
    (p : r.Pos) (hlt : ∃ d, depth[w.tree p]? = some d ∧ w.place p < 2 ^ d)
    (hpos : posAt (w.tree p) (w.place p) = some p) (hr : isRead p = true) :
    (match (rt[w.tree p]?).isSome, f p with
      | true, some op => op.sym
      | _, _ => w.pt.zero p) = extSyms tr w prj depth rt p := by
  obtain ⟨d, hd, hlt⟩ := hlt
  unfold extSyms
  rw [hd]
  cases hc : rt[w.tree p]? with
  | none => rfl
  | some c =>
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hcs
    obtain ⟨cs', h1, h2⟩ := mem_checksTrees posAt emb isRead f 0 depth rt l hl (w.tree p) d c hd hc
    rw [Nat.zero_add] at h1
    obtain ⟨op, hop, hmem⟩ := mem_checksComp
      (posAt (w.tree p)) d emb c isRead f _ cs' h1 (w.place p) (List.mem_range.2 hlt) p hpos hr
    obtain ⟨hwf, hrun⟩ := hall _ (List.mem_flatMap.2 ⟨_, h2, hmem⟩)
    have hx : extLeaf tr d c (w.place p) = some ⟨emb p op.sym, op.salt⟩ :=
      extLeaf_of_check _ hM hwf hrun
    show (match true, f p with
      | true, some op => op.sym
      | _, _ => w.pt.zero p) = (match extLeaf tr d c (w.place p) with
        | some x => (prj p x.body).getD (w.pt.zero p)
        | none => w.pt.zero p)
    rw [hop, hx]
    show op.sym = (prj p (emb p op.sym)).getD _
    rw [hprj]
    rfl

/-- Opened symbols are extracted symbols (openings agree with extraction, at all read positions of
the prover's oracles): outside `EM` and under the hypotheses below, at every position that the
slot's verifier reads, the transcript that the compiled verifier builds from the proof string and τ∗
hold the same symbol. -/
theorem read_mkTr_eq (hM : ¬ EM tr) :
    ∀ (s : Shape) (A : RoundSplits s), A.Coherent →
      ∀ (ws : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A ws →
        ∀ (embS : (p : OPos s) → OSym s p → Body L)
            (prjS : (p : OPos s) → Body L → Option (OSym s p)),
          (∀ p x, prjS p (embS p x) = some x) →
          ∀ (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
              (f : (p : OPos s) → Option (Opening lam (OSym s p))) (cs : List (Check lam L)),
            checksB s A ws embS rts isRead f = some cs →
            (∀ c ∈ cs, c.wellFormed = true ∧ RunsIn tr (runCheck (K := K) c) true) →
            ∀ (pls : Plains s) (ρ : Rho s) (p : OPos s), isRead p = true →
              (mkTr s A ws rts pls ρ f).read p = (trStar tr s A ws prjS rts pls ρ).read p
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, p, _ => nomatch p
  | r :: s, (a, A), hco, (w, ws), hws, embS, prjS, hprj, (rt, rts), isRead, f, cs, hcs, hall,
      (pl, pls), (c, ρ), p, hp =>
      by
      simp only [checksB] at hcs
      cases h0 : checksOpt w.posAt0 w.depth0 (fun p => embS (.inl p)) (rt.1.getD [])
          (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
      | none => rw [h0] at hcs; cases hcs
      | some c0 =>
        cases hJ : checksOpt w.posAtJ w.depthJ (fun p => embS (.inl p)) (rt.2.getD [])
            (fun p => isRead (.inl p)) (fun p => f (.inl p)) with
        | none => rw [h0, hJ] at hcs; cases hcs
        | some cJ =>
          cases h2 : checksB s A ws (fun p => embS (.inr p)) rts
              (fun p => isRead (.inr p)) (fun p => f (.inr p)) with
          | none => rw [h0, hJ, h2] at hcs; cases hcs
          | some c2 =>
            rw [h0, hJ, h2] at hcs
            cases hcs
            match p, hp with
            | .inl q, hp =>
              show r.rd (w.pt.ofSyms _) q = r.rd (msgStar tr w (fun p => prjS (.inl p)) rt pl).1 q
              unfold msgStar m0Of mJOf
              rw [w.pt.rd_ofSyms, rd_join w.pt hco.1]
              by_cases ho : a.own q = true
              · rw [if_pos ho]
                have := sym_eq_of_checksOpt hM w w.posAtJ w.depthJ (fun p => embS (.inl p))
                  (fun p => prjS (.inl p)) (fun p x => hprj (.inl p) x) (rt.2.getD []) _ _ cJ hJ
                  (fun c hc => hall c (List.mem_append_left _ (List.mem_append_right _ hc))) q
                  (hws.1.place_ltJ q ho) (hws.1.posAtJ_place q ho) hp
                have hs : rootAt w rt q = ((rt.2.getD [])[w.tree q]?).isSome := by
                  simp only [rootAt, ho, if_true]
                rw [hs]
                show _ = extSyms tr w (fun p => prjS (.inl p)) w.depthJ (rt.2.getD []) q
                rw [← this]
                generalize ((rt.2.getD [])[w.tree q]?).isSome = b
                generalize f (Sum.inl q) = o
                cases b <;> cases o <;> rfl
              · have ho' : a.own q = false := by simpa using ho
                rw [if_neg ho]
                have := sym_eq_of_checksOpt hM w w.posAt0 w.depth0 (fun p => embS (.inl p))
                  (fun p => prjS (.inl p)) (fun p x => hprj (.inl p) x) (rt.1.getD []) _ _ c0 h0
                  (fun c hc => hall c (List.mem_append_left _ (List.mem_append_left _ hc))) q
                  (hws.1.place_lt0 q ho') (hws.1.posAt0_place q ho') hp
                have hs : rootAt w rt q = ((rt.1.getD [])[w.tree q]?).isSome := by
                  simp only [rootAt, ho', Bool.false_eq_true, if_false]
                rw [hs]
                show _ = extSyms tr w (fun p => prjS (.inl p)) w.depth0 (rt.1.getD []) q
                rw [← this]
                generalize ((rt.1.getD [])[w.tree q]?).isSome = b
                generalize f (Sum.inl q) = o
                cases b <;> cases o <;> rfl
            | .inr q, hp =>
              exact read_mkTr_eq hM s A hco.2 ws hws.2 (fun p => embS (.inr p))
                (fun p => prjS (.inr p)) (fun p x => hprj (.inr p) x) rts
                (fun p => isRead (.inr p)) (fun p => f (.inr p)) c2 h2
                (fun c hc => hall c (List.mem_append_right _ hc)) pls ρ q hp

end Checks

end TypedOracleCompiler.Compile.Batch
