-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieSearch.lean: THE SEARCH FOR A NONCE OF THE TOKEN SIDE AGAINST THE COMPILED
PROVER's: searchT and fsT (Johnson/TokenSide/Chain.lean), as ordinary algorithms with the names
fbw t k written back to fb t (plainOf, Johnson/TokenSide/Erased.lean), do what searchO and fsO
(OnBytes/Prover/Defs.lean) do (Tie, Johnson/TokenSide/Tie.lean). Theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

No coin is drawn in a search: on both sides there is one query a try, at one point, and one branch
on the answer's blocks. What differs is what is kept: the token program appends each try's chaining
value to the store and returns its token.

Main names (namespace OnBytes.TokenSide).
  plainOf_fbT_bind   a try as an ordinary algorithm: a query to fb t, whatever the try's number is.
  hitK     what a search returns, at the store's values: the compiled prover's pair.
  HitOK    the token of the final try's chaining value is in the store, and its value is a digest.
  tie_search, tie_fs   THE TIES. The coins ω are handed on unchanged.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Erased
import Johnson.TokenSide.Chain

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A try as an ordinary algorithm. -/
theorem plainOf_fbT_bind {β : Type} (t : Tag) (n i : ℕ) (tk : Tok) (us : List Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (rt : List (Dig lam)) (pl : PlainPart (shapeOf L t) (annOf L t))
    (g : (Fin K → Dig lam) × Tok → StT lam K L β) (vs : List Bits) :
    plainOf ((fbT (K := K) t n i tk us hd hinj rt pl).bind g) vs =
      .query (S := typedOracleFamily lam K L) (OracleName.fb t)
        (⟨i, hd (us.map fun u => vs.getD u []) (vs.getD tk []), rt, pl⟩ : FbIn lam L t) fun a =>
        plainOf (g ((show FsAns lam K from a).1, vs.length))
          (vs ++ [List.ofFn (show FsAns lam K from a).2]) := by
  cases n <;> rfl

/-- what a search returns, at the store's values -/
def hitK {P : Type} (vs : List Bits) (q : Hit lam K P) : P × FsAns lam K :=
  (q.pl, (q.bl, digOf lam (vs.getD q.tl [])))

/-- the token of the chaining value is in the store, and its value is a digest -/
def HitOK {P : Type} (vs : List Bits) (q : Hit lam K P) : Prop :=
  q.tl < vs.length ∧ ∃ d : Dig lam, vs.getD q.tl [] = List.ofFn d

variable {Ω : Type} {μ : PMF Ω}

section
variable {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C) (t : Tag) (i : ℕ) (tk : Tok)
  (us : List Tok) (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
  (rt : List (Dig lam)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (h : Head lam X)

/-- **The search.** -/
theorem tie_search : ∀ (fuel n : ℕ) (dd : List Tok) (vs : List Bits), tk < vs.length →
    (∀ u ∈ us, u < vs.length) → hd (us.map fun u => vs.getD u []) (vs.getD tk []) = h →
    Tie μ (fun (p : Option (Hit lam K P) × List Bits) (ω : Ω) => (p.1.map (hitK p.2), ω))
      (fun p => vs <+: p.2 ∧ ∀ q, p.1 = some q → HitOK p.2 q)
      (plainOf (searchT (L := L) gr chal (fun n α => fbT (K := K) t n i tk us hd hinj rt (emb α)) α
        fuel n dd) vs)
      (fun ω => (searchO (L := L) gr chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
        (⟨i, h, rt, emb α⟩ : FbIn lam L t)) α fuel n).bind fun o => .pure (o, ω)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n dd vs _ _ _
    exact .done ⟨List.prefix_rfl, fun q hq => by cases hq⟩ fun _ => rfl
  | succ fuel ih =>
    intro n dd vs htk hus hh
    show Tie μ _ _ (plainOf ((fbT (K := K) t n i tk us hd hinj rt (emb (gr.put n α))).bind fun a =>
      if gr.ok (chal a.1) then Step.pure (some ⟨gr.put n α, a.1, a.2, dd⟩)
      else searchT gr chal (fun n α => fbT (K := K) t n i tk us hd hinj rt (emb α)) α fuel (n + 1)
        (a.2 :: dd)) vs) _
    rw [plainOf_fbT_bind, hh]
    refine Tie.query (fun ω a => (if gr.ok (chal (show FsAns lam K from a).1) then
        OComp.pure (some (gr.put n α, (show FsAns lam K from a)))
      else searchO (L := L) gr chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
        (⟨i, h, rt, emb α⟩ : FbIn lam L t)) α fuel (n + 1)).bind fun o => .pure (o, ω))
      (fun _ => rfl) fun a => ?_
    have hp : vs <+: vs ++ [List.ofFn (show FsAns lam K from a).2] := List.prefix_append _ _
    by_cases hc : gr.ok (chal (show FsAns lam K from a).1) = true
    · simp only [if_pos hc]
      refine .done ⟨hp, fun q hq => ?_⟩ fun ω => ?_
      · obtain rfl := Option.some.inj hq
        exact ⟨by simp, ⟨_, getD_length_append vs _ []⟩⟩
      · show OComp.pure _ = OComp.pure (some (gr.put n α, ((show FsAns lam K from a).1,
          digOf lam ((vs ++ [List.ofFn (show FsAns lam K from a).2]).getD vs.length []))), ω)
        rw [getD_length_append, digOf_ofFn]
        rfl
    · simp only [if_neg hc]
      refine (ih (n + 1) (vs.length :: dd) _ (Nat.lt_of_lt_of_le htk hp.length_le)
        (fun u hu => Nat.lt_of_lt_of_le (hus u hu) hp.length_le) ?_).mono
        fun p hq => ⟨hp.trans hq.1, hq.2⟩
      rw [← hh, getD_of_prefix hp htk]
      exact congrArg (fun l => hd l (vs.getD tk []))
        (List.map_congr_left fun u hu => getD_of_prefix hp (hus u hu))

end

/-- **A Fiat-Shamir query, with a test or without.** -/
theorem tie_fs {C P : Type} (gr : Option (GrW C P)) (cap : ℕ) (chal : (Fin K → Dig lam) → C)
    (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (rt : List (Dig lam))
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (h : Head lam X) (vs : List Bits)
    (htk : tk < vs.length) (hus : ∀ u ∈ us, u < vs.length)
    (hh : hd (us.map fun u => vs.getD u []) (vs.getD tk []) = h) :
    Tie μ (fun (p : Option (Hit lam K P) × List Bits) (ω : Ω) => (p.1.map (hitK p.2), ω))
      (fun p => vs <+: p.2 ∧ ∀ q, p.1 = some q → HitOK p.2 q)
      (plainOf (fsT (L := L) gr cap chal (fun n α => fbT (K := K) t n i tk us hd hinj rt (emb α))
        α) vs)
      (fun ω => (fsO (L := L) gr cap chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
        (⟨i, h, rt, emb α⟩ : FbIn lam L t)) α).bind fun o => .pure (o, ω)) := by
  cases gr with
  | some g => exact tie_search g chal t i tk us hd hinj rt emb α h (cap + 1) 0 [] vs htk hus hh
  | none =>
    show Tie μ _ _ (plainOf ((fbT (K := K) t 0 i tk us hd hinj rt (emb α)).bind fun a =>
      Step.pure (some (⟨α, a.1, a.2, []⟩ : Hit lam K P))) vs) _
    rw [plainOf_fbT_bind, hh]
    refine Tie.query (fun ω a => .pure (some (α, (show FsAns lam K from a)), ω)) (fun _ => rfl)
      fun a => ?_
    refine .done ⟨List.prefix_append _ _, fun q hq => ?_⟩ fun ω => ?_
    · obtain rfl := Option.some.inj hq
      exact ⟨by simp, ⟨_, getD_length_append vs _ []⟩⟩
    · show OComp.pure _ = OComp.pure (some (α, ((show FsAns lam K from a).1,
        digOf lam ((vs ++ [List.ofFn (show FsAns lam K from a).2]).getD vs.length []))), ω)
      rw [getD_length_append, digOf_ofFn]
      rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.tie_search
#print axioms OnBytes.TokenSide.tie_fs
