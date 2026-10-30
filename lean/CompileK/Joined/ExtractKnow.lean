-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Joined/ExtractKnow.lean: from the soundness clause of each of three chains to
round-by-round soundness of the one batch protocol in which they are joined. Definitions and proofs;
no hash, no oracle, no compiler.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

A file is verified along three chains of rounds: the first in local rounds (each slot of a batch has
its own verifier messages), the second in shared rounds (one verifier message for all slots), the
third in local rounds again. Each chain is a reduction (`Reduction`, Iop/Compose.lean) with the
clause `Know` (Ior/Know.lean): round-by-round knowledge soundness with a named extractor. What the
compiler's soundness proof takes is (Snd-B) in the late form (`BatchInteractiveOracleProof.SndBL`, Iop/Batch.lean) of
the joined protocol. This file leads from the one to the other.

Ior/BatchSeq.lean has the same rules for interactive oracle reductions (`IOR.KnowB`), at annotations
of the form `RoundSplits.const f`. Here they are said of reductions, and of every annotation whose rounds
have the right kind, since the joining round has an annotation of its own.

Main names:
  `AllKind k s A`: the library's `RoundSplits.AllKind k A` (Iop/JoinKit.lean): all rounds of the annotation
    A have the kind k.
  `KnowJ K An N adm on RA RB ext ε`: `IOR.KnowB` for a reduction: each statement has sets of bad
    verifier messages; on a full transcript without a bad one the extractor is right; for each
    admissible vector of at most N statements the sets are within ε, jointly (`JWithin`,
    Blocks/Batch/Kit.lean).
  `knowJ_lo`: from `Know`, in local rounds: the same errors.
  `knowJ_sh`: from `Know`, in shared rounds: N times the errors (the union bound over the slots).
  `knowJ_seq`: two in a row: errors in a row, the later extractor first (`Reduction.extSeq`).
  `sndBL_of_knowJ`: from `KnowJ` of a reduction to the trivial statement to `SndBL`, at late = none,
    of a batch protocol that is tied to the reduction (four hypotheses, below).
  `knowJ_key`, `knowJ_lost`: shared rounds in which only the shared part speaks: bad sets that are
    a function of a key of the statement are paid once, for vectors with one key.
  `sndBL_of_three`: the three together; all rounds of the second chain pay N times: with N slots
    that costs log₂ N bits in these rounds. `sndBL_of_three_worst`: with the bound computed.
  `sndBL_of_four`: the finer count: only the joining rounds pay N times.
  `KnowLate`, `sndBL_of_three_late`: a part of the instance enters the hash chain only in round n of
    the first chain (late = some n): the first chain's clause is asked jointly up to round n
    (`JDoomed`, Iop/Late.lean); the language then speaks of the whole instance.

  `sndBKT_of_three`, `sndBKT_of_three_late`: the same two with a witness (`BatchInteractiveOracleProof.SndBKT`,
    Ior/KnowWide.lean): the relation is the first chain's input relation, the witness map the three
    extractors in a row, and the list of errors stands by name.

  `OneKey`, `sndBKT_of_four`, `sndBKT_of_four_late`: the finer count with a witness: the second
    chain is cut into a head, whose errors count N times, and a tail, whose errors count once;
    `OneKey` is asked only of the vectors that the first chain can yield (`Reach`).

The hypotheses that tie a batch protocol Q to a reduction K (`sndBL_of_knowJ`):
  hs    Q has K's shape;
  ha    Q has the annotation An (an equation between types that agree by hs; where Q's shape is
        K's by unfolding, hs is rfl, ha is `HEq.rfl`, and the cast in hacc is the identity);
  hacc  where Q's verifier accepts the instance x, K's verifier outputs a statement on
        (early x, y): the state function sees of an instance what the first query holds;
  hLg   (x, y) is in the language if (early x, y) has a witness or is a statement of which the
        clause does not speak.

Limits: at late = none no part of the instance enters a later query. So there the conclusion binds
`early x` alone: hacc and hLg speak of (early x, y), and what `early` drops of an instance is bound
by nothing. hLg bounds the language from below only: it holds of the language of all pairs.
With on = "no statement" the clause `Know` is free and the language is everything. Nothing says that
a protocol with these ties exists.
In the forms with a witness the relation is "on₀ (early x, y) → R₀ (early x, y) w" (late: at x
itself): where on₀ fails every w is a witness.
The list of `sndBKT_of_four` charges the head's two rounds whole N times. The second of them is the
round in which the shared point is drawn. In the library that round's error for a batch has two
terms (`errPtB`, Cb/Ld/LdLinB.lean): one for the fold of the stored table, counted once, and one
for a slot's own claim at the point, counted N times. By a count made outside Lean from the
planner's printed numbers at the default setting (not checked here) the programs' plan does the
same, and the first term fills the bound of 2^-128 to within about a bit: so this list's bound is
not met there with 64 slots. In the form with links (OnBytes/TypedOracleCompiler/Joined/MidLinks.lean) the rule
adds no factor: it takes the batch link's own list. That this list is small is still owed there.
Of the count made outside Lean: which parameter file was the default then, and whether its 2^-128
counts a round's proof of work, is not recorded here.

Terms: lean/GLOSSARY.md.

-/
import Ior.BatchSeq
import Iop.Late
import Iop.JoinKit
import Ior.KnowWide
import Compile.Joined.Worst

set_option autoImplicit false

namespace CompileK.Joined
open Iop Prob
open scoped ENNReal

/-! ## Annotations of one kind -/

/-- `RoundSplits.AllKind` (Iop/JoinKit.lean: all rounds of the annotation have the kind k), with the shape
written -/
abbrev AllKind (k : Kind) (s : Shape) (A : RoundSplits s) : Prop := RoundSplits.AllKind k A

/-- `RoundSplits.allKind_const` (Iop/JoinKit.lean) -/
theorem allKind_const {k : Kind} {f : ∀ r : Round, RAnn r} (hf : ∀ r, (f r).kind = k)
    (s : Shape) : AllKind k s (RoundSplits.const f s) :=
  RoundSplits.allKind_const k f hf s

theorem allKind_app {k : Kind} :
    ∀ {s t : Shape} {A : RoundSplits s} {B : RoundSplits t}, RoundSplits.AllKind k A → RoundSplits.AllKind k B →
      RoundSplits.AllKind k (RoundSplits.app A B)
  | [], _, _, _, _, h => h
  | _ :: _, _, (_, _), _, h, h' => ⟨h.1, allKind_app h.2 h'⟩

/-- Local rounds: it is enough that the bad sets of each slot are within the errors. -/
theorem jWithin_lo (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s), AllKind .lo s A → ∀ (ε : Err s)
      (G : Fin N → Option (Bool × BadFam s)),
      (∀ j p, G j = some p → p.2.Within ε) → JWithin N s A ε G
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), hA, (e, ε), G, h => by
      intro m0 m
      refine ⟨?_, fun v => jWithin_lo N s A hA.2 ε _ fun j p hp => ?_⟩
      · rw [hA.1]
        exact fun j p hp _ => (h j p hp).1 _
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        exact (h j p' hp').2 _ _

/-- Shared rounds: if the bad sets of each slot are within the errors, their unions are within N
times the errors. -/
theorem jWithin_sh (N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s), AllKind .sh s A → ∀ (ε : Err s)
      (G : Fin N → Option (Bool × BadFam s)),
      (∀ j p, G j = some p → p.2.Within ε) → JWithin N s A (Err.times N ε) G
  | [], _, _, _, _, _ => trivial
  | r :: s, (a, A), hA, (e, ε), G, h => by
      show JWithin N (r :: s) (a, A) (N * e, Err.times N ε) G
      intro m0 m
      refine ⟨?_, fun v => jWithin_sh N s A hA.2 ε _ fun j p hp => ?_⟩
      · rw [hA.1]
        have h1 := cnt_exists_le_mul
          (fun (j : Fin N) (c : r.Chal) =>
            ∃ p, G j = some p ∧ p.1 = false ∧ c ∈ p.2.1 (a.join m0 (m j))) e fun j => by
          by_cases hj : ∃ p, G j = some p
          · obtain ⟨p, hp⟩ := hj
            refine le_trans (cnt_mono ?_) ((h j p hp).1 (a.join m0 (m j)))
            rintro c ⟨p', hp', -, hc⟩
            obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
            exact hc
          · rw [cnt_false]
            · exact Nat.zero_le _
            · rintro c ⟨p, hp, -⟩
              exact hj ⟨p, hp⟩
        rwa [Fintype.card_fin] at h1
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        exact (h j p' hp').2 _ _

/-- N times the errors are below N times the bound. -/
theorem below_times (N : ℕ) :
    ∀ {s : Shape} {ε : Err s} {c : ℝ≥0∞}, Err.Below ε c → Err.Below (Err.times N ε) ((N : ℝ≥0∞) * c)
  | [], _, _, _ => trivial
  | r :: _, (e, _), c, h =>
    ⟨by
      show ((N * e : ℕ) : ℝ≥0∞) ≤ (N : ℝ≥0∞) * c * (Fintype.card r.Chal : ℝ≥0∞)
      rw [Nat.cast_mul, mul_assoc]
      exact mul_le_mul' le_rfl h.1, below_times N h.2⟩

/-! ## The clause for the statements of a batch -/

section Know
variable {A B C WA WB WC : Type}

/-- Round-by-round knowledge soundness for the statements of a batch, for one reduction of a chain;
by sets of bad values (`IOR.KnowB`, Ior/BatchSeq.lean, for a reduction). -/
def KnowJ (K : Reduction A B) (An : RoundSplits K.shape) (N : ℕ) (adm : (Fin N → Option A) → Prop)
    (on : A → Prop) (RA : A → WA → Prop) (RB : B → WB → Prop) (ext : A → Tr K.shape → WB → WA)
    (ε : Err K.shape) : Prop :=
  ∃ bad : A → BadFam K.shape,
    (∀ a τ b w, on a → (bad a).Clean τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) ∧
    ∀ a : Fin N → Option A,
      adm a → JWithin N K.shape An ε fun j => (a j).map fun aj => (false, bad aj)

/-- A reduction with the clause `Know`, in every slot, in local rounds: the same errors. -/
theorem knowJ_lo {K : Reduction A B} {An : RoundSplits K.shape} (hAn : AllKind .lo K.shape An) (N : ℕ)
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : K.Know on RA RB ext ε) :
    KnowJ K An N (fun _ => True) on RA RB ext ε := by
  refine ⟨fun a => lostFam K.shape ε fun τ => ∀ b w, K.out a τ = some b → RB b w → RA a (ext a τ w),
    fun a τ b w ha hτ hb hw => lostFam_clean (h a ha) hτ b w hb hw,
    fun a _ => jWithin_lo N K.shape An hAn ε _ fun j p hp => ?_⟩
  obtain ⟨aj, _, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact lostFam_within _ _ _

/-- A reduction with the clause `Know`, in every slot, under shared verifier messages: N times the
errors. -/
theorem knowJ_sh {K : Reduction A B} {An : RoundSplits K.shape} (hAn : AllKind .sh K.shape An) (N : ℕ)
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : K.Know on RA RB ext ε) :
    KnowJ K An N (fun _ => True) on RA RB ext (Err.times N ε) := by
  refine ⟨fun a => lostFam K.shape ε fun τ => ∀ b w, K.out a τ = some b → RB b w → RA a (ext a τ w),
    fun a τ b w ha hτ hb hw => lostFam_clean (h a ha) hτ b w hb hw,
    fun a _ => jWithin_sh N K.shape An hAn ε _ fun j p hp => ?_⟩
  obtain ⟨aj, _, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact lostFam_within _ _ _

/-- fewer admissible vectors -/
theorem KnowJ.adm {K : Reduction A B} {An : RoundSplits K.shape} {N : ℕ}
    {adm adm' : (Fin N → Option A) → Prop} {on : A → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (h : KnowJ K An N adm on RA RB ext ε) (ha : ∀ a, adm' a → adm a) :
    KnowJ K An N adm' on RA RB ext ε := by
  obtain ⟨bad, c, J⟩ := h
  exact ⟨bad, c, fun a h' => J a (ha a h')⟩

/-- Shared rounds in which only the shared part speaks: bad sets that are a function of a key of the
statement, are within the errors and have the backward step are paid for once, not N times, for the
vectors whose statements have one key. -/
theorem knowJ_key {κ : Type} (K : Reduction A B) (N : ℕ) (key : A → κ) (bad₀ : κ → BadFam K.shape)
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (hW : ∀ k, (bad₀ k).Within ε)
    (hback : ∀ a τ b w,
      on a → (bad₀ (key a)).Clean τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) :
    KnowJ K (RoundSplits.const (RAnn.ofShared .sh) K.shape) N (IOR.SameKey key) on RA RB ext ε := by
  refine ⟨fun a => bad₀ (key a), hback, fun a ha => ?_⟩
  by_cases hne : ∃ j aj, a j = some aj
  · obtain ⟨j₀, a₀, h₀⟩ := hne
    refine jWithin_of_same N K.shape ε (bad₀ (key a₀)) _ (hW _) fun j p hp => ?_
    obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
    show bad₀ (key aj) = bad₀ (key a₀)
    rw [ha j j₀ aj a₀ haj h₀]
  · refine jWithin_of_same N K.shape ε (BadFam.empty _) _ (BadFam.empty_within _ _) fun j p hp => ?_
    obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact absurd ⟨j, aj, haj⟩ hne

/-- The same from "the prover has lost" (`Iop.Doomed`): the game that is lost is a function of a key
of the statement. -/
theorem knowJ_lost {κ : Type} (K : Reduction A B) (N : ℕ) (key : A → κ)
    (lost : κ → Tr K.shape → Prop) {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (hD : ∀ a, on a → Doomed K.shape ε (lost (key a)))
    (hback : ∀ a τ b w, on a → lost (key a) τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) :
    KnowJ K (RoundSplits.const (RAnn.ofShared .sh) K.shape) N (IOR.SameKey key) on RA RB ext ε :=
  knowJ_key K N key (fun k => lostFam K.shape ε (lost k)) (fun _ => lostFam_within _ _ _)
    fun a τ b w ha hτ hb hw => hback a τ b w ha (lostFam_clean (hD a ha) hτ) hb hw

/-- Two reductions in a row, with the first one's bad sets in the open: the bad sets of the two in a
row are the first one's, and then sets g that depend on the first part of the transcript. -/
theorem knowJ_seq_app {K₁ : Reduction A B} {K₂ : Reduction B C} {A₁ : RoundSplits K₁.shape}
    {A₂ : RoundSplits K₂.shape} {N : ℕ} {adm₁ : (Fin N → Option A) → Prop}
    {adm₂ : (Fin N → Option B) → Prop} {on₁ : A → Prop} {on₂ : B → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} {RC : C → WC → Prop} {e₁ : A → Tr K₁.shape → WB → WA}
    {e₂ : B → Tr K₂.shape → WC → WB} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    (bad₁ : A → BadFam K₁.shape)
    (c₁ : ∀ a τ b w, on₁ a → (bad₁ a).Clean τ → K₁.out a τ = some b → RB b w → RA a (e₁ a τ w))
    (J₁ : ∀ a : Fin N → Option A,
      adm₁ a → JWithin N K₁.shape A₁ ε₁ fun j => (a j).map fun aj => (false, bad₁ aj))
    (h₂ : KnowJ K₂ A₂ N adm₂ on₂ RB RC e₂ ε₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b)
    (hadm : ∀ a, adm₁ a →
      ∀ τ : BTr N K₁.shape A₁, adm₂ fun j => (a j).bind fun aj => K₁.out aj (τ.slot j)) (d : WA) :
    ∃ g : A → Tr K₁.shape → BadFam K₂.shape,
      (∀ a (τ : Tr (K₁.seq K₂).shape) c w, on₁ a → (BadFam.app (bad₁ a) (g a)).Clean τ →
        (K₁.seq K₂).out a τ = some c → RC c w → RA a (Reduction.extSeq K₁ K₂ e₁ e₂ d a τ w)) ∧
      ∀ a : Fin N → Option A, adm₁ a →
        JWithin N (K₁.seq K₂).shape (RoundSplits.app A₁ A₂) (Err.app ε₁ ε₂) fun j =>
          (a j).map fun aj => (false, BadFam.app (bad₁ aj) (g aj)) := by
  obtain ⟨bad₂, c₂, J₂⟩ := h₂
  let g : A → Tr K₁.shape → BadFam K₂.shape := fun a τ =>
    ((K₁.out a τ).map bad₂).getD (BadFam.empty K₂.shape)
  refine ⟨g, ?_, ?_⟩
  · intro a (τ : Tr (K₁.shape ++ K₂.shape)) c w ha hτ hc hw
    have hτ' : (bad₁ a).Clean (Tr.fst τ) ∧ (g a (Tr.fst τ)).Clean (Tr.snd (s := K₁.shape) τ) := by
      rw [← BadFam.clean_app, Tr.app_fst_snd]
      exact hτ
    have hc' : (K₁.out a (Tr.fst τ)).bind (fun b => K₂.out b (Tr.snd (s := K₁.shape) τ)) =
        some c := hc
    cases hb : K₁.out a (Tr.fst τ) with
    | none =>
      rw [hb] at hc'
      cases hc'
    | some b =>
      rw [hb, Option.bind_some] at hc'
      have hg : g a (Tr.fst τ) = bad₂ b := by
        show ((K₁.out a (Tr.fst τ)).map bad₂).getD _ = _
        rw [hb]
        rfl
      have h2 := c₂ b (Tr.snd (s := K₁.shape) τ) c w (hon a _ b ha hb) (hg ▸ hτ'.2) hc' hw
      have h1 := c₁ a (Tr.fst τ) b _ ha hτ'.1 hb h2
      have he : Reduction.extSeq K₁ K₂ e₁ e₂ d a τ w =
          e₁ a (Tr.fst τ) (e₂ b (Tr.snd (s := K₁.shape) τ) w) := by
        simp only [Reduction.extSeq]
        rw [hb]
      rw [he]
      exact h1
  · intro a ha
    have key := JWithin.app N K₁.shape K₂.shape A₁ A₂ ε₁ ε₂
      (fun j => (a j).map fun aj => (false, bad₁ aj))
      (fun j τ => (a j).elim (BadFam.empty _) fun aj => g aj τ) (J₁ a ha)
      (fun τ => JWithin.weaken N K₂.shape A₂ ε₂ _ _ (J₂ _ (hadm a ha τ)) fun j p hp => by
        beta_reduce at hp
        cases hx : a j with
        | none =>
          rw [hx] at hp
          cases hp
        | some aj =>
          rw [hx] at hp
          obtain rfl : _ = p := Option.some.inj hp
          cases hm : K₁.out aj (τ.slot j) with
          | none =>
            right
            show ((K₁.out aj (τ.slot j)).map bad₂).getD _ = _
            rw [hm]
            rfl
          | some b =>
            refine Or.inl ⟨(false, bad₂ b), ?_, ?_, fun h => Bool.noConfusion h⟩
            · show ((some aj).bind fun aj => K₁.out aj (τ.slot j)).map _ = _
              rw [Option.bind_some, hm]
              rfl
            · show ((K₁.out aj (τ.slot j)).map bad₂).getD _ = _
              rw [hm]
              rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) key
    funext j
    beta_reduce
    cases a j <;> rfl

/-- Two reductions in a row: the middle relations agree; every output of the first on a statement
with on₁ has on₂; the outputs of an admissible vector, on any transcript of the whole batch, are
admissible for the second. Errors in a row; the second's extractor, then the first's. -/
theorem knowJ_seq {K₁ : Reduction A B} {K₂ : Reduction B C} {A₁ : RoundSplits K₁.shape}
    {A₂ : RoundSplits K₂.shape} {N : ℕ} {adm₁ : (Fin N → Option A) → Prop}
    {adm₂ : (Fin N → Option B) → Prop} {on₁ : A → Prop} {on₂ : B → Prop} {RA : A → WA → Prop}
    {RB : B → WB → Prop} {RC : C → WC → Prop} {e₁ : A → Tr K₁.shape → WB → WA}
    {e₂ : B → Tr K₂.shape → WC → WB} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    (h₁ : KnowJ K₁ A₁ N adm₁ on₁ RA RB e₁ ε₁) (h₂ : KnowJ K₂ A₂ N adm₂ on₂ RB RC e₂ ε₂)
    (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b)
    (hadm : ∀ a, adm₁ a →
      ∀ τ : BTr N K₁.shape A₁, adm₂ fun j => (a j).bind fun aj => K₁.out aj (τ.slot j)) (d : WA) :
    KnowJ (K₁.seq K₂) (RoundSplits.app A₁ A₂) N adm₁ on₁ RA RC (Reduction.extSeq K₁ K₂ e₁ e₂ d)
      (Err.app ε₁ ε₂) := by
  obtain ⟨bad₁, c₁, J₁⟩ := h₁
  obtain ⟨g, hc, hJ⟩ := knowJ_seq_app bad₁ c₁ J₁ h₂ hon hadm d
  exact ⟨fun a => BadFam.app (bad₁ a) (g a), hc, hJ⟩

end Know

/-! ## From the clause to (Snd-B) -/

section End
variable {Y W₀ : Type} {E : ExtSpec}

/-- the statements of the vector have the same external strings -/
def SameStr {N : ℕ} (a : Fin N → Option (Y × E.Str)) : Prop := IOR.SameKey Prod.snd a

/-- (Snd-B), at late = none, from sets of bad values: the state function is given `early x`. -/
theorem sndBL_of_badFam (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y) (Lg : Y → E.Str → Prop)
    (ε : Err Q.loc.shape) (bad : Y → E.Str → BadFam Q.loc.shape)
    (hclean : ∀ x y τ, (bad (early x) y).Clean τ → Q.loc.accept x y τ = true → Lg x y)
    (hJ : ∀ y (x : Fin N → Option Y),
      JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (false, bad xj y)) :
    Q.SndBL N early none Lg ε := by
  refine ⟨fun n h => (by cases h), fun y x => stOf (false, bad x y), fun y x _ => ?_,
    fun y x τ m h => ?_, fun y x τ _ h => (by cases h), fun y x τ hL h => ?_, fun y x => ?_⟩
  · show (false || (bad (early x) y).dirty (PTr.empty _)) = false
    rw [BadFam.dirty_empty]
    rfl
  · show (false || (bad x y).dirty (.atV (τ.snoc m))) = false
    rw [BadFam.dirty_snoc]
    exact h
  · have h' : (false || (bad (early x) y).dirty (.full τ)) = false := h
    rw [Bool.false_or] at h'
    by_contra hacc
    exact hL (hclean x y τ ((BadFam.dirty_full _ τ).mp h') (by simpa using hacc))
  · have h1 := jointLaw_of_jWithin N _ _ ε _ (hJ y x)
    have h2 : (fun j => ((x j).map fun xj => ((false : Bool), bad xj y)).map stOf) =
        fun j => (x j).map fun xj => stOf (false, bad xj y) := by
      funext j
      cases x j <;> rfl
    rw [h2] at h1
    exact h1

/-- **From the clause of a reduction to the trivial statement to (Snd-B) of a batch protocol that is
tied to it** (the four ties: the head of this file). The errors are the reduction's. -/
theorem sndBL_of_knowJ (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y) (Lg : Y → E.Str → Prop)
    (K : Reduction (Y × E.Str) Unit) (An : RoundSplits K.shape) (on : Y × E.Str → Prop)
    (R₀ : Y × E.Str → W₀ → Prop) (ext : Y × E.Str → Tr K.shape → Unit → W₀) (ε : Err K.shape)
    {εs : ℝ≥0∞} (hε : Err.Below ε εs)
    (hK : KnowJ K An N SameStr on R₀ (fun _ (_ : Unit) => True) ext ε)
    (hs : Q.loc.shape = K.shape) (ha : HEq Q.ann An)
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      (K.out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true)
    (hLg : ∀ x y, (on (early x, y) → ∃ w, R₀ (early x, y) w) → Lg x y) :
    ∃ ε' : Err Q.loc.shape, Err.Below ε' εs ∧ Q.SndBL N early none Lg ε' := by
  obtain ⟨⟨sh, bl, er, rd, acc⟩, an⟩ := Q
  dsimp only at hs ha hacc ⊢
  subst hs
  obtain rfl : an = An := eq_of_heq ha
  obtain ⟨bad, c, J⟩ := hK
  refine ⟨ε, hε, sndBL_of_badFam (⟨⟨K.shape, bl, er, rd, acc⟩, an⟩ : BatchInteractiveOracleProof Y E) N early Lg ε
    (fun x y => bad (x, y)) ?_ ?_⟩
  · intro x y τ hτ ht
    refine hLg x y fun ho => ?_
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hacc x y τ ht)
    exact ⟨_, c (early x, y) τ u () ho hτ hu trivial⟩
  · intro y x
    have h := J (fun j => (x j).map fun a => (a, y)) (fun j j' aj aj' hj hj' => by
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp hj'
      rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) h
    funext j
    beta_reduce
    cases x j <;> rfl

/-- **Three chains in a row**: the first and the third in local rounds, the second in shared rounds.
From the clause `Know` of each, that each hands on only statements of which the next one's clause
speaks, and the four ties: (Snd-B) of the joined protocol, with every error at most εs. The second
chain's errors count N times. -/
theorem sndBL_of_three {A₁ A₂ W₁ W₂ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y)
    (Lg : Y → E.Str → Prop) (K₁ : Reduction (Y × E.Str) A₁) (K₂ : Reduction A₁ A₂)
    (K₃ : Reduction A₂ Unit) (An₁ : RoundSplits K₁.shape) (An₂ : RoundSplits K₂.shape) (An₃ : RoundSplits K₃.shape)
    (lo₁ : AllKind .lo K₁.shape An₁) (sh₂ : AllKind .sh K₂.shape An₂)
    (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {on₂ : A₂ → Prop}
    {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop} {R₂ : A₂ → W₂ → Prop}
    {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀} {e₂ : A₁ → Tr K₂.shape → W₂ → W₁}
    {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁)
    (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (know₂ : K₂.Know on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    {εs : ℝ≥0∞} (b₁ : Err.Below ε₁ εs) (b₂ : Err.Below (Err.times N ε₂) εs)
    (b₃ : Err.Below ε₃ εs)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true)
    (hLg : ∀ x y, (on₀ (early x, y) → ∃ w, R₀ (early x, y) w) → Lg x y) :
    ∃ ε : Err Q.loc.shape, Err.Below ε εs ∧ Q.SndBL N early none Lg ε :=
  sndBL_of_knowJ Q N early Lg (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) on₀ R₀
    (Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀)
    (Err.app ε₁ (Err.app (Err.times N ε₂) ε₃)) (Err.Below.app b₁ (Err.Below.app b₂ b₃))
    ((knowJ_seq (knowJ_lo lo₁ N know₁)
      (knowJ_seq (knowJ_sh sh₂ N know₂) (knowJ_lo lo₃ N know₃) hands₂ (fun _ _ _ => trivial) d₁)
      hands₁ (fun _ _ _ => trivial) d₀).adm fun _ _ => trivial)
    hs ha hacc hLg

/-- `sndBL_of_three` with the bound computed from the three lists of errors: the greatest error, as
a probability, where the second chain's count N times (`worst3`, Compile/Joined/Worst.lean). -/
theorem sndBL_of_three_worst {A₁ A₂ W₁ W₂ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y)
    (Lg : Y → E.Str → Prop) (K₁ : Reduction (Y × E.Str) A₁) (K₂ : Reduction A₁ A₂)
    (K₃ : Reduction A₂ Unit) (An₁ : RoundSplits K₁.shape) (An₂ : RoundSplits K₂.shape) (An₃ : RoundSplits K₃.shape)
    (lo₁ : AllKind .lo K₁.shape An₁) (sh₂ : AllKind .sh K₂.shape An₂)
    (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {on₂ : A₂ → Prop}
    {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop} {R₂ : A₂ → W₂ → Prop}
    {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀} {e₂ : A₁ → Tr K₂.shape → W₂ → W₁}
    {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁)
    (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (know₂ : K₂.Know on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true)
    (hLg : ∀ x y, (on₀ (early x, y) → ∃ w, R₀ (early x, y) w) → Lg x y) :
    ∃ ε : Err Q.loc.shape, Err.Below ε (Compile.Joined.worst3 N ε₁ ε₂ ε₃) ∧
      Q.SndBL N early none Lg ε :=
  sndBL_of_three Q N early Lg K₁ K₂ K₃ An₁ An₂ An₃ lo₁ sh₂ lo₃ d₀ d₁ know₁ know₂ know₃ hands₁ hands₂
    (Compile.Joined.below_worst3_fst N ε₁ ε₂ ε₃)
    (Err.Below.mono_bound (Compile.Joined.le_worst3_snd N ε₁ ε₂ ε₃)
      (below_times N (Compile.Joined.below_worst ε₂)))
    (Compile.Joined.below_worst3_thd N ε₁ ε₂ ε₃) hs ha hacc hLg

/-- **Three chains in a row, the finer count**: the second chain is cut into its joining rounds KJ,
in which the slots still send, and its further rounds K₂, in which only the shared part speaks. Only
the joining rounds' errors count N times. Against `sndBL_of_three` this asks more of the second
chain: behind the joining rounds the statements of all slots have one key (`oneKey`), and the game
that the prover has lost in K₂ is a function of that key (`lost₂`, `back₂`), in the place of the
clause `Know` of K₂. `oneKey` is asked at every vector of statements and every transcript of the
whole batch: so it can hold only where the key is read off the shared part of the joining rounds
alone. (A premise that speaks only of the vectors that can come from the first chain would ask
less.) -/
theorem sndBL_of_four {A₁ AJ A₂ W₁ WJ W₂ κ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y)
    (Lg : Y → E.Str → Prop) (K₁ : Reduction (Y × E.Str) A₁) (KJ : Reduction A₁ AJ)
    (K₂ : Reduction AJ A₂) (K₃ : Reduction A₂ Unit) (An₁ : RoundSplits K₁.shape) (AnJ : RoundSplits KJ.shape)
    (An₃ : RoundSplits K₃.shape) (lo₁ : AllKind .lo K₁.shape An₁) (shJ : AllKind .sh KJ.shape AnJ)
    (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {onJ : AJ → Prop}
    {on₂ : A₂ → Prop} {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop} {RJ : AJ → WJ → Prop}
    {R₂ : A₂ → W₂ → Prop} {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀}
    {eJ : A₁ → Tr KJ.shape → WJ → W₁} {e₂ : AJ → Tr K₂.shape → W₂ → WJ}
    {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {εJ : Err KJ.shape}
    {ε₂ : Err K₂.shape} {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁) (dJ : WJ)
    (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (knowJ : KJ.Know on₁ R₁ RJ eJ εJ)
    (key : AJ → κ) (lost : κ → Tr K₂.shape → Prop)
    (lost₂ : ∀ a, onJ a → Doomed K₂.shape ε₂ (lost (key a)))
    (back₂ : ∀ a τ b w, onJ a → lost (key a) τ → K₂.out a τ = some b → R₂ b w → RJ a (e₂ a τ w))
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (handsJ : ∀ a τ b, on₁ a → KJ.out a τ = some b → onJ b)
    (hands₂ : ∀ a τ b, onJ a → K₂.out a τ = some b → on₂ b)
    (oneKey : ∀ (a : Fin N → Option A₁) (τ : BTr N KJ.shape AnJ),
      IOR.SameKey key fun j => (a j).bind fun aj => KJ.out aj (τ.slot j))
    {εs : ℝ≥0∞} (b₁ : Err.Below ε₁ εs) (bJ : Err.Below (Err.times N εJ) εs)
    (b₂ : Err.Below ε₂ εs) (b₃ : Err.Below ε₃ εs)
    (hs : Q.loc.shape = (K₁.seq (KJ.seq (K₂.seq K₃))).shape)
    (ha : HEq Q.ann
      (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃))))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (KJ.seq (K₂.seq K₃))).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true)
    (hLg : ∀ x y, (on₀ (early x, y) → ∃ w, R₀ (early x, y) w) → Lg x y) :
    ∃ ε : Err Q.loc.shape, Err.Below ε εs ∧ Q.SndBL N early none Lg ε :=
  sndBL_of_knowJ Q N early Lg (K₁.seq (KJ.seq (K₂.seq K₃)))
    (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃))) on₀ R₀
    (Reduction.extSeq K₁ (KJ.seq (K₂.seq K₃)) e₁
      (Reduction.extSeq KJ (K₂.seq K₃) eJ (Reduction.extSeq K₂ K₃ e₂ e₃ dJ) d₁) d₀)
    (Err.app ε₁ (Err.app (Err.times N εJ) (Err.app ε₂ ε₃)))
    (Err.Below.app b₁ (Err.Below.app bJ (Err.Below.app b₂ b₃)))
    ((knowJ_seq (knowJ_lo lo₁ N know₁)
      (knowJ_seq (knowJ_sh shJ N knowJ)
        (knowJ_seq (knowJ_lost K₂ N key lost lost₂ back₂) (knowJ_lo lo₃ N know₃) hands₂
          (fun _ _ _ => trivial) dJ)
        handsJ (fun a _ τ => oneKey a τ) d₁)
      hands₁ (fun _ _ _ => trivial) d₀).adm fun _ _ => trivial)
    hs ha hacc hLg

end End

/-! ## An instance of which a part is fixed late -/

section Late
variable {Y W₀ : Type} {E : ExtSpec}

open Classical in
/-- Bad sets that agree in the rounds that are complete have the same state. -/
theorem dirty_agree :
    ∀ {s : Shape} {B B' : BadFam s} (τ : AtP s), BadFam.AgreeTo τ.idx B B' →
      B.dirty (.atP τ) = B'.dirty (.atP τ)
  | _ :: _, _, _, .inl _, _ => rfl
  | _ :: _, (B, k), (B', k'), .inr (m, c, τ), h => by
      have h' : (∀ m, B m = B' m) ∧ ∀ m c, BadFam.AgreeTo τ.idx (k m c) (k' m c) := h
      show (decide (c ∈ B m) || (k m c).dirty (.atP τ)) =
        (decide (c ∈ B' m) || (k' m c).dirty (.atP τ))
      rw [h'.1 m, dirty_agree τ (h'.2 m c)]

/-- (Snd-B), at late = some n, from sets of bad values: those of `early x` and of x agree in the
first n rounds (`hagree`); the backward step is asked at x itself (`hclean`). -/
theorem sndBL_of_badFam_late (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y) (n : ℕ)
    (Lg : Y → E.Str → Prop) (ε : Err Q.loc.shape) (bad : Y → E.Str → BadFam Q.loc.shape)
    (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hagree : ∀ x y, BadFam.AgreeTo n (bad (early x) y) (bad x y))
    (hclean : ∀ x y τ, (bad x y).Clean τ → Q.loc.accept x y τ = true → Lg x y)
    (hJ : ∀ y (x : Fin N → Option Y),
      JWithin N Q.loc.shape Q.ann ε fun j => (x j).map fun xj => (false, bad xj y)) :
    Q.SndBL N early (some n) Lg ε := by
  refine ⟨fun n' h => ?_, fun y x => stOf (false, bad x y), fun y x _ => ?_,
    fun y x τ m h => ?_, fun y x τ _ hl h => ?_, fun y x τ hL h => ?_, fun y x => ?_⟩
  · obtain rfl := Option.some.inj h
    exact h0
  · show (false || (bad (early x) y).dirty (PTr.empty _)) = false
    rw [BadFam.dirty_empty]
    rfl
  · show (false || (bad x y).dirty (.atV (τ.snoc m))) = false
    rw [BadFam.dirty_snoc]
    exact h
  · obtain rfl := Option.some.inj hl
    show (false || (bad x y).dirty (.atP τ)) = false
    rw [← dirty_agree τ (hagree x y)]
    exact h
  · have h' : (false || (bad x y).dirty (.full τ)) = false := h
    rw [Bool.false_or] at h'
    by_contra hacc
    exact hL (hclean x y τ ((BadFam.dirty_full _ τ).mp h') (by simpa using hacc))
  · have h1 := jointLaw_of_jWithin N _ _ ε _ (hJ y x)
    have h2 : (fun j => ((x j).map fun xj => ((false : Bool), bad xj y)).map stOf) =
        fun j => (x j).map fun xj => stOf (false, bad xj y) := by
      funext j
      cases x j <;> rfl
    rw [h2] at h1
    exact h1

/-- `KnowJ` for statements (x, y) of which x is fixed only in round n: the bad sets of (early x, y)
and of (x, y) agree in the first n rounds. -/
def KnowJL {B WB : Type} (K : Reduction (Y × E.Str) B) (An : RoundSplits K.shape) (N : ℕ)
    (adm : (Fin N → Option (Y × E.Str)) → Prop) (on : Y × E.Str → Prop)
    (RA : Y × E.Str → W₀ → Prop) (RB : B → WB → Prop) (ext : Y × E.Str → Tr K.shape → WB → W₀)
    (ε : Err K.shape) (early : Y → Y) (n : ℕ) : Prop :=
  ∃ bad : Y × E.Str → BadFam K.shape,
    (∀ a τ b w, on a → (bad a).Clean τ → K.out a τ = some b → RB b w → RA a (ext a τ w)) ∧
    (∀ a : Fin N → Option (Y × E.Str),
      adm a → JWithin N K.shape An ε fun j => (a j).map fun aj => (false, bad aj)) ∧
    ∀ x y, BadFam.AgreeTo n (bad (early x, y)) (bad (x, y))

/-- The clause of a reduction on statements (x, y) of which x is fixed only in round n: for each
early part x₀ and each y the prover has lost, jointly up to round n (`JDoomed`, Iop/Late.lean) for
all x with this early part, towards the goal of `Know`. (Iop/Late.lean has two rules by which such a
joint clause is had for reductions in a row, in the form for languages: `Reduction.JSound.seq_left`,
a first reduction that does not see what is fixed late, and `Reduction.JSound.seq_right`, a last one
after it is fixed.) -/
def KnowLate {B WB : Type} (K : Reduction (Y × E.Str) B) (on : Y × E.Str → Prop)
    (RA : Y × E.Str → W₀ → Prop) (RB : B → WB → Prop) (ext : Y × E.Str → Tr K.shape → WB → W₀)
    (ε : Err K.shape) (early : Y → Y) (n : ℕ) : Prop :=
  ∀ (x₀ : Y) (y : E.Str), JDoomed (Φ := {x : Y // early x = x₀}) n K.shape ε fun φ τ =>
    on (φ.1, y) → ∀ b w, K.out (φ.1, y) τ = some b → RB b w → RA (φ.1, y) (ext (φ.1, y) τ w)

/-- From `KnowLate`, in local rounds: the same errors. `early` is asked to be idempotent: the early
part of an instance is an instance with this early part. -/
theorem knowJL_lo {B WB : Type} {K : Reduction (Y × E.Str) B} {An : RoundSplits K.shape}
    (hAn : AllKind .lo K.shape An) (N : ℕ) {on : Y × E.Str → Prop} {RA : Y × E.Str → W₀ → Prop}
    {RB : B → WB → Prop} {ext : Y × E.Str → Tr K.shape → WB → W₀} {ε : Err K.shape}
    {early : Y → Y} (hid : ∀ x, early (early x) = early x) {n : ℕ}
    (h : KnowLate K on RA RB ext ε early n) :
    KnowJL K An N (fun _ => True) on RA RB ext ε early n := by
  choose B₀ Bf _ hB using fun x₀ y => JDoomed.exists_badFam n K.shape ε _ (h x₀ y)
  have key : ∀ (y : E.Str) (x₀ : Y) (φ : {x : Y // early x = x₀}),
      Bf (early φ.1) y ⟨φ.1, rfl⟩ = Bf x₀ y φ := by
    rintro y x₀ ⟨x, rfl⟩
    rfl
  refine ⟨fun a => Bf (early a.1) a.2 ⟨a.1, rfl⟩,
    fun a τ b w ha hτ hb hw => (hB (early a.1) a.2 ⟨a.1, rfl⟩).2.1 τ hτ ha b w hb hw,
    fun a _ => jWithin_lo N K.shape An hAn ε _ fun j p hp => ?_, fun x y => ?_⟩
  · obtain ⟨aj, _, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact (hB _ _ _).1
  · show BadFam.AgreeTo n (Bf (early (early x)) y ⟨early x, rfl⟩) (Bf (early x) y ⟨x, rfl⟩)
    rw [key y (early x) ⟨early x, hid x⟩]
    exact (hB (early x) y ⟨early x, hid x⟩).2.2.symm.trans (hB (early x) y ⟨x, rfl⟩).2.2

/-- A reduction with `KnowJL`, whose rounds hold round n, and then one with `KnowJ`. -/
theorem knowJL_seq {B C WB WC : Type} {K₁ : Reduction (Y × E.Str) B} {K₂ : Reduction B C}
    {A₁ : RoundSplits K₁.shape} {A₂ : RoundSplits K₂.shape} {N : ℕ}
    {adm₁ : (Fin N → Option (Y × E.Str)) → Prop} {adm₂ : (Fin N → Option B) → Prop}
    {on₁ : Y × E.Str → Prop} {on₂ : B → Prop} {RA : Y × E.Str → W₀ → Prop} {RB : B → WB → Prop}
    {RC : C → WC → Prop} {e₁ : Y × E.Str → Tr K₁.shape → WB → W₀} {e₂ : B → Tr K₂.shape → WC → WB}
    {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape} {early : Y → Y} {n : ℕ}
    (h₁ : KnowJL K₁ A₁ N adm₁ on₁ RA RB e₁ ε₁ early n) (h₂ : KnowJ K₂ A₂ N adm₂ on₂ RB RC e₂ ε₂)
    (hn : n ≤ K₁.shape.length) (hon : ∀ a τ b, on₁ a → K₁.out a τ = some b → on₂ b)
    (hadm : ∀ a, adm₁ a →
      ∀ τ : BTr N K₁.shape A₁, adm₂ fun j => (a j).bind fun aj => K₁.out aj (τ.slot j)) (d : W₀) :
    KnowJL (K₁.seq K₂) (RoundSplits.app A₁ A₂) N adm₁ on₁ RA RC (Reduction.extSeq K₁ K₂ e₁ e₂ d)
      (Err.app ε₁ ε₂) early n := by
  obtain ⟨bad₁, c₁, J₁, ag⟩ := h₁
  obtain ⟨g, hc, hJ⟩ := knowJ_seq_app bad₁ c₁ J₁ h₂ hon hadm d
  exact ⟨fun a => BadFam.app (bad₁ a) (g a), hc, hJ,
    fun x y => BadFam.AgreeTo.app (g (early x, y)) (g (x, y)) hn (ag x y)⟩

/-- **From `KnowJL` of a reduction to the trivial statement to (Snd-B), at late = some n, of a batch
protocol that is tied to it.** The ties are those of `sndBL_of_knowJ`, but hacc and hLg speak of the
instance x itself; and the rounds up to n are local (h0). -/
theorem sndBL_of_knowJL (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y) (n : ℕ)
    (Lg : Y → E.Str → Prop) (K : Reduction (Y × E.Str) Unit) (An : RoundSplits K.shape)
    (on : Y × E.Str → Prop) (R₀ : Y × E.Str → W₀ → Prop)
    (ext : Y × E.Str → Tr K.shape → Unit → W₀) (ε : Err K.shape) {εs : ℝ≥0∞}
    (hε : Err.Below ε εs)
    (hK : KnowJL K An N SameStr on R₀ (fun _ (_ : Unit) => True) ext ε early n)
    (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hs : Q.loc.shape = K.shape) (ha : HEq Q.ann An)
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      (K.out (x, y) (cast (congrArg Tr hs) τ)).isSome = true)
    (hLg : ∀ x y, (on (x, y) → ∃ w, R₀ (x, y) w) → Lg x y) :
    ∃ ε' : Err Q.loc.shape, Err.Below ε' εs ∧ Q.SndBL N early (some n) Lg ε' := by
  obtain ⟨⟨sh, bl, er, rd, acc⟩, an⟩ := Q
  dsimp only at hs ha hacc h0 ⊢
  subst hs
  obtain rfl : an = An := eq_of_heq ha
  obtain ⟨bad, c, J, ag⟩ := hK
  refine ⟨ε, hε, sndBL_of_badFam_late (⟨⟨K.shape, bl, er, rd, acc⟩, an⟩ : BatchInteractiveOracleProof Y E) N early n
    Lg ε (fun x y => bad (x, y)) h0 ag ?_ ?_⟩
  · intro x y τ hτ ht
    refine hLg x y fun ho => ?_
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hacc x y τ ht)
    exact ⟨_, c (x, y) τ u () ho hτ hu trivial⟩
  · intro y x
    have h := J (fun j => (x j).map fun a => (a, y)) (fun j j' aj aj' hj hj' => by
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp hj'
      rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) h
    funext j
    beta_reduce
    cases x j <;> rfl

/-- **Three chains in a row, with a part of the instance fixed in round n of the first chain.**
Against `sndBL_of_three_worst`: the first chain's clause is asked in the joint form `KnowLate`;
`early` is idempotent; round n lies in the first chain (`inFirst` admits n = the number of its
rounds, but there h0 fails, since the next round is shared), is not the first round, and it and all
rounds before it are local. The ties hacc and hLg, and so the language, speak of the instance
itself. -/
theorem sndBL_of_three_late {A₁ A₂ W₁ W₂ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y)
    (n : ℕ) (Lg : Y → E.Str → Prop) (K₁ : Reduction (Y × E.Str) A₁) (K₂ : Reduction A₁ A₂)
    (K₃ : Reduction A₂ Unit) (An₁ : RoundSplits K₁.shape) (An₂ : RoundSplits K₂.shape) (An₃ : RoundSplits K₃.shape)
    (lo₁ : AllKind .lo K₁.shape An₁) (sh₂ : AllKind .sh K₂.shape An₂)
    (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {on₂ : A₂ → Prop}
    {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop} {R₂ : A₂ → W₂ → Prop}
    {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀} {e₂ : A₁ → Tr K₂.shape → W₂ → W₁}
    {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
    {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁)
    (idem : ∀ x, early (early x) = early x) (inFirst : n ≤ K₁.shape.length)
    (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (know₁ : KnowLate K₁ on₀ R₀ R₁ e₁ ε₁ early n) (know₂ : K₂.Know on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (x, y) (cast (congrArg Tr hs) τ)).isSome = true)
    (hLg : ∀ x y, (on₀ (x, y) → ∃ w, R₀ (x, y) w) → Lg x y) :
    ∃ ε : Err Q.loc.shape, Err.Below ε (Compile.Joined.worst3 N ε₁ ε₂ ε₃) ∧
      Q.SndBL N early (some n) Lg ε := by
  have hK := knowJL_seq (knowJL_lo lo₁ N idem know₁)
    (knowJ_seq (knowJ_sh sh₂ N know₂) (knowJ_lo lo₃ N know₃) hands₂ (fun _ _ _ => trivial) d₁)
    inFirst hands₁ (fun _ _ _ => trivial) d₀
  obtain ⟨bad, c, J, ag⟩ := hK
  exact sndBL_of_knowJL Q N early n Lg (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) on₀
    R₀ (Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀)
    (Err.app ε₁ (Err.app (Err.times N ε₂) ε₃))
    (Err.Below.app (Compile.Joined.below_worst3_fst N ε₁ ε₂ ε₃)
      (Err.Below.app
        (Err.Below.mono_bound (Compile.Joined.le_worst3_snd N ε₁ ε₂ ε₃)
          (below_times N (Compile.Joined.below_worst ε₂)))
        (Compile.Joined.below_worst3_thd N ε₁ ε₂ ε₃)))
    ⟨bad, c, fun a _ => J a trivial, ag⟩ h0 hs ha hacc hLg

end Late

/-! ## The form with a witness -/

section Wit
variable {Y W₀ : Type} {E : ExtSpec}

/-- where the guarded verifier accepts, Q's accepts and "ok" fails -/
theorem guardP_accept {Q : BatchInteractiveOracleProof Y E} {ok : Y → E.Str → Tr Q.loc.shape → Prop} {x : Y}
    {y : E.Str} {τ : Tr Q.loc.shape} (h : (Q.guardP ok).loc.accept x y τ = true) :
    Q.loc.accept x y τ = true ∧ ¬ ok x y τ := by
  have h' : (Q.loc.accept x y τ && !@decide (ok x y τ) (Classical.propDecidable _)) = true := h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h'
  refine ⟨h1, fun hok => ?_⟩
  rw [@decide_eq_true _ (Classical.propDecidable _) hok] at h2
  cases h2

/-- **From `KnowJ` of a reduction to the trivial statement to (Snd-B) with a witness** (`SndBKT`,
Ior/KnowWide.lean), at late = none, of a batch protocol that is tied to it by hs, ha, hacc (the head
of this file). The relation is the reduction's, on the statements of which its clause speaks; the
witness map is its extractor; the errors are its errors. The two casts go along hs; where Q's shape
is K's by unfolding they are the identity. -/
theorem sndBKT_of_knowJ (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y)
    (K : Reduction (Y × E.Str) Unit) (An : RoundSplits K.shape) (on : Y × E.Str → Prop)
    (R₀ : Y × E.Str → W₀ → Prop) (ext : Y × E.Str → Tr K.shape → Unit → W₀) (ε : Err K.shape)
    (hK : KnowJ K An N SameStr on R₀ (fun _ (_ : Unit) => True) ext ε)
    (hs : Q.loc.shape = K.shape) (ha : HEq Q.ann An)
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      (K.out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early none (fun x y w => on (early x, y) → R₀ (early x, y) w)
      (fun x y τ => ext (early x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm) ε) := by
  obtain ⟨⟨sh, bl, er, rd, acc⟩, an⟩ := Q
  dsimp only at hs ha hacc ⊢
  subst hs
  obtain rfl : an = An := eq_of_heq ha
  obtain ⟨bad, c, J⟩ := hK
  refine sndBL_of_badFam
    ((⟨⟨K.shape, bl, er, rd, acc⟩, an⟩ : BatchInteractiveOracleProof Y E).guardP fun x y τ =>
      on (early x, y) → R₀ (early x, y) (ext (early x, y) τ ()))
    N early (fun _ _ => False) ε (fun x y => bad (x, y)) ?_ ?_
  · intro x y τ hτ ht
    obtain ⟨h1, h2⟩ := guardP_accept ht
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hacc x y τ h1)
    exact h2 fun ho => c (early x, y) τ u () ho hτ hu trivial
  · intro y x
    have h := J (fun j => (x j).map fun a => (a, y)) (fun j j' aj aj' hj hj' => by
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp hj'
      rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) h
    funext j
    beta_reduce
    cases x j <;> rfl

/-- The same at late = some n, from `KnowJL`: relation, witness map and hacc at the instance
itself. -/
theorem sndBKT_of_knowJL (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y) (n : ℕ)
    (K : Reduction (Y × E.Str) Unit) (An : RoundSplits K.shape) (on : Y × E.Str → Prop)
    (R₀ : Y × E.Str → W₀ → Prop) (ext : Y × E.Str → Tr K.shape → Unit → W₀) (ε : Err K.shape)
    (hK : KnowJL K An N SameStr on R₀ (fun _ (_ : Unit) => True) ext ε early n)
    (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (hs : Q.loc.shape = K.shape) (ha : HEq Q.ann An)
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      (K.out (x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early (some n) (fun x y w => on (x, y) → R₀ (x, y) w)
      (fun x y τ => ext (x, y) (cast (congrArg Tr hs) τ) ()) (cast (congrArg Err hs.symm) ε) := by
  obtain ⟨⟨sh, bl, er, rd, acc⟩, an⟩ := Q
  dsimp only at hs ha hacc h0 ⊢
  subst hs
  obtain rfl : an = An := eq_of_heq ha
  obtain ⟨bad, c, J, ag⟩ := hK
  refine sndBL_of_badFam_late
    ((⟨⟨K.shape, bl, er, rd, acc⟩, an⟩ : BatchInteractiveOracleProof Y E).guardP fun x y τ =>
      on (x, y) → R₀ (x, y) (ext (x, y) τ ()))
    N early n (fun _ _ => False) ε (fun x y => bad (x, y)) h0 ag ?_ ?_
  · intro x y τ hτ ht
    obtain ⟨h1, h2⟩ := guardP_accept ht
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hacc x y τ h1)
    exact h2 fun ho => c (x, y) τ u () ho hτ hu trivial
  · intro y x
    have h := J (fun j => (x j).map fun a => (a, y)) (fun j j' aj aj' hj hj' => by
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp hj'
      rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) h
    funext j
    beta_reduce
    cases x j <;> rfl

section Three
variable {A₁ A₂ W₁ W₂ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ) (early : Y → Y)
  (K₁ : Reduction (Y × E.Str) A₁) (K₂ : Reduction A₁ A₂) (K₃ : Reduction A₂ Unit)
  (An₁ : RoundSplits K₁.shape) (An₂ : RoundSplits K₂.shape) (An₃ : RoundSplits K₃.shape)
  (lo₁ : AllKind .lo K₁.shape An₁) (sh₂ : AllKind .sh K₂.shape An₂)
  (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {on₂ : A₂ → Prop}
  {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop} {R₂ : A₂ → W₂ → Prop}
  {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀} {e₂ : A₁ → Tr K₂.shape → W₂ → W₁}
  {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {ε₂ : Err K₂.shape}
  {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁)

include lo₁ sh₂ lo₃ in
/-- **Three chains in a row, with a witness**, at late = none: the premises of `sndBL_of_three`
without those on εs and on the language. The witness map is the three extractors in a row, the later
chain's first; the errors are the three lists in a row, the second chain's N times. -/
theorem sndBKT_of_three (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (know₂ : K₂.Know on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early none (fun x y w => on₀ (early x, y) → R₀ (early x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀
        (early x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm) (Err.app ε₁ (Err.app (Err.times N ε₂) ε₃))) :=
  sndBKT_of_knowJ Q N early (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) on₀ R₀ _ _
    ((knowJ_seq (knowJ_lo lo₁ N know₁)
      (knowJ_seq (knowJ_sh sh₂ N know₂) (knowJ_lo lo₃ N know₃) hands₂ (fun _ _ _ => trivial) d₁)
      hands₁ (fun _ _ _ => trivial) d₀).adm fun _ _ => trivial)
    hs ha hacc

include lo₁ sh₂ lo₃ in
/-- **Three chains in a row, with a witness, a part of the instance fixed in round n of the first
chain**: the premises of `sndBL_of_three_late` without that on the language. -/
theorem sndBKT_of_three_late (n : ℕ) (idem : ∀ x, early (early x) = early x)
    (inFirst : n ≤ K₁.shape.length) (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (know₁ : KnowLate K₁ on₀ R₀ R₁ e₁ ε₁ early n) (know₂ : K₂.Know on₁ R₁ R₂ e₂ ε₂)
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (hands₂ : ∀ a τ b, on₁ a → K₂.out a τ = some b → on₂ b)
    (hs : Q.loc.shape = (K₁.seq (K₂.seq K₃)).shape)
    (ha : HEq Q.ann (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (K₂.seq K₃)).out (x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early (some n) (fun x y w => on₀ (x, y) → R₀ (x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (K₂.seq K₃) e₁ (Reduction.extSeq K₂ K₃ e₂ e₃ d₁) d₀
        (x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm) (Err.app ε₁ (Err.app (Err.times N ε₂) ε₃))) := by
  obtain ⟨bad, c, J, ag⟩ := knowJL_seq (knowJL_lo lo₁ N idem know₁)
    (knowJ_seq (knowJ_sh sh₂ N know₂) (knowJ_lo lo₃ N know₃) hands₂ (fun _ _ _ => trivial) d₁)
    inFirst hands₁ (fun _ _ _ => trivial) d₀
  exact sndBKT_of_knowJL Q N early n (K₁.seq (K₂.seq K₃)) (RoundSplits.app An₁ (RoundSplits.app An₂ An₃)) on₀ R₀
    _ _ ⟨bad, c, fun a _ => J a trivial, ag⟩ h0 hs ha hacc

end Three

end Wit

/-! ## The finer count, with a witness -/

section Four
variable {Y W₀ : Type} {E : ExtSpec} {A₁ AJ A₂ W₁ WJ W₂ κ : Type} (Q : BatchInteractiveOracleProof Y E) (N : ℕ)
  (early : Y → Y) (K₁ : Reduction (Y × E.Str) A₁) (KJ : Reduction A₁ AJ) (K₂ : Reduction AJ A₂)
  (K₃ : Reduction A₂ Unit) (An₁ : RoundSplits K₁.shape) (AnJ : RoundSplits KJ.shape) (An₃ : RoundSplits K₃.shape)

/-- The vectors of statements that the first chain can yield from statements with one external
string. -/
def Reach (a : Fin N → Option A₁) : Prop :=
  ∃ a₀ : Fin N → Option (Y × E.Str), SameStr a₀ ∧ ∃ τ₁ : BTr N K₁.shape An₁,
    a = fun j => (a₀ j).bind fun x => K₁.out x (τ₁.slot j)

/-- **The one premise more of the finer count**: for slots with one external string, whatever the
batch's transcripts of the first chain and of the second chain's head: the statements of all slots
behind the head have one key. -/
def OneKey (key : AJ → κ) : Prop :=
  ∀ a₀ : Fin N → Option (Y × E.Str), SameStr a₀ →
    ∀ (τ₁ : BTr N K₁.shape An₁) (τJ : BTr N KJ.shape AnJ),
      IOR.SameKey key fun j =>
        ((a₀ j).bind fun a => K₁.out a (τ₁.slot j)).bind fun b => KJ.out b (τJ.slot j)

variable (lo₁ : AllKind .lo K₁.shape An₁) (shJ : AllKind .sh KJ.shape AnJ)
  (lo₃ : AllKind .lo K₃.shape An₃) {on₀ : Y × E.Str → Prop} {on₁ : A₁ → Prop} {onJ : AJ → Prop}
  {on₂ : A₂ → Prop} {R₀ : Y × E.Str → W₀ → Prop} {R₁ : A₁ → W₁ → Prop} {RJ : AJ → WJ → Prop}
  {R₂ : A₂ → W₂ → Prop} {e₁ : Y × E.Str → Tr K₁.shape → W₁ → W₀}
  {eJ : A₁ → Tr KJ.shape → WJ → W₁} {e₂ : AJ → Tr K₂.shape → W₂ → WJ}
  {e₃ : A₂ → Tr K₃.shape → Unit → W₂} {ε₁ : Err K₁.shape} {εJ : Err KJ.shape}
  {ε₂ : Err K₂.shape} {ε₃ : Err K₃.shape} (d₀ : W₀) (d₁ : W₁) (dJ : WJ)

include shJ lo₃ in
/-- The second chain, cut into head and tail, and the third: the head's errors N times, the tail's
once, for the vectors that the first chain can yield. -/
theorem knowJ_tail (knowJ : KJ.Know on₁ R₁ RJ eJ εJ) (key : AJ → κ)
    (lost : κ → Tr K₂.shape → Prop) (lost₂ : ∀ a, onJ a → Doomed K₂.shape ε₂ (lost (key a)))
    (back₂ : ∀ a τ b w, onJ a → lost (key a) τ → K₂.out a τ = some b → R₂ b w → RJ a (e₂ a τ w))
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (handsJ : ∀ a τ b, on₁ a → KJ.out a τ = some b → onJ b)
    (hands₂ : ∀ a τ b, onJ a → K₂.out a τ = some b → on₂ b)
    (oneKey : OneKey N K₁ KJ An₁ AnJ key) :
    KnowJ (KJ.seq (K₂.seq K₃))
      (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃)) N
      (Reach N K₁ An₁) on₁ R₁ (fun _ _ => True)
      (Reduction.extSeq KJ (K₂.seq K₃) eJ (Reduction.extSeq K₂ K₃ e₂ e₃ dJ) d₁)
      (Err.app (Err.times N εJ) (Err.app ε₂ ε₃)) :=
  knowJ_seq ((knowJ_sh shJ N knowJ).adm fun _ _ => trivial)
    (knowJ_seq (knowJ_lost K₂ N key lost lost₂ back₂) (knowJ_lo lo₃ N know₃) hands₂
      (fun _ _ _ => trivial) dJ)
    handsJ (fun a ha τ => by
      obtain ⟨a₀, h0, τ₁, rfl⟩ := ha
      exact oneKey a₀ h0 τ₁ τ) d₁

include lo₁ shJ lo₃ in
/-- **Three chains in a row, the finer count, with a witness**, at late = none. The second chain is
cut into a head KJ and a tail K₂; in the tail only the shared part speaks. The head's errors count N
times, the tail's once. In the place of the clause `Know` of the tail: each statement behind the
head has a key; the game that the prover has lost in the tail is a function of the key alone
(`lost₂`); on a transcript of that game each slot's backward step holds (`back₂`); and `OneKey`. -/
theorem sndBKT_of_four (know₁ : K₁.Know on₀ R₀ R₁ e₁ ε₁) (knowJ : KJ.Know on₁ R₁ RJ eJ εJ)
    (key : AJ → κ) (lost : κ → Tr K₂.shape → Prop)
    (lost₂ : ∀ a, onJ a → Doomed K₂.shape ε₂ (lost (key a)))
    (back₂ : ∀ a τ b w, onJ a → lost (key a) τ → K₂.out a τ = some b → R₂ b w → RJ a (e₂ a τ w))
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (handsJ : ∀ a τ b, on₁ a → KJ.out a τ = some b → onJ b)
    (hands₂ : ∀ a τ b, onJ a → K₂.out a τ = some b → on₂ b)
    (oneKey : OneKey N K₁ KJ An₁ AnJ key)
    (hs : Q.loc.shape = (K₁.seq (KJ.seq (K₂.seq K₃))).shape)
    (ha : HEq Q.ann
      (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃))))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (KJ.seq (K₂.seq K₃))).out (early x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early none (fun x y w => on₀ (early x, y) → R₀ (early x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (KJ.seq (K₂.seq K₃)) e₁
        (Reduction.extSeq KJ (K₂.seq K₃) eJ (Reduction.extSeq K₂ K₃ e₂ e₃ dJ) d₁) d₀
        (early x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm)
        (Err.app ε₁ (Err.app (Err.times N εJ) (Err.app ε₂ ε₃)))) :=
  sndBKT_of_knowJ Q N early (K₁.seq (KJ.seq (K₂.seq K₃)))
    (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃))) on₀ R₀
    _ _
    (knowJ_seq ((knowJ_lo lo₁ N know₁).adm fun _ _ => trivial)
      (knowJ_tail N K₁ KJ K₂ K₃ An₁ AnJ An₃ shJ lo₃ d₁ dJ knowJ key lost lost₂ back₂ know₃ handsJ
        hands₂ oneKey)
      hands₁ (fun a ha τ => ⟨a, ha, τ, rfl⟩) d₀)
    hs ha hacc

include lo₁ shJ lo₃ in
/-- **The same with a part of the instance fixed in round n of the first chain**: the first chain's
clause in the joint form `KnowLate`; relation, witness map and hacc at the instance itself. -/
theorem sndBKT_of_four_late (n : ℕ) (idem : ∀ x, early (early x) = early x)
    (inFirst : n ≤ K₁.shape.length) (h0 : 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann)
    (know₁ : KnowLate K₁ on₀ R₀ R₁ e₁ ε₁ early n) (knowJ : KJ.Know on₁ R₁ RJ eJ εJ)
    (key : AJ → κ) (lost : κ → Tr K₂.shape → Prop)
    (lost₂ : ∀ a, onJ a → Doomed K₂.shape ε₂ (lost (key a)))
    (back₂ : ∀ a τ b w, onJ a → lost (key a) τ → K₂.out a τ = some b → R₂ b w → RJ a (e₂ a τ w))
    (know₃ : K₃.Know on₂ R₂ (fun _ _ => True) e₃ ε₃)
    (hands₁ : ∀ a τ b, on₀ a → K₁.out a τ = some b → on₁ b)
    (handsJ : ∀ a τ b, on₁ a → KJ.out a τ = some b → onJ b)
    (hands₂ : ∀ a τ b, onJ a → K₂.out a τ = some b → on₂ b)
    (oneKey : OneKey N K₁ KJ An₁ AnJ key)
    (hs : Q.loc.shape = (K₁.seq (KJ.seq (K₂.seq K₃))).shape)
    (ha : HEq Q.ann
      (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃))))
    (hacc : ∀ x y (τ : Tr Q.loc.shape), Q.loc.accept x y τ = true →
      ((K₁.seq (KJ.seq (K₂.seq K₃))).out (x, y) (cast (congrArg Tr hs) τ)).isSome = true) :
    Q.SndBKT N early (some n) (fun x y w => on₀ (x, y) → R₀ (x, y) w)
      (fun x y τ => Reduction.extSeq K₁ (KJ.seq (K₂.seq K₃)) e₁
        (Reduction.extSeq KJ (K₂.seq K₃) eJ (Reduction.extSeq K₂ K₃ e₂ e₃ dJ) d₁) d₀
        (x, y) (cast (congrArg Tr hs) τ) ())
      (cast (congrArg Err hs.symm)
        (Err.app ε₁ (Err.app (Err.times N εJ) (Err.app ε₂ ε₃)))) := by
  obtain ⟨bad, c, J, ag⟩ := knowJL_lo lo₁ N idem know₁
  exact sndBKT_of_knowJL Q N early n (K₁.seq (KJ.seq (K₂.seq K₃)))
    (RoundSplits.app An₁ (RoundSplits.app AnJ (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) K₂.shape) An₃))) on₀ R₀
    _ _
    (knowJL_seq (adm₁ := SameStr) ⟨bad, c, fun a _ => J a trivial, ag⟩
      (knowJ_tail N K₁ KJ K₂ K₃ An₁ AnJ An₃ shJ lo₃ d₁ dJ knowJ key lost lost₂ back₂ know₃ handsJ
        hands₂ oneKey)
      inFirst hands₁ (fun a ha τ => ⟨a, ha, τ, rfl⟩) d₀)
    h0 hs ha hacc

end Four

end CompileK.Joined
