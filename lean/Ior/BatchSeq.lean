-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BatchSeq.lean: round-by-round knowledge soundness for the instances of a batch, for IORs in a
row.

Definitions, statements and proofs. (The honest side of such chains is not in this file.)
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. A slot is one of the N places of a batch, each with one
instance or empty, with its own local transcript.

Why: Ior/Batch.lean has (Snd-B) with a witness for a batch IOP (`SndBK`) and one rule of
composition: an IOR in every slot (local rounds), then a batch IOP. A batch IOP may itself be a
chain whose first links have shared rounds: a joining round (each slot sends, one verifier message
for all), rounds in which only the shared part of the prover speaks, an IOP on shared oracles, and
at the end an IOP in every slot.

The notion (`IOR.KnowB`). R is an IOR, A an annotation of its shape.
`R.KnowB A N adm on RA RB ext ε` says: every statement a has sets of bad values of the verifier
messages of a local transcript, such that
   (back) on a statement with "on", on a full local transcript without a bad value: whenever the
            verifier outputs b and w is a witness of b in RB, ext a τ w is a witness of a in RA;
   (joint) for every admissible vector of at most N statements the bad sets are within the errors ε,
            jointly (Blocks/Batch/Kit.lean: `JWithin`): in a local round the bad set of each slot in
            state 0 (no bad value so far in that slot: `stepOf`, `stOf`, Blocks/Batch/Kit.lean), in
            a shared round the union over the slots in state 0.
"adm" says what the statements of one batch have in common (the shared oracles; the shared part of
the explicit statement). Without it a shared round would have to pay for N unrelated statements.

Main names (each in `Iop.Spec`, with a theorem of the same name):
  `knowB_local`: an IOR with knowledge soundness (Ior/Know.lean), run in every slot in local rounds:
    same errors, any vector admissible.
  `knowB_joining`: an IOR with knowledge soundness, run in every slot under shared verifier messages
    (a joining round): N times the errors (the union bound, once and for all), any vector
    admissible.
  `knowB_of_key`: shared rounds in which only the shared part speaks: if the bad sets are a function
    of a key of the statement, are within the errors and have (back), then `KnowB` with the same
    errors (not N times), for the vectors whose statements have one key.
  `knowB_of_lost`: the same from "the prover has lost a game that is a function of the key", under
    the hypotheses of its statement.
  `knowB_seq`: two links in a row: the middle relations agree; errors in a row, extractors composed;
    every output of R₁ on a statement with on₁ must have on₂; the outputs of an admissible vector,
    on any transcript of the whole batch, must be admissible for the second link.
  `knowB_seq_ext`: the same, general form; see its docstring.
  `knowB_conseq`: fewer admissible vectors, fewer statements, a larger input relation, a smaller
    output relation.
  `sndBK_of_knowB`: from `KnowB` of a chain that ends in the trivial statement to `SndBK`, at early
    = id, late = none, of the batch IOP with the slots' own oracles moved into the instance
    (`BIOP.curry`); see its docstring.
  `know_of_knowB`: one slot: `KnowB` gives knowledge soundness of the IOR itself, with the same
    errors, on the statements that are admissible alone.

Limits: all of `KnowB`'s content hangs on adm: at adm = "no vector" the clause (joint) is empty, and
`KnowB` holds of every IOR with at least one round (take all values as bad). A `KnowB` counts only
at the adm that the next rule asks for: "the statements share the first implicit component" at the
head of a chain (`sndBK_of_knowB`), "admissible alone" for one slot (`know_of_knowB`).
Only this form: for the links of a batch there is no second form, with a state function or a
knowledge state function, and no equivalence: the form by bad sets is a working notion. A chain ends
in `SndBK`, which has both forms (Ior/BatchKProofs.lean, Ior/BatchKProofsBad.lean) (at early = id,
late = none). For a batch IOP, sets of bad values say the same as the state functions of (Snd-B),
with the same errors (Ior/BatchKProofsBad.lean), so `KnowB` at the trivial output statement gives
`SndBK` (`Spec.sndBK_of_knowB`, under its hypotheses).
This file says nothing on completeness or zero knowledge, nothing on the late form of (Snd-B) beyond
early = id, late = none, and nothing on any protocol. The bad sets stand under an existential: they
occur in no conclusion on a protocol.
Terms: lean/GLOSSARY.md: annotation, bad values, batch IOP, chain, error, honest side, IOR,
local round, the prover has lost, shape, (Snd-B), trivial statement.
-/
import Ior.OnlineK
import Ior.SeqProofs

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- Round-by-round knowledge soundness for the instances of a batch, for one link of a chain; by
sets of bad values. -/
def KnowB (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
    (adm : (Fin N → Option (Xi × Ei.Str)) → Prop) (on : Xi × Ei.Str → Prop)
    (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) : Prop :=
  ∃ bad : Xi × Ei.Str → BadFam R.shape,
    (∀ a τ b w, on a → (bad a).Clean τ → R.red.out a τ = some b → RB b w → RA a (ext a τ w)) ∧
    ∀ a : Fin N → Option (Xi × Ei.Str),
      adm a → JWithin N R.shape A ε fun j => (a j).map fun aj => (false, bad aj)

/-- All statements of the vector have the same key. -/
def SameKey {α κ : Type} {N : ℕ} (key : α → κ) (a : Fin N → Option α) : Prop :=
  ∀ j j' aj aj', a j = some aj → a j' = some aj' → key aj = key aj'

/-- The statement a alone, in the slot j. -/
def alone {α : Type} {N : ℕ} (j : Fin N) (a : α) : Fin N → Option α := fun i =>
  if i = j then some a else none

end IOR

/-- N times every error. -/
def Err.times (N : ℕ) : {s : Shape} → Err s → Err s
  | [], _ => ()
  | _ :: _, (e, ε) => (N * e, Err.times N ε)

namespace Spec
open IOR

/-- An IOR in every slot, under shared verifier messages: the union bound. -/
def knowB_joining : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (f : ∀ r : Round, RAnn r),
    (∀ r, (f r).kind = .sh) →
    ∀ (N : ℕ) (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop)
        (RB : Xo × Eo.Str → Wo → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
      R.red.Know on RA RB ext ε →
      R.KnowB (RoundSplits.const f R.shape) N (fun _ => True) on RA RB ext (Err.times N ε)

/-- An IOR in every slot, in local rounds. -/
def knowB_local : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (f : ∀ r : Round, RAnn r),
    (∀ r, (f r).kind = .lo) →
    ∀ (N : ℕ) (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop)
        (RB : Xo × Eo.Str → Wo → Prop) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
      R.red.Know on RA RB ext ε → R.KnowB (RoundSplits.const f R.shape) N (fun _ => True) on RA RB ext ε

/-- States, under the hypotheses below: shared rounds in which only the shared part speaks: bad sets
that are a function of a key of the statement are paid for once. -/
def knowB_of_key : Prop :=
  ∀ (Xi Xo κ : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (N : ℕ)
      (key : Xi × Ei.Str → κ) (bad₀ : κ → BadFam R.shape) (on : Xi × Ei.Str → Prop)
      (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    (∀ k, (bad₀ k).Within ε) →
    (∀ a τ b w,
      on a → (bad₀ (key a)).Clean τ → R.red.out a τ = some b → RB b w → RA a (ext a τ w)) →
    R.KnowB (RoundSplits.const (RAnn.ofShared .sh) R.shape) N (SameKey key) on RA RB ext ε

/-- The same from "the prover has lost" (Iop.Doomed): the game that is lost is a function of a key
of the statement. (not all hypotheses are named here: see the statement below) (An IOP on shared
oracles, run on a part of a larger statement: the key is that part.) -/
def knowB_of_lost : Prop :=
  ∀ (Xi Xo κ : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (N : ℕ)
      (key : Xi × Ei.Str → κ) (lost : κ → Tr R.shape → Prop) (on : Xi × Ei.Str → Prop)
      (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    (∀ a, on a → Doomed R.shape ε (lost (key a))) →
    (∀ a τ b w, on a → lost (key a) τ → R.red.out a τ = some b → RB b w → RA a (ext a τ w)) →
    R.KnowB (RoundSplits.const (RAnn.ofShared .sh) R.shape) N (SameKey key) on RA RB ext ε

/-- Two links in a row. -/
def knowB_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (N : ℕ)
      (adm₁ : (Fin N → Option (X₁ × E₁.Str)) → Prop) (adm₂ : (Fin N → Option (X₂ × E₂.Str)) → Prop)
      (on₁ : X₁ × E₁.Str → Prop) (on₂ : X₂ × E₂.Str → Prop) (RA : X₁ × E₁.Str → W₁ → Prop)
      (RB : X₂ × E₂.Str → W₂ → Prop) (RC : X₃ × E₃.Str → W₃ → Prop)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ε₁ : Err R₁.shape) (ε₂ : Err R₂.shape) (d : W₁),
    R₁.KnowB A₁ N adm₁ on₁ RA RB e₁ ε₁ → R₂.KnowB A₂ N adm₂ on₂ RB RC e₂ ε₂ →
    (∀ a τ b, on₁ a → R₁.red.out a τ = some b → on₂ b) →
    (∀ a, adm₁ a →
      ∀ τ : BTr N R₁.shape A₁, adm₂ fun j => (a j).bind fun aj => R₁.red.out aj (τ.slot j)) →
    (R₁.seq R₂).KnowB (RoundSplits.app A₁ A₂) N adm₁ on₁ RA RC (IOR.extSeq R₁ R₂ e₁ e₂ d) (Err.app ε₁ ε₂)

/-- Two links in a row, general form: any extractor that agrees with "the second's, then the
first's" wherever the first verifier outputs a statement. (not all hypotheses are named here: see
the statement below) (No default value. If the first extractor decodes the input statement, so does
the composed one.) -/
def knowB_seq_ext : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (N : ℕ)
      (adm₁ : (Fin N → Option (X₁ × E₁.Str)) → Prop) (adm₂ : (Fin N → Option (X₂ × E₂.Str)) → Prop)
      (on₁ : X₁ × E₁.Str → Prop) (on₂ : X₂ × E₂.Str → Prop) (RA : X₁ × E₁.Str → W₁ → Prop)
      (RB : X₂ × E₂.Str → W₂ → Prop) (RC : X₃ × E₃.Str → W₃ → Prop)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (ext : X₁ × E₁.Str → Tr (R₁.shape ++ R₂.shape) → W₃ → W₁) (ε₁ : Err R₁.shape)
      (ε₂ : Err R₂.shape),
    R₁.KnowB A₁ N adm₁ on₁ RA RB e₁ ε₁ → R₂.KnowB A₂ N adm₂ on₂ RB RC e₂ ε₂ →
    (∀ a τ b, on₁ a → R₁.red.out a τ = some b → on₂ b) →
    (∀ a, adm₁ a →
      ∀ τ : BTr N R₁.shape A₁, adm₂ fun j => (a j).bind fun aj => R₁.red.out aj (τ.slot j)) →
    (∀ a (τ : Tr (R₁.shape ++ R₂.shape)) b w, R₁.red.out a (Tr.fst τ) = some b →
      ext a τ w = e₁ a (Tr.fst τ) (e₂ b (Tr.snd (s := R₁.shape) τ) w)) →
    (R₁.seq R₂).KnowB (RoundSplits.app A₁ A₂) N adm₁ on₁ RA RC ext (Err.app ε₁ ε₂)

/-- Consequence. -/
def knowB_conseq : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (adm adm' : (Fin N → Option (Xi × Ei.Str)) → Prop) (on on' : Xi × Ei.Str → Prop)
      (RA RA' : Xi × Ei.Str → Wi → Prop) (RB RB' : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape),
    R.KnowB A N adm on RA RB ext ε → (∀ a, adm' a → adm a) →
    (∀ a, on' a → on a) → (∀ a w, on' a → RA a w → RA' a w) →
    (∀ b w, RB' b w → RB b w) → R.KnowB A N adm' on' RA' RB' ext ε

/-- States, under the hypotheses below: a chain that ends in the trivial statement has (Snd-B) with
a witness (`SndBK`, at early = id, late = none). The statements of a batch share the first implicit
component. R and wit are any relation and any extractor on oracles such that "on → RA at the chain's
extractor" gives R at wit. -/
def sndBK_of_knowB : Prop :=
  ∀ (X W Wc : Type) (E0 Ej : ExtSpec) (Q : BIOP X (E0.prod Ej)) (N : ℕ)
      (on : X × (E0.prod Ej).Str → Prop) (RA : X × (E0.prod Ej).Str → Wc → Prop)
      (ext : X × (E0.prod Ej).Str → Tr Q.ior.shape → Unit → Wc) (ε : Err Q.ior.shape)
      (R : X × Ej.Str → E0.Str → W → Prop) (wit : X × Ej.Str → Orcs Q.ior.shape → W),
    Q.ior.KnowB Q.ann N (SameKey fun a => a.2.1) on RA (fun _ (_ : Unit) => True) ext ε →
    (∀ (a : X × Ej.Str) (y0 : E0.Str) (τ : Tr Q.ior.shape),
      (on (a.1, (y0, a.2)) → RA (a.1, (y0, a.2)) (ext (a.1, (y0, a.2)) τ ())) →
      R a y0 (wit a τ.read)) →
    Q.curry.SndBK N id none R wit ε

/-- One slot. -/
def know_of_knowB : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo) (A : RoundSplits R.shape) (N : ℕ)
      (adm : (Fin N → Option (Xi × Ei.Str)) → Prop) (on : Xi × Ei.Str → Prop)
      (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) (j : Fin N),
    R.KnowB A N adm on RA RB ext ε → (∀ a, on a → adm (alone j a)) → R.red.Know on RA RB ext ε

end Spec

open IOR

theorem knowB_local : Spec.knowB_local := by
  intro Xi Xo Ei Eo Wi Wo R f hf N on RA RB ext ε h
  refine ⟨fun a =>
      lostFam R.shape ε fun τ => ∀ b w, R.red.out a τ = some b → RB b w → RA a (ext a τ w),
    fun a τ b w ha hτ hb hw => lostFam_clean (h a ha) hτ b w hb hw,
    fun a _ => jWithin_of_within N f hf R.shape ε _ fun j p hp => ?_⟩
  obtain ⟨aj, _, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact lostFam_within _ _ _

/-- Shared rounds: if the bad sets of each slot are within the errors, their unions are within N
times the errors. -/
theorem jWithin_times (N : ℕ) (f : ∀ r : Round, RAnn r) (hf : ∀ r, (f r).kind = .sh) :
    ∀ (s : Shape) (ε : Err s) (G : Fin N → Option (Bool × BadFam s)),
      (∀ j p, G j = some p → p.2.Within ε) → JWithin N s (RoundSplits.const f s) (Err.times N ε) G
  | [], _, _, _ => trivial
  | r :: s, (e, ε), G, h => by
      show JWithin N (r :: s) (f r, RoundSplits.const f s) (N * e, Err.times N ε) G
      intro m0 m
      refine ⟨?_, fun v => jWithin_times N f hf s ε _ fun j p hp => ?_⟩
      · rw [hf r]
        have h1 := cnt_exists_le_mul (fun (j : Fin N) (c : r.Chal) => ∃ p, G j = some p ∧ p.1 = false ∧ c ∈ p.2.1 ((f r).join m0 (m j))) e fun j => by
          by_cases hj : ∃ p, G j = some p
          · obtain ⟨p, hp⟩ := hj
            refine le_trans (cnt_mono ?_) ((h j p hp).1 ((f r).join m0 (m j)))
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

theorem knowB_joining : Spec.knowB_joining := by
  intro Xi Xo Ei Eo Wi Wo R f hf N on RA RB ext ε h
  refine ⟨fun a =>
      lostFam R.shape ε fun τ => ∀ b w, R.red.out a τ = some b → RB b w → RA a (ext a τ w),
    fun a τ b w ha hτ hb hw => lostFam_clean (h a ha) hτ b w hb hw,
    fun a _ => jWithin_times N f hf R.shape ε _ fun j p hp => ?_⟩
  obtain ⟨aj, _, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact lostFam_within _ _ _

theorem knowB_of_key : Spec.knowB_of_key := by
  intro Xi Xo κ Ei Eo Wi Wo R N key bad₀ on RA RB ext ε hW hback
  refine ⟨fun a => bad₀ (key a), hback, fun a ha => ?_⟩
  by_cases hne : ∃ j aj, a j = some aj
  · obtain ⟨j₀, a₀, h₀⟩ := hne
    refine jWithin_of_same N R.shape ε (bad₀ (key a₀)) _ (hW _) fun j p hp => ?_
    obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
    show bad₀ (key aj) = bad₀ (key a₀)
    rw [ha j j₀ aj a₀ haj h₀]
  · refine jWithin_of_same N R.shape ε (BadFam.empty _) _ (BadFam.empty_within _ _) fun j p hp => ?_
    obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact absurd ⟨j, aj, haj⟩ hne

theorem knowB_of_lost : Spec.knowB_of_lost := by
  intro Xi Xo κ Ei Eo Wi Wo R N key lost on RA RB ext ε hD hback
  exact knowB_of_key Xi Xo κ Ei Eo Wi Wo R N key (fun k => lostFam R.shape ε (lost k))
    on RA RB ext ε (fun k => lostFam_within _ _ _)
    fun a τ b w ha hτ hb hw => hback a τ b w ha (lostFam_clean (hD a ha) hτ) hb hw

theorem knowB_seq_ext : Spec.knowB_seq_ext := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ A₁ A₂ N adm₁ adm₂ on₁ on₂ RA RB RC e₁ e₂ ext ε₁ ε₂
    ⟨bad₁, c₁, J₁⟩ ⟨bad₂, c₂, J₂⟩ hon hadm hext
  let g : X₁ × E₁.Str → Tr R₁.shape → BadFam R₂.shape := fun a τ =>
    ((R₁.red.out a τ).map bad₂).getD (BadFam.empty R₂.shape)
  refine ⟨fun a => BadFam.app (bad₁ a) (g a), ?_, ?_⟩
  · intro a (τ : Tr (R₁.shape ++ R₂.shape)) c w ha hτ hc hw
    have hτ' : (bad₁ a).Clean (Tr.fst τ) ∧ (g a (Tr.fst τ)).Clean (Tr.snd (s := R₁.shape) τ) := by
      rw [← BadFam.clean_app, Tr.app_fst_snd]
      exact hτ
    have hc' : (R₁.red.out a (Tr.fst τ)).bind (fun b => R₂.red.out b (Tr.snd (s := R₁.shape) τ)) =
        some c :=
      (IOR.red_seq_out R₁ R₂ a τ).symm.trans hc
    cases hb : R₁.red.out a (Tr.fst τ) with
    | none =>
      rw [hb] at hc'
      cases hc'
    | some b =>
      rw [hb, Option.bind_some] at hc'
      have hg : g a (Tr.fst τ) = bad₂ b := by
        show ((R₁.red.out a (Tr.fst τ)).map bad₂).getD _ = _
        rw [hb]
        rfl
      have h2 := c₂ b (Tr.snd (s := R₁.shape) τ) c w (hon a _ b ha hb) (hg ▸ hτ'.2) hc' hw
      have h1 := c₁ a (Tr.fst τ) b _ ha hτ'.1 hb h2
      rw [hext a τ b w hb]
      exact h1
  · intro a ha
    have key := JWithin.app N R₁.shape R₂.shape A₁ A₂ ε₁ ε₂
      (fun j => (a j).map fun aj => (false, bad₁ aj))
      (fun j τ => (a j).elim (BadFam.empty _) fun aj => g aj τ) (J₁ a ha)
      (fun τ => JWithin.weaken N R₂.shape A₂ ε₂ _ _ (J₂ _ (hadm a ha τ)) fun j p hp => by
        beta_reduce at hp
        cases hx : a j with
        | none =>
          rw [hx] at hp
          cases hp
        | some aj =>
          rw [hx] at hp
          obtain rfl : _ = p := Option.some.inj hp
          cases hm : R₁.red.out aj (τ.slot j) with
          | none =>
            right
            show ((R₁.red.out aj (τ.slot j)).map bad₂).getD _ = _
            rw [hm]
            rfl
          | some b =>
            refine Or.inl ⟨(false, bad₂ b), ?_, ?_, fun h => Bool.noConfusion h⟩
            · show ((some aj).bind fun aj => R₁.red.out aj (τ.slot j)).map _ = _
              rw [Option.bind_some, hm]
              rfl
            · show ((R₁.red.out aj (τ.slot j)).map bad₂).getD _ = _
              rw [hm]
              rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) key
    funext j
    beta_reduce
    cases a j <;> rfl

theorem knowB_seq : Spec.knowB_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ A₁ A₂ N adm₁ adm₂ on₁ on₂ RA RB RC e₁
    e₂ ε₁ ε₂ d h₁ h₂ hon hadm
  refine knowB_seq_ext X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ A₁ A₂ N adm₁ adm₂ on₁ on₂ RA RB RC e₁ e₂ _
    ε₁ ε₂ h₁ h₂ hon hadm fun a τ b w hb => ?_
  have hb' : Option.map (fun xo => (xo, R₁.imp a.2 (Tr.fst τ))) (R₁.out a.1 a.2 (Tr.fst τ)) =
      some b := hb
  simp only [IOR.extSeq, Reduction.extSeq]
  rw [hb']

theorem knowB_conseq : Spec.knowB_conseq := by
  intro Xi Xo Ei Eo Wi Wo R A N adm adm' on on' RA RA' RB RB' ext ε ⟨bad, c, J⟩ hadm hon hA hB
  exact ⟨bad,
    fun a τ b w ha hτ hb hw => hA a _ ha (c a τ b w (hon a ha) hτ hb (hB b w hw)),
    fun a ha => J a (hadm a ha)⟩

theorem sndBK_of_knowB : Spec.sndBK_of_knowB := by
  intro X W Wc E0 Ej Q N on RA ext ε R wit ⟨bad, c, J⟩ hR
  refine BatchInteractiveOracleProof.sndBK_of_badFam Q.curry N R wit ε (fun a y0 => bad (a.1, (y0, a.2))) ?_ ?_
  · intro a y0 (τ : Tr Q.ior.shape) hτ hacc
    refine hR a y0 τ fun ha => ?_
    have hacc' : (Q.ior.out a.1 (y0, a.2) τ).isSome = true := hacc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hacc'
    exact c (a.1, (y0, a.2)) τ (u, Q.ior.imp (y0, a.2) τ) () ha hτ
      (by show (Q.ior.out a.1 (y0, a.2) τ).map _ = _; rw [hu]; rfl) trivial
  · intro y0 x
    have h := J (fun j => (x j).map fun a => (a.1, (y0, a.2))) (fun j j' aj aj' hj hj' => by
      obtain ⟨b, _, rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨b', _, rfl⟩ := Option.map_eq_some_iff.mp hj'
      rfl)
    refine cast (congrArg (JWithin N _ _ _) ?_) h
    funext j
    beta_reduce
    cases x j <;> rfl

/-- A verifier message of the whole batch of which the slot j sees c. -/
theorem Kind.exists_slot {C : Type} {N : ℕ} (j : Fin N) (c : C) :
    ∀ k : Kind, ∃ v : k.All N C, k.slot v j = c
  | .sh => ⟨c, rfl⟩
  | .lo => ⟨fun _ => c, rfl⟩

open Classical in
/-- One slot in state 0 of a vector whose bad sets are within the errors, jointly: if every full
transcript without a bad value is lost, the prover has lost at the start. -/
theorem doomed_of_jWithin {N : ℕ} (j : Fin N) :
    ∀ (s : Shape) (A : RoundSplits s) (ε : Err s) (B : BadFam s) (G : Fin N → Option (Bool × BadFam s)),
      G j = some (false, B) → JWithin N s A ε G →
      ∀ lost : Tr s → Prop, (∀ τ, B.Clean τ → lost τ) → Doomed s ε lost
  | [], _, _, _, _, _, _, _, h => h () trivial
  | r :: s, (a, A), (e, ε), (B, k), G, hG, hJ, lost, h => by
      intro m
      have hm : a.join (a.split m).1 (a.split m).2 = m := a.split.symm_apply_apply m
      obtain ⟨h1, h2⟩ := hJ (a.split m).1 fun _ => (a.split m).2
      have hsub : cnt (fun c : r.Chal => ¬ Doomed s ε fun τ => lost (m, c, τ)) ≤
          cnt (fun c : r.Chal => c ∈ B m) := by
        refine cnt_mono fun c hc => ?_
        by_contra hcB
        obtain ⟨v, hv⟩ := Kind.exists_slot (N := N) j c a.kind
        refine hc
          (doomed_of_jWithin j s A ε (k m c) _ ?_ (h2 v) _ fun τ hτ => h (m, c, τ) ⟨hcB, hτ⟩)
        beta_reduce
        rw [hG, hv, hm]
        show some ((false || decide (c ∈ B m)), k m c) = _
        rw [decide_eq_false hcB]
        rfl
      refine hsub.trans ?_
      cases hk : a.kind with
      | lo =>
        simp only [hk] at h1
        have := h1 j (false, (B, k)) hG rfl
        rwa [hm] at this
      | sh =>
        simp only [hk] at h1
        refine le_trans (cnt_mono fun c hc => ?_) h1
        exact ⟨j, (false, (B, k)), hG, rfl, by rw [hm]; exact hc⟩

theorem know_of_knowB : Spec.know_of_knowB := by
  intro Xi Xo Ei Eo Wi Wo R A N adm on RA RB ext ε j ⟨bad, c, J⟩ hadm a ha
  refine doomed_of_jWithin j R.shape A ε (bad a) _ ?_ (J _ (hadm a ha)) _
    fun τ hτ b w hb hw => c a τ b w ha hτ hb hw
  show (alone j a j).map _ = _
  unfold alone
  rw [if_pos rfl]
  rfl

end Iop
