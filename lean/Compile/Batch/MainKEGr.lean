-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/MainKEGr.lean: the scheme `argBKE`, at a wire record whose rounds may have
proof-of-work bits: index binding (for `L.PropsNoAcc`, `W.OKG`); index privacy and completeness from
those of other schemes (words of this library: lean/GLOSSARY.md). `argBKE`
(Compile/Batch/StarKE.lean): entries in the verification key, no query for an empty slot. This file
does not prove the compiler theorem for it (the three properties for `argBKE`:
`mainBatchKEGrWithBOf`, Compile/Batch/PubProgMainBGr.lean).
  `skipFPpU`            for every wire record: `PpU` is `Pp` without the work for the empty slots
  `argBPubU`, `via_KE`, `argBPubU_eq`
                        for every wire record: the scheme `argBPubU` between `argBU` and `argBKE`
  `honestKU`            for every wire record: `Pub.Honest` for `argBU`
  `privacyKE_of`        index privacy of `argBKE` with the simulator `simBKGr` from index privacy of
                        `argBPubU` with `simBPGr`, whatever the bound ζ is: post-processing
  `completeKE_of`       completeness, whatever the error, from completeness of `argBU`
  `bindingKEGr`         index binding, for `L.PropsNoAcc`, `W.OKG`: that of `argBK`, whose committer
                        and verifier these are

Notation: the schemes: `argBU` (Compile/Batch/StarU.lean): the compiled scheme without queries for
empty slots; `argBK` (Compile/Batch/StarK.lean): the compiled scheme with the entries in the
verification key; `argBPubU` (this file): the scheme between `argBU` and `argBKE`: entries in the
key, proofs with their own entry; the entries (`Links`, Compile/Batch/StarK.lean): for each copy the
root of its tree and Link's proof string; `reK ℓ π` (the same file): the proof π with the fields cm
and piL overwritten by entry number π.leaf, or by (zeros, none) if the list has no such entry, and
the field leaf by 0; `stripK` (the same file): take the fields cm and piL out of a proof;
`L.PropsNoAcc` (Iop/BatchGrind.lean): all properties of a record of protocols but completeness,
(Acc); `W.OKG` (Iop/BatchWire.lean): the laws of a wire whose rounds may have tests; `Via A A' φ τ`
(Compile/GenMap.lean): A is A' up to a map on proving keys and a map on proofs: equalities of
programs; `AllOut Q c` (Compile/GenPub.lean): every output of the algorithm, on every path of its
tree, has the property Q; `erase` (Compile/Star.lean): forget the rules: tokens are strings, kept in
a list; `Gen.HasCompletenessError`, `Gen.HasIndexBindingWith`, `Gen.HasIndexPrivacyWith`:
ZKCP/Gen.lean; `epsB` : Compile/Batch/SpecBinding.lean; slot, wire record: lean/GLOSSARY.md.

Limits: what the headers of Compile/Batch/SpecUGr.lean, Compile/Batch/SpecPubGr.lean and
Compile/Batch/SpecGrind.lean do not say is not said here either.
-/
import Compile.Batch.SpecUGr
import Compile.Batch.PubProgMainGr
import Compile.Batch.MaskU
import Compile.Batch.SkipU
import Compile.Batch.GhostRoutedU
import Compile.Batch.BindingG
import Compile.Batch.HonestK

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP Compile.GenMap Compile.GenPub
open Compile.BatchLife (Sims)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- `PpU` is `Pp` without the work for the empty slots (`SkipFProg`), for all flags -/
theorem skipFPpU (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    SkipFProg (Pp W WP p) (PpU W WP p) :=
  fun fr k xs w h0 hk => skipPp I X lam L W WP p k fr xs w h0 hk

/-- the scheme between `argBU` and `argBKE`: entries in the key, proofs with their own entry -/
abbrev argBPubU (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) (ISK lam L) (Prf lam L) :=
  argBPG W WP p (fun v key => (v, linksOf key)) (PpU W WP p) (fun v x π => V W p v.1 x (reK v.2 π))

theorem via_KE (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    Via (argBPubU W WP p) (argBKE W WP p) id stripK where
  C := fun i => by
    show ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)) =
      ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)).bind
        fun o => .pure (o.1, o.2)
    rw [OComp.bind_assoc]
    rfl
  P := fun _ _ => rfl
  V := fun _ _ _ => rfl

/-- Index privacy from that of `argBPubU` (`h`), whatever the bound: the simulator
(`simBKGr W p Sm i₀`) is that of the scheme whose prover hashes empty slots. -/
theorem privacyKE_of (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (R : Gen.RelPair I X Unit Unit)
    (Sm : Sims L) (i₀ : I) (ζ : ℕ → ℕ → ℝ≥0∞)
    (h : Gen.HasIndexPrivacyWith
      R (argBPubU W WP p) L.maxBatchSize (simBPGr W p (fun v key => (v, linksOf key)) Sm i₀) ζ) :
    Gen.HasIndexPrivacyWith R (argBKE W WP p) L.maxBatchSize (simBKGr W p Sm i₀) ζ :=
  GenMap.privacyWith (via_KE W WP p) _ h


/-! ## `Pub.Honest`: for V, overwriting an honest proof's entry from the key changes nothing -/

theorem allOut_PpJU (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (k : IskH lam L) (fr : ℕ → Bool)
    (xs : List X) (j : Fin (p.M + 1)) (σ : Equiv.Perm (Fin L.maxBatchSize)) (vs : List Bits) :
    AllOut (fun o : List (Prf lam L) × List Bits => ∀ π ∈ o.1, GoodK p k π)
      (erase (PpJU W WP p k fr xs j.val σ) vs) := by
  unfold PpJU
  rcases hl : k.leaves[j.val]? with _ | lf
  · show AllOut _ (OComp.pure (_, vs))
    intro π hπ
    obtain ⟨_, -, rfl⟩ := List.mem_map.1 hπ
    exact Or.inl rfl
  · dsimp only
    rw [erase_bind]
    refine AllOut.bind (allOut_true _) fun o _ => ?_
    show AllOut _ (OComp.pure (_, o.2))
    intro π hπ
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hπ
    exact Or.inr ⟨Nat.lt_succ_iff.1 j.isLt, lf, hl, rfl, rfl⟩

theorem allOut_PU (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    (k : ISK lam L) (b : List (X × Unit)) :
    AllOut (fun πs : Gen.Slots (Prf lam L) b => ∀ π ∈ πs.val, GoodK p k.1 π) (PU W WP p k b) := by
  unfold PU PtokU
  refine allOut_realQ _
    (AllOut.bind (Q' := fun o : List (Prf lam L) × List Bits => ∀ π ∈ o.1, GoodK p k.1 π) ?_
      fun o ho => ?_)
  · unfold PpU
    rw [erase_sample]
    intro j
    dsimp only
    rw [erase_bind]
    exact AllOut.bind (allOut_true _) fun o _ => allOut_PpJU W WP p k.1 _ _ j o.1 o.2
  · show ∀ π ∈ (fitLen (⟨0, default, none, none⟩ : Prf lam L) b.length o.1).val, GoodK p k.1 π
    intro π hπ
    rcases List.mem_append.1 (List.mem_of_mem_take hπ) with h | h
    · exact ho π h
    · rw [(List.mem_replicate.1 h).2]
      exact Or.inl rfl

/-- For V, overwriting from the key the entry of a proof that `PU` can output changes nothing
(`Pub.Honest`). -/
theorem honestKU (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    (pubK : Pub (IVK lam L) (ISK lam L) (Prf lam L) (Links lam L)).Honest (argBU W WP p) :=
  fun v k b => (allOut_PU W WP p k b).mono fun _ h π hπ x => V_reK_of_good W p (h π hπ) v x

/-- `argBPubU` is `argBU` with the entries published (`pubArg`) -/
theorem argBPubU_eq (W : QueryLayout lam L) (WP : WireBP L) (p : Params) :
    pubArg (argBU W WP p) pubK = argBPubU W WP p := rfl

/-- completeness, whatever the error, from that of `argBU` (`h`) -/
theorem completeKE_of (W : QueryLayout lam L) (WP : WireBP L) (p : Params) {PP : Type}
    (R : Gen.RelPair I X Unit PP) (α : ℝ≥0∞) (h : Gen.HasCompletenessError R (argBU W WP p) L.maxBatchSize α) :
    Gen.HasCompletenessError R (argBKE W WP p) L.maxBatchSize α :=
  GenMap.completeness (via_KE W WP p) _ (GenPub.completeness (honestKU W WP p) _ h)

/-- index binding, for `L.PropsNoAcc`, `W.OKG`: that of `argBK`, whose committer and verifier these
are -/
theorem bindingKEGr (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (Ryes Rno : I → X → Prop)
    (M : LH.Nums) (h : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) :
    Gen.HasIndexBindingWith (relPair Ryes Rno h.sub) (argBKE W WP p) (extractorBK W) (epsB W M) :=
  GenMap.binding (via_K W WP p)
    stripK_liftK _ (GenPub.binding pubK _ (bindingBatchG I X lam L W WP p Ryes Rno M h hW))


end Compile.Batch
