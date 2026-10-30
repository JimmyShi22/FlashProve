-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarK.lean: the compiled scheme with the entries in the verification key. Only
definitions and the lemmas that unfold them. (Words of this library: lean/GLOSSARY.md.)

The scheme (C, P, V) of Compile/Batch/Star.lean encodes the index once (the first encoding, under
cm) and M + 1 more times (the copies). piT, piL_j, piB are the proof strings of Test, of Link for
copy j, of one slot. Its key is ivk = (cm, piT), and every proof carries, beside the number j of the
copy that was sampled and piB, the entry of that copy, (cm_j, piL_j). Here the committer publishes
all M + 1 entries, and a proof is (j, piB):

  `IVKK`, `linksOf`   ivk' = (ivk, entries) = ((cm, piT), [(cm_0, piL_0), .., (cm_M, piL_M)]).
  `argBK`   C' is C, followed by the output of the entries, which are read off C's own output isk.
            P' is P, followed by the removal of the fields cm and piL from each proof (`stripK`);
            isk does not change. V' (ivk', x, (j, piB)) = V (ivk, x, (0, cm_j, piL_j, piB)) with
            entry number j of ivk' (`reK`, `liftK`).

V uses the field leaf of a proof for one check, leaf ≤ M (Compile/Batch/Star.lean); V' passes 0
there, so V' does not read M: the check is replaced by this: ivk' has an entry number j (`reK`).
That the honest key has exactly M + 1 entries, and that on a key with at most M + 1 entries V' is V
on (j, cm_j, piL_j, piB), is proved in Compile/Batch/HonestK.lean (`length_links_honest`,
`VK_eq_of_length_le`). Otherwise: the same programs `Cp` and `Pp`, the same coins, the same oracle
queries by C, P and V, the same isk.

  `pubK`   What is published and how a proof is read with it, in the form of Compile/GenPub.lean.
           `argBPub` = `pubArg argB pubK` is the scheme between the two: the entries are in the key,
           proofs are still long, and V' ignores their fields cm and piL.
  `via_K`   `argBPub` and `argBK` are in the relation `Via` of Compile/GenMap.lean (equalities of
            programs).
  `extractorBK`   The extractor: E_i decodes what the committer's trace determines under the root cm
                  of ivk', as before; it does not read the entries.

Limits: V' reads one entry of the list. The other entries, and the length of the list, are checked
against nothing. None of the three properties of a scheme is proved for `argBK` in this library;
index binding of `argBKE`, which has the same committer and verifier, for `L.PropsNoAcc`, `W.OKG`,
is `bindingKEGr` (Compile/Batch/MainKEGr.lean). What is proved of these definitions: the honest side
and sanity lemmas (Compile/Batch/HonestK.lean; elsewhere, for example: `extractorBK_local`,
Top/Prog.lean; `honestSoundBK`, CompileK/HonestKeySound.lean: a bound under an honest key, under the
hypotheses of its statement).
-/
import Compile.Batch.SpecBinding
import Compile.Batch.Mirror
import Compile.GenPub

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap Compile.GenPub

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the published entries: for each copy the root of its tree and Link's proof string -/
abbrev Links (lam : ℕ) (L : BatchProtocol I X) : Type :=
  List (Dig lam × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))

/-- the verification key with the entries -/
abbrev IVKK (lam : ℕ) (L : BatchProtocol I X) : Type := IVK lam L × Links lam L

/-- a proof without the entry -/
structure PrfK (lam : ℕ) (L : BatchProtocol I X) where
  leaf : ℕ
  piB : Option (OneProtocolProof lam L.onlineBatch)

/-- the entries, read off the list that holds for each copy its tree and Link's proof string (WKey,
keyOf: Compile/Batch/Mirror.lean) -/
def linksOf (key : WKey lam L) : Links lam L := key.map fun e => (e.1.root, e.2)

/-- the proof π with the fields cm and piL overwritten by entry number π.leaf, or by (zeros, none)
if the list has no such entry, and the field leaf by 0 (V compares that field with M and uses it for
nothing else) -/
def reK (ℓ : Links lam L) (π : Prf lam L) : Prf lam L :=
  match ℓ[π.leaf]? with
  | some e => ⟨0, e.1, e.2, π.piB⟩
  | none => ⟨0, default, none, π.piB⟩

/-- take the fields cm and piL out of a proof -/
def stripK (π : Prf lam L) : PrfK lam L := ⟨π.leaf, π.piB⟩
/-- a proof without entry in the format `Prf`, with (zeros, none) in the two fields; reK overwrites
them -/
def liftK (π : PrfK lam L) : Prf lam L := ⟨π.leaf, default, none, π.piB⟩

theorem stripK_liftK (π : PrfK lam L) : stripK (liftK π) = π := rfl
theorem reK_liftK_stripK (ℓ : Links lam L) (π : Prf lam L) : reK ℓ (liftK (stripK π)) = reK ℓ π :=
  rfl

/-- what is published, and how a proof is read with it -/
def pubK : Pub (IVK lam L) (ISK lam L) (Prf lam L) (Links lam L) where
  pub := fun _ k => linksOf (keyOf k.1)
  re := reK

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- the scheme between the two: the entries are in the key, the proofs are those of argB, and V'
does not use their fields cm and piL -/
abbrev argBPub : Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) (ISK lam L) (Prf lam L) :=
  pubArg (argB W WP p) pubK

/-- The compiled scheme with the entries in the verification key. -/
def argBK : Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) (ISK lam L) (PrfK lam L) where
  C := fun i => (C W WP p i).bind fun o => .pure ((o.1, linksOf (keyOf o.2.1)), o.2)
  P := fun k b => (P W WP p k b).bind fun l => .pure (mapS stripK l)
  V := fun v x π => V W p v.1 x (reK v.2 (liftK π))

theorem via_K : Via (argBPub W WP p) (argBK W WP p) id stripK where
  C := fun i => by
    show ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)) =
      ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)).bind
        fun o => .pure (o.1, o.2)
    rw [OComp.bind_assoc]
    rfl
  P := fun _ _ => rfl
  V := fun _ _ _ => rfl

/-- What V' does if the key has an entry of the proof's number: it runs V on the key without
entries, that entry and the slot's proof string. -/
theorem VK_of_some {v : IVKK lam L} {π : PrfK lam L}
    {e : Dig lam × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))}
    (h : v.2[π.leaf]? = some e) (x : X) :
    (argBK W WP p).V v x π = V W p v.1 x ⟨0, e.1, e.2, π.piB⟩ := by
  show V W p v.1 x (reK v.2 (liftK π)) = _
  unfold reK
  rw [show v.2[(liftK π).leaf]? = some e from h]
  rfl

/-- What V' does if the key has no entry of the proof's number: it rejects, without a query. -/
theorem VK_of_none {v : IVKK lam L} {π : PrfK lam L} (h : v.2[π.leaf]? = none) (x : X) :
    (argBK W WP p).V v x π = pure false := by
  show V W p v.1 x (reK v.2 (liftK π)) = _
  unfold reK
  rw [show v.2[(liftK π).leaf]? = none from h]
  unfold V
  cases v.1.piT <;> rfl

/-- The extractor. -/
def extractorBK : Gen.Extractor (spec lam W.K L) I X Unit (IVKK lam L) (PrfK lam L) :=
  pullE liftK (pubE pubK (extractorB W))

/-- E_i decodes what the committer's trace determines under the root in the key, as for argB -/
theorem extractorBK_Ei (v : IVKK lam L) (tr : Trace (spec lam W.K L)) :
    (extractorBK W).Ei v tr = (extractorB W).Ei v.1 tr := rfl

end Compile.Batch
