-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedFace.lean: the compiled scheme `argBKE` (entries in the verification key; no query
and no tree for an empty slot) is of the form `argOf` of Compile/Batch/SeedStar.lean. (Words of this
library: lean/GLOSSARY.md.)

The transformation of Compile/Batch/SeedStar.lean makes (i, seed) the proving key. It is stated for
a record `Face`: what is published, the program of one batch on the `Node` of the sampled copy, the
verifier.

Here is the record `faceKE` of `argBKE` (Compile/Batch/StarKE.lean; `argBKE_eq`):
* the entries are in ivk (for each copy the root of its tree and Link's proof string: `Links`,
  Compile/Batch/StarK.lean);
* a proof is (number of the copy, piB);
* the compiled prover is `proveBU` of Compile/Batch/ProverU.lean.

The transformation requires two properties of programs (`Face.TokFree`, `Face.NoOther`). For a
record made from any program pv (`faceOf`), they follow from the same properties of pv and, for
`NoOther`, the hypothesis that V never queries the auxiliary oracle (`tokFree_faceOf`,
`noOther_faceOf`). `P_eq`: the prover `PKOf` is the prover of `argOf` at that record.

Notation: `L`: an `BatchProtocol I X`: the record of protocols (Test, Link, Batch; Iop/Batch.lean); `W`: a
`QueryLayout lam L`, the wire record (Iop/BatchWire.lean); `WP`: a `WireBP L`: the prover's data for the
three protocols, and the enumeration of the encoding randomness (Iop/BatchWireP.lean); `p`: a
`Params` (Compile/Star.lean); `p.sMT`, `p.sFS`: the length of the salt of a leaf, and of the salt of
a chain (Compile/Batch/Verifier.lean); the number of copies is `p.M` + 1; `L.maxBatchSize`: the number of slots
(Iop/Batch.lean); `pv`: a `Run W`: what is in the place of the compiled prover of a batch: given the
trees over the encoded index, (i, r), the flags and the slots, a proof string or none for each slot;
`fr`, `fl`: maps `ℕ → Bool`: the flags of the requests, and these as flags of the slots
(`slotFlags`, Compile/Batch/Star.lean); fr: for which requests a proof string is made at all (the
head of that file); `Unit` in `List (X × Unit)`: the type argument `W` of `Gen.Arg` (ZKCP/Gen.lean);
`Tag.onl`: the `Tag` of Batch: `shapeOf L .onl` is `L.onlineBatch.loc.shape` (Compile/Batch/Oracles.lean);
`stripK`: take the fields cm and piL out of a proof; `liftK`: a proof without entry in the format
`Prf`, with (zeros, none) in the two fields; `reK`: the proof π with the fields cm and piL
overwritten by entry number π.leaf, or by (zeros, none) if the list has no such entry, and the field
leaf by 0 (these three: Compile/Batch/StarK.lean); `fitLen d n l`: a list cut or filled up to the
length n (Compile/Batch/Star.lean); `N₀`, `δ`: natural numbers, the arguments of `up`: `up N₀ δ v`
is v if v < N₀, else v + δ (Compile/Step1_life2_Virt.lean).

Limits: nothing is said about distributions or security: equalities of programs, and two properties
of programs.
-/
import Compile.Batch.SeedStar
import Compile.Batch.StarKE

noncomputable section

open Rom Iop ZKCP Compile.GenMap

namespace Compile.Batch
namespace Seed

open Compile.Seed (Par upTree)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- what is in the place of the compiled prover of a batch: given the trees over the encoded index,
(i, r), the flags and the slots, a proof string or none for each slot -/
abbrev Run (W : QueryLayout lam L) : Type :=
  List (TreeH lam) → I × L.EncodingRandomness → (ℕ → Bool) → List (Option X) →
  St lam W.K L (List (Option (OneProtocolProof lam L.onlineBatch)))

/-- the compiled prover of Compile/Batch/ProverU.lean, as the scheme calls it -/
def runBU : Run W := fun trees w fl xs =>
  proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩))
    id some W.depthReq trees w fl xs

variable {W}

/-- the proofs of the requests, from the proof strings of the slots -/
def prfsK (j : ℕ) (n : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) (πs : List (Option (OneProtocolProof lam L.onlineBatch))) :
    List (PrfK lam L) :=
  (List.range n).map fun a => ⟨j, if h : a < L.maxBatchSize then πs.getD (σ ⟨a, h⟩).val none else none⟩

/-- One batch on the `Node` of copy j: a sampled placement (uniform if `WP.perm` has `Enum.OK`,
Iop/Wire.lean), one execution of pv, a proof (j, piB) for each request (without a `Node`: every
proof is (j, none)). -/
def batOf (pv : Run W) (i : I) (j : ℕ) (nd : Option (Node lam L)) (b : List (X × Unit)) :
    St lam W.K L (Gen.Slots (PrfK lam L) b) :=
  (drawT WP.perm).bind fun σ =>
    match nd with
    | none => Step.pure (fitLen ⟨0, none⟩ b.length ((b.map Prod.fst).map fun _ => ⟨j, none⟩))
    | some nd =>
        (pv [nd.tree] (i, nd.r) (slotFlags σ fun _ => true)
            (slotsOfReq σ (b.map Prod.fst))).bind fun πs =>
        Step.pure (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length σ πs))

/-- The record `Face`: the entries are published; a batch is `batOf`; V is that of
Compile/Batch/StarK.lean. -/
def faceOf (pv : Run W) : Face W (IVKK lam L) (PrfK lam L) where
  key := fun v k => (v, linksOf (keyOf k))
  bat := batOf WP pv
  V := fun v x π => V W p v.1 x (reK v.2 (liftK π))

/-! ## The provers -/

theorem mapS_fitLen {β : Type} (b : List β) (d : Prf lam L) (l : List (Prf lam L)) :
    (mapS stripK (fitLen d b.length l : Gen.Slots (Prf lam L) b) : Gen.Slots (PrfK lam L) b) =
      fitLen (stripK d) b.length (l.map stripK) := by
  apply Subtype.ext
  show ((l ++ List.replicate b.length d).take b.length).map stripK =
    (l.map stripK ++ List.replicate b.length (stripK d)).take b.length
  rw [List.map_take, List.map_append, List.map_replicate]

/-- the batch of the scheme whose proofs hold the entry, for any pv: the definition of PpJ of
Compile/Batch/Star.lean -/
def PpJOf (pv : Run W) (k : IskH lam L) (fr : ℕ → Bool) (xs : List X)
    (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    St lam W.K L (List (Prf lam L)) :=
  match k.leaves[j]? with
  | none => pure (xs.map fun _ => ⟨j, default, none, none⟩)
  | some lf =>
      (pv [lf.node.tree] (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun πs =>
      pure ((List.range xs.length).map fun a =>
        ⟨j, lf.node.tree.root, lf.piL, if h : a < L.maxBatchSize then πs.getD (σ ⟨a, h⟩).val none else none⟩)

/-- the prover whose proofs are (j, piB), for any pv -/
def PKOf (pv : Run W) (k : ISK lam L) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  ((eraseR (Step.sample p.M fun j =>
        (drawT WP.perm).bind fun σ => PpJOf pv k.1 (fun _ => true) (b.map Prod.fst) j.val σ)
      k.2).bind fun o =>
        (.pure (fitLen ⟨0, default, none, none⟩ b.length
            o.1) : TypedOracleComputation lam W.K L (Gen.Slots (Prf lam L) b))).bind
    fun l => .pure (mapS stripK l)

/-- `PKOf` is the prover of `argOf` at the record `faceOf`. -/
theorem P_eq (pv : Run W) (k : ISK lam L) (b : List (X × Unit)) :
    PKOf WP p pv k b = (argOf WP p (faceOf WP p pv)).P k b := by
  show Rom.OComp.sample p.M _ = Rom.OComp.sample p.M _
  refine congrArg _ (funext fun j => ?_)
  show ((eraseR
        ((drawT WP.perm).bind fun σ => PpJOf pv k.1 (fun _ => true) (b.map Prod.fst) j.val σ)
        k.2).bind _).bind _ =
    (eraseR (batOf WP pv k.1.i j.val (k.1.leaves[j.val]?.map LeafRec.node) b) k.2).bind _
  unfold batOf
  rw [eraseR_bind, eraseR_bind, OComp.bind_assoc, OComp.bind_assoc, OComp.bind_assoc]
  refine congrArg _ (funext fun o => ?_)
  unfold PpJOf
  cases k.1.leaves[j.val]? with
  | none =>
    show Rom.OComp.pure (mapS stripK (fitLen _ b.length _)) = Rom.OComp.pure _
    rw [mapS_fitLen, List.map_map]
    rfl
  | some lf =>
    show (eraseR ((pv [lf.node.tree] (k.1.i, lf.node.r) _ _).bind _) o.2).bind _ =
      (eraseR ((pv [lf.node.tree] (k.1.i, lf.node.r) _ _).bind _) o.2).bind _
    rw [eraseR_bind, eraseR_bind, OComp.bind_assoc, OComp.bind_assoc]
    refine congrArg _ (funext fun c => ?_)
    show Rom.OComp.pure (mapS stripK (fitLen _ b.length _)) = Rom.OComp.pure _
    rw [mapS_fitLen, List.map_map]
    rfl

variable (W)

/-- the provers P and PU: writing the ghost names back (`realQ`) commutes with the last step, which
makes no query -/
theorem P_real (k : ISK lam L) (b : List (X × Unit)) :
    P W WP p k b =
      (eraseR (Pp W WP p k.1 (fun _ => true) (b.map Prod.fst)) k.2).bind fun o =>
        .pure (fitLen ⟨0, default, none, none⟩ b.length o.1) := realQ_bind _ _
theorem PU_real (k : ISK lam L) (b : List (X × Unit)) :
    PU W WP p k b =
      (eraseR (PpU W WP p k.1 (fun _ => true) (b.map Prod.fst)) k.2).bind fun o =>
        .pure (fitLen ⟨0, default, none, none⟩ b.length o.1) := realQ_bind _ _

/-- the record `Face` of `argBKE` -/
def faceKE : Face W (IVKK lam L) (PrfK lam L) := faceOf WP p (runBU W WP p)

/-- `argBKE` is `argOf` at the record `faceKE`. -/
theorem argBKE_eq : argBKE W WP p = argOf WP p (faceKE W WP p) := by
  have hP : PKE W WP p = (argOf WP p (faceKE W WP p)).P := funext fun k => funext fun b => by
    show (PU W WP p k b).bind _ = _
    rw [PU_real]
    exact P_eq WP p (runBU W WP p) k b
  show (⟨_, PKE W WP p, _⟩ : Gen.Arg _ _ _ _ _ _ _) = ⟨_, (argOf WP p (faceKE W WP p)).P, _⟩
  rw [hP]
  rfl

/-! ## The two properties of programs, from those of pv and V -/

variable {W}

theorem length_slotsOfReq (σ : Equiv.Perm (Fin L.maxBatchSize)) (xs : List X) :
    (slotsOfReq σ xs).length = L.maxBatchSize := by
  simp [slotsOfReq]

/-- If pv, on lists of L.maxBatchSize slots, does not look at the numbers of its tokens, neither does `faceOf`.
-/
theorem tokFree_faceOf (pv : Run W)
    (h : ∀ (N₀ δ : ℕ) trees w fl xs,
      xs.length = L.maxBatchSize → Par N₀ δ Eq (pv (trees.map (upTree N₀ δ)) w fl xs) (pv trees w fl xs)) :
    (faceOf WP p pv).TokFree := by
  intro N₀ δ i j nd b
  show Par N₀ δ Eq (batOf WP pv i j (some (upNode N₀ δ nd)) b) (batOf WP pv i j (some nd) b)
  unfold batOf
  refine Par.bind (r := Eq) (Par.sample _ fun _ => Par.pure rfl) fun σ σ' e => ?_
  subst e
  refine Par.bind (r := Eq)
    (h N₀ δ [nd.tree] (i, nd.r) _ _ (length_slotsOfReq σ _)) fun πs πs' e => ?_
  subst e
  exact Par.pure rfl

/-- If pv and V never query the auxiliary oracle, `faceOf` has `NoOther`. -/
theorem noOther_faceOf (pv : Run W)
    (h : ∀ trees w fl xs vs, (erase (pv trees w fl xs) vs).Avoids OracleName.other)
    (hV : ∀ v x π, (V W p v x π).Avoids OracleName.other) : (faceOf WP p pv).NoOther where
  bat := fun i j nd b vs => by
    refine avoids_realQ OracleName.other (fun _ => nofun) _ ?_
    show (erase (batOf WP pv i j nd b) vs).Avoids OracleName.other
    unfold batOf
    rw [erase_bind]
    refine Derive.Avoids.bind (fun _ => trivial) fun o => ?_
    cases nd with
    | none => exact trivial
    | some nd =>
      show (erase ((pv [nd.tree] (i, nd.r) _ _).bind _) o.2).Avoids OracleName.other
      rw [erase_bind]
      exact Derive.Avoids.bind (h _ _ _ _ _) fun _ => trivial
  V := fun v x π => hV v.1 x _

end Seed
end Compile.Batch
