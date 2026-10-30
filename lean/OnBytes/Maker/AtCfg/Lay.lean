-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/AtCfg/Lay.lean: the makers of a key file's and a proof file's protocol read neither
the digest of the public files nor the parameter bytes.

The parameters of a chain (`Params.Given`, OnBytes/Params/Given.lean) hold four fields: the bytes as
they are hashed, the plan, the digest of the public files, the further items. The digest is an
answer of the hash function, and the bytes hold it. The makers (OnBytes/Maker/Files.lean) take a
file's three chains' parameters whole (`Params.KeyChains`, `Params.ProofChains`). Here: whatever
digest and whatever bytes are laid into the three chains' parameters, the makers give the same
values. Definitions, and equations that hold by unfolding.

Main names:
  `Params.Lay3`: three pairs (digest, bytes), one for each chain of a file.
  `Given.lay`, `First.lay`, `KeyChains.lay`, `ProofChains.lay`: the parameters with these laid in
    the place of their own. Every other field stays.
  `KeyChains.wipe`, `ProofChains.wipe`: with empty strings laid.
  `KeyChains.atCfg`, `ProofChains.atCfg`: with one digest d laid, and the bytes spelled anew from
    each chain's plan, d and its items: the terms that `KeyChains.read_at` and `ProofChains.read_at`
    (OnBytes/Params/ReadBackAt.lean) have as the readers' answers at another digest.
  `KeyChains.atCfg_eq_lay`, `KeyChains.lay_own`, `KeyChains.lay_holds`, `KeyChains.wipe_lay` and the
    proof file's: `atCfg` is a value of `lay`; the own values laid give the parameters back; what is
    laid stands there; wiping forgets what was laid.
  `dryKey_lay`, `decideKey_lay`, `keyIOR_lay`, `keyAnn_lay`: the dry runs' rounds, the three
    decisions, the reduction and the annotation of its shape at `k.lay x` are those at k.
  `dryProof_lay`, `decideProof_lay`, `proofIOR_lay`, `proofAnn_lay`: the same at `c.lay x`, at every
    first block. `firstBlock_lay`: the program's first block at `p.lay x` is that at p.
  `dryKey_of_wipe`, `decideKey_of_wipe`, `dryProof_of_wipe`, `decideProof_of_wipe`: two values that
    are wiped to one value have the same rounds and decisions.

The equations named `…_lay`, `…_own`, `…_holds` and `atCfg_eq_lay` are proved by `rfl`; the four
`…_of_wipe` follow from them. So the two sides of a `…_lay` are equal by definition, and in
`keyAnn_lay` and `proofAnn_lay`, whose two sides have types that name the parameters, no transport
stands.

Limits: nothing on the readers: `Key.check`, `Key.readKey`, `Proof.readTail`, `Given.describe` read
both fields. TWO FIELDS OF A CHAIN's PARAMETERS ARE LAID, `cfg` and `bytes`, AND NO OTHER: the plan,
the field `items` (the further items as bytes) and, in a proof's first chain, the field `more` (the
items of a caller's sub-proofs) stay as they are. That these hold no answer of a hash function, and
that no maker reads `items` or `more`, is not said here. That a
planner's parameters at another digest are `atCfg` of those at this one is not said here
(`plannedAt_at`, OnBytes/Tie/ChainsAtCfg.lean, says it with `chainsAtCfg`, at two digests of 32
bytes and strings below 2 ^ 64 bytes; the tie to `atCfg`: Johnson/Flat/AtCfg/PlanLay.lean [not in
this library; so here read: not proved in this library]). Of a proof file the links' block is a
letter (an argument of `firstBlock_lay`): whether the program's links read a digest is not said.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Files
import OnBytes.Params.ReadBackAt

set_option autoImplicit false

namespace OnBytes.Params

/-- Three pairs (digest of the public files, parameter bytes): one for each chain of a file. -/
abbrev Lay3 : Type := (ByteArray × ByteArray) × (ByteArray × ByteArray) × (ByteArray × ByteArray)

/-- Three pairs of empty strings. -/
def Lay3.none : Lay3 :=
  ((ByteArray.empty, ByteArray.empty), (ByteArray.empty, ByteArray.empty),
    (ByteArray.empty, ByteArray.empty))

/-- g with the digest x.1 and the bytes x.2 in the place of its own. -/
def Given.lay (g : Given) (x : ByteArray × ByteArray) : Given := { g with cfg := x.1, bytes := x.2 }

/-- The parameters of a proof's first chain with x laid. -/
def First.lay (p : First) (x : ByteArray × ByteArray) : First := { p with given := p.given.lay x }

/-- The parameters of a key's three chains with x laid. -/
def KeyChains.lay (k : KeyChains) (x : Lay3) : KeyChains :=
  ⟨{ k.oneTime with given := k.oneTime.given.lay x.1 },
    { k.shared with given := k.shared.given.lay x.2.1 },
    { k.second with given := k.second.given.lay x.2.2 }⟩

/-- The parameters of a proof's three chains with x laid. -/
def ProofChains.lay (c : ProofChains) (x : Lay3) : ProofChains :=
  ⟨c.first.lay x.1, { c.shared with given := c.shared.given.lay x.2.1 },
    { c.second with given := c.second.given.lay x.2.2 }⟩

/-- With empty strings laid. -/
def KeyChains.wipe (k : KeyChains) : KeyChains := k.lay Lay3.none

/-- With empty strings laid. -/
def ProofChains.wipe (c : ProofChains) : ProofChains := c.lay Lay3.none

/-- With the digest d laid in all three chains, and each chain's bytes spelled anew. -/
def KeyChains.atCfg (k : KeyChains) (d : ByteArray) : KeyChains :=
  ⟨{ k.oneTime with given := k.oneTime.given.atCfg d },
    { k.shared with given := k.shared.given.atCfg d },
    { k.second with given := k.second.given.atCfg d }⟩

/-- With the digest d laid in all three chains, and each chain's bytes spelled anew. -/
def ProofChains.atCfg (c : ProofChains) (d : ByteArray) : ProofChains :=
  ⟨{ c.first with given := c.first.given.atCfg d },
    { c.shared with given := c.shared.given.atCfg d },
    { c.second with given := c.second.given.atCfg d }⟩

theorem KeyChains.atCfg_eq_lay (k : KeyChains) (d : ByteArray) :
    k.atCfg d = k.lay ((d, (k.oneTime.given.atCfg d).bytes), (d, (k.shared.given.atCfg d).bytes),
      (d, (k.second.given.atCfg d).bytes)) := rfl

theorem ProofChains.atCfg_eq_lay (c : ProofChains) (d : ByteArray) :
    c.atCfg d = c.lay ((d, (c.first.given.atCfg d).bytes), (d, (c.shared.given.atCfg d).bytes),
      (d, (c.second.given.atCfg d).bytes)) := rfl

/-- The own values laid give the parameters back. -/
theorem KeyChains.lay_own (k : KeyChains) :
    k.lay ((k.oneTime.given.cfg, k.oneTime.given.bytes), (k.shared.given.cfg, k.shared.given.bytes),
      (k.second.given.cfg, k.second.given.bytes)) = k := rfl

theorem ProofChains.lay_own (c : ProofChains) :
    c.lay ((c.first.given.cfg, c.first.given.bytes), (c.shared.given.cfg, c.shared.given.bytes),
      (c.second.given.cfg, c.second.given.bytes)) = c := rfl

/-- What is laid stands there: `lay` is not the identity. -/
theorem KeyChains.lay_holds (k : KeyChains) (x : Lay3) :
    ((k.lay x).oneTime.given.cfg, (k.lay x).oneTime.given.bytes) = x.1 ∧
      ((k.lay x).shared.given.cfg, (k.lay x).shared.given.bytes) = x.2.1 ∧
      ((k.lay x).second.given.cfg, (k.lay x).second.given.bytes) = x.2.2 := ⟨rfl, rfl, rfl⟩

theorem ProofChains.lay_holds (c : ProofChains) (x : Lay3) :
    ((c.lay x).first.given.cfg, (c.lay x).first.given.bytes) = x.1 ∧
      ((c.lay x).shared.given.cfg, (c.lay x).shared.given.bytes) = x.2.1 ∧
      ((c.lay x).second.given.cfg, (c.lay x).second.given.bytes) = x.2.2 := ⟨rfl, rfl, rfl⟩

/-- Wiping forgets what was laid. -/
theorem KeyChains.wipe_lay (k : KeyChains) (x : Lay3) : (k.lay x).wipe = k.wipe := rfl

theorem ProofChains.wipe_lay (c : ProofChains) (x : Lay3) : (c.lay x).wipe = c.wipe := rfl

end OnBytes.Params

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds Lay3)

/-! ## A key file -/

/-- **The dry runs of a key file's blocks read neither the digest nor the parameter bytes.** -/
theorem dryKey_lay (k : Params.KeyChains) (x : Lay3) : dryKey (k.lay x) = dryKey k := rfl

/-- **The three decisions on a key file read neither.** -/
theorem decideKey_lay (k : Params.KeyChains) (x : Lay3) : decideKey (k.lay x) = decideKey k := rfl

theorem dryKey_of_wipe {k k' : Params.KeyChains} (h : k.wipe = k'.wipe) : dryKey k = dryKey k' :=
  (dryKey_lay k Lay3.none).symm.trans ((congrArg dryKey h).trans (dryKey_lay k' Lay3.none))

theorem decideKey_of_wipe {k k' : Params.KeyChains} (h : k.wipe = k'.wipe) :
    decideKey k = decideKey k' :=
  (decideKey_lay k Lay3.none).symm.trans ((congrArg decideKey h).trans (decideKey_lay k' Lay3.none))

/-! ## A proof file -/

/-- The program's first block of a proof file reads neither. links: a letter. -/
theorem firstBlock_lay (p : Params.First) (x : ByteArray × ByteArray)
    (links : Blk Proof.LinksResult) (reply : E) :
    Proof.firstBlock (p.lay x) links reply = Proof.firstBlock p links reply := rfl

/-- **The dry runs of a proof file's blocks read neither**, at every first block. -/
theorem dryProof_lay (c : Params.ProofChains) (x : Lay3) : dryProof (c.lay x) = dryProof c := rfl

/-- **The three decisions on a proof file read neither**, at every first block. -/
theorem decideProof_lay (c : Params.ProofChains) (x : Lay3) :
    decideProof (c.lay x) = decideProof c := rfl

theorem dryProof_of_wipe {c c' : Params.ProofChains} (h : c.wipe = c'.wipe) :
    dryProof c = dryProof c' :=
  (dryProof_lay c Lay3.none).symm.trans ((congrArg dryProof h).trans (dryProof_lay c' Lay3.none))

theorem decideProof_of_wipe {c c' : Params.ProofChains} (h : c.wipe = c'.wipe) :
    decideProof c = decideProof c' :=
  (decideProof_lay c Lay3.none).symm.trans
    ((congrArg decideProof h).trans (decideProof_lay c' Lay3.none))

/-! ## The two reductions and their annotations -/

section
variable (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **A key file's reduction at `k.lay x` is that at k.** -/
theorem keyIOR_lay {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (x : Lay3) (rec₀ : R) :
    keyIOR C a tF tJ t3 silent key (k.lay x) rec₀ = keyIOR C a tF tJ t3 silent key k rec₀ := rfl

/-- The annotation of its shape alike. The two sides' types are equal by definition. -/
theorem keyAnn_lay {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (x : Lay3) (rec₀ : R) :
    keyAnn C a tF tJ t3 silent key (k.lay x) rec₀ = keyAnn C a tF tJ t3 silent key k rec₀ := rfl

/-- **A proof file's reduction at `c.lay x` is that at c.** -/
theorem proofIOR_lay {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (x : Lay3) (block : X → Blk Proof.FirstEnd) (z₀ : X × R) :
    proofIOR C a tF tJ t3 silent key (c.lay x) block z₀ =
      proofIOR C a tF tJ t3 silent key c block z₀ := rfl

/-- The annotation of its shape alike. The two sides' types are equal by definition. -/
theorem proofAnn_lay {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (x : Lay3) (block : X → Blk Proof.FirstEnd) (z₀ : X × R) :
    proofAnn C a tF tJ t3 silent key (c.lay x) block z₀ =
      proofAnn C a tF tJ t3 silent key c block z₀ := rfl

end

end OnBytes.Maker
