-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedAvoidU.lean: the compiled prover that makes no query and builds no tree for an
empty slot never queries the auxiliary oracle. (Words of this library: lean/GLOSSARY.md.)

Why. The scheme with isk = (i, seed) (Compile/Batch/SeedStar.lean) requires of the program of a
batch that it never queries the oracle `OracleName.other` (`Face.NoOther`). For the prover `proveB` of
Compile/Batch/Prover.lean this is `avoids_proveB` of Compile/Batch/SeedShape.lean. Here the same is
shown for `proveBU` of Compile/Batch/ProverU.lean, in which an empty slot samples nothing, builds
nothing and queries nothing, and its leaf of the request tree is a fresh string.

How. What `proveBU` samples depends on which slots are empty, so its samples have no weight that is
the same for all lists of slots. With the weight 0 for every sample the predicate `Compile.Seed.Sh`
says only that the oracle is never queried: `Av c` is Sh OracleName.other (fun _ => 0) 0 c. What is
unchanged against Compile/Batch/Prover.lean is taken from Compile/Batch/SeedShape.lean.
`avoids_proveBU`: for every tag, protocol, wire records, flags, list of slots and store, what
`erase` makes of `proveBU` never queries `OracleName.other`.

Notation: `Sh o₀ μ n c`: for an oracle o₀, a map μ : ℕ → ℕ (the weight of a sample), a number n and
a token program c: every path has uniform samples of the total weight n, and the oracle o₀ is never
queried (Compile/SeedShape.lean); `sMT`, `sFS`: natural numbers: the length of the salt of a leaf,
and of the salt of a chain (Compile/Batch/Verifier.lean); `t`, `Q`, `wq` and `wp`, `fl`, `xs`, `vs`:
the tag, the protocol, the wire records, the flags, the list of slots and the store of
`avoids_proveBU`.

Limits: nothing about the number or the weight of the samples of `proveBU`. (The committer, `C` of
Compile/Batch/Star.lean, runs Test and Link, by `proveB`, on one full slot each; no weight of
`proveBU` on other lists is needed for the labels, on which see "Labels." in the head of
Compile/Batch/SeedStar.lean.)
-/
import Compile.Batch.SeedShape
import Compile.Batch.ProverU

open Rom Iop

namespace Compile.Batch
namespace Seed

open Compile.Seed (Sh)

/-- if every sample counts 0, the weighted number of samples is 0 -/
theorem Sh.av {S : OSpec} {sp : Split S} {α : Type} {o₀ : S.ι} {n : ℕ}
    {c : Step S sp α} (h : Sh o₀ (fun _ => 0) n c) : Sh o₀ (fun _ => 0) 0 c := by
  induction h with
  | pure a => exact .pure a
  | sample m _ ih => exact .sample m ih
  | plain o ho q _ ih => exact .plain o ho q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o ho t us pt inj _ ih => exact .marked o ho t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- the program never asks the spare oracle -/
local notation "Av" => Sh (S := spec lam K L) (sp := split lam K L) OracleName.other (fun _ => 0) 0

theorem av_rleavesTU : ∀ l : List (Option Tok), Av (rleavesTU (lam := lam) (K := K) (L := L) l)
  | [] => .pure _
  | some c :: t => (sh_rleafT _ c).bind0 fun _ => (av_rleavesTU t).bind0 fun _ => .pure _
  | none :: t => .fresh lam fun _ => (av_rleavesTU t).bind0 fun _ => .pure _

theorem av_reqTU (d : ℕ) (cs : List (Option Tok)) :
    Av (reqTU (lam := lam) (K := K) (L := L) d cs) :=
  (av_rleavesTU cs).bind0 fun ls => (sh_levelsM _ (sh_rnodeT _) d ls).bind0 fun _ => .pure _

theorem av_eachM {σ τ : Type} {f : σ → St lam K L τ} (h : ∀ a, Av (f a)) :
    ∀ l : List σ, Av (eachM f l)
  | [] => .pure _
  | a :: t => (h a).bind0 fun _ => (av_eachM h t).bind0 fun _ => .pure _

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem av_slotLoU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    Av (slotLoU sMT t cms xin a w emb plJ i ph z) := by
  unfold slotLoU
  split
  · exact Sh.av (sh_slotLo _ sMT t cms xin a w emb plJ i ph z)
  · exact .pure _

theorem av_slotJoinU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (z : SlotSt lam K Y (r :: s)) :
    Av (slotJoinU sMT t a w emb plJ i z) := by
  unfold slotJoinU
  split
  · exact Sh.av (sh_slotJoin _ sMT t a w emb plJ i z)
  · exact .pure _

theorem av_joinMU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam K Y (r :: s)), Av (joinMU sMT t a w emb plJ i zs)
  | [] => .pure _
  | z :: zs =>
    (av_slotJoinU sMT t a w emb plJ i z).bind0 fun _ =>
      (av_joinMU a w emb plJ i zs).bind0 fun _ => .pure _

theorem av_chainTU (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      Av (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, _, _ => .pure _
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0 => by
      obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
      cases kind with
      | lo =>
        exact (av_eachM
            (av_slotLoU sMT t cms xin _ w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i ph)
            zs).bind0 fun zs' =>
          av_chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
            (i + 1) ph.afterLo _ zs' _
      | sh =>
        cases ph with
        | first =>
          exact av_chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            .first _ (zs.map (hear w (blk0 lam K) false)) _
        | aft =>
          exact av_chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            .aft _ (zs.map (hear w (blk0 lam K) false)) _
        | loc =>
          exact (av_joinMU sMT t _ w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i zs).bind0 fun o =>
            (av_reqTU depthReq o.2).bind0 fun rq =>
              Sh.av (sh_tree0 _ sMT _ w (fun p => embS (.inl p)) m0 (n := 0) fun tr0 =>
                  sh_fbG _ _ _ _ _ _ _ _ _ _ _ _ fun _ _ bl tl =>
                    av_chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
                      (i + 1) (.shr tl) _ (o.1.map (hear w bl true)) _)
        | shr tk0 =>
          exact Sh.av
            (sh_tree0 _ sMT _ w (fun p => embS (.inl p)) m0 (n := 0) fun tr0 =>
              sh_fbG _ _ _ _ _ _ _ _ _ _ _ _ fun _ _ bl tl =>
                av_chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
                  (.shr tl) _ (zs.map (hear w bl false)) _)

end Rounds

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt' : Type} (H : BatchHonestProver Q Wt') (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt')

theorem av_initSlotU (c0 : H.Coin0) :
    ∀ x : Option Y, Av (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x)
  | some x => Sh.av (sh_initSlot _ sFS Q H wp w c0 (some x))
  | none => .pure _

theorem av_proveBU (fl : ℕ → Bool) (xs : List (Option Y)) :
    Av (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) :=
  (Sh.av (sh_drawT _ wp.coin0)).bind0 fun c0 =>
      (av_eachM (av_initSlotU sFS Q H wp w c0) xs).bind0 fun zs =>
    (av_chainTU sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _).bind0 fun out =>
      sh_finishAll _ Q H wq wp trees w fl c0 out.2 0 out.1

/-- The compiled prover `proveBU` never queries the auxiliary oracle: for every tag, protocol, wire
records, flags, list of slots and store. -/
theorem avoids_proveBU (fl : ℕ → Bool) (xs : List (Option Y)) (vs : List Bits) :
    (erase (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs).Avoids OracleName.other :=
  (av_proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs).avoids vs

end Prove

end Seed
end Compile.Batch
