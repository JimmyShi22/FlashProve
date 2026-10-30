-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/GhostRoutedU.lean: for every well-formed wire record (`W.OKG`), the program `PpU` of
the prover with no query for an empty slot is routed. Statement and proof (words of this library:
lean/GLOSSARY.md). (`proveBU`: Compile/Batch/ProverU.lean; `PpU`: Compile/Batch/StarU.lean; routed:
`RoutedT`, Compile/Batch/SpecGhost.lean.)
Routed means, as for `Cp` and `Pp` (Compile/Batch/GhostRouted.lean): it queries `fb t` only where
the plain part in the query holds the nonce for 0, or the component that the query holds has no
proof-of-work record; and it queries the ghost name `fbw t k` only where the plain part holds the
nonce for k + 1.
    `Spec.routedPpU`, `routedPpU`
                        statement and proof, by induction on the program; an empty slot queries
                        nothing
    `realQ_via_PpU`     so for the erased program (`erase`, Compile/Star.lean) `realQ`
                        (Compile/Batch/Oracles.lean: queries to `fbw` become queries to `fb`) is
                        translation by `ghost W`
    `PU_via_law`        the same for the prover of the scheme, given only that the proof-of-work
                        records are well-formed (`Ghost.GrLawB`)

Notation: `fb t` (`OracleName`, Compile/Batch/Oracles.lean): Fiat-Shamir for the protocol t; `fbw t k`: an
oracle of the analysis, never queried by the scheme: proof-of-work attempt k + 1 is written as a
query to `fbw t k`, and `realQ` maps it back to `fb t`; `Rt`: `RoutedT W`
(Compile/Batch/SpecGhost.lean): `Routed` for a token program: whatever strings its tokens denote; a
theorem whose name begins with rt_ states, under its hypotheses, `Rt` of the program named behind
it; names that end in U: the forms with no query for an empty slot (`proveBU`,
Compile/Batch/ProverU.lean); `GrLaw`, `ClsAt` (Compile/Batch/GhostRouted.lean): the proof-of-work
records are well-formed (`GrW.OK`), round by round; the invariant of the induction over the rounds;
`sMT`, `sFS`: natural numbers, fields of `Params` (Compile/Star.lean); `depthReq` (`QueryLayout`,
Iop/BatchWire.lean): depth of a request tree; plain part, nonce, ghost name: lean/GLOSSARY.md.

Limits: beyond `PU_via_law`, nothing is said on the scheme that runs this program: whether its P is
the erased program or `realQ` of it is a matter of its definition (Compile/Batch/StarU.lean). The
forms of the scheme with a seed are not treated here.

On the pattern of Compile/Batch/GhostRouted.lean.
-/
import Compile.Batch.GhostRouted
import Compile.Batch.GhostGuards
import Compile.Batch.StarU

noncomputable section

namespace Compile.Batch
open Iop Rom Compile.GlueB

def Spec.routedPpU : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : IskH lam L) (fr : ℕ → Bool) (xs : List X),
    W.OKG → RoutedT W (PpU W WP p k fr xs)


variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

namespace Ghost

variable (W : QueryLayout lam L)

local notation "Rt" => RoutedT W

/-! ## Empty slots -/

theorem rt_rleavesTU : ∀ l : List (Option Tok), Rt (rleavesTU (lam := lam) (K := W.K) (L := L) l)
  | [] => trivial
  | some c :: t => (rt_rleafT W c).bind fun _ => (rt_rleavesTU t).bind fun _ => trivial
  | none :: t => fun _ => (rt_rleavesTU t).bind fun _ => trivial

theorem rt_reqTU (d : ℕ) (cs : List (Option Tok)) :
    Rt (reqTU (lam := lam) (K := W.K) (L := L) d cs) :=
  (rt_rleavesTU W cs).bind fun ls => (rt_levelsM W (rt_rnodeT W) d ls).bind fun _ => trivial

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem rt_slotLoU {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam W.K r a}
    {Ws : RoundsQueryLayout lam W.K s A} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)}
    (hE : ClsAt W t (s := r :: s) (A := (a, A)) (w, Ws) embP) (hw : ∀ g, w.grJ = some g → g.OK)
    (emb : (p : r.Pos) → r.Sym p → Body L) (i : ℕ) (ph : PhT) (z : SlotSt lam W.K Y (r :: s)) :
    Rt (slotLoU sMT t cms xin a w emb (fun α => embP (.inl (.inr α))) i ph z) := by
  unfold slotLoU
  cases z.2.x with
  | none => trivial
  | some _ => exact rt_slotLo W sMT t cms xin hE hw emb i ph z

theorem rt_slotJoinU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam W.K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (z : SlotSt lam W.K Y (r :: s)) :
    Rt (slotJoinU sMT t a w emb plJ i z) := by
  unfold slotJoinU
  cases z.2.x with
  | none => trivial
  | some _ => exact rt_slotJoin W sMT t a w emb plJ i z

theorem rt_joinMU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam W.K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam W.K Y (r :: s)), Rt (joinMU sMT t a w emb plJ i zs)
  | [] => trivial
  | z :: zs =>
    (rt_slotJoinU W sMT t a w emb plJ i z).bind fun _ =>
      (rt_joinMU a w emb plJ i zs).bind fun _ => trivial

theorem rt_chainTU (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam W.K Y s)) (a0 : Acc0),
      GrLaw s A Ws → ClsAt W t Ws embP →
      Rt (chainTU sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, hW, hE => by
      simp only [chainTU]
      split
      · exact (rt_eachM W (rt_slotLoU W sMT t cms xin hE hW.1.2 _ i _) zs).bind
          fun zs' => rt_chainTU depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)
      · exact (rt_joinMU W sMT t a w _ _ i zs).bind fun o =>
            (rt_reqTU W depthReq o.2).bind fun rq => rt_tree0 W sMT a w _ m0 fun tr0 =>
          rt_fbG W t i _ _ _ _ _ w.chal (fun α => embP (.inl (.inl α))) _ w.gr0
              (fun h => cls0_none hE h _)
              (fun g h m hm => cls0_put hE hW.1.1 g h _ m hm) fun _ _ _ _ =>
            rt_chainTU depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)
      · exact rt_tree0 W sMT a w _ m0 fun tr0 =>
          rt_fbG W t i _ _ _ _ _ w.chal (fun α => embP (.inl (.inl α))) _ w.gr0
              (fun h => cls0_none hE h _)
              (fun g h m hm => cls0_put hE hW.1.1 g h _ m hm) fun _ _ _ _ =>
            rt_chainTU depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)
      · exact rt_chainTU depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)

variable (stp : Y → List (Blk lam W.K) → Bool)


end Rounds

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam W.K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt) (stp : Y → List (Blk lam W.K) → Bool)

theorem rt_initSlotU (c0 : H.Coin0) : ∀ x : Option Y, Rt (initSlotU (L := L) sFS Q H wp w c0 x)
  | some x => rt_initSlot W sFS Q H wp w c0 (some x)
  | none => trivial

theorem rt_proveBU (hW : GrLaw Q.loc.shape Q.ann wq.sh) (hE : ClsAt W t wq.sh embP)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    Rt (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) :=
  (rt_drawT W wp.coin0).bind fun c0 =>
      (rt_eachM W (rt_initSlotU W sFS Q H wp w c0) xs).bind fun zs =>
    (rt_chainTU W sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hW hE).bind fun out =>
      rt_finishAll W Q H wq wp trees w fl c0 out.2 0 out.1


end Prove

/-! ## The provers -/

variable (WP : WireBP L) (p : Params) (stp : X → List (Blk lam W.K) → Bool) (hW : GrLawB W)
include hW

theorem rt_PpJU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    Rt (PpJU W WP p k fr xs j σ) := by
  unfold PpJU
  cases k.leaves[j]? with
  | none => trivial
  | some lf =>
    exact (rt_proveBU W _ _ Tag.onl _ _ W.B _ _ id _ _ _ _ hW.B (fun _ => rfl) _ _).bind
      fun _ => trivial

theorem rt_PpU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : Rt (PpU W WP p k fr xs) := fun j =>
  (rt_drawT W WP.perm).bind fun σ => rt_PpJU W WP p hW k fr xs j.val σ



end Ghost

/-- The program `PpU` is routed, for `W.OKG`. -/
theorem routedPpU : Spec.routedPpU := fun _ _ _ _ W WP p k fr xs hW =>
  Ghost.rt_PpU W WP p (.of_okg hW) k fr xs

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (stp : X → List (Blk lam W.K) → Bool)

/-- For `W.OKG`: on the erased program, `realQ` is translation by `ghost W`. -/
theorem realQ_via_PpU (hW : W.OKG) (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (vs : List Bits) :
    realQ (erase (PpU W WP p k fr xs) vs) = (erase (PpU W WP p k fr xs) vs).via (ghost W) :=
  realQ_via I X lam L W _ _ (routedErase I X lam L W _ _ vs (routedPpU I X lam L W WP p k fr xs hW))

/-- The prover `PU` is `PtokU` (the erased program) translated by `ghost W`, if the proof-of-work
records are well-formed (`Ghost.GrLawB`: a well-formed wire record, or one without any such
record). -/
theorem PU_via_law {W : QueryLayout lam L} (WP : WireBP L) (p : Params) (hW : Ghost.GrLawB W)
    (k : ISK lam L) (b : List (X × Unit)) :
    PU W WP p k b = (PtokU W WP p k b).via (ghost W) :=
  realQ_via I X lam L W _ _
    (Routed.bind
      (routedErase I X lam L W _ _ k.2
        (Ghost.rt_PpU W WP p hW k.1 (fun _ => true) (b.map Prod.fst)))
      fun _ => trivial)

end Compile.Batch
