-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedBlocksU.lean: which blocks of an answer the prover with no query for an empty
  slot may read. A companion to Compile/Batch/NeedBlocks.lean (words of this library:
  lean/GLOSSARY.md).

  The prover is `PU` (Compile/Batch/ProverU.lean, Compile/Batch/StarU.lean); the leaf of the request
  tree that belongs to an empty slot is a fresh uniform string. Table, hypothesis and relation on
  states are those of Compile/Batch/NeedTable.lean and Compile/Batch/NeedBlocks.lean (`need`,
  `QueryLayout.NB`, `SlotRel`). An empty slot still receives the shared challenges (its stored blocks grow
  in the shared rounds only), so the number of its stored blocks is not the number of rounds that
  have passed; the relation on states asks nothing of the stored blocks of an empty slot, which are
  never read.
    `alike_chainTU`, `sfr_chainTU`   all chains of a batch
    `sf_proveBU`, `sf_PpU`, `facBy_PU`
                                     one execution, for any slots and flags; the prover's program;
                                     the prover
  The proofs for the chain are those of Compile/Batch/NeedBlocks.lean, word for word, as `chainTU`
  is the text of `chainT`, with `slotLoU`, `joinMU`, `reqTU`.
  Notation:
    `nb`: a map `Tag → ℕ → ℕ`; `QueryLayout.NB W nb` (Compile/Batch/NeedTable.lean): in round i of
      protocol t the challenge is a function of the blocks below nb t i;
    `sMT`, `sFS`: natural numbers; sMT is the length of the salt of a leaf, sFS that of the salt
      of a chain (Compile/Batch/Verifier.lean);
    `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the
      trees over the external strings;
    `ph`: a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`, `shr tk0` or `aft`;
    `σ0`: an `SStrat s A` (Iop/Batch.lean): a strategy for the shared part: m_0 in every round;
    `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
    `fl`: a map ℕ → Bool; it says for which slots a proof string is made at all (`finishAll`,
      Compile/Batch/Prover.lean);
    `fr`: a map ℕ → Bool; for which requests a proof string is made at all (the head of
      Compile/Batch/Star.lean).
  Limits: as in Compile/Batch/NeedBlocks.lean.
-/
import Compile.Batch.NeedBlocks
import Compile.Batch.StarU

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.Need (SFac SFacR Alike)

section Rounds
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

local notation "Fc" => SFac (S := spec lam K L) (sp := split lam K L) (agree nb)
local notation "FR" => SFacR (S := spec lam K L) (sp := split lam K L) (agree nb)

theorem sf_rleavesTU : ∀ l : List (Option Tok), Fc (rleavesTU (lam := lam) (K := K) (L := L) l)
  | [] => .pure _
  | some c :: t => (sf_rleafT nb c).bind fun _ => (sf_rleavesTU t).bind fun _ => .pure _
  | none :: t => .fresh _ fun _ => (sf_rleavesTU t).bind fun _ => .pure _

theorem sf_reqTU (depthReq : ℕ) (cs : List (Option Tok)) :
    Fc (reqTU (lam := lam) (K := K) (L := L) depthReq cs) :=
  (sf_rleavesTU nb cs).bind fun ls =>
    (sf_levelsM nb (sf_rnodeT nb) depthReq ls).bind fun _ => .pure _

theorem SlotRel.x {nbf : ℕ → ℕ} {i : ℕ} {s : Shape}
    {z z' : SlotSt lam K Y s} (h : SlotRel nbf i z z') : z'.2.x = z.2.x := by
  obtain ⟨bls', rfl, _⟩ := h
  rfl

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem slotLoU_some (ph : PhT) {z : SlotSt lam K Y (r :: s)} {y : Y} (h : z.2.x = some y) :
    slotLoU sMT t cms xin a w emb plJ i ph z = slotLo sMT t cms xin a w emb plJ i ph z := by
  unfold slotLoU
  rw [h]

theorem slotLoU_none (ph : PhT) {z : SlotSt lam K Y (r :: s)} (h : z.2.x = none) :
    slotLoU sMT t cms xin a w emb plJ i ph z = Step.pure (z.1.2 (w.chal (blk0 lam K)), z.2) := by
  unfold slotLoU
  rw [h]

theorem slotJoinU_some {z : SlotSt lam K Y (r :: s)} {y : Y} (h : z.2.x = some y) :
    slotJoinU sMT t a w emb plJ i z = slotJoin sMT t a w emb plJ i z := by
  unfold slotJoinU
  rw [h]

theorem slotJoinU_none {z : SlotSt lam K Y (r :: s)} (h : z.2.x = none) :
    slotJoinU sMT t a w emb plJ i z = Step.pure z := by
  unfold slotJoinU
  rw [h]

theorem alike_slotLoU (ph : PhT) {z z' : SlotSt lam K Y (r :: s)} (h : SlotRel (nb t) i z z') :
    Alike (SlotRel (nb t) (i + 1)) (slotLoU sMT t cms xin a w emb plJ i ph z)
      (slotLoU sMT t cms xin a w emb plJ i ph z') := by
  cases hx : z.2.x with
  | some y =>
    rw [slotLoU_some sMT t cms xin a w emb plJ i ph hx,
      slotLoU_some sMT t cms xin a w emb plJ i ph (h.x.trans hx)]
    exact alike_slotLo nb sMT t cms xin a w emb plJ i ph h
  | none =>
    rw [slotLoU_none sMT t cms xin a w emb plJ i ph hx,
      slotLoU_none sMT t cms xin a w emb plJ i ph (h.x.trans hx)]
    obtain ⟨bls', rfl, _⟩ := h
    exact .pure ⟨bls', rfl, .inl hx⟩

theorem sfr_slotLoU (hw : w.ReadsBelow (nb t i)) (ph : PhT) {z : SlotSt lam K Y (r :: s)}
    (h : z.2.x = none ∨ z.2.blocks.length = i) :
    FR (SlotRel (nb t) (i + 1)) (slotLoU sMT t cms xin a w emb plJ i ph z) := by
  cases hx : z.2.x with
  | some y =>
    rw [slotLoU_some sMT t cms xin a w emb plJ i ph hx]
    exact sfr_slotLo nb sMT t cms xin a w emb plJ i hw ph h
  | none =>
    rw [slotLoU_none sMT t cms xin a w emb plJ i ph hx]
    exact .pure (SlotRel.self (.inl hx))

theorem alike_slotJoinU {z z' : SlotSt lam K Y (r :: s)} (h : SlotRel (nb t) i z z') :
    Alike (SlotRel (nb t) i) (slotJoinU sMT t a w emb plJ i z)
      (slotJoinU sMT t a w emb plJ i z') := by
  cases hx : z.2.x with
  | some y =>
    rw [slotJoinU_some sMT t a w emb plJ i hx, slotJoinU_some sMT t a w emb plJ i (h.x.trans hx)]
    exact alike_slotJoin nb sMT t a w emb plJ i h
  | none =>
    rw [slotJoinU_none sMT t a w emb plJ i hx, slotJoinU_none sMT t a w emb plJ i (h.x.trans hx)]
    exact .pure h

theorem sfr_slotJoinU {z : SlotSt lam K Y (r :: s)} (h : z.2.x = none ∨ z.2.blocks.length = i) :
    FR (SlotRel (nb t) i) (slotJoinU sMT t a w emb plJ i z) := by
  cases hx : z.2.x with
  | some y =>
    rw [slotJoinU_some sMT t a w emb plJ i hx]
    exact sfr_slotJoin nb sMT t a w emb plJ i h
  | none =>
    rw [slotJoinU_none sMT t a w emb plJ i hx]
    exact .pure (SlotRel.self h)

/-- what the joining round returns: the slots, and for each its slot value or none -/
def JRelU (nbf : ℕ → ℕ) (i : ℕ) (o o' : List (SlotSt lam K Y (r :: s)) × List (Option Tok)) :
    Prop :=
  List.Forall₂ (SlotRel nbf i) o.1 o'.1 ∧ o.2 = o'.2

theorem SlotRel.xc {nbf : ℕ → ℕ} {z z' : SlotSt lam K Y (r :: s)} (h : SlotRel nbf i z z') :
    (z.2.x.map fun _ => z.2.c) = (z'.2.x.map fun _ => z'.2.c) := by
  obtain ⟨bls', rfl, _⟩ := h
  rfl

theorem alike_joinMU :
    ∀ {zs zs' : List (SlotSt lam K Y (r :: s))}, List.Forall₂ (SlotRel (nb t) i) zs zs' →
      Alike (JRelU (nb t) i) (joinMU sMT t a w emb plJ i zs) (joinMU sMT t a w emb plJ i zs')
  | _, _, .nil => .pure ⟨.nil, rfl⟩
  | _, _, .cons h1 h2 =>
    (alike_slotJoinU nb sMT t a w emb plJ i h1).bind fun _ _ hz =>
      (alike_joinMU h2).bind fun _ _ ho =>
        .pure ⟨.cons hz ho.1, congrArg₂ List.cons (SlotRel.xc i hz) ho.2⟩

theorem sfr_joinMU :
    ∀ {zs : List (SlotSt lam K Y (r :: s))},
      List.Forall₂ (SlotRel (nb t) i) zs zs → FR (JRelU (nb t) i) (joinMU sMT t a w emb plJ i zs)
  | _, .nil => .pure ⟨.nil, rfl⟩
  | _, .cons h1 h2 =>
    (sfr_slotJoinU nb sMT t a w emb plJ i h1.lawful).bind
      (fun _ _ hz =>
        (alike_joinMU nb sMT t a w emb plJ i h2).bind fun _ _ ho =>
          .pure ⟨.cons hz ho.1, congrArg₂ List.cons (SlotRel.xc i hz) ho.2⟩) fun _ hz =>
            (sfr_joinMU h2).bind
              (fun _ _ ho => .pure ⟨.cons hz ho.1, congrArg₂ List.cons (SlotRel.xc i hz) ho.2⟩)
              fun _ ho => .pure ⟨.cons hz ho.1, rfl⟩

end One

/-! the four kinds of rounds of chainTU, written out -/

section Unfold
variable (depthReq : ℕ) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L) (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
  (m0 : a.M0) (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0)

theorem chainTU_lo (hk : a.kind = .lo) (ph : PhT) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      (eachM
        (slotLoU sMT t cms xin a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        zs).bind fun zs' =>
          chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl

theorem chainTU_join (hk : a.kind = .sh) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0 =
      (joinMU sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqTU depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

theorem chainTU_shr (hk : a.kind = .sh) (tk0 : Tok) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) zs a0
      = tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

/-- a shared round at the start or after the later local rounds: nothing is hashed -/
theorem chainTU_none (hk : a.kind = .sh) (ph : PhT) (hph : ph = .first ∨ ph = .aft) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
        ph (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
        { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl <;> rfl

end Unfold

variable (depthReq : ℕ)

/-- Under `ReadsFrom`: all chains of a batch, from states that are alike (`SlotRel`), are alike
(`OutRel`). -/
theorem alike_chainTU :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs zs' : List (SlotSt lam K Y s)) (a0 : Acc0),
      RoundsQueryLayout.ReadsFrom (nb t) s A W i → List.Forall₂ (SlotRel (nb t) i) zs zs' →
      Alike (OutRel (nb t)) (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
        (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs' a0)
  | [], _, _, _, _, _, _, _, _, _, _, _, hz => .pure ⟨forall₂_map (fun _ _ h => h.acc) hz, rfl⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, zs', a0, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph,
          chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk ph]
        exact (alike_eachM (fun _ _ h => alike_slotLoU nb sMT t cms xin a w _ _ i ph h) hz).bind
          fun zs1 zs1' h1 => alike_chainTU s A W _ _ (i + 1) _ _ zs1 zs1' _ H.2 h1
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk',
            chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk']
          refine (alike_joinMU nb sMT t a w _ _ i hz).bind fun o o' ho => ?_
          obtain ⟨o1, o2⟩ := o
          obtain ⟨o1', o2'⟩ := o'
          obtain ⟨h1, h2⟩ := ho
          obtain rfl : o2 = o2' := h2
          exact Alike.bindSame _ fun rq =>
              alike_withTree _ _ _ _ fun tr0 => alike_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
            alike_chainTU s A W _ _ (i + 1) _ _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) true h) h1)
        | shr tk0 =>
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0,
            chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk' tk0]
          exact alike_withTree _ _ _ _ fun tr0 => alike_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
            alike_chainTU s A W _ _ (i + 1) _ _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
        | first =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl),
            chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk' _ (.inl rfl)]
          exact alike_chainTU s A W _ _ (i + 1) _ _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
        | aft =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl),
            chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk' _ (.inr rfl)]
          exact alike_chainTU s A W _ _ (i + 1) _ _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)

/-- Under `ReadsFrom`, from slots' states that are each related to themselves (`SlotRel`): all
chains of a batch go on in the same way, up to the stored blocks, after two answers that agree on
what is needed. -/
theorem sfr_chainTU :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      RoundsQueryLayout.ReadsFrom (nb t) s A W i → List.Forall₂ (SlotRel (nb t) i) zs zs →
      FR (OutRel (nb t)) (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, _, _, _, hz => .pure ⟨forall₂_map (fun _ _ h => h.acc) hz, rfl⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        exact (sfr_eachM nb (fun _ _ h => alike_slotLoU nb sMT t cms xin a w _ _ i ph h)
            (fun _ h => sfr_slotLoU nb sMT t cms xin a w _ _ i H.1 ph h.lawful) hz).bind
          (fun zs1 zs1' h1 =>
            alike_chainTU nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ zs1 zs1' _ H.2 h1)
          fun zs1 h1 => sfr_chainTU s A W _ _ (i + 1) _ _ zs1 _ H.2 h1
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine (sfr_joinMU nb sMT t a w _ _ i hz).bind (fun o o' ho => ?_) fun o ho => ?_
          · obtain ⟨o1, o2⟩ := o
            obtain ⟨o1', o2'⟩ := o'
            obtain ⟨h1, h2⟩ := ho
            obtain rfl : o2 = o2' := h2
            exact Alike.bindSame _ fun rq =>
                alike_withTree _ _ _ _ fun tr0 => alike_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
              alike_chainTU nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2
                (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) true h) h1)
          · refine SFacR.bindFac (sf_reqTU nb _ _) fun rq =>
                sfr_withTree nb _ _ _ _ fun tr0 =>
                    sfr_fbG nb _ _ _ _ _ _ _ _ _ _ H.1 _
                        (fun nc dd bl bl' e tl => ?_) fun nc dd bl tl =>
              sfr_chainTU s A W _ _ (i + 1) _ _ _ _ H.2
                (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) true h) ho.1)
            rw [H.1 bl bl' e]
            exact alike_chainTU nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 e true h) ho.1)
        | shr tk0 =>
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine sfr_withTree nb _ _ _ _ fun tr0 =>
              sfr_fbG nb _ _ _ _ _ _ _ _ _ _ H.1 _ (fun nc dd bl bl' e tl => ?_) fun nc dd bl tl =>
            sfr_chainTU s A W _ _ (i + 1) _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
          rw [H.1 bl bl' e]
          exact alike_chainTU nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 e false h) hz)
        | first =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl)]
          exact sfr_chainTU s A W _ _ (i + 1) _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
        | aft =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl)]
          exact sfr_chainTU s A W _ _ (i + 1) _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)

end Rounds

section Prove
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

local notation "Fc" => SFac (S := spec lam K L) (sp := split lam K L) (agree nb)
local notation "FR" => SFacR (S := spec lam K L) (sp := split lam K L) (agree nb)

variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

theorem sfr_initSlotU (c0 : H.Coin0) :
    ∀ x : Option Y,
      FR (SlotRel (nb t) 0) (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x)
  | some x => sfr_initSlot nb sFS t Q H wp w c0 (some x)
  | none => .pure (SlotRel.self (.inl rfl))

/-- Under `ReadsFrom`: one execution of the compiled prover `proveBU` goes on in the same way after
two answers that agree on what is needed. -/
theorem sf_proveBU (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    Fc (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) := by
  unfold proveBU
  refine (sf_drawT nb wp.coin0).bind fun c0 => SFacR.toFac ?_
  refine (sfr_eachM nb (Q := Eq) (fun a _ h => h ▸ (sfr_initSlotU nb sFS t Q H wp w c0 a).self)
      (fun a _ => sfr_initSlotU nb sFS t Q H wp w c0 a) (forall₂_eq_self xs)).bind
    (fun zs zs' hz => ?_) fun zs hz => ?_
  · exact (alike_chainTU nb sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs zs' _ hW hz).bind
        fun out out' ho => by
      obtain ⟨o1, o2⟩ := out
      obtain ⟨o1', o2'⟩ := out'
      obtain ⟨h1, h2⟩ := ho
      obtain rfl : o2 = o2' := h2
      exact Alike.of_eq (finishAll_congr nb t Q H wq wp trees w hW fl c0 o2 0 h1)
  · exact (sfr_chainTU nb sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hW hz).bind (fun out out' ho => by
      obtain ⟨o1, o2⟩ := out
      obtain ⟨o1', o2'⟩ := out'
      obtain ⟨h1, h2⟩ := ho
      obtain rfl : o2 = o2' := h2
      exact Alike.of_eq (finishAll_congr nb t Q H wq wp trees w hW fl c0 o2 0 h1)) fun out _ => (sf_finishAll nb Q H wq wp trees w fl c0 out.2 0 out.1).toR

end Prove

section Star
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) {nb : Tag → ℕ → ℕ} (hW : W.NB nb)

local notation "Fc" => SFac (S := spec lam W.K L) (sp := split lam W.K L) (agree nb)
local notation "Fo" => OComp.FactorsBy (S := spec lam W.K L) (agree nb)

include hW

theorem sf_PpJU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    Fc (PpJU W WP p k fr xs j σ) := by
  unfold PpJU
  cases k.leaves[j]? with
  | none => exact .pure _
  | some lf => exact (sf_proveBU nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.B _ _).bind fun _ => .pure _

theorem sf_PpU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : Fc (PpU W WP p k fr xs) :=
  .sample _ fun j => (sf_drawT nb WP.perm).bind fun σ => sf_PpJU W WP p hW k fr xs j.val σ

/-- Under `W.NB nb`: the prover `PU` goes on in the same way after two answers that agree on what is
needed. -/
theorem facBy_PU (k : ISK lam L) (b : List (X × Unit)) : Fo (PU W WP p k b) :=
  facBy_realQ W _ (OComp.FactorsBy.bind ((sf_PpU W WP p hW k.1 _ _).erase k.2) fun _ => trivial)

end Star

end Need
end Compile.Batch
