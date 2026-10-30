-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadUP.lean: under `W.OKG`, if σ.o = other, the prover of `argP` (the scheme whose
proving key is (i, seed), Compile/Batch/StarS.lean) depends on its oracle answers only up to `agF W`
(words of this library: lean/GLOSSARY.md).

  `ends_slotLoU`, `ends_joinMU`, `ends_chainTU`  A slot that holds a request has a list of tokens
                                                 (`toks`) that is not empty, all along the chains,
                                                 if it is so at their start (of an empty slot
                                                 nothing is said: its list is empty).
  `lw_proveBU`, `lw_batOf`  One execution of the compiled prover with free empty slots, and one
                            batch on a given node, are a `LiveW` (Compile/LiveWalk.lean), under the
                            hypotheses of their statements.
  `OComp.FactorsBy.bindAll`  Sequential composition where what follows needs a fact on the values
                             that the first part can return (`All`, Compile/SeedFix.lean).
                             `OComp.FactorsBy.bind` asks its second part for all values.
  `facF_P_argP`  The title's statement, for every key (i, seed) and every batch:
                 `FactorsBy (agF W)`: after two failed attempts that are not the last it goes on in
                 the same way, whatever their other hash blocks and their tails are (a tail: the
                 part of an answer that the program gets as a new token: Rom/Defer.lean).

Why `bindAll`: the prover first makes the node of the sampled copy again, on an empty store, and
then runs the batch on that node and the store that it has left. For the batch all tokens below the
length of the store are taken as live; the tokens of the node's tree are among them for a node and a
store that `nodeP'` returns (`all_nodeP'`, Compile/Batch/SeedParNode.lean), not for an arbitrary
pair. The node has no Fiat-Shamir query, so there is nothing to show of it, though it returns its
store (`still_nodeP'`, Compile/Batch/DeadStill.lean). `W.OKG` is used for: there are 2^depthReq
slots, so there is one; the records of Batch's searches are well-formed (`fitsSh_agF`,
Compile/Batch/DeadFits.lean).

Limits: those in the header of Compile/Batch/DeadFrame.lean; those on `LiveW` in the header of
Compile/LiveWalk.lean (the larger T, the less is said).
Nothing on C or V, on the lazy prover, on pruning, on numbers of queries.
-/
import Compile.Batch.DeadU
import Compile.Batch.DeadO
import Compile.Batch.DeadFits
import Compile.Batch.DeadStill
import Compile.Batch.StarS
import Compile.Batch.SeedCache
import Compile.Batch.SeedParNode
import Rom.OverOneNDerive

noncomputable section

namespace Compile

theorem Ends.mono {S : Rom.OSpec} {sp : Rom.Split S} {α : Type} {G G' : α → Prop} :
    ∀ {c : Rom.Step S sp α}, Ends G c → (∀ a, G a → G' a) → Ends G' c
  | .pure a, h, hg => hg a h
  | .sample _ k, h, hg => fun r => Ends.mono (c := k r) (h r) hg
  | .plain _ _ k, h, hg => fun r => Ends.mono (c := k r) (h r) hg
  | .fresh _ k, h, hg => fun t => Ends.mono (c := k t) (h t) hg
  | .marked _ _ _ _ _ k, h, hg => fun v t => Ends.mono (c := k v t) (h v t) hg
  | .reveal _ k, h, hg => fun w => Ends.mono (c := k w) (h w) hg

end Compile

namespace Rom

/-- Sequential composition, where what follows needs a fact on the values that the first part can
return. -/
theorem OComp.FactorsBy.bindAll {S : OSpec} {α β : Type}
    {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} {Q : α → Prop}
    {c : OComp S α} {g : α → OComp S β} (h : c.FactorsBy ag)
    (hQ : Compile.Seed.All Q c) (hg : ∀ a, Q a → (g a).FactorsBy ag) : (c.bind g).FactorsBy ag := by
  induction c with
  | pure a => exact hg a hQ
  | sample n k ih => exact fun r => ih r (h r) (hQ r)
  | query o q k ih =>
    exact ⟨fun r r' hr => congrArg (fun c => c.bind g) (h.1 r r' hr), fun r => ih r (h.2 r) (hQ r)⟩

end Rom

namespace Compile.Batch.Dead
open Iop Rom Compile
open Compile.Batch.Need (chainTU_lo chainTU_join chainTU_shr chainTU_none)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop}

local notation "Lw" => LiveW (S := spec lam K L) (sp := split lam K L) ag
local notation "En" => Ends (S := spec lam K L) (sp := split lam K L)

/-- a slot that holds a request has a list of tokens (`toks`) that is not empty -/
def HasTok {Y : Type} (acc : SlotAcc lam K Y) : Prop := acc.x ≠ none → acc.toks ≠ []

/-! ## The fact on the lists `toks`, along the chains -/

section EndsU
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem ends_slotLoU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    En (fun z' => HasTok z'.2) (slotLoU sMT t cms xin a w emb plJ i ph z) := by
  unfold slotLoU
  cases hx : z.2.x with
  | none => exact fun h => absurd hx h
  | some y => exact (ends_slotLo sMT t cms xin a w emb plJ i ph z).mono fun _ h _ => h

theorem ends_joinMU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      En (fun o => ∀ z ∈ o.1, HasTok z.2) (joinMU sMT t a w emb plJ i zs)
  | [] => fun _ h => nomatch h
  | z :: zs => Ends.bind (G := fun z' => HasTok z'.2) (by
      unfold slotJoinU
      cases hx : z.2.x with
      | none => exact fun h => absurd hx h
      | some y =>
        obtain ⟨⟨m, k⟩, acc⟩ := z
        dsimp only [slotJoin]
        exact ends_withTree _ _ _ _ fun tr => fun _ c _ => by
          show acc.toks ++ [c] ≠ []
          simp) fun z' hz' => Ends.bind (ends_joinMU a w emb plJ i zs) fun o ho => fun y hy => by
      rcases List.mem_cons.1 hy with e | e
      · exact e ▸ hz'
      · exact ho y e

theorem hasTok_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (z : SlotSt lam K Y (r :: s)) (h : HasTok z.2) :
    HasTok (hear w bl noted z).2 := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  exact h

/-- The chains return slots with `HasTok`, if they are given such slots. -/
theorem ends_chainTU (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      (∀ z ∈ zs, HasTok z.2) →
      En (fun out => ∀ acc ∈ out.1, HasTok acc)
        (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, zs, a0, hz => fun acc ha => by
      obtain ⟨z, hzm, rfl⟩ := List.mem_map.1 ha
      exact hz z hzm
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, hz => by
      have hh : ∀ (l : List (SlotSt lam K Y (r :: s))) bl noted,
          (∀ z ∈ l, HasTok z.2) → ∀ z ∈ l.map (hear w bl noted), HasTok z.2 := by
        intro l bl noted h z hzm
        obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hzm
        exact hasTok_hear w bl noted z0 (h z0 hz0)
      by_cases hk : a.kind = .lo
      · rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        exact Ends.bind (ends_eachM (fun z => ends_slotLoU sMT t cms xin a w _ _ i ph z) zs)
          fun zs' h => ends_chainTU depthReq s A W _ _ (i + 1) _ _ zs' _ h.2
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          exact Ends.bind (ends_joinMU sMT t a w _ _ i zs) fun o ho =>
              Ends.bind (ends_true _) fun rq _ =>
                  ends_withTree _ _ _ _ fun tr0 => ends_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
            ends_chainTU depthReq s A W _ _ (i + 1) _ _ _ _ (hh o.1 bl true ho)
        | shr tk0 =>
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          exact ends_withTree _ _ _ _ fun tr0 =>
            ends_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
              ends_chainTU depthReq s A W _ _ (i + 1) _ _ _ _ (hh zs bl false hz)
        | first =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl)]
          exact ends_chainTU depthReq s A W _ _ (i + 1) _ _ _ _ (hh zs _ false hz)
        | aft =>
          rw [chainTU_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl)]
          exact ends_chainTU depthReq s A W _ _ (i + 1) _ _ _ _ (hh zs _ false hz)

end EndsU

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

theorem lw_initSlotU {T : Tok → Prop} (c0 : H.Coin0) (x : Option Y) :
    Lw T (fun z u => liveAccU z.2 u)
      (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) := by
  cases x with
  | none => exact .pure fun _ hu => absurd rfl hu.1
  | some x => exact (lw_initSlot sFS Q H wp w c0 (some x)).imp (fun _ h => h) fun _ _ h => h.2

theorem ends_initSlotU (c0 : H.Coin0) (x : Option Y) :
    En (fun z => HasTok z.2) (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) := by
  cases x with
  | none => exact fun h => absurd rfl h
  | some x => exact (ends_initSlot sFS Q H wp w c0 (some x)).mono fun _ h _ => h

/-- For every ag with `OnlyFb`, `FitsSh`, under hT: one execution of the compiled prover with free
empty slots is a `LiveW ag`; in particular, started on a store that holds all tokens taken as live,
after two answers that ag relates it never uses the new tail. hT: the live tokens of the given trees
are among the tokens T that are taken as live. It needs either a slot (empty or not) or a token in
T. -/
theorem lw_proveBU (hag : OnlyFb ag) {T : Tok → Prop}
    (hF : FitsSh ag t Q.loc.shape Q.ann wq.sh embP) (hT : ∀ tr ∈ trees, ∀ u, liveTH tr u → T u)
    (fl : ℕ → Bool) (xs : List (Option Y)) (h1 : xs ≠ [] ∨ ∃ u, T u) :
    Lw T (fun _ _ => False) (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) := by
  unfold proveBU
  refine (lw_drawT wp.coin0).bind fun c0 => ?_
  refine LiveW.bindG (G := fun zs => zs.length = xs.length ∧ ∀ z ∈ zs, HasTok z.2)
    (lw_eachM (T0 := fun _ => False) (lσ := fun _ _ => False)
      (lτ := fun z u => liveAccU z.2 u) (fun _ _ x _ => lw_initSlotU sFS Q H wp w c0 x) xs _
      (fun _ h => h.elim) fun _ _ _ h => h.elim)
    ?_ fun zs hzs => ?_
  · exact ends_eachM (fun x => ends_initSlotU sFS Q H wp w c0 x) xs
  · refine LiveW.bindG (G := fun out => ∀ acc ∈ out.1, HasTok acc)
      (lw_chainTU sMT t _ _ hag depthReq _ _ _ _ _ 0 _ _ zs _ _ hF ?_
        (fun z hz u hu => .inr ⟨z, hz, hu⟩) (fun u hu => ?_) fun _ hu => hu.elim)
      (ends_chainTU sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hzs.2) fun out ho => ?_
    · rcases h1 with h1 | ⟨u, hu⟩
      · exact .inl fun e => h1 (List.length_eq_zero_iff.1 (by rw [← hzs.1, e]; rfl))
      · exact .inr ⟨u, .inl (.inl hu)⟩
    · rcases hu with h | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · exact nomatch h
      · exact nomatch h
      · exact nomatch h
    · exact lw_finishAll Q H wq wp trees w fl c0 out.2 0 out.1 _
        (fun tr htr u hu => .inl (.inl (.inl (hT tr htr u hu)))) (fun u hu => .inr (.inr hu))
        (fun acc ha hx u hu => .inr (.inl ⟨acc, ha, hx, hu⟩)) fun acc ha hx => ho acc ha hx

end Prove

end Compile.Batch.Dead

/-! ## One batch on a node; the prover of the scheme whose proving key is (i, seed) -/

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- one batch on a given node, for any program in the place of the compiled prover that is a `LiveW`
(not all hypotheses are named here: see the statement below) -/
theorem lw_batOf {W : QueryLayout lam L} (WP : WireBP L)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop}
    {T : Tok → Prop} {pv : Seed.Run W}
    (hpv : ∀ tree w fl xs, (∀ u, liveTH tree u → T u) → xs.length = L.maxBatchSize →
      LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T
        (fun _ _ => False) (pv [tree] w fl xs))
    (i : I) (j : ℕ) (nd : Option (Node lam L)) (b : List (X × Unit))
    (hnd : ∀ x, nd = some x → ∀ u, liveTH x.tree u → T u) :
    LiveW (S := spec lam W.K L) (sp := split lam W.K L) ag T
      (fun _ _ => False) (Seed.batOf WP pv i j nd b) :=
  (lw_drawT WP.perm).bind fun σ => by
    cases nd with
    | none => exact .pure fun _ hu => hu.elim
    | some nd =>
      exact ((hpv nd.tree _ _ _ (hnd nd rfl) (by simp [slotsOfReq])).imp
          (fun _ h => .inl h) fun _ _ h => h).bind
        fun _ => .pure fun _ hu => hu.elim

/-- Under `W.OKG`, if σ.o = other: the prover of the scheme whose proving key is (i, seed) has
`FactorsBy (agF W)`. -/
theorem facF_P_argP (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hW : W.OKG) (hσ : σ.o = OracleName.other)
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) :
    ((argP W WP p bk σ).P k b).FactorsBy (agF W) := by
  have hN : 0 < L.maxBatchSize := by rw [hW.slots]; exact Nat.two_pow_pos _
  have hF : FitsSh (agF W) Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh id :=
    fitsSh_agF W Tag.onl _ _ W.B.sh id hW.B.sh fun _ => rfl
  rw [argP_P]
  intro j
  refine OComp.FactorsBy.bindAll
    (Q := fun o : Node lam L × List Bits => Compile.Seed.SaltsLt o.2.length o.1.tree.salts)
    ((((still_nodeP' W WP p (onlyFb_agF W) k.1).erase []).blocks bk).derive
      σ k.2 (no_seed W σ hσ) _).fac
    (Compile.Batch.Seed.all_derive
      σ k.2 ((Compile.Batch.Seed.all_nodeP' W WP p k.1 []).blocks bk) _) fun a ha => ?_
  have hb : LiveW (S := spec lam W.K L) (sp := split lam W.K L) (agF W) (fun u => u < a.2.length)
      (fun _ _ => False) (Seed.batOf WP (Seed.runBU W WP p) k.1 j.val (some a.1) b) :=
    lw_batOf WP (fun tree w fl xs hT hl =>
      lw_proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq
        [tree] w (onlyFb_agF W) hF
      (fun tr htr u hu => hT u ((List.mem_singleton.1 htr) ▸ hu)) fl xs (.inl fun e => by rw [e] at hl; exact absurd hl.symm (Nat.ne_of_gt hN))) k.1 j.val (some a.1) b fun x hx u hu => by
        obtain rfl : a.1 = x := Option.some.inj hx
        obtain ⟨y, hy, e⟩ := hu
        rcases e with e | e
        · exact e ▸ (ha y hy).1
        · exact e ▸ (ha y hy).2
  have e : ((eraseR (Seed.batOf WP (Seed.runBU W WP p) k.1 j.val (some a.1) b) a.2).bind
        fun o => (OComp.pure o.1 : TypedOracleComputation lam W.K L _)) =
      realQ ((erase (Seed.batOf WP (Seed.runBU W WP p) k.1 j.val (some a.1) b) a.2).bind
          fun o => OComp.pure o.1) := by
    rw [realQ_bind]
    rfl
  rw [e]
  exact facF_realQ W _ (hb.erase a.2 (fun _ h => h) (fun x => OComp.pure x) fun _ => trivial)

end Compile.Batch.Dead
