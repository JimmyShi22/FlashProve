-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadL.lean: under `W.OKG`, if σ.o = `OracleName.other` (σ reads the spare oracle), the
committer and the prover of the scheme with the lazy prover, the cache and pruned Merkle paths
(`prunedK W p (Seed.argPL ..)`) depend on their oracle answers only up to `agF W`: the proof of
`Spec.facF_PL` (Compile/Batch/SpecOneCall.lean; words of this library: lean/GLOSSARY.md).

That is: after two answers that are both failed proof-of-work attempts, and not the last, they go on
as the same program, whatever the other hash blocks and the tails of the two answers are (a tail:
the part of an answer that the program gets as a new token: Rom/Defer.lean). The same for
`prunedK W p (argP ..)` is not in this library.

Why the proof is not that for the prover of `argP` (Compile/Batch/DeadUP.lean): the lazy prover is
cut in two after the erasure of the token language: the erased chains return their store (the list
of the tokens' strings), the tails of failed attempts in it, and the second half (`Seed.finishAllL`,
a plain oracle algorithm) goes on with that store. So the last step is not "the store is forgotten"
(`LiveW.erase`, Compile/LiveWalk.lean) but `LiveW.eraseStG` (Compile/StillWalk.lean): what follows
is the same algorithm on two stores that differ at a dead place (dead: no live token;
Compile/LiveWalk.lean). That is Part 3.

  Part 1  pieces that query no Fiat-Shamir oracle: `still_openT` .. `still_opensB` (the tree over an
          encoded index: Compile/Batch/DeadStill.lean: `still_drawT` .. `still_commitE`);
          `sto_nodeV`, `sto_pairUpV`, `sto_levelsV`
  Part 2  `lw_finishSlotG`: the proof string of a slot, the external openings given: its one reveal
          (in this sense: the `Step.reveal` in the body of `finishSlotG`; `openT` is a further one)
          names the tails of the failed tries too and nothing of their strings is used (it asks that
          the slot has a token of its own, `acc.toks ≠ []`) (not all hypotheses are named here: see
          its statement).
  Part 3  `alike_finishSlotL`, `alike_finishAllL`: on two stores that agree but at d, where d is not
          0, is in the store and is no live token of the slots with a request or of the shared part,
          and every slot with a request has a token of its own (`acc.toks ≠ []`): the same tree, the
          same strings, stores that agree but at d.
  Part 4  `lw_chainsU`, `ends_chainsU`.
  Part 5  `sto_rD` .. `sto_cacheFrom`: `StillBy` (Compile/StillWalk.lean); σ.o = other enters here
          (`no_seed`, Compile/Batch/DeadStill.lean).

Notation:
  `bk`: a `CoinPlan` (Rom/Blocks.lean): how a uniform sample is made from small ones;
  `ℓ`: a natural number; the cache holds the digests of one level ℓ (the head of
    Compile/Batch/SeedLazyDefs.lean);
  `no j b`: a `ZKCP.Gen.Slots (PrfK lam L) b`; the value that is returned for a batch that ends
    without a proof (the head of Compile/Batch/SeedLazyDefs.lean);
  `st`, `hi`, `r` in `facF_PLrun` (as in `PLrun`, Compile/Batch/SeedLazyDefs.lean): a
    `Dig lam × List (Dig lam)`, the stored pair (root, level) of copy j; a `List (List (Dig lam))`,
    the levels above the stored level; an `L.EncodingRandomness`, the randomness of the copy's encoding (in Part 3
    `st`, `st'` are the two stores);
  `c0`: an `H.Coin0`: the randomness of the shared part (`BatchHonestProver`, Iop/Batch.lean);
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
  `fl`: a map ℕ → Bool; it says for which slots a proof string is made at all (`finishAll`,
    Compile/Batch/Prover.lean);
  `opL q`: an `TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))`; in `opensExtL`
    (Compile/Batch/SeedLazyDefs.lean): the salt and the path of leaf q, or none.

Limits: this file says nothing on V, and nothing on counts. It says nothing on the exit itself, the
step to one hash function (Compile/Batch/SpecOneCall.lean): that C and P may be run under the rule
"block 0 first" (`ruleT` there, `needT` in Compile/Batch/CutFit.lean: at a query to `fb t` with
proof-of-work bits block 0 first; the rest only if it passes or the attempt is the last) is not
drawn here. For the step that splits a Fiat-Shamir answer after its first hash block (the cut behind
block 0, Rom/SpecCut.lean) it is drawn from `facF_PL` in Compile/Batch/CutFit.lean (`needOKCut_of`,
`needOKCut_PL`; under `Test0 W`). The statement for the step with an adaptive rule (the exit with a
reading rule, Rom/SpecOverOneA.lean), from `facF_PL` and `FacOK (agree nb)` (Rom/OverOneNGen.lean,
Compile/Batch/NeedTable.lean; the old walk), is not in this library. For the schemes whose proving
key isk holds the store (`argB` .. `argBKE`) the claim is not made; by the argument in the header of
Compile/Batch/SpecOneCall.lean (no Lean fact) it fails. On `LiveW` (Parts 2 and 4): the limits in
the header of Compile/LiveWalk.lean (the larger the set T of the tokens taken as live, the less is
said).

The still pieces after Compile/Batch/RealQTree.lean, SeedLazyFin.lean and SeedGhost.lean (the walk
for ghost names); `lw_finishSlotG` after Compile/Batch/DeadProver.lean: `lw_finishSlot`;
`lw_chainsU` after Compile/Batch/DeadUP.lean: `lw_proveBU`.
-/
import Compile.StillWalk
import Compile.Batch.DeadStill
import Compile.Batch.DeadProver
import Compile.Batch.DeadO
import Compile.Batch.DeadUP
import Compile.Batch.DeadCBox
import Compile.Batch.SeedGhost

set_option autoImplicit false

namespace Compile.Batch.Dead
open Iop Rom Compile Compile.Batch.Seed

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop}

local notation "Lw" => LiveW (S := spec lam K L) (sp := split lam K L) ag
local notation "Stl" => Still (S := spec lam K L) (sp := split lam K L) ag
local notation "Sto" => OComp.StillBy (S := spec lam K L) ag

/-! ## Part 1. Pieces that query no Fiat-Shamir oracle -/

theorem still_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    Stl (openT (lam := lam) (K := K) (L := L) t j a) := fun _ => trivial

theorem still_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, Stl (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => trivial
  | j :: js => (still_opensComp dec posAt o tr isRead f js).bind fun f' => by
      show Stl (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => exact trivial
      | some p =>
        show Stl (if isRead p then _ else _)
        split_ifs
        · exact (still_openT tr j _).bind fun _ => trivial
        · exact trivial

theorem still_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Stl (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => exact trivial
  | some tr => exact still_opensComp dec posAt o tr isRead f _

/-- Opening the positions read in the trees of one component, from tree number k on, is still
(`Still`, Compile/StillWalk.lean): it makes no query at which ag relates two answers. The depths and
the trees are two lists of any lengths: where either list ends, nothing more is opened. -/
theorem still_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      Stl (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    (still_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      still_opensComp dec (posAt k) o tr isRead f' _

theorem still_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      Stl (opensB (L := L) s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, _, τ), tjs, t0s, _ =>
      (still_opensOpt _ _ _ _ _ _ _).bind fun _ =>
        (still_opensOpt _ _ _ _ _ _ _).bind fun _ =>
          (still_opensB s A W τ tjs.tail t0s.tail _).bind fun _ => trivial

theorem sto_nodeV (hag : OnlyFb ag) (a b : Dig lam) : Sto (hashTreeNode (K := K) (L := L) a b) :=
  ⟨fun r r' => no_node hag _ r r', fun _ => trivial⟩

theorem sto_pairUpV (hag : OnlyFb ag) :
    ∀ l : List (Dig lam), Sto (pairUp (hashTreeNode (K := K) (L := L)) l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => (sto_nodeV hag a b).bind fun _ => (sto_pairUpV hag t).bind fun _ => trivial

theorem sto_levelsV (hag : OnlyFb ag) :
    ∀ (d : ℕ) (l : List (Dig lam)), Sto (levelsM (hashTreeNode (K := K) (L := L)) d l)
  | 0, _ => trivial
  | d + 1, l => (sto_pairUpV hag l).bind fun u => (sto_levelsV hag d u).bind fun _ => trivial

/-! ## Part 2. The second half of the lazy prover -/

theorem still_finishSlotG {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
    (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
    (ext : (E.Pos → Bool) → ExtF lam E) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    Stl (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · exact trivial
  · exact fun vs => (still_opensB _ _ _ _ _ _ _).bind fun f => trivial

/-- Under the hypotheses below: the proof string of a slot (`finishSlotG`), the openings in the
external oracles given, is a `LiveW`; its one reveal (in this sense: the `Step.reveal` in the body
of `finishSlotG`; `openT` is a further one) names the tails of the failed tries too; nothing of
their strings is used. -/
theorem lw_finishSlotG {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt) (ext : (E.Pos → Bool) → ExtF lam E)
    {T : Tok → Prop} (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (h0 : ∀ u, liveA0 a0 u → T u)
    (ha : ∀ u, liveAcc acc u → T u) (hne : acc.toks ≠ []) :
    Lw T (fun _ _ => False) (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · exact .pure fun _ hu => hu.elim
  · have hl : 0 < acc.toks.length := List.length_pos_of_ne_nil hne
    refine LiveW.revealMore
      (ts := acc.toks.headD 0 ::
          (rootToks acc.trees a0.trees ++ (a0.req.map fun rq => pathOf rq.levels j).getD [] ++
            (a0.req.map TTree.root).toList ++
            (a0.req.map fun rq => ancOf rq.levels j).getD [] ++ acc.toks ++ a0.toks))
      (more := acc.dead ++ a0.dead) (fun u hu => ?_) (fun v x y hv => ?_) fun vs => ?_
    · rcases List.mem_cons.1 hu with e | hu
      · exact (headD_or acc.toks).imp
          (fun h => ha u (.inr (.inr (.inl (e ▸ h))))) fun h => e.trans h
      · simp only [List.mem_append] at hu
        rcases hu with ((((hu | hu) | hu) | hu) | hu) | hu
        · exact (mem_rootToks _ _ u hu).imp
            (fun h => h.elim (fun h => ha u (.inr (.inr (.inr h)))) fun h => h0 u (.inr (.inl h)))
            id
        · cases hr : a0.req with
          | none => rw [hr] at hu; exact nomatch hu
          | some rq => rw [hr] at hu; exact (mem_pathOf _ _ u hu).imp (fun h => h0 u (.inr (.inr ⟨rq, hr, .inl h⟩))) id
        · exact (rootOT_or a0.req u hu).imp (fun h => h0 u (.inr (.inr h))) id
        · cases hr : a0.req with
          | none => rw [hr] at hu; exact nomatch hu
          | some rq => rw [hr] at hu; exact (mem_ancOf _ _ u hu).imp (fun h => h0 u (.inr (.inr ⟨rq, hr, .inl h⟩))) id
        · exact .inl (ha u (.inr (.inr (.inl hu))))
        · exact .inl (h0 u (.inl hu))
    · simp only [List.length_cons, List.length_append] at hv
      rw [headD_app v x (by omega), headD_app v y (by omega), take_drop_app v x _ _ (by omega),
        take_drop_app v y _ _ (by omega), take_drop_app v x _ _ (by omega),
        take_drop_app v y _ _ (by omega), getD_app v x _ (by omega), getD_app v y _ (by omega)]
    · exact (lw_opensB _ _ _ _ _ _ _ _ (fun u hu => ha u (.inr (.inr (.inr hu))))
          fun u hu => h0 u (.inr (.inl hu))).bind
        fun f => .pure fun _ hu => hu.elim

theorem sto_opensExtL {E : ExtSpec} {opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))}
    (hn : ∀ q, Sto (opL q)) (we : WireE E) (y : E.Str) (isRead : E.Pos → Bool) :
    ∀ ps, Sto (opensExtL we y opL isRead ps)
  | [] => trivial
  | p :: ps => (sto_opensExtL hn we y isRead ps).bind fun of => by
      cases of with
      | none => exact trivial
      | some f =>
        show Sto (if isRead p then _ else _ : TypedOracleComputation lam K L _)
        split_ifs
        · exact (hn _).bind fun _ => trivial
        · exact trivial

theorem sto_finishSlotL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
    {opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))} (hn : ∀ q, Sto (opL q)) (c0 : H.Coin0)
    (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    Sto (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc vs) := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · exact trivial
  · refine (sto_opensExtL hn _ _ _ _).bind fun og => ?_
    cases og with
    | none => exact trivial
    | some gx =>
      exact ((still_finishSlotG Q H wq wp w _ c0 a0 j x cj acc).erase vs).bind fun _ => trivial

theorem sto_finishAllL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
    {opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))} (hn : ∀ q, Sto (opL q)) (fl : ℕ → Bool)
    (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits),
      Sto (Seed.finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs vs)
  | _, [], _ => trivial
  | j, acc :: zs, vs => by
    unfold Seed.finishAllL slotL
    refine OComp.StillBy.bind ?_ fun o1 => ?_
    · cases acc.x with
      | none => exact trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · exact sto_finishSlotL Q H wq wp w hn c0 a0 j x cj acc vs
        · exact trivial
    · cases o1 with
      | none => exact trivial
      | some o =>
        exact (sto_finishAllL Q H wq wp w hn fl c0 a0 (j + 1) zs o.2).bind fun _ => trivial

/-! ## Part 3. The second half on two stores that differ at a dead place -/

/-- Two results of the second half: both none, or the same value with stores that agree but at d,
which is in them. -/
def RelS {β : Type} (d : Tok) : Option (β × List Bits) → Option (β × List Bits) → Prop
  | none, none => True
  | some a, some b => a.1 = b.1 ∧ StoreRel (fun t => t = d) a.2 b.2 ∧ d < a.2.length
  | _, _ => False

theorem alike_finishSlotL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
    (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
    (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam))))
    (ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop) (c0 : H.Coin0) (a0 : Acc0)
    (j : ℕ) (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) {d : Tok} (hd0 : 0 < d)
    (h0 : ∀ u, liveA0 a0 u → u ≠ d) (ha : ∀ u, liveAcc acc u → u ≠ d) (hne : acc.toks ≠ [])
    {st st' : List Bits} (hs : StoreRel (fun t => t = d) st st') (hd : d < st.length) :
    OAlike (RelS d) (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc st)
      (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc st') := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · exact .pure ⟨rfl, hs, hd⟩
  · refine OAlike.bind (OAlike.refl (R := Eq) (fun _ => rfl) _) fun og og' e => ?_
    subst e
    cases og with
    | none => exact .pure trivial
    | some gx =>
      have hw := lw_finishSlotG (ag := ag) Q H wq wp w (fun _ => gx) (T := fun u => u ≠ d)
        c0 a0 j x cj acc h0 ha hne
      have hn := LiveWalk.nu hw d st.length hd0 hd fun _ hu => hu
      exact OAlike.bind (eraseDead _ _ _ _ _ _ st st' hs hn) fun o o' ho =>
        .pure ⟨ho.1, ho.2.1, ho.2.2.2⟩

theorem alike_finishAllL {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
    (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
    (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam))))
    (ag : ∀ o, domOf lam L o → rngOf lam K o → rngOf lam K o → Prop) (fl : ℕ → Bool) (c0 : H.Coin0)
    (a0 : Acc0) {d : Tok} (hd0 : 0 < d) (h0 : ∀ u, liveA0 a0 u → u ≠ d) :
    ∀ (zs : List (SlotAcc lam K (Y × H.Coin))) (j : ℕ),
      (∀ acc ∈ zs, acc.x ≠ none → ∀ u, liveAcc acc u → u ≠ d) →
      (∀ acc ∈ zs, acc.x ≠ none → acc.toks ≠ []) →
      ∀ {st st' : List Bits}, StoreRel (fun t => t = d) st st' → d < st.length →
        OAlike (RelS d) (Seed.finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs st)
          (Seed.finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs st')
  | [], _, _, _, _, _, hs, hd => .pure ⟨rfl, hs, hd⟩
  | acc :: zs, j, ha, hne, st, st', hs, hd => by
    unfold Seed.finishAllL
    refine OAlike.bind (R := RelS d) ?_ fun o1 o1' ho => ?_
    · unfold slotL
      cases hx : acc.x with
      | none => exact .pure ⟨rfl, hs, hd⟩
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · exact alike_finishSlotL Q H wq wp w opL ag c0 a0 j x cj acc hd0 h0
            (ha acc (List.mem_cons_self) (by rw [hx]; exact nofun))
            (hne acc (List.mem_cons_self) (by rw [hx]; exact nofun)) hs hd
        · exact .pure ⟨rfl, hs, hd⟩
    · cases o1 with
      | none =>
        cases o1' with
        | none => exact .pure trivial
        | some _ => exact ho.elim
      | some o =>
        cases o1' with
        | none => exact ho.elim
        | some o' =>
          obtain ⟨e1, e2, e3⟩ := ho
          refine OAlike.bind
            (alike_finishAllL Q H wq wp w opL ag fl c0 a0 hd0 h0 zs (j + 1)
              (fun a h => ha a (List.mem_cons_of_mem _ h))
              (fun a h => hne a (List.mem_cons_of_mem _ h)) e2 e3)
            fun o2 o2' h2 => ?_
          cases o2 with
          | none =>
            cases o2' with
            | none => exact .pure trivial
            | some _ => exact h2.elim
          | some r =>
            cases o2' with
            | none => exact h2.elim
            | some r' =>
              exact .pure ⟨by show (o.1 :: r.1) = (o'.1 :: r'.1); rw [e1, h2.1], h2.2.1, h2.2.2⟩

/-! ## Part 4. The first half: all chains -/

/-- Under the hypotheses below, the first half of the compiled prover with free empty slots
(`chainsU`) is a `LiveW` (limits: the header of Compile/LiveWalk.lean): in particular, started on a
store that holds all tokens taken as live, after two answers that ag relates it never uses the new
tail, and that tail is none of the live tokens of what it returns. -/
theorem lw_chainsU (hag : OnlyFb ag) (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
    (cms : List (Dig lam)) (w : Wt) {T : Tok → Prop} (hF : FitsSh ag t Q.loc.shape Q.ann wq.sh embP)
    (xs : List (Option Y)) (h1 : xs ≠ [] ∨ ∃ u, T u) :
    Lw T (fun o u => liveOutU o.2 u)
      (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs) := by
  unfold chainsU
  refine (lw_drawT wp.coin0).bind fun c0 => ?_
  refine LiveW.bindG (G := fun zs => zs.length = xs.length ∧ ∀ z ∈ zs, HasTok z.2)
    (lw_eachM (T0 := fun _ => False) (lσ := fun _ _ => False)
      (lτ := fun z u => liveAccU z.2 u) (fun _ _ x _ => lw_initSlotU sFS Q H wp w c0 x) xs _
      (fun _ h => h.elim) fun _ _ _ h => h.elim)
    ?_ fun zs hzs => ?_
  · exact ends_eachM (fun x => ends_initSlotU sFS Q H wp w c0 x) xs
  · refine (lw_chainTU sMT t _ _ hag depthReq _ _ _ _ _ 0 .first _ zs _ _ hF ?_
        (fun z hz u hu => .inr ⟨z, hz, hu⟩) (fun u hu => ?_) fun _ hu => hu.elim).bind
      fun out => .pure fun u hu => .inr hu
    · rcases h1 with h1 | ⟨u, hu⟩
      · exact .inl fun e => h1 (List.length_eq_zero_iff.1 (by rw [← hzs.1, e]; rfl))
      · exact .inr ⟨u, .inl (.inl hu)⟩
    · rcases hu with h | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · exact nomatch h
      · exact nomatch h
      · exact nomatch h

/-- Every slot with a request that `chainsU` returns has a list `toks` that is not empty (`HasTok`,
Compile/Batch/DeadUP.lean). -/
theorem ends_chainsU (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
    (cms : List (Dig lam)) (w : Wt) (xs : List (Option Y)) :
    Ends (S := spec lam K L) (sp := split lam K L) (fun o => ∀ acc ∈ o.2.1, HasTok acc)
      (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs) := by
  unfold chainsU
  refine Ends.bind (ends_true _) fun c0 _ =>
    Ends.bind (ends_eachM (fun x => ends_initSlotU sFS Q H wp w c0 x) xs) fun zs hzs =>
      Ends.bind (ends_chainTU sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hzs.2) fun out ho => ho

end Compile.Batch.Dead

/-! ## Part 5. The lazy prover; the cache; pruning -/

namespace Compile.Batch.Dead
open Iop Rom Compile Compile.Batch.Seed

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem sto_rD (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    (rD W WP p bk σ k j).StillBy (agF W) :=
  (((still_drawT WP.ri).erase []).blocks bk).derive σ k.2 (no_seed W σ hσ) _

theorem sto_opL (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ)
    (r : L.EncodingRandomness) (lvl : List (Dig lam)) (hi : List (List (Dig lam))) (q : ℕ) :
    (Seed.opL W WP p bk σ ℓ k j r lvl hi q).StillBy (agF W) :=
  OComp.StillBy.bind ((((still_leavesE (onlyFb_agF W) p.sMT _).erase []).blocks bk).derive
      σ k.2 (no_seed W σ hσ) _)
    fun a => (sto_levelsV (onlyFb_agF W) ℓ a.1.1).bind fun _ => trivial

theorem sto_nodeD (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    (nodeD W WP p bk σ k j).StillBy (agF W) :=
  (((Still.bind (still_drawT WP.ri) fun _ =>
        (still_commitE (onlyFb_agF W) p.sMT W.depth _).bind fun _ =>
          trivial : Still (agF W) (nodeP' W WP p k.1)).erase
      []).blocks bk).derive
    σ k.2 (no_seed W σ hσ) _

theorem sto_cacheFrom (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) :
    ∀ js, (cacheFrom W WP p bk σ ℓ k js).StillBy (agF W)
  | [] => trivial
  | j :: js =>
    (sto_nodeD W WP p bk σ hσ k j).bind fun _ =>
      (sto_cacheFrom W WP p bk σ hσ ℓ k js).bind fun _ => trivial

/-- Steps (4) to (6) of the lazy prover (`PLrun`; the steps: the head of
Compile/Batch/SeedLazyDefs.lean). -/
theorem facF_PLrun (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hW : W.OKG) (hσ : σ.o = OracleName.other) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : ℕ) (st : Dig lam × List (Dig lam))
    (hi : List (List (Dig lam))) (r : L.EncodingRandomness) :
    (PLrun W WP p bk σ ℓ no k b j st hi r).FactorsBy (agF W) := by
  have hN : 0 < L.maxBatchSize := by rw [hW.slots]; exact Nat.two_pow_pos _
  have hF : FitsSh (agF W) Tag.onl L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh id :=
    fitsSh_agF W Tag.onl _ _ W.B.sh id hW.B.sh fun _ => rfl
  have hg : ∀ t j', σ.o ≠ OracleName.fbw t j' := fun _ _ => by rw [hσ]; exact nofun
  intro z
  -- what follows the chains
  let g : (L.honestOnlineBatchProver.Coin0 × (List (SlotAcc lam W.K (X × L.honestOnlineBatchProver.Coin)) × Acc0)) × List Bits →
      TypedOracleComputation lam W.K L (ZKCP.Gen.Slots (PrfK lam L) b) := fun o =>
    (Seed.finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) (Seed.opL W WP p bk σ ℓ k j r st.2 hi)
        (slotFlags (WP.perm.e z) fun _ => true) o.1.1 o.1.2.2 0 o.1.2.1 o.2).bind fun oπ =>
      match oπ with
      | none => .pure (no j b)
      | some πs =>
        .pure (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length (WP.perm.e z) πs.1))
  have hgN : ∀ o, NoGhost (g o) := fun o =>
    NoGhost.bind
        (ng_finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) _
          (ng_opL W WP p bk σ hg ℓ k j r st.2 hi) _ _ _ 0 _ _) fun oπ => by
    cases oπ with
    | none => exact trivial
    | some πs => exact trivial
  have e : (eraseR
        (chainsU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩))
          id some W.depthReq [st.1] (k.1, r) (slotsOfReq (WP.perm.e z) (b.map Prod.fst)))
        []).bind g =
      realQ ((erase
          (chainsU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
            (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq [st.1] (k.1, r)
            (slotsOfReq (WP.perm.e z) (b.map Prod.fst)))
          []).bind g) := by
    rw [realQ_bind]
    exact congrArg _ (funext fun o => (realQ_of_noGhost _ (hgN o)).symm)
  show ((eraseR _ []).bind g).FactorsBy (agF W)
  rw [e]
  refine facF_realQ W _
    (LiveW.eraseStG (T := fun _ => False)
      (lw_chainsU (onlyFb_agF W) p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [st.1]
        (k.1, r) hF _ (.inl fun e0 => ?_))
      (ends_chainsU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [st.1] (k.1, r) _)
      [] (fun _ h => h.elim) g (fun d a s s' hG hd0 hd hl hs => ?_) fun a s _ _ => ?_)
  · have := Need.length_slotsOfReq (WP.perm.e z) (b.map Prod.fst)
    rw [e0] at this
    exact absurd this.symm (Nat.ne_of_gt hN)
  · exact alikeBind _ _ _ _ _ _ _ _
      (alike_finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) _ (agF W) _ a.1 a.2.2 hd0
        (fun u hu => hl u (.inr hu)) a.2.1 0 (fun acc ha hx u hu => hl u (.inl ⟨acc, ha, hx, hu⟩))
        (fun acc ha hx => hG acc ha hx) hs hd)
      fun o o' ho => by
        cases o with
        | none =>
          cases o' with
          | none => rfl
          | some _ => exact ho.elim
        | some x =>
          cases o' with
          | none => exact ho.elim
          | some x' =>
            show OComp.pure (fitLen _ _ (prfsK _ _ _ x.1)) =
              OComp.pure (fitLen _ _ (prfsK _ _ _ x'.1))
            rw [ho.1]
  · exact (OComp.StillBy.bind (sto_finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) (sto_opL W WP p bk σ hσ ℓ k j r st.2 hi) _ _ _ 0 _ _) fun oπ => by
      cases oπ with
      | none => exact trivial
      | some πs => exact trivial).fac

/-- Under `W.OKG`, if σ.o = other: the lazy prover `PL` has `FactorsBy (agF W)`. -/
theorem facF_PL_P (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hW : W.OKG) (hσ : σ.o = OracleName.other) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) :
    (PL W WP p bk σ ℓ no kc b).FactorsBy (agF W) := by
  intro j
  show (PLat W WP p bk σ ℓ no kc b j.val).FactorsBy (agF W)
  unfold PLat
  cases kc.2[j.val]? with
  | none => exact trivial
  | some st =>
    refine OComp.FactorsBy.bind (sto_levelsV (onlyFb_agF W) _ _).fac fun hi => ?_
    split_ifs
    · exact OComp.FactorsBy.bind (sto_rD W WP p bk σ hσ kc.1 j.val).fac fun ra =>
        facF_PLrun W WP p bk σ hW hσ ℓ no kc.1 b j.val st hi ra.1
    · exact trivial

/-- `Spec.facF_PL`: C and P of the scheme with the lazy prover and pruned Merkle paths. -/
theorem facF_PL : Spec.facF_PL := fun _ _ _ _ W WP p bk σ ℓ hW hσ =>
  ⟨fun i =>
      OComp.FactorsBy.map
        (OComp.FactorsBy.bind (facF_C W WP p bk σ hW hσ i) fun o =>
          OComp.StillBy.fac (OComp.StillBy.map (sto_cacheFrom W WP p bk σ hσ ℓ o.2 _) _)) _,
    fun kc b => OComp.FactorsBy.map (facF_PL_P W WP p bk σ hW hσ ℓ Seed.noK kc b) _⟩

end Compile.Batch.Dead
