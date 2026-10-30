-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieOwn.lean: THE CHAIN OF THE TOKEN SIDE AGAINST THE COMPILED PROVER's CHAIN, ONE
CASE OF A ROUND: the slot's component is hashed by one Fiat-Shamir query, with a search for a nonce
or without (the formats (F1), (F2), (F3)). One theorem with its proof.

A lemma of one step of a proof. This file states no goal of the release.

  chain_own   from ChainTie (Johnson/TokenSide/TieChain.lean) for the later rounds to the tie for
              such a round and the later rounds.

How it goes, along the two texts: the trees over the slot's component (tie_trees: here the coins are
drawn); the Fiat-Shamir query with its search (tie_fs); if the search has run out, both sides stop
with the same outcome; else the later rounds (the premise), which do not read this round's salts
(chainO_congr); at the end both sides lay this round's message, trees and verifier message in front
of what the later rounds have yielded.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieChain

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop}

/-- **A round in which the slot's component is hashed by one Fiat-Shamir query, with a search or
without.** -/
theorem chain_own (ll : LeafLens Ω μ ℓ Z) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) {r : Round}
    {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
    (IH : ChainTie ll t cms x pre salt cd cap s A W)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (m : r.Msg)
    (k : r.Chal → Strat s Unit) (vs : List Bits) (hs : salt < vs.length) (hph : PhOK lam vs ph)
    (hc : Covers Z (r :: s) (a, A) (w, W) i) {tk : Tok} {us : List Tok}
    {hd : List Bits → Bits → Head lam X}
    {inj : ∀ (xl : Option X) (vs : List Bits), Function.Injective fun v => (hd vs v).withLate xl}
    {next : Tok → PhT}
    (h : actT cms (x.map L.early) salt a.kind ph = some (.one tk us hd inj true next)) :
    Tie μ
      (fun (p : Res (OutT lam L (r :: s)) × List Bits) ω =>
        p.1.map fun z => outW ll (fun i b => pre i b (vs.getD salt [])) p.2 i z ω)
      (fun p => vs <+: p.2 ∧ ∀ z, p.1 = .ok z → OutOK ℓ (r :: s) (a, A) (w, W) z p.2)
      (plainOf (chainT t cms x ℓ pre salt cd cap (r :: s) (a, A) (w, W) embS embP i ph (m, k)) vs)
      (fun ω => (chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap (r :: s) (a, A) (w, W) embS
        embP i (ph.val lam fun u => vs.getD u []) (m, k)).bind
        fun r => .pure (r.map fun z => (z, ω))) := by
  obtain ⟨nextO, hO, htk, hus, hnext⟩ := act_one h hs hph
  have eT : chainT t cms x ℓ pre salt cd cap (r :: s) (a, A) (w, W) embS embP i ph (m, k) =
      (treesT (K := K) ℓ [salt] (fun vs => pre i true (vs.headD [])) cd.pad w.posAtJ
        (fun p => embS (.inl p)) m.1 0 w.depthJ).bind fun TJ =>
      (fsT w.grJ (cap i) w.chal (fun n α => fbT (K := K) t n i tk us
          (fun vs v => (hd vs v).withLate (lateInstancePart L i x)) (inj (lateInstancePart L i x))
          (TJ.map TreeT.root) (embP (.inl (.inr α)))) (a.plain m.2).2).bind <| onFsT i fun q =>
        (chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
          (fun z => embP (.inr z)) (i + 1) (next q.tl) (k (w.chal q.bl))).bind fun r =>
        .pure (r.map (consT (w.chal q.bl)
          ((m.1, a.plain.symm ((a.plain m.2).1, q.pl)), [], TJ) none (q.tl :: q.dead))) := by
    rw [chainT, h]
  have eO : ∀ ω, chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap (r :: s) (a, A) (w, W) embS
      embP i (ph.val lam fun u => vs.getD u []) (m, k) =
      (treesO (K := K) cd.pad (fun k j => pre i true (vs.getD salt []) ++ ll.get ω i true k j)
        w.posAtJ (fun p => embS (.inl p)) m.1 0 w.depthJ).bind fun TJ =>
      (fsO w.grJ (cap i) w.chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
          (⟨i, (hd (us.map fun u => vs.getD u []) (vs.getD tk [])).withLate (lateInstancePart L i x),
            TJ.map TreeK.root, embP (.inl (.inr α))⟩ : FbIn lam L t)) (a.plain m.2).2).bind <|
        onFs i fun q =>
        (chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap s A W (fun p => embS (.inr p))
          (fun z => embP (.inr z)) (i + 1) (nextO (List.ofFn q.2.2)) (k (w.chal q.2.1))).bind
          fun r => .pure (r.map (consP (w.chal q.2.1)
            ((m.1, a.plain.symm ((a.plain m.2).1, q.1)), [], TJ) none)) := by
    intro ω
    rw [chainO]
    show (match actOf cms (x.map L.early) (vs.getD salt []) a.kind
      (ph.val lam fun u => vs.getD u []) with
      | some (.one h true next) => _
      | some (.one h false next) => _
      | some (.join ρ) => _
      | none => _) = _
    rw [hO]
    rfl
  rw [eT, plainOf_bind]
  refine (Tie.bindW (tie_trees ll [salt] (fun vs => pre i true (vs.headD []))
    (pre i true (vs.getD salt [])) i true cd.pad w.posAtJ (fun p => embS (.inl p)) m.1 w.depthJ 0 vs
    hc.1 (fun u hu => by rw [List.mem_singleton.mp hu]; exact hs) rfl)
    (f' := fun ω TJ =>
      ((fsO w.grJ (cap i) w.chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
          (⟨i, (hd (us.map fun u => vs.getD u []) (vs.getD tk [])).withLate (lateInstancePart L i x),
            TJ.map TreeK.root, embP (.inl (.inr α))⟩ : FbIn lam L t)) (a.plain m.2).2).bind <|
        onFs i fun q =>
        (chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap s A W (fun p => embS (.inr p))
          (fun z => embP (.inr z)) (i + 1) (nextO (List.ofFn q.2.2)) (k (w.chal q.2.1))).bind
          fun r => .pure (r.map (consP (w.chal q.2.1)
            ((m.1, a.plain.symm ((a.plain m.2).1, q.1)), [], TJ) none))).bind
        fun r => .pure (r.map fun z => (z, ω))) fun p hp => ?_).congr fun ω => ?_
  swap
  · rw [eO, Tie.obind_assoc]
  -- behind the trees
  obtain ⟨TJ, vs₁⟩ := p
  have hp1 : vs <+: vs₁ := hp.1
  rw [plainOf_bind]
  refine (Tie.bindW (tie_fs (μ := μ) w.grJ (cap i) w.chal t i tk us
    (fun vs v => (hd vs v).withLate (lateInstancePart L i x)) (inj (lateInstancePart L i x)) (TJ.map TreeT.root)
    (fun α => embP (.inl (.inr α))) (a.plain m.2).2
    ((hd (us.map fun u => vs.getD u []) (vs.getD tk [])).withLate (lateInstancePart L i x)) vs₁
    (Nat.lt_of_lt_of_le htk hp1.length_le)
    (fun u hu => Nat.lt_of_lt_of_le (hus u hu) hp1.length_le) (by
      rw [getD_of_prefix hp1 htk]
      exact congrArg (fun l => (hd l (vs.getD tk [])).withLate (lateInstancePart L i x))
        (List.map_congr_left fun u hu => getD_of_prefix hp1 (hus u hu))))
    (f' := fun ω o => (onFs i (fun q =>
        (chainO t cms x (coOf ll (vs.getD salt []) cd pre (patchTs ll i true 0 TJ vs₁ ω)) cap s A W
          (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (nextO (List.ofFn q.2.2))
          (k (w.chal q.2.1))).bind
          fun r => .pure (r.map (consP (w.chal q.2.1)
            ((m.1, a.plain.symm ((a.plain m.2).1, q.1)), [],
              mkKs ll (pre i true (vs.getD salt [])) i true (patchTs ll i true 0 TJ vs₁ ω) 0 TJ)
            none))) o).bind
        fun r => .pure (r.map fun z => (z, patchTs ll i true 0 TJ vs₁ ω))) fun p2 hp2 => ?_).congr
    fun ω => ?_
  swap
  · beta_reduce
    rw [map_root_mkKs, Tie.obind_assoc]
  -- behind the Fiat-Shamir query
  obtain ⟨oq, vs₂⟩ := p2
  have hp2' : vs₁ <+: vs₂ := hp2.1
  cases oq with
  | none => exact .done ⟨hp1.trans hp2', fun z hz => by cases hz⟩ fun _ => rfl
  | some q =>
    obtain ⟨hq1, d, hq2⟩ := hp2.2 q rfl
    obtain ⟨hn1, hn2⟩ := hnext vs₂ q.tl d (hp1.trans hp2') hq1 hq2
    have hsv : vs₂.getD salt [] = vs.getD salt [] := getD_of_prefix (hp1.trans hp2') hs
    have IH' := IH (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (next q.tl)
      (k (w.chal q.bl)) vs₂ (Nat.lt_of_lt_of_le hs (hp1.trans hp2').length_le) hn2 hc.2.2
    rw [hsv, ← hn1] at IH'
    show Tie μ _ _ (plainOf ((chainT t cms x ℓ pre salt cd cap s A W (fun p => embS (.inr p))
      (fun z => embP (.inr z)) (i + 1) (next q.tl) (k (w.chal q.bl))).bind fun r =>
      Step.pure (r.map (consT (w.chal q.bl)
        ((m.1, a.plain.symm ((a.plain m.2).1, q.pl)), [], TJ) none (q.tl :: q.dead)))) vs₂) _
    rw [plainOf_bind]
    refine (IH'.bind (f' := fun r' => .pure (r'.map fun y =>
      (consP (w.chal q.bl) ((m.1, a.plain.symm ((a.plain m.2).1, q.pl)), [],
        mkKs ll (pre i true (vs.getD salt [])) i true (patchTs ll i true 0 TJ vs₁ y.2) 0 TJ) none
            y.1,
        patchTs ll i true 0 TJ vs₁ y.2))) fun p3 hp3 => ?_).congr fun ω => ?_
    swap
    · show ((chainO t cms x (coOf ll (vs.getD salt []) cd pre (patchTs ll i true 0 TJ vs₁ ω)) cap s
          A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (nextO (List.ofFn (digOf lam (vs₂.getD q.tl [])))) (k (w.chal q.bl))).bind _).bind _ = _
      rw [hq2, digOf_ofFn, Tie.obind_assoc, Tie.obind_assoc]
      have e1 : chainO t cms x (coOf ll (vs.getD salt []) cd pre (patchTs ll i true 0 TJ vs₁ ω)) cap
          s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (nextO (List.ofFn d))
          (k (w.chal q.bl)) =
          chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap s A W (fun p => embS (.inr p))
            (fun z => embP (.inr z)) (i + 1) (nextO (List.ofFn d)) (k (w.chal q.bl)) :=
        chainO_congr t cms x _ _ _ _ _ _ _ cap s A W _ _ (i + 1) _ _ fun i' hi =>
          funext fun b => funext fun k' => funext fun j => by
            rw [get_patchTs_ne ll i true vs₁ i' b k' j (fun e => by omega)]
      rw [e1]
      refine congrArg _ (funext fun r3 => ?_)
      cases r3 <;> rfl
    · obtain ⟨r3, vs₃⟩ := p3
      have hp3' : vs₂ <+: vs₃ := hp3.1
      cases r3 with
      | noFormat =>
        exact .done ⟨(hp1.trans hp2').trans hp3', fun z hz => by cases hz⟩ fun _ => rfl
      | ranOut j =>
        exact .done ⟨(hp1.trans hp2').trans hp3', fun z hz => by cases hz⟩ fun _ => rfl
      | ok z =>
        refine .done ⟨(hp1.trans hp2').trans hp3', fun z' hz' => ?_⟩ fun ω => ?_
        · cases hz'
          exact ⟨⟨Or.inl rfl, Or.inr (hp.2.mono (hp2'.trans hp3')), (hp3.2 z rfl).1⟩,
            fun u hu => List.mem_append_right _ ((hp3.2 z rfl).2 u hu)⟩
        have es : ∀ ω', patchTs ll i true 0 TJ vs₃ ω' = patchTs ll i true 0 TJ vs₁ ω' := fun ω' =>
          patchTs_store ll i true (hp2'.trans hp3') TJ 0 ω' hp.2.lt
        show OComp.pure (Res.ok _) = OComp.pure (Res.ok
          ((((w.chal q.bl, z.rho),
            (((m.1, a.plain.symm ((a.plain m.2).1, q.pl)), [],
              mkKs ll (pre i true (vs.getD salt [])) i true
                (patchTs ll i true 0 TJ vs₃ (actK ll s (i + 1) z.kept vs₃ ω)) 0 TJ),
            keptW ll (fun i b => pre i b (vs.getD salt []))
              (patchTs ll i true 0 TJ vs₃ (actK ll s (i + 1) z.kept vs₃ ω)) s (i + 1) z.kept),
            z.ph.val lam (fun u => vs₃.getD u []),
            z.rq.map fun u => digOf lam (vs₃.getD u [])) : OutP lam L (r :: s)),
            patchTs ll i true 0 TJ vs₃ (actK ll s (i + 1) z.kept vs₃ ω)))
        rw [es, keptW_congr ll _ (patchTs ll i true 0 TJ vs₁ (actK ll s (i + 1) z.kept vs₃ ω))
          (actK ll s (i + 1) z.kept vs₃ ω) s (i + 1) z.kept fun i' b k' j hi =>
            get_patchTs_ne ll i true vs₁ i' b k' j (fun e => by omega) TJ 0 _]
        rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.chain_own
