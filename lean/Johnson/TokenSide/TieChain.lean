-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/TieChain.lean: THE CHAIN OF THE TOKEN SIDE AGAINST THE COMPILED PROVER's CHAIN:
the statement (ChainTie), and the lemmas that its proof shares between the cases of a round. The
cases are in Johnson/TokenSide/TieOwn.lean, TieShared.lean and TieJoin.lean, the whole in
TieAll.lean. Definitions, and theorems with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

ChainTie says: chainT (Johnson/TokenSide/Chain.lean), as an ordinary algorithm with the names
fbw t k written back (plainOf, Johnson/TokenSide/Erased.lean), does what chainO
(OnBytes/Prover/Defs.lean) does at coins that are handed over at the start (Tie,
Johnson/TokenSide/Tie.lean): the same queries at the same points in the same order, each leaf's free
bits drawn where the leaf is hashed. By Tie.sound it gives an equation of laws UNDER EVERY HANDLER
of queries.

The compiled prover's coins are coOf: the first salt is the value of its token; a leaf's salt is its
start, then the free bits that are read off ω; the rest are the values cd.

What the two sides return. The token side: handles and a store. The compiled prover: values, among
them trees that hold the salts of ALL leaf numbers, as a function. outW writes the second out of the
first and of ω: the salts are read at the coins with the drawn bits laid in (actK).

Main names (namespace OnBytes.TokenSide).
  coOf, actK, keptW, outW   the coins; the coins with all drawn bits laid in; what is kept and
      yielded, as the compiled prover has it.
  KeptOK, OutOK   what is kept, what is yielded, is in order at a store (TreeOK, TreesOK:
      Johnson/TokenSide/TieTree.lean).
  PhOK, Covers   the tokens of a phase are in the store, a slot value's is a digest; the coordinates
      that a chain reads lie in Z.
  ChainTie   THE STATEMENT, for the rounds s.
  act_one    the case split of the two sides agrees.
  chainO_congr   the compiled prover's chain from round i on reads the leaves' salts of the rounds
      from i on alone.
  get_patchTs_ne, patchTs_store, keptW_congr, map_root_mkKs   what a round's drawn bits do not
      touch.

Limits. All is said of the ERASED program (plainOf, Johnson/TokenSide/Erased.lean): tokens are
strings in a store, and the names fbw t k are written back to fb t. Nothing here speaks of these
names, or of the two modes of deferred programming (Rom/Defer.lean): they are the matter of
Johnson/HopSide/, Johnson/GhostSide/ and Compile/DeferRun/.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.TieTree
import Johnson.TokenSide.TieSearch

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable {Ω : Type} {μ : PMF Ω} {ℓ : ℕ} {Z : ℕ → Bool → ℕ → ℕ → Prop}

/-! ## From handles to values -/

/-- the compiled prover's coins: the first salt sv, the values cd, the leaves' free bits off ω -/
def coOf (ll : LeafLens Ω μ ℓ Z) (sv : Bits) (cd : CoinsD lam L) (pre : ℕ → Bool → Bits → Bits)
    (ω : Ω) : Coins lam L :=
  ⟨sv, fun i b k j => pre i b sv ++ ll.get ω i b k j, cd.pad, cd.slot, cd.path, cd.rsalt⟩

/-- the coins with the values of all kept trees' tokens laid in; i: the number of the first round -/
def actK (ll : LeafLens Ω μ ℓ Z) : (s : Shape) → ℕ → KeptT lam L s → List Bits → Ω → Ω
  | [], _, _, _, ω => ω
  | _ :: s, i, (kp, ks), vs, ω =>
      patchTs ll i true 0 kp.2.2 vs (patchTs ll i false 0 kp.2.1 vs (actK ll s (i + 1) ks vs ω))

/-- what is kept, as the compiled prover has it, the salts read at the coins ωa -/
def keptW (ll : LeafLens Ω μ ℓ Z) (st : ℕ → Bool → Bits) (ωa : Ω) :
    (s : Shape) → ℕ → KeptT lam L s → Kept lam L s
  | [], _, _ => ()
  | _ :: s, i, (kp, ks) =>
      ((kp.1, mkKs ll (st i false) i false ωa 0 kp.2.1, mkKs ll (st i true) i true ωa 0 kp.2.2),
        keptW ll st ωa s (i + 1) ks)

/-- what the chain yields, as the compiled prover has it, and the coins with the drawn bits laid
in -/
def outW (ll : LeafLens Ω μ ℓ Z) (st : ℕ → Bool → Bits) (vs : List Bits) (i : ℕ) {s : Shape}
    (z : OutT lam L s) (ω : Ω) : OutP lam L s × Ω :=
  ((z.rho, keptW ll st (actK ll s i z.kept vs ω) s i z.kept, z.ph.val lam (fun t => vs.getD t []),
    z.rq.map fun u => digOf lam (vs.getD u [])), actK ll s i z.kept vs ω)

/-- the tokens of a phase are in the store, and the value of a slot value's token is a digest -/
def PhOK (lam : ℕ) (vs : List Bits) : PhT → Prop
  | .first => True
  | .loc tk => tk < vs.length
  | .shr tk0 c => tk0 < vs.length ∧ c < vs.length ∧ ∃ d : Dig lam, vs.getD c [] = List.ofFn d
  | .aft tk c => tk < vs.length ∧ c < vs.length ∧ ∃ d : Dig lam, vs.getD c [] = List.ofFn d

/-- the coordinates of all leaves of all trees of the rounds s lie in Z -/
def Covers (Z : ℕ → Bool → ℕ → ℕ → Prop) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), i =>
      (∀ n d, w.depthJ[n]? = some d → ∀ j, j < 2 ^ d → Z i true (0 + n) j) ∧
      (∀ n d, w.depth0[n]? = some d → ∀ j, j < 2 ^ d → Z i false (0 + n) j) ∧ Covers Z s A W (i + 1)

/-- what is kept of the rounds s is in order at a store: in each round the trees over a component
are none, or one for each depth of the wire's list, each in order -/
def KeptOK (ℓ : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → KeptT lam L s → List Bits →
    Prop
  | [], _, _, _, _ => True
  | _ :: s, (_, A), (w, W), (kp, ks), vs =>
      (kp.2.1 = [] ∨ TreesOK ℓ w.depth0 vs kp.2.1) ∧ (kp.2.2 = [] ∨ TreesOK ℓ w.depthJ vs kp.2.2) ∧
        KeptOK ℓ s A W ks vs

/-- what the chain yields is in order at a store: what is kept is; the token of the request root is
among the chain's tokens -/
def OutOK (ℓ : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (z : OutT lam L s)
    (vs : List Bits) : Prop :=
  KeptOK ℓ s A W z.kept vs ∧ ∀ u, z.rq = some u → u ∈ z.toks

/-- **THE STATEMENT, for the rounds s.** -/
def ChainTie (ll : LeafLens Ω μ ℓ Z) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (pre : ℕ → Bool → Bits → Bits) (salt : Tok) (cd : CoinsD lam L) (cap : ℕ → ℕ) (s : Shape)
    (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) : Prop :=
  ∀ (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (ph : PhT) (σ : Strat s Unit) (vs : List Bits),
    salt < vs.length → PhOK lam vs ph → Covers Z s A W i →
    Tie μ
      (fun (p : Res (OutT lam L s) × List Bits) ω =>
        p.1.map fun z => outW ll (fun i b => pre i b (vs.getD salt [])) p.2 i z ω)
      (fun p => vs <+: p.2 ∧ ∀ z, p.1 = .ok z → OutOK ℓ s A W z p.2)
      (plainOf (chainT t cms x ℓ pre salt cd cap s A W embS embP i ph σ) vs)
      (fun ω => (chainO t cms x (coOf ll (vs.getD salt []) cd pre ω) cap s A W embS embP i
        (ph.val lam fun u => vs.getD u []) σ).bind fun r => .pure (r.map fun z => (z, ω)))

/-! ## The case split -/

theorem phOK_mono {vs ws : List Bits} (h : vs <+: ws) : ∀ {ph : PhT}, PhOK lam vs ph → PhOK lam ws
    ph
  | .first, _ => trivial
  | .loc _, h1 => Nat.lt_of_lt_of_le h1 h.length_le
  | .shr _ _, h1 => ⟨Nat.lt_of_lt_of_le h1.1 h.length_le, Nat.lt_of_lt_of_le h1.2.1 h.length_le,
      h1.2.2.imp fun _ e => by rw [getD_of_prefix h h1.2.1]; exact e⟩
  | .aft _ _, h1 => ⟨Nat.lt_of_lt_of_le h1.1 h.length_le, Nat.lt_of_lt_of_le h1.2.1 h.length_le,
      h1.2.2.imp fun _ e => by rw [getD_of_prefix h h1.2.1]; exact e⟩

/-- **The two sides' case splits agree**, where the token side has one Fiat-Shamir query. -/
theorem act_one {cms : List (Dig lam)} {x : Option X} {salt : Tok} {kd : Kind} {ph : PhT}
    {tk : Tok} {us : List Tok} {hd : List Bits → Bits → Head lam X}
    {inj : ∀ (xl : Option X) (vs : List Bits), Function.Injective fun v => (hd vs v).withLate xl}
    {own : Bool} {next : Tok → PhT} (h : actT cms x salt kd ph = some (.one tk us hd inj own next))
    {vs : List Bits} (hs : salt < vs.length) (hph : PhOK lam vs ph) :
    ∃ nextO : Bits → Phase lam,
      actOf cms x (vs.getD salt []) kd (ph.val lam fun u => vs.getD u []) =
        some (.one (hd (us.map fun u => vs.getD u []) (vs.getD tk [])) own nextO) ∧
      tk < vs.length ∧ (∀ u ∈ us, u < vs.length) ∧
      ∀ (ws : List Bits) (tl : Tok) (d : Dig lam), vs <+: ws → tl < ws.length →
        ws.getD tl [] = List.ofFn d →
        nextO (List.ofFn d) = (next tl).val lam (fun u => ws.getD u []) ∧ PhOK lam ws (next
            tl) := by
  cases kd with
  | lo =>
    cases ph with
    | first =>
      simp only [actT, Option.some.injEq] at h
      cases h
      exact ⟨_, rfl, hs, fun u hu => absurd hu (List.not_mem_nil), fun ws tl d _ h2 h3 =>
        ⟨by show Phase.loc (List.ofFn d) = Phase.loc (ws.getD tl []); rw [h3], h2⟩⟩
    | loc tk' =>
      simp only [actT, Option.some.injEq] at h
      cases h
      exact ⟨_, rfl, hph, fun u hu => absurd hu (List.not_mem_nil), fun ws tl d _ h2 h3 =>
        ⟨by show Phase.loc (List.ofFn d) = Phase.loc (ws.getD tl []); rw [h3], h2⟩⟩
    | shr tk0 c =>
      simp only [actT, Option.some.injEq] at h
      cases h
      obtain ⟨h1, h2, d0, h3⟩ := hph
      refine ⟨fun v => .aft v (digOf lam (vs.getD tk [])), ?_, h2,
        fun u hu => by rw [List.mem_singleton.mp hu]; exact h1,
        fun ws tl d hw h4 h5 => ⟨?_, h4, Nat.lt_of_lt_of_le h2 hw.length_le, d0, by
          rw [getD_of_prefix hw h2]; exact h3⟩⟩
      · show some (Act.one (Head.f3 (vs.getD tk0 []) (List.ofFn (digOf lam (vs.getD tk [])))) true
          fun v => Phase.aft v (digOf lam (vs.getD tk []))) =
          some (Act.one (Head.f3 (vs.getD tk0 []) (vs.getD tk [])) true _)
        rw [h3, digOf_ofFn]
      · show Phase.aft (List.ofFn d) (digOf lam (vs.getD tk [])) =
          Phase.aft (ws.getD tl []) (digOf lam (ws.getD tk []))
        rw [h5, getD_of_prefix hw h2]
    | aft tk' c =>
      simp only [actT, Option.some.injEq] at h
      cases h
      obtain ⟨h1, h2, d0, h3⟩ := hph
      exact ⟨_, rfl, h1, fun u hu => absurd hu (List.not_mem_nil), fun ws tl d hw h4 h5 =>
        ⟨by
          show Phase.aft (List.ofFn d) (digOf lam (vs.getD c [])) =
            Phase.aft (ws.getD tl []) (digOf lam (ws.getD c []))
          rw [h5, getD_of_prefix hw h2],
          h4, Nat.lt_of_lt_of_le h2 hw.length_le, d0, by rw [getD_of_prefix hw h2]; exact h3⟩⟩
  | sh =>
    cases ph with
    | first => simp [actT] at h
    | loc tk' => simp [actT] at h
    | aft tk' c => simp [actT] at h
    | shr tk0 c =>
      simp only [actT, Option.some.injEq] at h
      cases h
      obtain ⟨h1, h2, d0, h3⟩ := hph
      exact ⟨_, rfl, h1, fun u hu => absurd hu (List.not_mem_nil), fun ws tl d hw h4 h5 =>
        ⟨by
          show Phase.shr (List.ofFn d) (digOf lam (vs.getD c [])) =
            Phase.shr (ws.getD tl []) (digOf lam (ws.getD c []))
          rw [h5, getD_of_prefix hw h2],
          h4, Nat.lt_of_lt_of_le h2 hw.length_le, d0, by rw [getD_of_prefix hw h2]; exact h3⟩⟩

/-! ## What the later rounds read -/

/-- The compiled prover's chain from round i on reads the leaves' salts of the rounds from i on
alone. -/
theorem chainO_congr (t : Tag) (cms : List (Dig lam)) (x : Option X) (sv : Bits) (pad : Body L)
    (slot : ℕ) (path : List (Dig lam)) (rs : Bits) (lf lf' : ℕ → Bool → ℕ → ℕ → Bits)
    (cap : ℕ → ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam) (σ : Strat s Unit),
      (∀ i', i ≤ i' → lf i' = lf' i') →
      chainO t cms x ⟨sv, lf, pad, slot, path, rs⟩ cap s A W embS embP i ph σ =
        chainO t cms x ⟨sv, lf', pad, slot, path, rs⟩ cap s A W embS embP i ph σ
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), h => by
    have e := h i (Nat.le_refl i)
    have ih := fun e1 e2 ph' σ' => chainO_congr t cms x sv pad slot path rs lf lf' cap s A W e1 e2
      (i + 1) ph' σ' fun i' hi => h i' (Nat.le_of_succ_le hi)
    simp only [chainO, e, ih]

theorem get_patchTs_ne (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) (vs : List Bits)
    (i' : ℕ) (b' : Bool) (k' j' : ℕ) (h : ¬(i' = i ∧ b' = b)) :
    ∀ (Ts : List (TreeT lam L)) (k : ℕ) (ω : Ω),
      ll.get (patchTs ll i b k Ts vs ω) i' b' k' j' = ll.get ω i' b' k' j'
  | [], _, _ => rfl
  | T :: Ts, k, ω => by
    show ll.get (patchL ll i b k _ _ vs (patchTs ll i b (k + 1) Ts vs ω)) i' b' k' j' = _
    rw [get_patchL_ne ll i b k vs _ i' b' k' j' fun e => h ⟨e.1, e.2.1⟩]
    exact get_patchTs_ne ll i b vs i' b' k' j' h Ts (k + 1) ω

theorem patchTs_store (ll : LeafLens Ω μ ℓ Z) (i : ℕ) (b : Bool) {vs ws : List Bits}
    (hp : vs <+: ws) : ∀ (Ts : List (TreeT lam L)) (k : ℕ) (ω : Ω),
      (∀ T ∈ Ts, ∀ a ∈ T.tok, a.1 < vs.length) →
      patchTs ll i b k Ts ws ω = patchTs ll i b k Ts vs ω
  | [], _, _, _ => rfl
  | T :: Ts, k, ω, h => by
    show patchL ll i b k _ _ ws (patchTs ll i b (k + 1) Ts ws ω) =
      patchL ll i b k _ _ vs (patchTs ll i b (k + 1) Ts vs ω)
    rw [patchTs_store ll i b hp Ts (k + 1) ω fun T' hT' => h T' (List.mem_cons_of_mem _ hT'),
      patchL_store ll i b k hp _ _ _ (h T (List.mem_cons_self ..))]

theorem keptW_congr (ll : LeafLens Ω μ ℓ Z) (st : ℕ → Bool → Bits) (ωa ωb : Ω) :
    ∀ (s : Shape) (i : ℕ) (ks : KeptT lam L s),
      (∀ i' b k j, i ≤ i' → ll.get ωa i' b k j = ll.get ωb i' b k j) →
      keptW ll st ωa s i ks = keptW ll st ωb s i ks
  | [], _, _, _ => rfl
  | _ :: s, i, (kp, ks), h => by
    show ((kp.1, mkKs ll (st i false) i false ωa 0 kp.2.1, mkKs ll (st i true) i true ωa 0 kp.2.2),
        keptW ll st ωa s (i + 1) ks) =
      ((kp.1, mkKs ll (st i false) i false ωb 0 kp.2.1, mkKs ll (st i true) i true ωb 0 kp.2.2),
        keptW ll st ωb s (i + 1) ks)
    rw [keptW_congr ll st ωa ωb s (i + 1) ks fun i' b k j hi => h i' b k j (Nat.le_of_succ_le hi),
      mkKs_congr ll (st i false) i false ωa ωb kp.2.1 0 fun k j _ => h i false k j (Nat.le_refl i),
      mkKs_congr ll (st i true) i true ωa ωb kp.2.2 0 fun k j _ => h i true k j (Nat.le_refl i)]

theorem map_root_mkKs (ll : LeafLens Ω μ ℓ Z) (st : Bits) (i : ℕ) (b : Bool) (ωa : Ω) :
    ∀ (Ts : List (TreeT lam L)) (k : ℕ),
      (mkKs ll st i b ωa k Ts).map TreeK.root = Ts.map TreeT.root
  | [], _ => rfl
  | T :: Ts, k => congrArg (T.root :: ·) (map_root_mkKs ll st i b ωa Ts (k + 1))

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.act_one
#print axioms OnBytes.TokenSide.chainO_congr
