-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/WholeKey/Complete.lean: COMPLETENESS, FROM NAMED PREMISES, OF THE SCHEME WITH THE WHOLE KEY
(argW, Johnson/WholeKey/Defs.lean), in the form of the library's own definition over typed oracles
(ZKCP.Gen.HasCompletenessError, ZKCP/Gen.lean), for batches of at most
one request, at the number of the prover of a whole request (alphaAll, Johnson/Prover/All/Law.lean).
AT LETTERS: any interface whose keys hold an OOD sample, any wires, any honest side.

How. Fix all coins. The committer, the prover and the verifier behind their coins have no coins, so
an event passes between such programs by their values under fixed oracle functions alone
(PrFrom_le_of_det, Johnson/Prover/Law/Stages.lean). Under fixed oracle functions the key (root, OOD
sample) and the typed proof that the verifier re-packs are those of the prover of a whole request
(allY, allX, Johnson/Prover/All/Defs.lean) at the sample that the committer's coins, its coins for
the copy at the sampled place, and the prover's coins make up (drawOf): the order of the runs and
the other copies' runs move no value. Outside that prover's event no run has run out, none is
without a format (all_format, under WiresFit's clause on the marks: spent inside ok_of_not_ev), and
no test for a stop fires (StopsIn): so the verifier accepts (all_good,
Johnson/Prover/All/Good.lean). The event's measure is allY_law's (Johnson/Prover/All/Law.lean), from
the empty table. A bound at every value of the coins is a bound in the mean.

Main names (namespace OnBytes.WholeKey).
  SideFit, StopsIn   the two new structures of premises: the lengths of what the honest side's
    enumerations hold, AS IT IS HANDED ON (a table's salts cut at its tree's leaves: cutS; the
    compiled runs' coins: dressT, dressL, dressB); each test for a stop returns true only inside the
    set of the same run.
  tabG, det_tabO, det_tabsO, det_linkO, det_linksO, det_commitAt, det_proveAt, det_allY_parts
    values under fixed oracle functions.
  yes_of_not_ev   POINTWISE: outside the event the verifier accepts.
  noCoin_tabO … noCoin_proveAt   the programs behind the coins have no coins.
  OnlyCoins, PrFrom_coins_le, PrFrom_bind_coins_le   a program that samples coins and makes no
    query: a bound at every value that it can return is a bound, in front of a program and behind
    one. (Kin, at another type and without a predicate on the value: Adv.Quiet, Rom/LateAdv.lean.)
  CopyOf, DrawCOf, DrawPOf, onlyCoins_coinsC, onlyCoins_coinsP   what the coins' programs can
    sample.
  fixed_law   at fixed coins.
  complete_argW   THE STATEMENT.

By (through the one import Johnson/Prover/All/Good.lean): all_good · ok_of_not_ev, det_allX,
AccLaws, PrFrom_sample_le, PrFrom_bind_sample_le, noCoin_VRA, noCoin_verifyAll, det_verifyAll_one,
freshAll_empty (Johnson/Prover/All/End.lean) · allY_law, EvY, LawFit, noCoin_allY, noCoin_seedsO
(Johnson/Prover/All/Law.lean) · WiresFit, DrawFit, three_eq_ok, det_committerAtFixedCoins
(Johnson/Prover/All/Yes.lean) · PrFrom_le_of_det (Johnson/Prover/Law/Stages.lean) · PrFrom_bind_le
(Johnson/Prover/Law/Round.lean) · PrFrom_pure (Johnson/Prover/Law/Chain.lean) · noCoin_committerTreeKeptByProver
(Johnson/Prover/CommitterTreeKeptByProver.lean) · noCoin_proveX (OnBytes/Prover/Main.lean) · OComp.bind_assoc
(Rom/Bridge.lean).

WHAT IT DOES NOT SAY. The accept laws and the bounds on the sets' measures are PREMISES (AccLaws):
without them the right side holds five letters. NO FACTOR FOR THE NUMBER OF COPIES: THAT IS A WORD
ON THIS DEFINITION ALONE: one commitment, one request, both fixed before the oracles are sampled.
Under a key whose proof on the first table has stopped, EVERY later request is rejected, and under a
key with stopped links every request at their places: failures under one key are not independent;
nothing here speaks of bad keys (ZKCP.Gen.HasRefinedCompletenessError) or of a second request. Seeds
in Z₁ and Z₂ are not tested by the honest side: they are in the number. No law of an enumeration is
asked: a clause at every listed value. Typed oracles, typed keys and proofs, fixed wires: no hash
function, no bytes, no public reading, no commitment ID. Nothing on argLow. The premises are met
together at a toy (Johnson/WholeKey/CompleteToy.lean); at no intended file. It states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import Johnson.Prover.All.Good
import Rom.Bridge

set_option autoImplicit false

noncomputable section

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-! ## The premises that are new -/

/-- The lengths that the strict format asks of what the honest side's enumerations hold: of the
salts as a table is handed them (cutS); of the compiled runs' coins AS THEY ARE HANDED TO THE RUNS
(dressT, dressL, dressB), at the listed coins of the strategies. -/
structure SideFit (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params)
    (h : HonestSide lam L Bd aT aL) : Prop where
  sl : ∀ a j, j < L.wordLength → (cutS (2 ^ W.depth) (h.sl.e a) j).length = p.sMT
  coT : ∀ a c, (h.dressT (h.rvT (h.kT.e c)) (h.coT.e a)).Fit p.sMT p.sFS
    W.depthReqT
  coL : ∀ a c, (h.dressL (h.rvL (h.kL.e c)) (h.coL.e a)).Fit p.sMT p.sFS
    W.depthReqL
  coB : ∀ a c, (h.dressB (h.rvB (h.kB.e c)) (h.coB.e a)).Fit p.sMT p.sFS
    W.depthReq

/-- Where the honest side stops, the accept laws ask nothing: each test for a stop returns true only
inside the set of the same run. -/
structure StopsIn {KT KL KB : Type} (st : Plays L KT KL KB)
    (Bs : I → L.EncodingRandomness → X → Draw lam L Bd aT aL (KT × KL × KB) → Bads L) : Prop where
  T : ∀ i r₁ x d e ρ, st.stopT i r₁ e ρ = true → ρ ∈ (Bs i r₁ x d).T e
  Lk : ∀ i r₁ x d e e' ρ, st.stopL i (r₁, e) (d.r, e') ρ = true → ρ ∈ (Bs i r₁ x d).Lk e e'
  B : ∀ i r₁ x d e ρ, st.stopB i d.r e x d.n ρ = true → ρ ∈ (Bs i r₁ x d).B e

/-! ## Values under fixed oracle functions -/

theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by
    show (a, f a) :: l.zip (l.map f) = _
    rw [zip_map_self f l]
    rfl

theorem shown_ok {P : Type} {s : Shape} {stop : Rho s → Bool} {a : P × Tr s}
    (h : stop a.2.rho = false) : shown stop (.ok a) = some a.1 := by
  show (if stop a.2.rho then none else some a.1) = _
  rw [h]
  rfl

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (h : HonestSide lam L Bd aT aL)
  (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- a table under g, at the salts as they are handed on -/
def tabG (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) : TabK lam L Bd aT aL :=
  ⟨r, (committerTreeKeptByProver W h.b₀ (L.encodeIndex i r) (cutS (2 ^ W.depth) s)).det g,
    (seedsO W S ((committerTreeKeptByProver W h.b₀ (L.encodeIndex i r) (cutS (2 ^ W.depth) s)).det g).root).det g⟩

theorem det_tabO (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) :
    (tabO W S h.b₀ i r (cutS (2 ^ W.depth) s)).det g = tabG W S h g i r s := by
  unfold tabO tabG
  simp only [OComp.det_bind]
  rfl

theorem det_tabsO (i : I) : ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
    (tabsO W S h i ds).det g = ds.map fun d => tabG W S h g i d.r d.s
  | [] => rfl
  | d :: ds => by
    show ((tabO W S h.b₀ i d.r (cutS (2 ^ W.depth) d.s)).bind fun t =>
      (tabsO W S h i ds).bind fun ts => .pure (t :: ts)).det g = _
    simp only [OComp.det_bind]
    rw [det_tabsO i ds, det_tabO]
    rfl

theorem det_linksO (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (linksO W cA h i t₁ l).det g = l.map fun a => (linkO W cA h i t₁ a.2 a.1).det g
  | [] => rfl
  | a :: l => by
    show ((linkO W cA h i t₁ a.2 a.1).bind fun e =>
      (linksO W cA h i t₁ l).bind fun es => .pure (e :: es)).det g = _
    simp only [OComp.det_bind]
    rw [det_linksO i t₁ l]
    rfl

/-- the committer's values under g -/
theorem det_commitAt (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) :
    (commitAt W S cA h i c).det g =
      (⟨(tabG W S h g i c.r c.s).tree.root, L.recOf i c.r (tabG W S h g i c.r c.s).seed,
        shown (h.st.stopT i c.r (tabG W S h g i c.r c.s).seed)
          ((proveTA W cA (fun _ => (tabG W S h g i c.r c.s).tree)
            (h.dressT (h.rvT c.κ) c.co) h.capT
            (tabG W S h g i c.r c.s).tree.root (L.recOf i c.r (tabG W S h g i c.r c.s).seed)
            (L.encodeIndex i c.r) (h.st.T i c.r (tabG W S h g i c.r c.s).seed c.κ)).det g),
        c.copies.map fun e =>
          (linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g⟩,
       ⟨i, c.copies.map fun e => tabG W S h g i e.r e.s⟩) := by
  unfold commitAt
  simp only [OComp.det_bind]
  rw [det_tabO, det_tabsO, det_linksO, zip_map_self, List.map_map]
  rfl

/-- the runs of the prover of a whole request under g, part by part -/
theorem det_allY_parts (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X)
    (d : Draw lam L Bd aT aL (h.KT × h.KL × h.KB)) (s₂ : ℕ → Bits)
    (hs : d.s = cutS (2 ^ W.depth) s₂) :
    (allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, r₁, cutS (2 ^ W.depth) s₁) x
      d).det g =
      (((tabG W S h g i r₁ s₁).tree.root, (tabG W S h g i d.r s₂).tree.root),
        (tabG W S h g i r₁ s₁).seed, (tabG W S h g i d.r s₂).seed,
        (proveTA W cA (fun _ => (tabG W S h g i r₁ s₁).tree) d.coT h.capT
          (tabG W S h g i r₁ s₁).tree.root (L.recOf i r₁ (tabG W S h g i r₁ s₁).seed)
          (L.encodeIndex i r₁) (h.st.T i r₁ (tabG W S h g i r₁ s₁).seed d.κ.1)).det g,
        (proveLA W cA (fun k => if k = 0 then (tabG W S h g i r₁ s₁).tree
            else (tabG W S h g i d.r s₂).tree) d.coL h.capL (tabG W S h g i r₁ s₁).tree.root
          (tabG W S h g i d.r s₂).tree.root (L.recOf i r₁ (tabG W S h g i r₁ s₁).seed)
          (L.recOf i d.r (tabG W S h g i d.r s₂).seed) (L.encodeIndex i r₁, L.encodeIndex i d.r)
          (h.st.Lk i (r₁, (tabG W S h g i r₁ s₁).seed) (d.r, (tabG W S h g i d.r s₂).seed)
            d.κ.2.1)).det g,
        (proveBA W cA r₀ (fun _ => (tabG W S h g i d.r s₂).tree) d.coB h.capB
          (tabG W S h g i d.r s₂).tree.root x (L.recOf i d.r (tabG W S h g i d.r s₂).seed)
          (L.encodeIndex i d.r) (h.st.B i d.r (tabG W S h g i d.r s₂).seed x d.n d.κ.2.2)).det g) := by
  obtain ⟨r, s, n, κ, a, b, c⟩ := d
  obtain rfl : s = cutS (2 ^ W.depth) s₂ := hs
  unfold allY
  simp only [OComp.det_bind]
  rfl

theorem det_linkO (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (e : DrawCopy lam L Bd aT aL h.KL) :
    (linkO W cA h i t₁ t₂ e).det g =
      (t₂.tree.root, L.recOf i t₂.r t₂.seed,
        shown (h.st.stopL i (t₁.r, t₁.seed) (t₂.r, t₂.seed))
          ((proveLA W cA (fun k => if k = 0 then t₁.tree else t₂.tree)
            (h.dressL (h.rvL e.κ) e.co) h.capL t₁.tree.root t₂.tree.root
            (L.recOf i t₁.r t₁.seed) (L.recOf i t₂.r t₂.seed)
            (L.encodeIndex i t₁.r, L.encodeIndex i t₂.r)
            (h.st.Lk i (t₁.r, t₁.seed) (t₂.r, t₂.seed) e.κ)).det g)) := by
  unfold linkO
  simp only [OComp.det_bind]
  rfl

theorem det_proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB)
    (t : TabK lam L Bd aT aL) (ht : isk.copies[d.j]? = some t) :
    (proveAt W cA r₀ h isk x d).det g =
      ⟨d.j, h.nm d.j, shown (h.st.stopB isk.i t.r t.seed x (h.nm d.j))
        ((proveBA W cA r₀ (fun _ => t.tree) (h.dressB (h.rvB d.κ) d.co) h.capB
          t.tree.root x (L.recOf isk.i t.r t.seed) (L.encodeIndex isk.i t.r)
          (h.st.B isk.i t.r t.seed x (h.nm d.j) d.κ)).det g)⟩ := by
  unfold proveAt
  rw [ht]
  simp only [OComp.det_bind]
  rfl

/-- **Pointwise: outside the event of the prover of a whole request, at the sample that the coins
make up, the verifier accepts the whole key and the proof.** -/
theorem yes_of_not_ev (hW : WiresFit W cA) (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB)
    (hj : c.copies[dP.j]? = some e) (l₁ : ∀ j, j < L.wordLength → (cutS (2 ^ W.depth) c.s j).length = p.sMT)
    (hd : DrawFit W p (drawOf W h c e dP)) (Bs : Bads L)
    (acc : AccAt W S h.st.joint i c.r x (drawOf W h c e dP) Bs)
    (sT : ∀ e₁ ρ, h.st.stopT i c.r e₁ ρ = true → ρ ∈ Bs.T e₁)
    (sL : ∀ e₁ e₂ ρ, h.st.stopL i (c.r, e₁) (e.r, e₂) ρ = true → ρ ∈ Bs.Lk e₁ e₂)
    (sB : ∀ e₂ ρ, h.st.stopB i e.r e₂ x (h.nm dP.j) ρ = true → ρ ∈ Bs.B e₂)
    (hn : (allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c e dP)).det g ∉ EvY Bs) :
    (verifyW W S cA r₀ p ((commitAt W S cA h i c).det g).1 x
      ((proveAt W cA r₀ h ((commitAt W S cA h i c).det g).2 x dP).det g)).det g = true := by
  obtain ⟨π, e₁, e₂, τT, τL, τB, hx, -, -, h3, h4, h5⟩ :=
    ok_of_not_ev W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB g hW
      (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c e dP) Bs hn
  obtain ⟨π', e₁', e₂', τT', τL', τB', hx', -, -, -, -, -, hy⟩ :=
    all_good W S cA r₀ p h.b₀ h.st.joint h.capT h.capL h.capB g hW i c.r
      (cutS (2 ^ W.depth) c.s) x
      (drawOf W h c e dP) l₁ hd Bs acc hn
  obtain rfl : π' = π := by
    have := hx'.symm.trans hx
    exact congrArg Prod.fst (Res.ok.inj this)
  rw [det_allX, det_allY_parts W S cA r₀ h g i c.r c.s x _ e.s rfl] at hx
  obtain ⟨a, b, c', ha, hb, hc, hz⟩ := three_eq_ok hx
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ : π' = _ ∧ e₁ = _ ∧ e₂ = _ ∧ τT = _ ∧ τL = _ ∧ τB = _ :=
    ⟨congrArg Prod.fst hz, congrArg (·.2.1) hz, congrArg (·.2.2.1) hz, congrArg (·.2.2.2.1) hz,
      congrArg (·.2.2.2.2.1) hz, congrArg (·.2.2.2.2.2) hz⟩
  have ft : ((commitAt W S cA h i c).det g).2.copies[dP.j]? = some (tabG W S h g i e.r e.s) := by
    rw [det_commitAt]
    show (c.copies.map fun e => tabG W S h g i e.r e.s)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  have fl : ((commitAt W S cA h i c).det g).1.links[dP.j]? =
      some ((linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g) := by
    rw [det_commitAt]
    show (c.copies.map fun e =>
      (linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  have hk : lowKey ((commitAt W S cA h i c).det g).1 =
      ((committerAtFixedCoins W S h.b₀ i c.r (cutS (2 ^ W.depth) c.s)).det g).1 := by
    rw [det_commitAt, det_committerAtFixedCoins]
    rfl
  have pT : ((commitAt W S cA h i c).det g).1.piT = some a.1 := by
    rw [det_commitAt]
    exact (congrArg (shown (h.st.stopT i c.r (tabG W S h g i c.r c.s).seed)) ha).trans
      (shown_ok (Bool.eq_false_iff.2 fun hs => h3 (sT _ _ hs)))
  have pL : (linkO W cA h i (tabG W S h g i c.r c.s) (tabG W S h g i e.r e.s) e).det g =
      ((tabG W S h g i e.r e.s).tree.root, L.recOf i e.r (tabG W S h g i e.r e.s).seed,
        some b.1) := by
    rw [det_linkO]
    exact congrArg (fun z => ((tabG W S h g i e.r e.s).tree.root,
      L.recOf i e.r (tabG W S h g i e.r e.s).seed, z))
      ((congrArg (shown (h.st.stopL i (c.r, (tabG W S h g i c.r c.s).seed)
        (e.r, (tabG W S h g i e.r e.s).seed))) hb).trans
        (shown_ok (Bool.eq_false_iff.2 fun hs => h4 (sL _ _ _ hs))))
  have pB : shown (h.st.stopB i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j))
      ((proveBA W cA r₀ (fun _ => (tabG W S h g i e.r e.s).tree)
        (h.dressB (h.rvB dP.κ) dP.co) h.capB
        (tabG W S h g i e.r e.s).tree.root x (L.recOf i e.r (tabG W S h g i e.r e.s).seed)
        (L.encodeIndex i e.r) (h.st.B i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j) dP.κ)).det g) =
      some c'.1 :=
    (congrArg (shown (h.st.stopB i e.r (tabG W S h g i e.r e.s).seed x (h.nm dP.j))) hc).trans
      (shown_ok (Bool.eq_false_iff.2 fun hs => h5 (sB _ _ hs)))
  have hi : ((commitAt W S cA h i c).det g).2.i = i := by
    rw [det_commitAt]
  rw [det_proveAt W cA r₀ h g _ x dP _ ft, hi]
  unfold verifyW lowPrf
  dsimp only
  rw [hk, pT, fl, Option.getD_some, pL]
  refine Eq.trans (congrArg (fun z => (verifyAtKeyRoot W S cA r₀ p
    ((committerAtFixedCoins W S h.b₀ i c.r (cutS (2 ^ W.depth) c.s)).det g).1 x
    ⟨h.nm dP.j, some a.1, ((tabG W S h g i e.r e.s).tree.root,
      L.recOf i e.r (tabG W S h g i e.r e.s).seed, some b.1), z⟩).det g) pB) ?_
  exact hy

/-! ## The programs behind the coins have no coins -/

theorem noCoin_tabO (i : I) (r : L.EncodingRandomness) (s : ℕ → Bits) : (tabO W S h.b₀ i r s).NoCoin :=
  (noCoin_committerTreeKeptByProver W h.b₀ _ _).bind fun _ => (noCoin_seedsO W S _).bind fun _ => trivial

theorem noCoin_tabsO (i : I) : ∀ ds : List (DrawCopy lam L Bd aT aL h.KL),
    (tabsO W S h i ds).NoCoin
  | [] => trivial
  | d :: ds => (noCoin_tabO W S h i d.r _).bind fun _ =>
      (noCoin_tabsO i ds).bind fun _ => trivial

theorem noCoin_linkO (i : I) (t₁ t₂ : TabK lam L Bd aT aL) (e : DrawCopy lam L Bd aT aL h.KL) :
    (linkO W cA h i t₁ t₂ e).NoCoin :=
  (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

theorem noCoin_linksO (i : I) (t₁ : TabK lam L Bd aT aL) :
    ∀ l : List (DrawCopy lam L Bd aT aL h.KL × TabK lam L Bd aT aL),
      (linksO W cA h i t₁ l).NoCoin
  | [] => trivial
  | a :: l => (noCoin_linkO W cA h i t₁ a.2 a.1).bind fun _ =>
      (noCoin_linksO i t₁ l).bind fun _ => trivial

theorem noCoin_commitAt (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) :
    (commitAt W S cA h i c).NoCoin :=
  (noCoin_tabO W S h i c.r _).bind fun _ => (noCoin_tabsO W S h i _).bind fun _ =>
    (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ =>
      (noCoin_linksO W cA h i _ _).bind fun _ => trivial

theorem noCoin_proveAt (isk : Isk lam L Bd aT aL) (x : X) (d : DrawP lam L Bd aT aL h.KB) :
    (proveAt W cA r₀ h isk x d).NoCoin := by
  unfold proveAt
  split
  · trivial
  · exact (noCoin_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

/-! ## A program that samples coins and makes no query -/

/-- The program queries no oracle, and every value that it can return has the property P. -/
def OnlyCoins {S' : OSpec} {γ : Type} (P : γ → Prop) : OComp S' γ → Prop
  | .pure a => P a
  | .sample _ k => ∀ r, OnlyCoins P (k r)
  | .query _ _ _ => False

theorem OnlyCoins.bind {S' : OSpec} {γ δ : Type} {P : γ → Prop} {Q : δ → Prop} :
    ∀ {c : OComp S' γ} {f : γ → OComp S' δ}, OnlyCoins P c → (∀ a, P a → OnlyCoins Q (f a)) →
      OnlyCoins Q (c.bind f)
  | .pure a, _, hc, hf => hf a hc
  | .sample _ _, _, hc, hf => fun r => OnlyCoins.bind (hc r) hf
  | .query _ _ _, _, hc, _ => hc.elim

/-- In front: a bound at every value that can be sampled is a bound. -/
theorem PrFrom_coins_le {S' : OSpec} {γ β : Type} {P : γ → Prop} (T : Table S')
    (k : γ → OComp S' β) (E : Set β) {ε : ℝ≥0∞} (hk : ∀ a, P a → PrFrom T (k a) E ≤ ε) :
    ∀ c : OComp S' γ, OnlyCoins P c → PrFrom T (c.bind k) E ≤ ε
  | .pure a, hc => hk a hc
  | .sample n kk, hc => PrFrom_sample_le T n _ E fun r => PrFrom_coins_le T k E hk (kk r) (hc r)
  | .query _ _ _, hc => hc.elim

/-- Behind a program: the same. -/
theorem PrFrom_bind_coins_le {S' : OSpec} {α γ β : Type} {P : γ → Prop} (T : Table S')
    (c₀ : OComp S' α) (R : α → γ → OComp S' β) (E : Set β) {ε : ℝ≥0∞}
    (hR : ∀ a, P a → PrFrom T (c₀.bind fun k => R k a) E ≤ ε) :
    ∀ c : OComp S' γ, OnlyCoins P c → PrFrom T (c₀.bind fun k => c.bind (R k)) E ≤ ε
  | .pure a, hc => hR a hc
  | .sample n kk, hc => PrFrom_bind_sample_le T c₀ n (fun k r => (kk r).bind (R k)) E fun r =>
      PrFrom_bind_coins_le T c₀ R E hR (kk r) (hc r)
  | .query _ _ _, hc => hc.elim

/-! ## What the coins' programs can sample -/

/-- a copy's coins hold enumerated values -/
def CopyOf (d : DrawCopy lam L Bd aT aL h.KL) : Prop :=
  (∃ b, d.s = h.sl.e b) ∧ ∃ e c, d.co = h.coL.e e ∧ d.κ = h.kL.e c

theorem onlyCoins_coinsCopy : OnlyCoins (CopyOf h) (coinsCopy W h) :=
  fun _ b c e => ⟨⟨b, rfl⟩, ⟨e, c, rfl, rfl⟩⟩

theorem onlyCoins_coinsCopies : ∀ n : ℕ,
    OnlyCoins (fun ds => ds.length = n ∧ ∀ d ∈ ds, CopyOf h d) (coinsCopies W h n)
  | 0 => ⟨rfl, fun _ hd => absurd hd (List.not_mem_nil)⟩
  | n + 1 => OnlyCoins.bind (onlyCoins_coinsCopy W h) fun d hd =>
      OnlyCoins.bind (onlyCoins_coinsCopies n) fun ds hds =>
        (⟨congrArg (· + 1) hds.1, fun d' hd' => by
          rcases List.mem_cons.1 hd' with rfl | h'
          · exact hd
          · exact hds.2 d' h'⟩ : (d :: ds).length = n + 1 ∧ ∀ d' ∈ d :: ds, CopyOf h d')

/-- the committer's coins hold enumerated values, and one entry for each of the M + 1 copies -/
def DrawCOf (c : DrawC lam L Bd aT aL h.KT h.KL) : Prop :=
  (∃ b, c.s = h.sl.e b) ∧ (∃ e k, c.co = h.coT.e e ∧ c.κ = h.kT.e k) ∧
    c.copies.length = h.M + 1 ∧
    ∀ d ∈ c.copies, CopyOf h d

theorem onlyCoins_coinsC : OnlyCoins (DrawCOf h) (coinsC W h) :=
  fun _ b k e => OnlyCoins.bind (onlyCoins_coinsCopies W h (h.M + 1)) fun _ hds =>
    (⟨⟨b, rfl⟩, ⟨e, k, rfl, rfl⟩, hds.1, hds.2⟩ : DrawCOf h ⟨_, _, _, _, _⟩)

/-- the prover's coins: a place among the M + 1; an enumerated value -/
def DrawPOf (d : DrawP lam L Bd aT aL h.KB) : Prop :=
  d.j < h.M + 1 ∧ ∃ e c, d.co = h.coB.e e ∧ d.κ = h.kB.e c

theorem onlyCoins_coinsP : OnlyCoins (DrawPOf h) (coinsP W h) :=
  fun j c e => ⟨j.isLt, ⟨e, c, rfl, rfl⟩⟩

/-! ## The end -/

/-- **At fixed coins**: committer, prover, verifier: the verifier rejects with probability at most
the number of the prover of a whole request. -/
theorem fixed_law (Yes : I → X → Prop)
    (Bs : I → L.EncodingRandomness → X → Draw lam L Bd aT aL (h.KT × h.KL × h.KB) → Bads L)
    {ζ₁ ζ₂ δT δL δB : ℝ≥0∞} (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA)
    (hF : SideFit W p h) (acc : AccLaws W S h.st.joint Yes Bs ζ₁ ζ₂ δT δL δB) (hS : StopsIn h.st Bs)
    (i : I) (x : X) (hY : Yes i x) (c : DrawC lam L Bd aT aL h.KT h.KL) (hc : DrawCOf h c)
    (dP : DrawP lam L Bd aT aL h.KB) (hd : DrawPOf h dP) :
    PrFrom (Table.empty _) ((commitAt W S cA h i c).bind fun key =>
      (proveAt W cA r₀ h key.2 x dP).bind fun π => verifyW W S cA r₀ p key.1 x π)
      {b | b = false} ≤ alphaAll W h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB := by
  obtain ⟨⟨b₁, hs₁⟩, ⟨a₁, k₁, hco₁, hk₁⟩, hlen, hcop⟩ := hc
  obtain ⟨hj, ⟨a₃, k₃, hco₃, hk₃⟩⟩ := hd
  have hj' : dP.j < c.copies.length := by rw [hlen]; exact hj
  have he : c.copies[dP.j]? = some c.copies[dP.j] := List.getElem?_eq_getElem hj'
  obtain ⟨⟨b₂, hs₂⟩, ⟨a₂, k₂, hco₂, hk₂⟩⟩ := hcop _ (List.getElem_mem hj')
  have hD : DrawFit W p (drawOf W h c c.copies[dP.j] dP) :=
    ⟨fun j hjn => by
        show (cutS (2 ^ W.depth) (c.copies[dP.j]).s j).length = _
        rw [hs₂]
        exact hF.sl b₂ j hjn,
      by
        show (h.dressT (h.rvT c.κ) c.co).Fit _ _ _
        rw [hco₁, hk₁]
        exact hF.coT a₁ k₁,
      by
        show (h.dressL (h.rvL (c.copies[dP.j]).κ) (c.copies[dP.j]).co).Fit _ _ _
        rw [hco₂, hk₂]
        exact hF.coL a₂ k₂,
      by
        show (h.dressB (h.rvB dP.κ) dP.co).Fit _ _ _
        rw [hco₃, hk₃]
        exact hF.coB a₃ k₃⟩
  refine (PrFrom_le_of_det
    (E' := EvY (Bs i c.r x (drawOf W h c c.copies[dP.j] dP))) ?_
    (noCoin_allY W S cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c c.copies[dP.j] dP)) _ fun g hg => ?_).trans
    (allY_law cA r₀ h.b₀ h.st.joint h.capT h.capL h.capB (freshAll_empty W S) hL
      (i, c.r, cutS (2 ^ W.depth) c.s) x
      (drawOf W h c c.copies[dP.j] dP) _ (acc.small i c.r x _ hY))
  · exact (noCoin_commitAt W S cA h i c).bind fun key =>
      (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun π => noCoin_VRA W S cA r₀ p _ _ _
  · by_contra hn
    have hy := yes_of_not_ev W S cA r₀ p h g hW i x c c.copies[dP.j] dP he
      (fun j hjn => by rw [hs₁]; exact hF.sl b₁ j hjn) hD _ (acc.acc i c.r x _ hY)
      (fun e₁ ρ => hS.T i c.r x (drawOf W h c c.copies[dP.j] dP) e₁ ρ)
      (fun e₁ e₂ ρ => hS.Lk i c.r x (drawOf W h c c.copies[dP.j] dP) e₁ e₂ ρ)
      (fun e₂ ρ => hS.B i c.r x (drawOf W h c c.copies[dP.j] dP) e₂ ρ) hn
    have hg' : OComp.det g _ = false := hg
    simp only [OComp.det_bind] at hg'
    rw [hy] at hg'
    cases hg'

/-- **COMPLETENESS OF THE SCHEME WITH THE WHOLE KEY**, from named premises, in the form of the
library's definition over typed oracles, for batches of at most one request. -/
theorem complete_argW (Yes : I → X → Prop)
    (Bs : I → L.EncodingRandomness → X → Draw lam L Bd aT aL (h.KT × h.KL × h.KB) → Bads L)
    {ζ₁ ζ₂ δT δL δB : ℝ≥0∞} (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA)
    (hF : SideFit W p h) (acc : AccLaws W S h.st.joint Yes Bs ζ₁ ζ₂ δT δL δB)
    (hS : StopsIn h.st Bs) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (argW W S cA r₀ p h) 1 (alphaAll W h.capT h.capL h.capB ζ₁ ζ₂ δT δL δB) := by
  intro i b hb
  show PrFrom (Table.empty _) _ {c | c = false} ≤ _
  match b, hb with
  | [], _ =>
    refine le_of_eq_of_le ?_ (zero_le _)
    refine le_antisymm (PrFrom_bind_le _ _ _ _ fun out _ => ?_) (zero_le _)
    exact le_of_eq (PrFrom_pure _ true _ (by intro h; cases h))
  | [(x, u)], hb =>
    have hY : Yes i x := hb.2 (x, u) (by simp)
    show PrFrom _ (((coinsC W h).bind fun d => commitAt W S cA h i d).bind fun key =>
      ((coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π =>
        (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof lam L) [(x, u)]))).bind fun πs =>
          ZKCP.Gen.verifyAll (argW W S cA r₀ p h) key.1 (([(x, u)].map Prod.fst).zip πs.val)) _ ≤ _
    simp only [OComp.bind_assoc]
    refine PrFrom_coins_le _ _ _ (fun c hc => ?_) _ (onlyCoins_coinsC W h)
    refine PrFrom_bind_coins_le _ (commitAt W S cA h i c) _ _ (fun dP hdP => ?_) _
      (onlyCoins_coinsP W h)
    refine (PrFrom_le_of_det (E' := {b | b = false}) ?_ ?_ _ fun g hg => ?_).trans
      (fixed_law W S cA r₀ p h Yes Bs hL hW hF acc hS i x hY c hc dP hdP)
    · exact (noCoin_commitAt W S cA h i c).bind fun key =>
        (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun π =>
          noCoin_verifyAll _ (fun k x π => noCoin_VRA W S cA r₀ p _ _ _) _ _
    · exact (noCoin_commitAt W S cA h i c).bind fun key =>
        (noCoin_proveAt W cA r₀ h key.2 x dP).bind fun π => noCoin_VRA W S cA r₀ p _ _ _
    · have h1 : OComp.det g _ = false := hg
      simp only [OComp.det_bind] at h1
      change (ZKCP.Gen.verifyAll _ _ [(x, _)]).det g = false at h1
      rw [det_verifyAll_one, Bool.and_true] at h1
      show OComp.det g _ = false
      simp only [OComp.det_bind]
      exact h1
  | _ :: _ :: _, hb => exact absurd hb.1 (by simp)

end OnBytes.WholeKey
