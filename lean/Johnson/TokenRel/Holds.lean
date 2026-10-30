-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Holds.lean: THE INVARIANT THAT THE RULE OF RELEASE LIVES ON, and that it is kept:
at the start, by a query of the adversary, by the making of a table, by a compiled run. DEFINITIONS,
STATEMENTS AND THEIR PROOFS.

General statements. This file states no goal of the release. The token programs are a device of one
step of a proof of index privacy and stand in no statement on the scheme.

The rule of release (Spec.release, Johnson/TokenRules/ReleaseSpec.lean) asks of the state before a
compiled run: it is well formed (TidyO); the point of each released evaluation has an entry in the
table (Laid); each tree over an external string can be shown leaf by leaf (TreeOKT) and has, for
each leaf, just one evaluation, at the leaf's input and with the leaf's digest (LeafAt).

  Holds Rl preE D Ts   all this of the state D and the trees of the list Ts.

In the mode in which marked evaluations are deferred, on supports:
  Spec.holdsStart   it holds of the first state and no tree;
  Spec.holdsAsk     a query of the adversary that writes a new entry keeps it;
  Spec.holdsTab     the making of a table keeps it and adds the table's tree, which has 2 ^ depth
                    leaves;
  Spec.holdsRun     a compiled run on trees of the list keeps it, whatever its outcome.
The rules' part of holdsRun is Spec.safeProveC (Johnson/TokenRules/EndC.lean), called.
Members: Johnson/TokenRel/HoldsMembers.lean [not in this library]; for the rule's live case,
Johnson/TokenRel/ReleaseMember.lean.

-/
import Johnson.TokenRel.Release
import Johnson.TokenRules.EndC
import Johnson.TokenRel.Rules

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

/-- See the head. -/
def Holds {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (Rl : Rules (typedOracleFamily lam K L)) (preE : Bits)
    (D : DSt (typedOracleFamily lam K L)) (Ts : List (TreeT lam L)) : Prop :=
  TidyO Rl D ∧ Laid D ∧ ∀ T ∈ Ts, TreeOKT D [] T ∧ LeafAt D T preE

namespace Spec

def holdsStart : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (Rl : Rules (typedOracleFamily lam K L)) (preE : Bits),
    Holds Rl preE (DSt.init _) []

def holdsAsk : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (Rl : Rules (typedOracleFamily lam K L)) (preE : Bits)
      (D : DSt (typedOracleFamily lam K L)) (Ts : List (TreeT lam L)) (o : OracleName) (q : (typedOracleFamily lam K L).Dom o)
      (r : (typedOracleFamily lam K L).Rng o),
    Holds Rl preE D Ts → D.table o q = none →
    Holds Rl preE { D with table := D.table.set o q r } Ts

def holdsTab : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)
      (bl bf : ℕ) (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (D : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
      (Ts : List (TreeT lam (typedOracleCarrier L Bd aT aL))),
    bl ≤ tl.frE →
    Holds (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) tl.preE D Ts →
    ∀ v ∈ ((tabT W S h tl b₀ i r).run true D).support,
      Holds (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) tl.preE v.2
        (v.1.tree :: Ts) ∧ v.1.tree.tok.length = 2 ^ W.depth

def holdsRun : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (bl bf : ℕ) (sd : (t : Tag) → FbIn lam L t → Prop)
      (t : Tag) (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeT lam L) (preE : Bits)
      (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits)
      (cap : ℕ → ℕ) (stop : Rho Q.loc.shape → Bool) (D : DSt (typedOracleFamily lam K L))
      (Ts : List (TreeT lam L)),
    bl ≤ ln.fr → bf ≤ ln.sFS → bf ≤ lam →
    Holds (rulesT K L lam bl bf sd) preE D Ts → (∀ k, xt k ∈ Ts) →
    ∀ v ∈ ((proveC t Q wq embS embP xin cms x y xt preE σ ln pre cap stop).run true D).support,
      Holds (rulesT K L lam bl bf sd) preE v.2 Ts

end Spec

theorem holdsStart : Spec.holdsStart := fun _ _ _ _ _ _ _ =>
  ⟨TidyO.init, laid_init _, fun _ h => absurd h List.not_mem_nil⟩

theorem holdsAsk : Spec.holdsAsk := by
  intro I X lam K L Rl preE D Ts o q r h hn
  refine ⟨h.1.table _, Laid.table h.2.1 rfl fun o' q' h' => ?_, h.2.2⟩
  show D.table.set o q r o' q' ≠ none
  rw [← Table.lay1_of_none hn r]
  exact lay_ne_none (l := [⟨o, q, r⟩]) h'

/-! ## A table -/

section Table
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)

theorem safe_tabT {bl bf : ℕ} (hbl : bl ≤ tl.frE) (b₀ : Bd) (i : I) (r : L.EncodingRandomness)
    {d : DSt (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hd : TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d) :
    SafeO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) (tabT W S h tl b₀ i r) d
      fun t d' =>
      TidyO (rulesT W.K (typedOracleCarrier L Bd aT aL) lam bl bf (seedPts W S)) d' ∧
      Charges noTok d d' ∧ Adds (NewLeaf d.vals.length) d d' ∧ TreeOKT d' [] t.tree ∧
      LeafAt d' t.tree tl.preE ∧ t.tree.tok.length = 2 ^ W.depth := by
  unfold tabT
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_treeT hbl [] (fun _ => tl.preE) W.depth _ hd
    fun _ h => absurd h List.not_mem_nil))
  rintro T d₁ ⟨hd₁, hr₁, _, hT, _, ha₁, hL, hlen⟩
  refine SafeO.bind _ _ d₁ ?_
  refine ⟨Or.inl ⟨_, rfl⟩, fun a0 T₁ => ⟨Or.inr ⟨_, rfl⟩, fun a1 T₂ => ?_⟩⟩
  have c1 := (run_ofPlain (Cc := noTok) (Ch := noTok) (R := noTok) (M := zr) d₁ (OracleName.fb S.t)
    T₁).charges
  have c2 := (run_ofPlain (Cc := noTok) (Ch := noTok) (R := noTok) (M := zr)
    (afterPlain d₁ (OracleName.fb S.t) T₁) (OracleName.fb S.t) T₂).charges
  have c12 := c1.trans c2 fun _ h => Or.inl h
  have a12 : Adds (NewLeaf d.vals.length) d₁ (afterPlain (afterPlain d₁ (OracleName.fb S.t) T₁)
      (OracleName.fb S.t) T₂) := (Adds.ofPlain _ d₁ _ T₁).trans (Adds.ofPlain _ _ _ T₂)
  exact ⟨(hd₁.plain _ T₁).plain _ T₂, hr₁.charges.trans c12 fun _ h => Or.inl h, ha₁.trans a12,
    TreeOKT.keeps hT c12 fun _ _ h => h,
    LeafAt.adds hL (fun u hu => TreeOKT.lt hT hu) c12.vals
      ((Adds.ofPlain (fun _ => False) d₁ _ T₁).trans (Adds.ofPlain _ _ _ T₂)) fun _ h => h.elim,
    hlen⟩

end Table

theorem holdsTab : Spec.holdsTab := by
  intro I X lam L Bd aT aL W S h tl bl bf b₀ i r D Ts hbl hH v hv
  obtain ⟨hd', hc, ha, hT, hL, hlen⟩ := safeRunO _ _ _ _ _ _ _ true
    (safe_tabT W S h tl hbl b₀ i r hH.1) v hv
  refine ⟨⟨hd', laid_run _ D hH.2.1 v hv, fun T hT' => ?_⟩, hlen⟩
  rcases List.mem_cons.mp hT' with rfl | hT'
  · exact ⟨hT, hL⟩
  · obtain ⟨h1, h2⟩ := hH.2.2 T hT'
    exact ⟨TreeOKT.keeps h1 hc fun _ _ h => h,
      LeafAt.adds h2 (fun u hu => TreeOKT.lt h1 hu) hc.vals ha fun e he hcc =>
        absurd (TreeOKT.lt h1 hcc) (Nat.not_lt.mpr he.2)⟩

theorem holdsRun : Spec.holdsRun := by
  intro I X lam K L bl bf sd t Y E Q wq embS embP xin cms x y xt preE σ ln pre cap stop D Ts hbl hbf
    hlam hH hxt v hv
  obtain ⟨hd', hg⟩ := safeRunO _ _ _ _ _ _ _ true
    (safeProveC safeChain I X lam K L bl bf sd t Y E Q wq embS embP xin cms x y xt preE σ ln pre cap
      stop D hbl hbf hlam hH.1 fun k => (hH.2.2 _ (hxt k)).1) v hv
  refine ⟨hd', laid_run _ D hH.2.1 v hv, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hH.2.2 T hT
  refine ⟨TreeOKT.keeps h1 hg.charges fun _ _ h => h, ?_⟩
  unfold proveC at hv
  rw [Life2.run_bind, PMF.mem_support_bind_iff] at hv
  obtain ⟨⟨a, D₁⟩, hm, hv⟩ := hv
  obtain ⟨_, hg₁, _, hadd, _⟩ := safeRunO _ _ _ _ _ _ _ true
    (safe_hashT t Q wq embS embP xin cms x σ ln pre cap D hbl hbf hlam hH.1) (a, D₁) hm
  exact endC_leafAt Q wq x y xt preE pre stop a D₁ v hv
    (LeafAt.adds h2 (fun u hu => TreeOKT.lt h1 hu) hg₁.vals hadd fun e he hc =>
      absurd (TreeOKT.lt h1 hc) (Nat.not_lt.mpr he))

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.holdsStart
#print axioms OnBytes.TokenRel.holdsAsk
#print axioms OnBytes.TokenRel.holdsTab
#print axioms OnBytes.TokenRel.holdsRun
