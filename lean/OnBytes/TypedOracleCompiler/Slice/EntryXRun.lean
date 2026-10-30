-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean: what the entry's judge hands to the join and to a yes: from its
language to the join's language of the entry; the two records in what a checker returns; and: its
comparisons say yes under the family read out of an oracle EXACTLY IF both seeds in its instance are
the seeds under that oracle, under a law on a page.

Main definitions.
 `LXEs`                 the interface of the entry's frame at the seeds' protocol.
 `recE₀`, `recE₁`       THE FIRST TABLE'S AND THE COPY'S RECORD IN WHAT THE ENTRY'S CHECKER RETURNS.
Main theorems.
 `langE_of_judgeE`, `langE_of_judgeE_out`   FROM THE LANGUAGE OF `judgeE` AT THE RECORD'S TERMS, in
                        the form of the language of a part over the one oracle, TO `DecR.LangE` AT
                        `wayColl`, at the two records that stand in the instance; the second in the
                        letters in which the join asks it.
 `cmpT_det_true`, `cmpT_det_of`, `judgeRunE_det`, `judgeRunEL_det`   the comparisons, both ways, and
                        the judge's run, with and without the test of the strict format, under a
                        family F of oracle functions; general, as OnBytes/TypedOracleCompiler/Slice/JudgeE.lean.
 `seedUnder_of_blocks_of`   `seedUnder_of_blocks` (OnBytes/Slice/SeedDrawn.lean) in a field that is
                        the second.
 `entry_chain_seed`     under `SeedsPage` (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean), what the seeds'
                        chain yields under one root, in the family read out of g, is the seed under
                        g. By `chainAt_seeds_det` (OnBytes/TypedOracleCompiler/Slice/SeedsRun.lean).
 `entry_run_seeds`      IF THE ENTRY'S JUDGE'S RUN SAYS YES UNDER THE FAMILY READ OUT OF g, BOTH
                        SEEDS IN ITS INSTANCE ARE THE SEEDS UNDER g.
 `entry_cmp_yes`        THE CONVERSE, WHICH `fit` WANTS: if both are, the comparisons say yes.
 `Part.on_chk_of_eq`, `Part.on_chk_self`   for the sibling's parts: a checker that is answered by a
                        table with g's own values has under g the value of the part's own checker
                        (the like of OnBytes/Slice/OverSelf.lean). At tables that are cut to the
                        public strings the first is the one that serves.

Asked by `entry_run_seeds` and `entry_cmp_yes`: the description's field is the second; 0 < s; enough
blocks; two outer roots; the implementation obeys `SeedsPage` at the name of a key k₀ under the
first root and at the name of a key k₁ under the second.

Not claimed. NO IMPLEMENTATION IS SHOWN TO OBEY `SeedsPage`: no page with the seeds' tag is written.
That the roots are the keys' roots: `SeedsPage` names a key's name and a root side by side, and
whoever gives a page ties them; a key's root is a byte string and an output's a digest: that the one
is the other's bytes wants 32 bytes. The answers of the two records: nothing here. The compiled
verifier's half of `fit`: nothing here. That the judge ever says yes. NOTHING ON SOUNDNESS IS SHOWN;
no probability. What the heads of EntryXJudge.lean, SeedsBridge.lean and SeedsRun.lean do not claim.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryXJudge
import OnBytes.TypedOracleCompiler.Slice.SeedsRun
import OnBytes.TypedOracleCompiler.Slice.PartOn
import OnBytes.Slice.OverSelf

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open _root_.Run.PQ (View SgX)
open _root_.Run (ckP chalP digToBytes bytesToBits oB)
open OnBytes.Slice (DecR decRec seedBS seedOfDrawn roundDraws GE NZ seedEntry dsOf_seedEntry
  seedUnder seedUnder_of_blocks rawOf Raw blockStr seedFirst)
open scoped ENNReal

/-! ## From the judge's language to the join's -/

section
variable {An : Type} (T : _root_.Fmt.M1.Code) (v eM lg s : ℕ) (D : XD)

/-- From the language of `judgeE` at the record's terms, in the form of the language of a part
over the one oracle, to the join's language of the entry (`DecR.LangE` at `wayColl`), at the two
records that stand in the instance. The test is used at the COPY alone. -/
theorem langE_of_judgeE (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)
    (x : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ)))
    (Y₀ Y₁ : Raw SgX)
    (h : ∃ ys : List (Fin (2 ^ D.a) → SgX), [Y₀, Y₁] = ys.map (rawOf (Equiv.refl _)) ∧
      ∀ f : ℕ → Fin (2 ^ D.a) → SgX, (∀ i, i < 2 → ys[i]? = some (f i)) →
        lgEX T v eM lg s D an x (f 0, f 1) ∧ ∀ i, i < 2 →
          DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id (f i) ((pack2 _).get x.2 i) =
            false) :
    DecR.LangE (DecR.wayColl (decRec T v eM lg s)) (x.2.1, an x.1.1) (x.2.2, an x.1.2) Y₀ Y₁ := by
  obtain ⟨ys, e, h⟩ := h
  match ys, e, h with
  | [y₀, y₁], e, h =>
    rw [(List.cons.inj e).1, (List.cons.inj (List.cons.inj e).2).1]
    obtain ⟨h1, h2⟩ := h (fun i => if i = 0 then y₀ else y₁) (fun i hi => by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · rfl
      · rfl)
    exact DecR.langE_of_typed (D := decRec T v eM lg s) (Equiv.refl _) an id (x.1.1, x.2.1)
      (x.1.2, x.2.2) y₀ y₁ ⟨h1, h2 1 (by decide)⟩

end

/-! ## The comparisons under a family of oracle functions -/

section
variable {I A Sd S : Type} [DecidableEq S] {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L}
  {Ex : ExtRd L} (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
  (plainsT : Plains ZT.P.shape) (seedOf : Rho ZT.P.shape → S) (Pk : Pack Ex.k S Sd)

/-- If the comparisons say yes under F, then under each root of the list the chain yields under F
the value of the same number in s. -/
theorem cmpT_det_true (F : Fam (typedOracleFamily lam W.K L)) : ∀ (l : List (Dig lam)) (i : ℕ) (s : Sd),
    (cmpT ZT saltT rtT rootsT plainsT seedOf Pk l i s).det F = true →
    ∀ j, j < l.length → ∃ y,
      (ZT.chainT saltT rtT rootsT plainsT [l.getD j default]).det F = some y ∧
        seedOf y.1 = Pk.get s (i + j)
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: l, i, s, h, j, hj => by
    have h' : (((ZT.chainT saltT rtT rootsT plainsT [c]).bind fun z =>
        match z with
        | some y => if seedOf y.1 = Pk.get s i then
            cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false
        | none => OComp.pure false).det F) = true := h
    rw [OComp.det_bind] at h'
    cases hz : (ZT.chainT saltT rtT rootsT plainsT [c]).det F with
    | none =>
      rw [hz] at h'
      cases h'
    | some y =>
      rw [hz] at h'
      have h3 : ((if seedOf y.1 = Pk.get s i then
          cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s
          else OComp.pure false).det F) = true := h'
      by_cases hs : seedOf y.1 = Pk.get s i
      · rw [if_pos hs] at h3
        cases j with
        | zero => exact ⟨y, hz, hs⟩
        | succ j =>
          obtain ⟨y', h4, h5⟩ := cmpT_det_true F l (i + 1) s h3 j (Nat.lt_of_succ_lt_succ hj)
          exact ⟨y', h4, by rw [h5]; congr 1; omega⟩
      · rw [if_neg hs] at h3
        cases h3

/-- The converse: if under each root of the list the chain yields under F the value of the same
number in s, the comparisons say yes under F. -/
theorem cmpT_det_of (F : Fam (typedOracleFamily lam W.K L)) : ∀ (l : List (Dig lam)) (i : ℕ) (s : Sd),
    (∀ j, j < l.length → ∃ y,
      (ZT.chainT saltT rtT rootsT plainsT [l.getD j default]).det F = some y ∧
        seedOf y.1 = Pk.get s (i + j)) →
    (cmpT ZT saltT rtT rootsT plainsT seedOf Pk l i s).det F = true
  | [], _, _, _ => rfl
  | c :: l, i, s, h => by
    obtain ⟨y, hy, hs⟩ := h 0 (Nat.succ_pos _)
    have hy' : (ZT.chainT saltT rtT rootsT plainsT [c]).det F = some y := hy
    show (((ZT.chainT saltT rtT rootsT plainsT [c]).bind fun z =>
        match z with
        | some y => if seedOf y.1 = Pk.get s i then
            cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false
        | none => OComp.pure false).det F) = true
    rw [OComp.det_bind, hy']
    show ((if seedOf y.1 = Pk.get s i then
      cmpT ZT saltT rtT rootsT plainsT seedOf Pk l (i + 1) s else OComp.pure false).det F) = true
    rw [if_pos (by rw [hs, Nat.add_zero])]
    refine cmpT_det_of F l (i + 1) s fun j hj => ?_
    obtain ⟨y', h1, h2⟩ := h (j + 1) (Nat.succ_lt_succ hj)
    exact ⟨y', h1, by rw [h2]; congr 1; omega⟩

/-- The judge's run says yes under F exactly if the comparisons and the compiled verifier do. -/
theorem judgeRunE_det (Z : WrittenE W Ex) (sMT sFS : ℕ) (F : Fam (typedOracleFamily lam W.K L)) (o : OutE Z) :
    (judgeRunE Z ZT saltT rtT rootsT plainsT seedOf Pk sMT sFS o).det F = true ↔
      (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).det F = true ∧
        (Z.verifierS sMT sFS o.1 o.2.1 o.2.2).det F = true := by
  unfold judgeRunE
  rw [OComp.det_bind]
  cases (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).det F with
  | true =>
    rw [if_pos rfl]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact ⟨fun h => (by cases h), fun h => (by cases h.1)⟩

/-- The same for the run without the test of the strict format. -/
theorem judgeRunEL_det (Z : WrittenE W Ex) (F : Fam (typedOracleFamily lam W.K L)) (o : OutE Z) :
    (judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk o).det F = true ↔
      (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).det F = true ∧
        (Z.verifier o.1 o.2.1 o.2.2).det F = true := by
  unfold judgeRunEL
  rw [OComp.det_bind]
  cases (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).det F with
  | true =>
    rw [if_pos rfl]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | false =>
    rw [if_neg Bool.false_ne_true]
    exact ⟨fun h => (by cases h), fun h => (by cases h.1)⟩

end

/-! ## The seeds in the instance are the seeds under the oracle -/

/-- `seedUnder_of_blocks` (OnBytes/Slice/SeedDrawn.lean) in a field that is the second. -/
theorem seedUnder_of_blocks_of (f : _root_.Fmt.Fld) (hf : f = .two) (lg s K : ℕ)
    (e : _root_.Fmt.Entry) (h : _root_.Fmt.dsOf e .seeds = roundDraws lg s)
    (hK : (seedBS lg s).b ≤ K) (k : OnBytes.Tie.IdKey) (g : Fam (rom 256)) (B : Fin K → Dig 256)
    (hB : ∀ i : Fin K, B i = g () (bytesToBits (blockStr
      (oB (g ()) (seedFirst (OnBytes.Key.nameOf k.1 k.2.1 k.2.2))) (i.val + 1)))) :
    seedUnder lg s k g =
      some (seedOfDrawn lg s [(ckP f).dr e .seeds (chalP f K e .seeds B)]) := by
  subst hf
  exact seedUnder_of_blocks lg s K e h hK k g B hB

section
variable {An : Type} (lg s : ℕ) [DecidableEq (Fin s → (Fin lg → GE) × NZ)] (D : XD)
  (dec : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ)) → View → Bool)
  {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (d₁ : Fin s → (Fin lg → GE) × NZ)

/-- The interface of the entry's frame at the seeds' protocol. -/
abbrev LXEs : BatchProtocolWithLeafBody Unit
    ((An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ))) :=
  LXE (Bd := Bd) D (earlyTwo d₁) (TSE D (seedEntry lg s))

omit [DecidableEq (Fin s → (Fin lg → GE) × NZ)] in
/-- UNDER THE LAW ON A PAGE, WHAT THE SEEDS' CHAIN YIELDS UNDER ONE ROOT, IN THE FAMILY READ OUT
OF g, IS THE SEED UNDER g of a key at whose name, and under which root, the implementation obeys
`SeedsPage`. -/
theorem entry_chain_seed (hf : D.base.plan.field = .two) (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ D.K)
    (m : OracleCoding (typedOracleFamily 256 (D.K + 1) (LXEs (An := An) (Bd := Bd) lg s D d₁)) 256)
    (k : OnBytes.Tie.IdKey) (cm : Dig 256)
    (hp : SeedsPage m .test (OnBytes.Key.nameOf k.1 k.2.1 k.2.2)
      (q0S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id [cm])
      (q1S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id))
    (g : Fam (rom 256)) (y)
    (hy : ((testXE D B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
      (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _)).chainT [] default []
        (plainsT D.C (dSeed (seedEntry lg s)) _) [cm]).det (readBlocks m g) = some y) :
    seedUnder lg s k g = some (seedOfE D (seedEntry lg s) (seedOfDrawn lg s) y.1) := by
  have h1 := chainAt_seeds_det (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C
    (seedEntry lg s) _ id D.K (chalP D.base.plan.field D.K) (we1 D.a) (readBlocks m g) [cm]
  have h2 := Option.some.inj (hy.symm.trans h1)
  rw [h2]
  exact seedUnder_of_blocks_of D.base.plan.field hf lg s D.K (seedEntry lg s)
    (dsOf_seedEntry lg s hs0) hK k g
    (firstBlocks 256 (D.K + 1) D.K (fbAt m g .test
      (q1S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id
        (Batch.link (fbAt m g .test
          (q0S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id
            [cm]))))).1)
    fun i => by
      have hi : i.val < D.K + 1 := Nat.lt_succ_of_lt i.isLt
      unfold firstBlocks
      rw [dif_pos hi]
      refine (hp.round g _ ⟨i.val, hi⟩).trans ?_
      rw [hp.first g]
      rfl

/-- IF THE ENTRY'S JUDGE'S RUN SAYS YES UNDER THE FAMILY READ OUT OF g, BOTH SEEDS IN ITS INSTANCE
ARE THE SEEDS UNDER g: the first of a key k₀, the second of a key k₁, at whose names, and under
the output's first and second root, the implementation obeys `SeedsPage`. What a yes asks of the
entry's two records, for the seeds. -/
theorem entry_run_seeds (hf : D.base.plan.field = .two) (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ D.K)
    (m : OracleCoding (typedOracleFamily 256 (D.K + 1) (LXEs (An := An) (Bd := Bd) lg s D d₁)) 256)
    (k₀ k₁ : OnBytes.Tie.IdKey) (g : Fam (rom 256))
    (o : OutE (ZXE D dec B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
      (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _)))
    (hlen : o.1.length = 2)
    (hp₀ : SeedsPage m .test (OnBytes.Key.nameOf k₀.1 k₀.2.1 k₀.2.2)
      (q0S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id
        [o.1.getD 0 default])
      (q1S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id))
    (hp₁ : SeedsPage m .test (OnBytes.Key.nameOf k₁.1 k₁.2.1 k₁.2.2)
      (q0S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id
        [o.1.getD 1 default])
      (q1S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id))
    (h : (judgeRunEL
        (ZXE D dec B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
          (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _))
        (testXE D B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
          (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _))
        [] default [] (plainsT D.C (dSeed (seedEntry lg s)) _)
        (seedOfE D (seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) o).det
          (readBlocks m g) = true) :
    seedUnder lg s k₀ g = some o.2.1.2.1 ∧ seedUnder lg s k₁ g = some o.2.1.2.2 := by
  have htake : o.1.take 2 = o.1 := by rw [← hlen, List.take_length]
  have hc := ((judgeRunEL_det _ [] default [] _ _ (pack2 _) _ (readBlocks m g) o).1 h).1
  have hc' : (ext2R (LXEs (An := An) (Bd := Bd) lg s D d₁)).k = 2 := rfl
  rw [hc', htake] at hc
  have hall := cmpT_det_true (Ex := ext2R (LXEs (An := An) (Bd := Bd) lg s D d₁))
    (testXE D B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
      (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _))
    [] default [] (plainsT D.C (dSeed (seedEntry lg s)) _)
    (seedOfE D (seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) (readBlocks m g) o.1 0 o.2.1.2 hc
  obtain ⟨y₀, hy₀, hs₀⟩ := hall 0 (by omega)
  obtain ⟨y₁, hy₁, hs₁⟩ := hall 1 (by omega)
  refine ⟨?_, ?_⟩
  · rw [entry_chain_seed lg s D B E d₁ hf hs0 hK m k₀ _ hp₀ g y₀ hy₀, hs₀]
    rfl
  · rw [entry_chain_seed lg s D B E d₁ hf hs0 hK m k₁ _ hp₁ g y₁ hy₁, hs₁]
    rfl

/-- THE CONVERSE, WHICH `fit` WANTS: IF BOTH SEEDS IN AN OUTPUT'S INSTANCE ARE THE SEEDS UNDER g,
THE COMPARISONS SAY YES UNDER THE FAMILY READ OUT OF g. Under the same law on a page. The seeds'
chain never refuses (`chainAt_seeds_det` is an equation). -/
theorem entry_cmp_yes (hf : D.base.plan.field = .two) (hs0 : 0 < s) (hK : (seedBS lg s).b ≤ D.K)
    (m : OracleCoding (typedOracleFamily 256 (D.K + 1) (LXEs (An := An) (Bd := Bd) lg s D d₁)) 256)
    (k₀ k₁ : OnBytes.Tie.IdKey) (g : Fam (rom 256))
    (o : OutE (ZXE D dec B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
      (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _)))
    (hlen : o.1.length = 2)
    (hp₀ : SeedsPage m .test (OnBytes.Key.nameOf k₀.1 k₀.2.1 k₀.2.2)
      (q0S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id
        [o.1.getD 0 default])
      (q1S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id))
    (hp₁ : SeedsPage m .test (OnBytes.Key.nameOf k₁.1 k₁.2.1 k₁.2.2)
      (q0S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id
        [o.1.getD 1 default])
      (q1S (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C (seedEntry lg s) _ id))
    (h₀ : seedUnder lg s k₀ g = some o.2.1.2.1) (h₁ : seedUnder lg s k₁ g = some o.2.1.2.2) :
    (cmpT (Ex := ext2R (LXEs (An := An) (Bd := Bd) lg s D d₁))
      (testXE D B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
        (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _))
      [] default [] (plainsT D.C (dSeed (seedEntry lg s)) _)
      (seedOfE D (seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) o.1 0 o.2.1.2).det
        (readBlocks m g) = true := by
  refine cmpT_det_of (Ex := ext2R (LXEs (An := An) (Bd := Bd) lg s D d₁))
    (testXE D B E (earlyTwo d₁) (TSE D (seedEntry lg s)) (wTSE D (seedEntry lg s))
      (embST D.C (seedEntry lg s) _) (prjST D.C (seedEntry lg s) _))
    [] default [] (plainsT D.C (dSeed (seedEntry lg s)) _)
    (seedOfE D (seedEntry lg s) (seedOfDrawn lg s)) (pack2 _) (readBlocks m g) o.1 0 o.2.1.2
    fun j hj => ?_
  have hdet := fun cm => chainAt_seeds_det (L := LXEs (An := An) (Bd := Bd) lg s D d₁) .test D.C
    (seedEntry lg s) _ id D.K (chalP D.base.plan.field D.K) (we1 D.a) (readBlocks m g) [cm]
  obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
  · refine ⟨_, hdet _, ?_⟩
    have h2 := entry_chain_seed lg s D B E d₁ hf hs0 hK m k₀ _ hp₀ g _ (hdet _)
    exact Option.some.inj (h2.symm.trans h₀)
  · refine ⟨_, hdet _, ?_⟩
    have h2 := entry_chain_seed lg s D B E d₁ hf hs0 hK m k₁ _ hp₁ g _ (hdet _)
    exact Option.some.inj (h2.symm.trans h₁)

end

/-! ## The two records, read off what the checker returns -/

section
variable {An : Type} (T : _root_.Fmt.M1.Code) (v eM : ℕ) {lg s : ℕ}
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) {β : Type}

/-- The first table's record in what the entry's checker returns: the first seeds in the
instance; the answers that `an` reads off the first answers there. β: the type of argument strings.
-/
def recE₀ (o : List (Dig 256) × ((An × An) ×
    ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ))) × β) :
    (decRec T v eM lg s).Rec := (o.2.1.2.1, an o.2.1.1.1)

/-- The copy's record there: the second seeds, the second answers. -/
def recE₁ (o : List (Dig 256) × ((An × An) ×
    ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ))) × β) :
    (decRec T v eM lg s).Rec := (o.2.1.2.2, an o.2.1.1.2)

/-- `langE_of_judgeE` in the letters in which the join asks it: at an output and its two records. -/
theorem langE_of_judgeE_out (D : XD) (o : List (Dig 256) × ((An × An) ×
      ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ))) × β) (Y₀ Y₁ : Raw SgX)
    (h : ∃ ys : List (Fin (2 ^ D.a) → SgX), [Y₀, Y₁] = ys.map (rawOf (Equiv.refl _)) ∧
      ∀ f : ℕ → Fin (2 ^ D.a) → SgX, (∀ i, i < 2 → ys[i]? = some (f i)) →
        lgEX T v eM lg s D an o.2.1 (f 0, f 1) ∧ ∀ i, i < 2 →
          DecR.badK (D := decRec T v eM lg s) (Equiv.refl _) id (f i) ((pack2 _).get o.2.1.2 i) =
            false) :
    DecR.LangE (DecR.wayColl (decRec T v eM lg s)) (recE₀ T v eM an o) (recE₁ T v eM an o) Y₀ Y₁ :=
  langE_of_judgeE T v eM lg s D an o.2.1 Y₀ Y₁ h

end

/-! ## A table that holds the oracle's own values, at the sibling's parts -/

section
variable {lam : ℕ} {γ Sg : Type}

/-- A part of the sibling whose checker is answered by a table that has g's own values at the
strings of S: its checker has under g the value of the part's own checker under g. -/
theorem Part.on_chk_of_eq (p : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam)
    (g : Fam (rom lam)) (h : ∀ x ∈ S, T x = g () x) (x : γ) :
    ((p.on S T).chk x).det g = (p.chk x).det g :=
  OnBytes.Slice.det_pinOn_of_eq S T g h _

/-- At g's own function as the table. -/
theorem Part.on_chk_self (p : Part lam γ Sg) (S : Finset (List Bool)) (g : Fam (rom lam)) (x : γ) :
    ((p.on S fun y => g () y).chk x).det g = (p.chk x).det g :=
  p.on_chk_of_eq S _ g (fun _ _ => rfl) x

end

end TypedOracleCompiler.Slice
