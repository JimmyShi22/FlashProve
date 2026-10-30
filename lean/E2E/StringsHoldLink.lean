-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsHoldLink.lean: at the verifier's parameters at Z, for every Z, a produced link proof
opens a column of the encoder's first table of the index and a column of the copy's table.

Summary. E2E/StringsHold.lean proves that a produced proof opens exactly what the verifier reads.
This file proves that the link's verifier always reads a column of each of its two tables. The
result on proofs holds for any three provers, all oracle functions and all coins. No probability
occurs. One closed fact is evaluated by Lean's kernel.

Main results.
  `readsLink_description`: for every Z, in scope or not, whether or not the description is live, the
    link's verifier reads a column of the first table and a column of the copy, for every instance
    and all verifier messages (`ReadsLink`). The link's rounds' data do not depend on the public
    files.
  `link_columns`: under `ReadsLink r`, a produced link proof for the copy at place j holds `r.protocol.encodeIndex
    i c.r p` at a position p of the first table and `r.protocol.encodeIndex i e.r q` at a position q of that copy's
    table, each with a salt and a path.
  `linkW_reads_some`: for arbitrary rounds' data: where the test `OpensX` passes for one of the two
    tables, the verifier of a copy's file (`linkProtocolOfRoundData`, OnBytes/Flat/LinkSib.lean) reads a column of
    that table.

Terms: E2E/HidingTerms.lean.

Limits. This file does not prove:
- how many columns are opened: the lower bound is one per table (upper bounds, 62 and 62:
  E2E/ReadsAtFiles.lean, E2E/StringsHoldClosed.lean); or which positions;
- anything about the openings of the strategies' own oracle messages, or about the plain parts;
- that a column tells anything about the index, or nothing;
- that a link proof is produced, or that the verifier accepts it;
- anything on completeness, on soundness or on what is hidden.

Definitions and helper lemmas.
  `OpensX b ds xs`: a test on the data of a copy's file: some external opening of the table b has a
    non-empty part of its round's sampled positions.
  `ReadsLink r`: the property that `readsLink_description` proves.
  `drawn_at`, `list_some`, `wantedXL_mem`: a round samples as many positions as its entry names;
    such a part gives a position below the tables' length; that position is among those that the
    sampled positions ask for.
  `opensX_written`: the link's written data pass the test for both tables.
  `readsLink_atFiles`: `ReadsLink` at the structure of parameters from which the verifier is
    compiled.


-/
import E2E.StringsHoldAtInput

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Shown
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Flat (linkProtocolOfRoundData)
open TypedOracleCompiler.Run.PQ (RD drawnSL wantedXL wantedX xWanted)
open _root_.Run.PQ (CK View XO xPos xsAt storedKey)
open _root_.Run (ckP)
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey
open OnBytes.Slice (frS frZ)
open VerifiableInference.OnPublicFiles (InnerCompilerInput innerCompilerInputAtFullSize)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)

/-! ## 1. The verifier of a copy's file reads a column of each table -/

/-- Some external opening of the table b has a non-empty part of its round's sampled positions. -/
def OpensX (b : Bool) (ds : List RD) (xs : List XO) : Bool :=
  xs.any fun o => o.which == b && decide (0 < o.count) &&
    (ds[o.round]?).any fun d => decide (o.from_ < d.entry.poss)

theorem drawn_at (f : _root_.Fmt.Fld) : ∀ (ds : List RD)
    (ρ : Rho (TypedOracleCompiler.Run.PQ.uL (ckP f) ds)) (j : ℕ) (d : RD), ds[j]? = some d →
    ∃ D, (drawnSL (ckP f) ds ρ)[j]? = some D ∧ D.poss.length = d.entry.poss
  | [], _, _, _, h => by cases h
  | d₀ :: _, (c, _), 0, d, h => by
    obtain rfl : d₀ = d := Option.some.inj h
    exact ⟨_, rfl, AtPublicFiles.Reads.dr_poss f _ _ _⟩
  | _ :: ds, (_, ρ), j + 1, d, h => drawn_at f ds ρ j d h

theorem list_some (a : ℕ) (o : XO) (D : _root_.Fmt.Drawn) (h₁ : o.from_ < D.poss.length)
    (h₂ : 0 < o.count) : ∃ x, x < 2 ^ a ∧ x ∈ o.list a D := by
  have hne : o.raw D ≠ [] := by
    intro h
    have hl : (o.raw D).length = 0 := by rw [h]; rfl
    unfold XO.raw at hl
    rw [List.length_take, List.length_drop] at hl
    omega
  obtain ⟨y, l, hy⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨y % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a), ?_⟩
  unfold XO.list
  refine (_root_.Fmt.listOf_mem _ _).2 ?_
  rw [hy]
  exact List.mem_map.2 ⟨y, List.mem_cons_self, rfl⟩

theorem wantedXL_mem (a : ℕ) (all : List RD) (xs : List XO) (o : XO) (ho : o ∈ xs) (x : ℕ) :
    ∀ (ds : List RD) (Ds : List _root_.Fmt.Drawn) (i j : ℕ) (d : RD) (D : _root_.Fmt.Drawn),
      o.round = i + j → ds[j]? = some d → Ds[j]? = some D → x ∈ o.list a D →
      (storedKey o.which, x) ∈ wantedXL a all xs i ds Ds
  | [], _, _, _, _, _, _, h, _, _ => by cases h
  | _ :: _, [], _, _, _, _, _, _, h, _ => by cases h
  | d₀ :: ds, D₀ :: Ds, i, 0, d, D, hr, _, hD, hx => by
    obtain rfl : D₀ = D := Option.some.inj hD
    unfold wantedXL
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨o, ?_, ?_⟩))
    · unfold xsAt
      exact List.mem_filter.2 ⟨ho, by simpa using hr⟩
    · exact List.mem_map.2 ⟨x, hx, rfl⟩
  | d₀ :: ds, D₀ :: Ds, i, j + 1, d, D, hr, hd, hD, hx => by
    unfold wantedXL
    exact List.mem_append_right _
      (wantedXL_mem a all xs o ho x ds Ds (i + 1) j d D (by omega) hd hD hx)

section
variable (f : _root_.Fmt.Fld) (ds : List RD) (a : ℕ) (xs : List XO) {X : Type}
  (dec : X → View → Bool)

/-- **Where the test passes for the table b, the verifier of a copy's file reads a column of that
table, for every instance and all verifier messages.** -/
theorem linkW_reads_some (b : Bool) (h : OpensX b ds xs = true) (x : X)
    (ρ : Rho (linkProtocolOfRoundData (ckP f) ds a xs dec).shape) :
    ∃ p ∈ (linkProtocolOfRoundData (ckP f) ds a xs dec).extReads x ρ, p.isRight = b := by
  unfold OpensX at h
  obtain ⟨o, ho, hc⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hw, hcnt⟩, hd⟩ := hc
  cases hdd : ds[o.round]? with
  | none => rw [hdd] at hd; cases hd
  | some d =>
    rw [hdd] at hd
    have hfrom : o.from_ < d.entry.poss := by simpa using hd
    obtain ⟨D, hD, hlen⟩ := drawn_at f ds ρ.2 o.round d hdd
    obtain ⟨y, hy, hm⟩ := list_some a o D (by rw [hlen]; exact hfrom) hcnt
    have hw' := wantedXL_mem a ds xs o ho y ds (drawnSL (ckP f) ds ρ.2) 0 o.round d D
      (Nat.zero_add _).symm hdd hD hm
    have hx : (b, y) ∈ xWanted a ds xs (drawnSL (ckP f) ds ρ.2) := by
      unfold xWanted
      refine List.mem_filterMap.2 ⟨(storedKey o.which, y), hw', ?_⟩
      rw [hw]
      cases b with
      | false => simp
      | true =>
        have hne : storedKey true ≠ storedKey false := by decide
        simp [hne]
    refine ⟨if b then .inr ⟨y, hy⟩ else .inl ⟨y, hy⟩,
      List.mem_toFinset.2 (List.mem_filterMap.2 ⟨(b, y), hx, ?_⟩), by cases b <;> rfl⟩
    unfold xPos
    rw [dif_pos hy]

end

/-- The link's written data pass the test for both tables. -/
theorem opensX_written : OpensX false PV.EntryFive.dsF PV.EntryFive.xsF = true ∧
    OpensX true PV.EntryFive.dsF PV.EntryFive.xsF = true := by decide +kernel

/-! ## 2. At the verifier's parameters -/

/-- The link's verifier reads a column of the first table and a column of the copy, for every
instance and all verifier messages. -/
def ReadsLink (r : InnerCompilerInput) : Prop :=
  ∀ x ρ, (∃ p, Sum.inl p ∈ r.protocol.link.extReads x ρ) ∧ ∃ p, Sum.inr p ∈ r.protocol.link.extReads x ρ

theorem readsLink_atFiles (Z : PublicFiles) (c₀ : VerifiableInference.Digest) (m₀ : List (Dig 256)) :
    ReadsLink (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  intro x ρ
  obtain ⟨p, hp, e⟩ := linkW_reads_some .two PV.EntryFive.dsF frS.P.T.a PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec false opensX_written.1 x ρ
  obtain ⟨q, hq, e'⟩ := linkW_reads_some .two PV.EntryFive.dsF frS.P.T.a PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec true opensX_written.2 x ρ
  constructor
  · cases p with
    | inl a => exact ⟨a, hp⟩
    | inr a => cases e
  · cases q with
    | inl a => cases e'
    | inr a => exact ⟨a, hq⟩

/-- **At the verifier's parameters at Z, for every Z**: in scope or not, whether or not the
description is live. -/
theorem readsLink_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      ReadsLink ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More), ReadsLink (D.input Z c m))
    fun c m => readsLink_atFiles Z c m

/-- **Under `ReadsLink r`, a produced link proof for the copy at place j holds a column of the
encoder's first table of the index i and a column of that copy's table**, each with a salt and a
path. -/
theorem link_columns (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (g : Fam (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))) (hR : ReadsLink r) (i : r.Index)
    (c : DrawC 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KT h.KL) (j : ℕ)
    (e : DrawCopy 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits h.KL) (hj : c.copies[j]? = some e)
    (l : Dig 256 × r.protocol.Rec × Option (OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)))
    (hl : ((commitAt r.queryLayout r.seedQueries r.answerCode h i c).det g).1.links[j]? = some l)
    (π : OneProtocolProof 256 (batLC r.protocol r.linkRoundSplits)) (hπ : l.2.2 = some π) :
    (∃ p sa pa, π.ext (.inl p) = some ⟨r.protocol.encodeIndex i c.r p, sa, pa⟩) ∧
      ∃ p sa pa, π.ext (.inr p) = some ⟨r.protocol.encodeIndex i e.r p, sa, pa⟩ := by
  obtain ⟨ρ, ho, -⟩ := link_opens r.queryLayout r.seedQueries r.answerCode h g i c j e hj l hl π hπ
  obtain ⟨⟨p, hp⟩, q, hq⟩ := hR (r.protocol.recOf i c.r (tabG r.queryLayout r.seedQueries h g i c.r c.s).seed,
    r.protocol.recOf i e.r (tabG r.queryLayout r.seedQueries h g i e.r e.s).seed) ρ
  exact ⟨⟨p, _, _, ho _ hp⟩, q, _, _, ho _ hq⟩

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.readsLink_atFiles
#print axioms AtPublicFiles.Shown.readsLink_description
#print axioms AtPublicFiles.Shown.link_columns
#print axioms AtPublicFiles.Shown.drawn_at
#print axioms AtPublicFiles.Shown.list_some
#print axioms AtPublicFiles.Shown.wantedXL_mem
#print axioms AtPublicFiles.Shown.linkW_reads_some
#print axioms AtPublicFiles.Shown.opensX_written
