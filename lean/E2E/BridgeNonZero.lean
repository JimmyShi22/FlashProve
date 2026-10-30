-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeNonZero.lean: in the description of the proof file's IOP as written in Lean
(`descZ Zp Np cF`), no declared round asks for more non-zero elements than elements: in every
round's entry, `drawNZ` (how many of the drawn field elements must not be 0) is at most `drawE` (how
many are drawn). This is proved at three public files Z in scope (`InScope Z = true`), at a
description that `LaidAt` (Johnson/P5J/LaidOpens.lean) ties to Z. So `nonZero`, one of the six
clauses of `PlainAt` (E2E/BridgeJoinAtFiles.lean), is a theorem there, and so is the hypothesis hz
of `due_atFiles` (E2E/BridgePaidAtFiles.lean). `nz_decl` and `seal_nz` are general: they hold at
every value of `FileDescription` (Johnson/Desc/Block.lean) for which `FileDescription.data` returns.

  `nonZero_atFiles`: in scope, under `LaidAt`: `drawNZ ≤ drawE` in the entry of every declared round
    of the three chains of `descZ Zp Np cF`
  `plainAt_of_five`: in scope, under `LaidAt`: `PlainAt Z Zp Np cF B G H` from its other five
    clauses
  `nz_decl`: F, the file's name and D are free parameters: where `F.data` returns the data D and
    `drawNZ ≤ drawE` holds in the entry of every round of D, it holds in the entry of every declared
    round of F
  `seal_nz`: with the same free parameters: where `F.data` returns, the first chain has a last
    declared round, and that round's entry has `drawNZ` = 0
  `partnerR`: a small fact on lists: of two lists that are related member by member
    (`List.Forall₂`), each member of the right list has a partner in the left one

By what. `nonZero_atFiles` is `nz_decl` at the field `data` of `LaidAt`. In scope the data D of
`LaidAt` are the library's written data `writtenPFull`, by `LPFD.Full.laidPOf_written`
(Johnson/Desc/Laid/ProofFullScope.lean) at `LaidAt.laidPOf` (Johnson/P5T/FenceAtMg.lean), and
`nz_writtenP` (E2E/WrittenNonZero.lean) has the inequality at all rounds of these. `nz_decl`: by
`ProofFile.Honest.kinds_of_data` (Johnson/Desc/ProofFile/Honest/Law/DataKinds.lean) every declared round
but the first chain's last has the entry of a round of the data. The first chain's last declared
round is paired with no round of the data; `seal_nz` is for it. `seal_nz` goes by the steps of the
proof of `kinds_of_data`, which keeps of that round that the empty challenge fits it (`drawFit`) and
drops `drawNZ` = 0. Called there: `data_ok`, `writtenOf_ok`, `round_ok`
(Johnson/Desc/BlockSlotProofs.lean), `okAt_parts` (OnBytes/Maker/Files.lean), `seal_of_fits`,
`forall₂_last` (DataKinds.lean).

Hypotheses. scope: `InScope Z = true`. L: `LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF`, at
some data D and some r. The others of `plainAt_of_five` are fields of `PlainAt`, word for word.
plainSeal: the first chain's last declared round states no item but roots, and no root. halved: the
prover `provG Z Zp Np cF B G H` has a part (`Placed`) for each sub-protocol that states an item that
is no root. rooted: it has one for each sub-protocol that sends a root. width: every declared stored
table has the encoder's width. ready₁: `ready` returns once, at some input and coins.

Limits. Those of E2E/WrittenNonZero.lean, among them: `nz_writtenP` rests on a closed statement
(`proofPricesWritten`, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean) that rests on evaluations
in Lean's kernel, made in its own file; and that the written priced plans of that statement are the
planner's is no theorem. The statements are on the entries of declared rounds: nothing is said of
any value that is drawn. Whether any public files are in scope and meet `LaidAt` is not shown here.
`plainAt_of_five` proves none of the other five clauses. No property of a protocol is stated:
nothing on completeness, soundness or hiding.
-/
import E2E.BridgeJoinAtFiles
import E2E.WrittenNonZero

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.Written
open VerifiableInference.Desc
open OnBytes OnBytes.Maker
open ProofFile.Honest (kinds_of_data forall₂_last)

variable {Xi : Type}

/-- Where `F.data` returns for a value F of `FileDescription`, the first chain has a last declared round,
and that round asks for no non-zero element. -/
theorem seal_nz {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D) :
    ∃ d, F.roundsDeclaredByBlocks.1.getLast? = some d ∧ d.entry.drawNZ = 0 := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, -, -⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  obtain ⟨r, hr, -, -, -, -, q8, -, -⟩ := ProofFile.Honest.seal_of_fits hf
  obtain ⟨d, hd, y, hy, rfl⟩ := forall₂_last w₁ r hr
  have e := (round_ok hy).1
  have q8' : y.entry.drawNZ = 0 := q8
  rw [e] at q8'
  exact ⟨d, hd, q8'⟩

/-- Of two lists that are related member by member, each member of the right list has a partner in
the left one. -/
theorem partnerR {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ z ∈ l₂, ∃ d ∈ l₁, R d z
  | _, _, .nil, _, h => absurd h (by simp)
  | _, _, .cons h t, z, hz => by
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨d, hd, hr⟩ := partnerR t z hz
      exact ⟨d, List.mem_cons_of_mem _ hd, hr⟩

/-- **From the rounds of the data to the declared rounds**: where `F.data` returns D and no round of
D asks for more non-zero elements than elements, no declared round of F does. -/
theorem nz_decl {F : FileDescription Xi} {file : String} {D : WholeD} (h : F.data file = .ok D)
    (hw : ∀ d ∈ D.ds₁ ++ D.ds₂ ++ D.ds₃, d.entry.drawNZ ≤ d.entry.drawE) :
    ∀ z ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, z.entry.drawNZ ≤ z.entry.drawE := by
  obtain ⟨k1, k2, k3, -⟩ := kinds_of_data h
  obtain ⟨s, hs, hs0⟩ := seal_nz h
  have e : F.roundsDeclaredByBlocks.1.dropLast ++ [s] = F.roundsDeclaredByBlocks.1 := List.dropLast_append_getLast? s hs
  intro z hz
  rw [← e] at hz
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with ((hz | rfl) | hz) | hz
  · obtain ⟨d, hd, hr⟩ := partnerR k1 z hz
    rw [← hr.1]
    exact hw d (by simp [hd])
  · rw [hs0]
    exact Nat.zero_le _
  · obtain ⟨d, hd, hr⟩ := partnerR k2 z hz
    rw [← hr.1]
    exact hw d (by simp [hd])
  · obtain ⟨d, hd, hr⟩ := partnerR k3 z hz
    rw [← hr.1]
    exact hw d (by simp [hd])

end AtPublicFiles.Written

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides halvedAll sealPlain rootedAll ready)
open VerifierAndGoals (PublicFiles InScope)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

/-- **The clause `nonZero` of `PlainAt`**, in scope, at a description that `LaidAt` ties to Z. -/
theorem nonZero_atFiles (scope : InScope Z = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.2,
      d.entry.drawNZ ≤ d.entry.drawE :=
  AtPublicFiles.Written.nz_decl L.data
    ((LPFD.Full.laidPOf_written scope L.laidPOf).symm ▸ AtPublicFiles.Written.nz_writtenP)

variable {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- `PlainAt` from its other five clauses, in scope, at a description that `LaidAt` ties to Z. -/
theorem plainAt_of_five (scope : InScope Z = true) {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (plainSeal : sealPlain (descZ Zp Np cF) = true)
    (halved : halvedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true)
    (rooted : rootedAll (descZ Zp Np cF) (provG Z Zp Np cF B G H) = true)
    (width : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, t.sh.W = 2 ^ frS.P.v)
    (ready₁ : ∃ w₀ rc x k R, ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x k = .ok R) :
    PlainAt Z Zp Np cF B G H :=
  ⟨plainSeal, halved, rooted, nonZero_atFiles Z Zp Np cF scope L, width, ready₁⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Written.seal_nz
#print axioms AtPublicFiles.Written.partnerR
#print axioms AtPublicFiles.Written.nz_decl
#print axioms AtPublicFiles.AtFiles.nonZero_atFiles
#print axioms AtPublicFiles.AtFiles.plainAt_of_five
