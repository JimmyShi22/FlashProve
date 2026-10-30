-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/ReadsAtFull.lean: THE SIX HYPOTHESES OF THE LOOKUPS' ROWS ON THE PUBLIC DATA HOLD
AT WHAT THE PUBLIC PART's MAKER RETURNS AT THE LIBRARY's WRITTEN COPY OF THE FULL-SIZE PUBLIC FILES
(VerifierAndGoals.storedPublicFiles, as Ladder/Stored.lean spells it). A joining, under one premise on the layout file's
size.

  `six_zFull`: at each of the 25 links the six statements (SixAt, Johnson/AtFull/K3X/SixAt.lean).
  **`readsX_zFull`**: ReadsX X₀ (Johnson/AtFull/Desc/Lots/K3RowX.lean).
  **`readsXB_zFull`**: readsXB X₀ = true (Johnson/AtFull/Desc/Lots/K3RowXB.lean).
Each at whatever letter X₀ the maker publicOfO, at the second hash function, returns there.

How. The maker's return names its value's parts by letters, each with its own maker's equation
(publicOfO_zFull_of_rest, Johnson/AtFull/Public/Join.lean). The twelve layers' links and the twelve
attention's links: small closed facts at the makers, proved by evaluation in Lean's kernel, carried
to these letters (Johnson/AtFull/K3X/SixBefore.lean). What was reckoned too heavy for the kernel
comes by laws: the layers' sixteen counts of padding keys (CountsAtFull.lean), the layers' host's
count (LaidAtFull.lean), the attention's test on the padding key (PadKeyLaw.lean), the output head's
host's count (HeadLaidAtFull.lean). The output head's link: HeadSegment.lean. An earlier try at one
test that holds all six at one link, asked of the kernel outright, ended at a cap on memory; none of
the heavy parts was tried alone in the kernel (Lean's evaluator, on a sheet not in this repository,
said yes to each of the last three, at five links in all: no proof; the first was not tried alone).

Limits. UNDER hsz : the written layout file has 224975 bytes, WHICH IS NOT PAID HERE. readsXB IS
THIS LIBRARY's COMPARISON WITH WRITTEN VALUES; THE VERIFIER DOES NOT ASK IT: these statements are
steps on the way to "the maker of the proof file's description returns", not tests that pass.
`VerifierAndGoals.storedPublicFiles` is three terms written in Ladder/Stored.lean: no Lean code ties them to the
repository's folder examples/; the example's weights are synthetic. The counts of padding places are
made next to the key forms, from the lists of columns and pieces, not from the forms: a fault inside
a form or in a list is not seen by them, and nothing here says otherwise. Nothing on soundness.

-/
import Johnson.AtFull.K3X.ReadsOfSix
import Johnson.AtFull.K3X.LaidAtFull
import Johnson.AtFull.K3X.SixBefore
import Johnson.AtFull.K3X.PadKeyLaw
import Johnson.AtFull.K3X.HeadSegment
import Johnson.AtFull.K3X.HeadLk
import Johnson.AtFull.Public.AtX0All

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.K3X

open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Public (Makers opens_yFull)
open Johnson.AtFull.Lots.K3 (ReadsX readsXB)
open OnBytes.Road.K4.Trial.Values (PW yFull polLayout_W)
open OnBytes.Model.Layer (ropeTable)
open OnBytes.Road.K4.Trial.AttL2 (AOf)
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (shape_at_stored)

/-- **The six statements at each of the 25 links.** -/
theorem six_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : ∀ i, i < 25 → SixAt X₀ i := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e1, e2, ⟨e3, -, e3L⟩, e4, ⟨e5, -⟩, e6, e7,
    e8, -, -, hX'⟩ := _root_.AtFull.Public.publicOfO_zFull_of_rest hsz
  obtain ⟨pp, hF, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hF polLayout_W
  have M : Makers yFull sc wsLay (ropeTable 12 500000 128 10) l ps layers G seenA :=
    { groups := _root_.AtFull.Public.yFull_NGr, p3 := _root_.AtFull.Public.yFull_p3,
      p4 := _root_.AtFull.Public.yFull_p4, scales := e1, weights := e2, rotary := p10, lines := e4,
      twins := e5, record := e6, plans := e7, owners := e8 }
  have ey : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have e : X₀ = _ := Except.ok.inj (hX.symm.trans hX')
  have eL : X₀.layers = layers := by rw [e]
  have eG : X₀.G = G := by rw [e]
  have eA : X₀.A = AOf ps.toArray seenA := by rw [e]
  have eS : X₀.hS = headShape PW yFull := by rw [e]
  have eY : X₀.HLy = HLy := by rw [e]
  have eH : X₀.H = { _root_.AtFull.Head.HW with Fp := _root_.AtFull.Head.HW.Fp.trimL } := by rw [e]
  have hN : X₀.NGr = 12 := by
    show X₀.layers.y.NGr = 12
    rw [eL, ey]
    exact _root_.AtFull.Public.yFull_NGr
  have h4 : X₀.p4 = true := by
    show X₀.layers.y.h.p4 = true
    rw [eL, ey]
    exact _root_.AtFull.Public.yFull_p4
  have hS : headShape PW yFull = Cond.hFull :=
    (shape_at_stored yFull).trans (by rw [_root_.AtFull.Public.yFull_lPd]; rfl)
  intro i hi
  rcases Nat.lt_or_ge i 24 with h24 | h24
  · obtain ⟨g, hg⟩ : ∃ g, i = 2 * g ∨ i = 2 * g + 1 := ⟨i / 2, by omega⟩
    rcases hg with rfl | rfl
    · exact six_layers opens_yFull M hN h4 eL eG (by rw [ey]; exact counts_yFull) (laid_of_y ey) g
        (by omega)
    · exact six_attention opens_yFull M hN h4 eA (padKeyAtt_public_o hX) g (by omega)
  · obtain rfl : i = 24 := by omega
    exact seg24 h4 hN (eS.trans hS) (by rw [eY, ← e3]; exact e3L) eH
      (by rw [eL]; exact lk_at opens_yFull M)

/-- **The six hypotheses on the public data.** -/
theorem readsX_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : ReadsX X₀ := readsX_of_six (six_zFull hsz hX)

/-- **The comparison with code accepts.** -/
theorem readsXB_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : readsXB X₀ = true := readsXB_of_six (six_zFull hsz hX)

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.six_zFull
#print axioms Johnson.AtFull.K3X.readsX_zFull
#print axioms Johnson.AtFull.K3X.readsXB_zFull
