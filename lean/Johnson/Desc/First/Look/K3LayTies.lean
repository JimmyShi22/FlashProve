-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LayTies.lean: the lookup on a LAYERS' link's calls: the ties t3 and t4
between our relations and the table of joints' items at the lookup's place: THE LOWER STOREY (t1:
Johnson/Desc/First/Look/K3CallsTies.lean; t2: K3CallsLookOut.lean). Ties: no error term. NO
SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: our relations LayFront, LayBehind.
Used by K3CallsAt.lean, K3CallsAtR.lean, K3CallsMeanOf.lean (Johnson/Desc/First/Look/) and 18 more.
LETTERS: those of k3_lay_goodIn_any.
Built on: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

Main names:
  `layObjects`, `layWorthPlanes`, `layWorthKeys`, `layWorthRider`: the general items
    (Johnson/Top/H/K3Worth.lean) at the layers' letters.
  `k3_lay_t3` · `layBehind_items` (t3's converse) · `k3_lay_t4`.

Limits. The lower storey alone. THE STORED TABLE STANDS AT LETTERS: LayPin's second half (the stored
table's word decodes, with the sample that the record holds, to the witness's message msgW w) is
taken and given as it stands: its tie to the table's item pinW is not here. t4 ends at our own
sentence LaySays and at LayPin.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Top.H.K3Worth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (q : LayPub) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard)

abbrev layObjects (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3Objects fork heard x.fs x.lm x.F.next (layNu x q tl D rad oW wOf nr nc seatT arr msgW) s w

abbrev layWorthPlanes (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthPlanes fork heard x.fs x.lm x.F.next (layNu x q tl D rad oW wOf nr nc seatT arr msgW) s w

abbrev layWorthKeys (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthKeys fork heard x.fs x.lm x.F.next (layNu x q tl D rad oW wOf nr nc seatT arr msgW)
    (fun w => forK Cb.Gl.E (layLay q x.fs x.lm x.F.next x.ns tl nr nc) ()
      (zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w))) s w

abbrev layWorthRider (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthRider fork heard (layRider x q tl D rad oW wOf nr nc extNone Unit) x.lm x.F.next
    (fun _ => ()) (layMs x D rad oW seatT arr msgW) s w

variable {x q tl D rad oW wOf nr nc}
variable (smp : S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str) (Own : S → Prop)

/-- **t3, the lower storey.** -/
theorem k3_lay_t3 (b : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (hPin : LayPin G x D rad oW seatT arr smp smpW strW msgW b w)
    (hOn' : LayOn' G x D rad oW seatT smp smpW strW fork heard Own b)
    (hRows : layObjects x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w)
    (hPlanes : layWorthPlanes x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w)
    (hKeys : layWorthKeys x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w)
    (hRider : layWorthRider x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w) :
    LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW fork heard b w := by
  obtain ⟨-, g, F', hf, hh, -, -⟩ := hOn'
  exact ⟨hPin, g, F', hf, hh, ⟨hRows g F' hf hh, hPlanes g F' hf hh, hKeys g F' hf hh⟩,
    hRider g F' hf hh⟩

/-- **The other way.** -/
theorem layBehind_items (b : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW fork heard b w) :
    LayPin G x D rad oW seatT arr smp smpW strW msgW b w ∧
      layObjects x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w ∧
      layWorthPlanes x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w ∧
      layWorthKeys x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w ∧
      layWorthRider x q tl D rad oW wOf nr nc seatT arr msgW fork heard b.1 w := by
  obtain ⟨hp, g₀, F₀, hf₀, hh₀, hK, hR⟩ := h
  have key : ∀ g F', fork b.1 = some F' → heard b.1 = some g → F₀ = F' ∧ g₀ = g :=
    fun g F' hf hh => ⟨Option.some.inj (hf₀.symm.trans hf), Option.some.inj (hh₀.symm.trans hh)⟩
  refine ⟨hp, fun g F' hf hh => ?_, fun g F' hf hh => ?_, fun g F' hf hh => ?_,
    fun g F' hf hh => ?_⟩ <;> obtain ⟨rfl, rfl⟩ := key g F' hf hh
  · exact hK.1
  · exact hK.2.1
  · exact hK.2.2
  · exact hR

/-- **t4, the lower storey.** -/
theorem k3_lay_t4 (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW a w) :
    LaySays x q tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w) ∧
      LayPin G x D rad oW seatT arr smp smpW strW msgW a w :=
  ⟨h.2, h.1⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lay_t3
#print axioms VerifiableInference.OnPublicFiles.layBehind_items
#print axioms VerifiableInference.OnPublicFiles.k3_lay_t4
