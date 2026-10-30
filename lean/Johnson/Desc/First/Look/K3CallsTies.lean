-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsTies.lean: the lookup on a link's CALLS: THE TIES BETWEEN OUR
CONDITIONS AND RELATIONS AND THE TABLE OF JOINTS' PROMISE AND ITEMS AT THE LOOKUP's PLACE: THE LOWER
STOREY: at the carried record and the oracles' strings, free of the table's own files but the two
Bools of Johnson/Desc/First/Look/K3Borders.lean: the table's clauses stand as named premises in our
letters. What the table's items worth "planes", "keys", "rider" say is Johnson/Top/H/K3Worth.lean's.
Attention; of the layers t1. Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: our conditions and relations (AttOn, AttBehind, ...), which speak of the
  calls' seat's readers.
USER: k3_att_atTable (Johnson/Desc/First/Look/K3AttAtTable.lean).
LETTERS: those of k3_att_goodIn_any and k3_lay_goodIn_any.
GROUND: Johnson/Desc/Block.lean,
  Johnson/Desc/First/State.lean,
  Johnson/Desc/First/Look/K3Lookup.lean.

The ties are numbered as the table's door numbers them: t1: the promise in front gives our condition
in front. t2: our condition behind, behind a yes, gives the promise behind. t3: what the row opens,
at the statement behind, gives our relation behind. t4: our relation in front gives what the row
closes.

Main names:
  `attObjects`, `attWorthPlanes`, `attWorthKeys`, `attWorthRider`: the general items at attention's
    letters.
  `k3_att_t1`, `k3_lay_t1` · `k3_att_t3` · `attBehind_items` (t3's converse: for the rows that
  close these items) · `k3_att_t4`. (t2: Johnson/Desc/First/Look/K3CallsLookOut.lean; the layers' t3
  and t4: K3LayTies.lean.)

Limits. THE LOWER STOREY ALONE: nothing here names the table's onQ, meansQ or its door. t1 takes as
premises what the table's promise must hold for it: k3OnIn; the record's own five are D's; at every
member of the link's list: a sample held, every leaf shown, no collision. t4 ends at our own
sentence AttSays and the pins: FROM THERE TO THE MODEL's CLAUSES (constr lookCalls, constr rider) is
other files' to show. The item "objects" is taken in our form (K3OutRows), not in the
table's (forms worth 0 in a world).
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Desc.First.Look.K3DigitsTies
import Johnson.Top.H.K3Worth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-! ## Attention -/

section
variable {S Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (A : Attention.Shape) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard)

/-- The general items (Johnson/Top/H/K3Worth.lean) at attention's letters. -/
abbrev attObjects (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3Objects fork heard x.fs x.lm x.F.next (attNu x A tl D rad seatT arr) s w

abbrev attWorthPlanes (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthPlanes fork heard x.fs x.lm x.F.next (attNu x A tl D rad seatT arr) s w

abbrev attWorthKeys (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthKeys fork heard x.fs x.lm x.F.next (attNu x A tl D rad seatT arr)
    (fun w => forK Cb.Gl.E (attLay A x.fs x.lm x.F.next x.ns tl) ()
      (zext (attMu x tl D rad seatT arr w))) s w

abbrev attWorthRider (s : S) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  K3WorthRider fork heard (attRider x A tl D rad extNone Unit) x.lm x.F.next (fun _ => ())
    (attMs x D rad seatT arr) s w

variable {x A tl D rad}
variable (smp : S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp) (Own : S → Prop)

/-- **t3, the lower storey.** -/
theorem k3_att_t3 (b : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (hPin : PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) b.1
      (strsOf Fr b.2) w)
    (hOn' : AttOn' G x D rad seatT smp fork heard Own b)
    (hRows : attObjects x A tl D rad seatT arr fork heard b.1 w)
    (hPlanes : attWorthPlanes x A tl D rad seatT arr fork heard b.1 w)
    (hKeys : attWorthKeys x A tl D rad seatT arr fork heard b.1 w)
    (hRider : attWorthRider x A tl D rad seatT arr fork heard b.1 w) :
    AttBehind G x A tl D rad seatT arr smp fork heard b w := by
  obtain ⟨-, -, g, F', hf, hh, -, -⟩ := hOn'
  exact ⟨hPin, g, F', hf, hh, ⟨hRows g F' hf hh, hPlanes g F' hf hh, hKeys g F' hf hh⟩,
    hRider g F' hf hh⟩

/-- **The other way**: the relation behind gives the pins and the four items. -/
theorem attBehind_items (b : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : AttBehind G x A tl D rad seatT arr smp fork heard b w) :
    PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) b.1
        (strsOf Fr b.2) w ∧
      attObjects x A tl D rad seatT arr fork heard b.1 w ∧
      attWorthPlanes x A tl D rad seatT arr fork heard b.1 w ∧
      attWorthKeys x A tl D rad seatT arr fork heard b.1 w ∧
      attWorthRider x A tl D rad seatT arr fork heard b.1 w := by
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
theorem k3_att_t4 (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT)
    (h : AttFront G x A tl D rad seatT arr smp a w) :
    AttSays x A tl D rad (attMs x D rad seatT arr w) ∧
      PinSig G D.codes (sigListCalls D rad x.link) seatT smp arr (fun _ => True) a.1
        (strsOf Fr a.2) w :=
  ⟨h.2, h.1⟩

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

/-- **t1, the lower storey, at attention.** -/
theorem k3_att_t1 (claim : Aff → Cl) {set : Params.Setting} (a : Desc.First.S × Fr.E.Str)
    (hOwn : OwnIs D x.link a.1)
    (hCf : ∀ i, CfAt G D.codes (sigListCalls D rad x.link) seatT smp i a.1 (strsOf Fr a.2))
    (hIn : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace set false x) a.1 = true) :
    AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link) a := by
  obtain ⟨Fk, hf, hz, -⟩ := k3OnIn_ledger hIn
  exact ⟨hOwn, fun i _ => hCf i, Fk, hf, hz⟩

/-- **t1, the lower storey, at the layers**: with the stored table's clause. -/
theorem k3_lay_t1 {oW : Cb.OMsg Cb.Gl.E} (smpW : Desc.First.S → Option oW.Smp)
    (strW : Fr.E.Str → oW.Str) (claim : Aff → Cl) {set : Params.Setting}
    (a : Desc.First.S × Fr.E.Str) (hOwn : OwnIs D x.link a.1)
    (hCf : ∀ i, CfAt G D.codes (sigListCalls D rad x.link) seatT smp i a.1 (strsOf Fr a.2))
    (hW : ∃ σW, smpW a.1 = some σW ∧ ¬ oW.Clash (strW a.2) σW.1)
    (hIn : Desc.K3.k3OnIn (Desc.First.Look.P.ofPlace set false x) a.1 = true) :
    LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link) a := by
  obtain ⟨Fk, hf, hz, -⟩ := k3OnIn_ledger hIn
  exact ⟨⟨hOwn, fun i _ => hCf i, hW⟩, Fk, hf, hz⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_att_t1
#print axioms VerifiableInference.OnPublicFiles.k3_lay_t1
#print axioms VerifiableInference.OnPublicFiles.k3_att_t3
#print axioms VerifiableInference.OnPublicFiles.attBehind_items
#print axioms VerifiableInference.OnPublicFiles.k3_att_t4
