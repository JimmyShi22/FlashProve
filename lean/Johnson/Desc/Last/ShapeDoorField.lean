-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorField.lean: SH₃ IN THE LETTERS OF THE FIELD: the field SH₃ of the
structure of what makes the three tables fit at the chains' ends (`TablesFitR`,
Johnson/P5J/TopTablesR.lean): inside the shared
table's promise at its last border, with the first table's whole promise at its last border and a
condition Rc on what the first chain hands on, where the last chain's start accepts, the last
table's book-keeping accepts at border 0. One statement with its proof; no definition.

Main name (namespace `VerifiableInference.Desc.Last`).
  **`sh₃_field`**: ITS CONCLUSION IS THAT FIELD'S TEXT at the seated description's types, with that
    structure's `ocR get N₁ Mg₁ links ps Rc` unfolded (`fun q y => ocEnd … q y ∧ Rc q`) and start₃
    := the seated description's own (`ProofFile.seatedAt o Z Np c`), as an Option. GENERAL IN the shared
    table's promise's meaning Pm, the last table's book-keeping PLm, Rc, a test X on the shared
    chain's last state, the pieces T, the numbers N, the first table's meaning and lists.

Its premises, each by name.
  hZ: the public part is the computed one (spent for one test on the plan: the masks stand ahead).
    hg: g leaves the verifier's state.
  H : `DoorStays N₁ Mg₁ links ps Pw V` (Johnson/Desc/Last/ShapeDoorFold.lean).
  hR: inside the first table's last promise, under Rc, without a mark: `FourFacts V` of the first
    chain's last state (tidy · the book fits · the pending rows' weights · the two own seats sit).
  hD, hX: OF Pm ITS TEST AT THE SHARED CHAIN'S LAST BORDER ALONE IS READ: where it accepts, the
    shared chain's text at the door holds (`doorSharedB`), and X accepts.
  hPL: where `fillZ`'s book-keeping accepts at border 0 and X accepts, PLm's accepts at border 0.

By: `sh₃_of_first` (Johnson/Desc/Last/ShapeDoorSays.lean), `doorFirstB_of_fold`, and the seat's
three laws. THE FORM `sh₃_fold_X` (Johnson/Desc/Last/ShapeDoorFold.lean) stands at Pm :=
`besideP Pm₀ …`, where what hD and hX ask holds by the make and is no premise; it concludes
`fillZ`'s book-keeping at border 0 AND X of the shared chain's last state; its hR has no promise in
front.
Limits. A rule over letters: no member: that one V, one Pm, one PLm and one Rc meet all premises
together is shown by nobody. That the conclusion's two fences are met anywhere is not shown. Nothing
on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeDoorFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open OnBytes

namespace VerifiableInference.Desc.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets weightsB openSets sampledIn)
open _root_.Desc.K14 (St)

/-- **SH₃, IN THE LETTERS OF THE FIELD**: the shared table's promise's meaning Pm and the last
table's book-keeping PLm are letters; of Pm its test at the shared chain's last border alone is
read. -/
theorem sh₃_field {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (R : List Fmt.DeclaredRound)
    (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm : PromMeaning St)
    (PLm : PromMeaningL St S₃ (ProofFile.InstPub × First.S)) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (Pw : K13.Where)
    (V : OwnSeats) (H : DoorStays N₁ Mg₁ links ps Pw V)
    (Rc : ProofFile.InstPub × First.S → Prop)
    (hR : ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc q → (g q).2.failed = none →
      FourFacts V (g q).2) (X : St → Bool)
    (hD : ∀ d, Pm.shape (1 + T.l₂.length) d = true → doorSharedB (ProofFile.pAt Z) d = true)
    (hX : ∀ d, Pm.shape (1 + T.l₂.length) d = true → X d = true)
    (hPL : ∀ q e s, (fillZ (ProofFile.pAt Z) R fun q => (g q).2).shape 0 q e s = true → X e = true →
      PLm.shape 0 q e s = true) :
    ∀ (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃),
      onQ₂ N Pm (fun q y => ocEnd g N₁ Mg₁ links ps q y ∧ Rc q) split T.p₂ T.l₂
        (1 + T.l₂.length) b →
      ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s →
      PLm.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true := by
  intro b s hb hs
  have hmem : PromS.shape (1 + T.l₂.length) ∈ promsAt split (1 + T.l₂.length) := by
    unfold promsAt
    simp
  refine hPL _ _ _ ?_ (hX _ (hb.1 _ hmem))
  exact sh₃_of_first (ProofFile.pAt Z) R g
    (fun q a d => ((ProofFile.seatedAt o Z Np c).start₃ q a d).toOption) T N Pm _ split hD
    (fun q y hq hm => doorFirstB_of_fold g N₁ Mg₁ links ps Pw V H q y hq.1 hm (hR q y hq.1 hq.2 hm))
    (ProofFile.hmark_at o Z Np c g hg) (ProofFile.hstart_at o Z Np c g hg) (ahead_at_seat hZ) b s hb hs

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.sh₃_field
