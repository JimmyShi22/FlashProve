-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmHeadB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmHead.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 3 OF ITS
DECLARATIONS: head_at_reads_of_b · head_at_reads_b · arm_at_reads_three_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the elder's block binds
dk (no twin's statement names it any more; it is kept so that a copied call has the elder's number
of arguments). Kept as they stand in the elder: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmHead
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open OnBytes.Road.Hd (FullH)
open OnBytes.Road (Switches Sized Sized2)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)
open VerifiableInference.Desc.Kinds.Head.Law.Planes

end

open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn ArmCellIn)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (uHeadK6 K6Name TablesCome)
open VerifiableInference.Desc.First.Att.P (uArm)
open OnBytes.Road.K4 (uLay)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- **The premise hHead of arm_at_reads_of.** -/
theorem head_at_reads_of_b (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hUH : Dm.uH = uHeadK6 XV) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hK6 : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms Dm.N
        24 w l₀ piece states cU)
    (hPl : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU)
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l) := by
  intro l X arrs x x' y y' w p A B F hsub
  obtain rfl : l = 24 := by
    have t := List.all_eq_true.1 headIs24 l (List.mem_range.2 F.lt)
    rw [hsub] at t
    exact eq_of_beq t
  have hr := rides_at_reads_b F
  by_cases hn : K6Name p.2
  · have hTC : TablesCome XV x.2 x'.2 := by
      obtain ⟨_, rs, gs, hfit, hd⟩ := F.yes
      have hlen : (rs.map noDigest).length = 2 := by
        rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
      rw [← hWX]
      exact tablesCome_at_reads Z Bs.G₀ X F.built _ arrs x.2 x'.2 _ gs hlen hd
    obtain ⟨l₀, piece, states, cU, L⟩ := hK6 X arrs x x' y y' w p A B F hn
    rw [hUH]
    exact armCellIn_head L hS hR (hWX ▸ O.public) x'.2 x'.1 hr.arrays hTC F.behind F.tie p.2 hn
  · by_cases hp : p.2 = "planes"
    · obtain ⟨states, cU, L⟩ := hPl X arrs x x' y y' w p A B F hp
      rw [hUH, hp]
      exact armCellIn_headPlanes L (by rw [hr.arrays]; exact L.hArr)
    · exact hElse X arrs x x' y y' w p A B F hn hp

/-- **THE PREMISE hHead OF arm_at_reads, TO THE LETTER.** -/
theorem head_at_reads_b (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hUH : Dm.uH = uHeadK6 XV) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hK6 : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms Dm.N
        24 w l₀ piece states cU)
    (hPl : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU)
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .head →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH l) :=
  head_at_reads_of_b Dm dk mgBase J hS hR O hUH hWX aN R₁ R₂ R₃ hK6 hPl hElse

/-- **THE BINDER hArm, BEHIND THE TIE AND ArmOk J, WITH ALL THREE SORTS' HALVES CALLED**:
arm_at_reads with its premise hHead paid by head_at_reads: Lean's own check that the two fit. -/
theorem arm_at_reads_three_b (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hDlk : Dm.links = linksFull) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hLay : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w))
    (hUA : Dm.uA = uArm XV)
    (hAtt : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w))
    (hUH : Dm.uH = uHeadK6 XV) (hWX : Bs.G₀.W = XV)
    (hK6 : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms Dm.N
        24 w l₀ piece states cU)
    (hPl : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → p.2 = "planes" →
      ∃ states cU, PlanesLeft XV (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) states cU)
    (hElse : ∀ X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → ¬ K6Name p.2 → p.2 ≠ "planes" →
      ArmCellIn (Dm.Rd 24) (Dm.N.sent 24 0) (Dm.N.group 24) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (Dm.uH 24)) :
    ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (x x' : ProofFile.InstPub × S) y y'
      (w : Wit (CellsQ rows cols) Tok MsgT),
      YesOf (blkL Z Bs.G₀ l false X arrs) x x' → InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull (flatPlacesOf linksFull true) (noL l false) x y →
      ArmOk J x.2 →
      KeptBelow (baseL aN R₁ R₂ R₃ c l false) y y' → (mgAll Dm mgBase).tie l x' y' w →
      ∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
      ∀ p ∈ Dm.runs l j n, ∀ A B, K9.segAt? x.2 = some A → K9.segAt? x'.2 = some B →
      ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 x.2 A B
        (seatTab Dm.cs Dm.arr Dm.ms w) (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l) :=
  arm_at_reads_b Dm dk J hDlk Z Bs aN R₁ R₂ R₃ c hLay hUA hAtt
    (head_at_reads_b Dm dk J hS hR O hUH hWX aN R₁ R₂ R₃ hK6 hPl hElse)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.head_at_reads_of_b
#print axioms VerifiableInference.Desc.K1.head_at_reads_b
#print axioms VerifiableInference.Desc.K1.arm_at_reads_three_b
