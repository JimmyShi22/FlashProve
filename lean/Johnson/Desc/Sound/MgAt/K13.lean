-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K13.lean: what the authors of the last sub-protocols of a request's own
rounds (kind K13: the claims on the committed table are joined into one) assume of a `Meaning`
holds at THE WIDER MEANING (`mgWide`, Johnson/Desc/Sound/MgWide.lean). A definition and theorems.
`K13.Law.FillsK13` (Johnson/Desc/K13/Law/FillsK13.lean) is a structure of 21 fields, each "this
field, or this public test, of the meaning is this term". Six of them name public tests that the
table does not ask at the composed meaning (`mgAll`), and one the wide test "in
order": so the structure holds at `mgWide`, not at `mgAll`; a tie that is typed under it is
carried to `mgAll` by the bridge (Johnson/Desc/Sound/PlusDoorA.lean).
  `rest13W 𝔇 E Mg`: the conjuncts of the wide test "in order" that are not these authors'.
  `mgWide_pubP_quiet`: the public sentences at these authors' nine quiet items hold at `mgWide`,
    where they hold at Mg (none of the nine is left, leftOn or hasRow).
  `fillsK13_mgWide`: `FillsK13 … (mgWide 𝔇 E Mg) …` at the term's own parameters, UNDER TWO
    PREMISES: on a datum of the struck parts: the proximity test's first Merkle tree has number 0
    (E.d12.ft = 0); on Mg: its public sentences hold AT THE NINE QUIET ITEMS (not at every item:
    the closed base says False at an item that nobody answers for).
  `weights_mgWide`: the public test on the weights' claims is its authors' own.
Limits: it says which terms the fields and tests ARE at the wider meaning. Nothing is said of any
sub-protocol. No soundness is claimed.

-/
import Johnson.Desc.Sound.MgWide
import Johnson.Desc.K13.Law.FillsK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (Meaning Pub)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (E : WideData P)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The conjuncts of the wide "in order" that are not these authors'. -/
def rest13W (x : P × First.S) : Bool :=
  (((Mg.inOrder x && First.eqsB 𝔇.cs 𝔇.shape 𝔇.layout x.2) && First.reqIsB (E.reqW x.1) x.2) &&
    (_root_.Meaning.backReq (𝔇.reqB x.1)).isSome)

theorem mgWide_pubP_quiet (hP : ∀ q ∈ K13.Law.quietK13, ∀ x, Mg.pubP q x) (q : Pub)
    (hq : q ∈ K13.Law.quietK13) (x : P × First.S) : (mgWide 𝔇 E Mg).pubP q x := by
  have h0 := hP q hq x
  show (mgAll 𝔇 Mg).pubP q x
  rw [mgAll_pubP]
  simp only [K13.Law.quietK13, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact h0

theorem fillsK13_mgWide (hft : E.d12.ft = 0) (hP : ∀ q ∈ K13.Law.quietK13, ∀ x, Mg.pubP q x) :
    K13.Law.FillsK13 𝔇.P13 𝔇.N (mgWide 𝔇 E Mg) 𝔇.cs 𝔇.shape 𝔇.layout (rest13W 𝔇 E Mg) 𝔇.arr 𝔇.mat13
      𝔇.G 𝔇.smp 𝔇.ms 𝔇.decT E.d12.M E.d12.L where
  pile := fun _ _ _ => Iff.rfl
  pileOne := fun _ _ _ => Iff.rfl
  frontOk := fun _ => rfl
  evalLaid := fun _ => rfl
  wSits := fun _ => rfl
  indexIs := fun _ => rfl
  indexThere := fun _ => rfl
  masks := fun _ => rfl
  within := fun _ => rfl
  oneRow := fun _ => rfl
  inOrder := fun x => by
    rw [mgWide_inOrder_at]
    exact Bool.and_right_comm _ _ _
  book := fun x => by
    rw [← hft]
    rfl
  seats := fun _ => rfl
  shapes := fun _ => rfl
  held := fun _ => rfl
  shown := fun _ => Iff.rfl
  noColl := fun _ _ => Iff.rfl
  pin := fun _ _ _ => Iff.rfl
  pinW := fun _ _ _ => Iff.rfl
  decodes := fun _ _ => Iff.rfl
  quiet := mgWide_pubP_quiet 𝔇 E Mg hP

theorem weights_mgWide (x : P × First.S) :
    (mgWide 𝔇 E Mg).pub (.more none "K13.weightsOk") x = First.weightsB x.2 := rfl

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mgWide_pubP_quiet
#print axioms VerifiableInference.Desc.Sound.fillsK13_mgWide
#print axioms VerifiableInference.Desc.Sound.weights_mgWide
