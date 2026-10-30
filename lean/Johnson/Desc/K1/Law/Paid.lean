-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/Paid.lean: PaidAt reaches K1's 51 own Par terms, by paid_of_placeOk ∘ k01_sits_first_chain.
PaidAt P rad (Johnson/Desc/K1/Law/RoundsLit.lean):
the kind's Boolean · one seed · the error's number · the comparison powB P rad 128, whose right side bears 2 ^ P.work (P.work is 0 at the places of this file) · the two pieces' errors below 2⁻¹²⁸.
  k01_paid_first_chain     at the written codes and the written shape: firstPar and every parLater (l < 25; m = 1 | 2) are paid at their written record's radii
  k01_paid_digits | _reads in scope: at the description's own entry b: IsSend ∧ PaidAt
Nothing on soundness. PaidAt's comparison has a factor for a round's proof of work; at the places of this file that work is 0. What PaidAt's own head does not claim is not claimed here.
-/
import Johnson.Desc.K1.Law.SitsAtt
import Johnson.Desc.K1.Law.RoundsLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.ReqLit (shapeFull)
open ProofFile (Cl)
open IM (Open k1Ix)

/-- A place is paid at the radii of record number k of the proof file's first chain. -/
def PaidRec (k : Nat) (P : Par) : Prop :=
  ∃ y, (litAt sendsFullLit packFullLit 2 0)[k]? = some y ∧ PaidAt P (radFrom P y.2.l)

theorem k01_paid_first_chain (q : Params.First) (gp : GPar) (hc : q.codes = codesFull2)
    (hs : q.shape = shapeFull) :
    PaidRec 0 (firstPar q gp) ∧
      ∀ l piece m, l < 25 → (m = 1 ∨ m = 2) → PaidRec (3 * l + m) (parLater q gp l piece m) :=
  ⟨paid_of_placeOk (k01_sits_first_chain q gp hc hs).1,
    fun l piece m hl hm => paid_of_placeOk ((k01_sits_first_chain q gp hc hs).2.1 l piece m hl hm)⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem k01_paid_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l true]? = some b ∧
      IsSend (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) (fun s : S => s.st) b ∧
      PaidRec (3 * l + 2) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) := by
  intro l hl
  obtain ⟨Lk, b, e1, e2, h, hp, -⟩ := k01_law_digits hS hR O hc hs l hl
  exact ⟨Lk, b, e1, e2, h, paid_of_placeOk hp⟩

theorem k01_paid_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l false]? = some b ∧
      IsSend (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) (fun s : S => s.st) b ∧
      PaidRec (3 * l + 1) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) := by
  intro l hl
  obtain ⟨Lk, b, e1, e2, h, hp, -⟩ := k01_law_reads_whole hS hR O hc hs l hl
  exact ⟨Lk, b, e1, e2, h, paid_of_placeOk hp⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_paid_first_chain
#print axioms VerifiableInference.Desc.K1.k01_paid_digits
#print axioms VerifiableInference.Desc.K1.k01_paid_reads
