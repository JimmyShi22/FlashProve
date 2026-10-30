--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/RowsAtRch.lean: OUR 101 NUMBERS, AND K8's 25 AMONG THEM, IN THE LETTERS
OF SharesRB: HandsR at the narrow fence RB: "reached by the wrapped sub-protocols'
steps". Two theorems, proved: calls.



  rows_at_rch   rows_at_plan at Fk := RB c Z p, hFk := rb_wide. The debt
    MadeOwed is asked at that same fence.
  k8_rows_rch   k8_rows (Johnson/IMR/K8Owed.lean) likewise: hBl and "new", the latter at that fence.

OBJECT: c.blocksInOrder[k]. USER: none in Lean yet. LETTERS: N₀, D, base, z, p: free.

What is not claimed. MadeOwed, hBl or "new" anywhere. No soundness.
-/
import Johnson.IMR.GrownRch
import Johnson.IMR.K8Owed

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K8 (TlBlind)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **OUR 101 AT THE NARROW FENCE.** -/
theorem rows_at_rch {Q : Type} {D : PubData} {base : Pub → Q × S → Bool} {z : Q}
    {p : ProofFile.InstPub} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hF : F.planOk = true)
    (N₀ : Numbers) (alike : ∀ q s s', base q (z, s') = base q (z, s)) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true)
    (M : MadeOwed (RB c Z p) (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW D
      base z 0 k b b.place) :
    HandsR (RB c Z p) (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
      (LPFK9.HandsAt.EW D base z) 0 k b :=
  rows_at_plan hS hR O hF N₀ alike hb hq rb_wide M

/-- **K8's 25 AT THE NARROW FENCE.** -/
theorem k8_rows_rch {Q : Type} {D : PubData} {z : Q} {p : ProofFile.InstPub}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hk : b.place.kind = .K8) {l : ℕ} (hl : b.place.link = some l)
    (hBl : ∀ j r, j < b.place.piece → ∀ q ∈ D.runs l j r,
      TlBlind fun s => if D.ah q.1 q.2 then
          VerifiableInference.Desc.K9.formsInA (D.Rd l) (D.N.sent l) (D.N.group l) q.1 q.2 s
        else VerifiableInference.Desc.K9.formsIn (D.Rd l) (D.N.group l) q.1 q.2 s)
    (new : ∀ s s', RB c Z p k s → Yes 0 b s s' → s.failed = none → s'.failed = none →
      XK (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
        (EAt D (fun _ _ => false) linksW placesW z) k s = true →
      pubAll D (fun _ _ => false) (.formsIn l b.place.piece "small") (z, s') = true) :
    HandsR (RB c Z p) (N₀.withTold placesW (Meaning.Carry.toldOf c.blocksInOrder)) linksW placesW
      (LPFK9.HandsAt.EW D (fun _ _ => false) z) 0 k b :=
  k8_rows hS hR O hF N₀ hb hk hl rb_wide hBl new

end IM

#print axioms IM.rows_at_rch
#print axioms IM.k8_rows_rch
