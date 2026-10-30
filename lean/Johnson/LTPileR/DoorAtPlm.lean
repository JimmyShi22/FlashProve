-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LTPileR/DoorAtPlm.lean
(over PlmCode.lean): SH₃, THE FIELD, AT THE LAST TABLE'S MEANT BOOK-KEEPING: the
one with two layers at which the last chain's row concludes. Statements with proofs; no definition.

Why. The last table's row concludes at PLm := `besideS (fillAt p R hand (endedX X)) (yTree cs S)`:
the book-keeping, with a test X on the shared chain's last state laid into "ended", and a test on
the last chain's own state at borders 1 and 2 (`yTree`). `sh₃_field`
(Johnson/Desc/Last/ShapeDoorField.lean) takes PLm as a letter, under hPL: where `fillZ`'s
book-keeping accepts at border 0 and X accepts, PLm's accepts at border 0. Here hPL is paid at that
term.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`shape0_at_layers`**: from `(fillZ p R fs).shape 0 q e s = true` and `X e = true`: `(besideS
    (fillAt p R (fun q => firstOfS (fs q)) (endedX X)) (yTree cs S)).shape 0 q e s = true`. At
    border 0 `yTree` accepts every state; where X accepts, `endedX X` is `fillZ`'s own "ended".
    General in p, R, fs, X, cs, S.
  **`sh₃_field_plm`**: `sh₃_field` at that PLm, at p := `ProofFile.pAt Z`, every cs and S: ITS PREMISES:
    hZ · hg · H · hR · hD · hX, as there; hPL IS NO PREMISE.
  `promSigS_beside`: `promSigS … (besideP Pm₀ X) = besideP (promSigS … Pm₀) X`: rfl: the two
    fillings of the shared table's promise commute.

Limits. Those of ShapeDoorField.lean: a rule over letters; no member. PlmCode.lean's head writes
the parameters as `ToldDesc.p14At Z` (Johnson/ToldDescR/RcLastCode.lean): one text with `ProofFile.pAt Z`;
that equation is not here (it would bring that file's cone). Nothing on soundness or on hiding.

-/
import Johnson.Desc.Last.ShapeDoorField
import Johnson.Desc.Sound.BordersSharedFill
import Johnson.LLT25R.PlmCode

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
open LLT25 (besideS yTree endedX)

/-- **The door's two halves, at the book-keeping with the two layers.** -/
theorem shape0_at_layers {P S₁ : Type} (p : P₁₄) (R : List Fmt.DeclaredRound) (fs : P × S₁ → First.S)
    (X : St → Bool) (cs : Codes) (S : Params.LinShape) (q : P × S₁) (e : St) (s : S₃)
    (h1 : (fillZ p R fs).shape 0 q e s = true) (h2 : X e = true) :
    (besideS (fillAt p R (fun q => firstOfS (fs q)) (endedX X)) (yTree cs S)).shape 0 q e s =
      true := by
  have e1 : endedX X e = (_root_.Desc.K14.ended e).map sharedOfEnd := by
    unfold endedX
    rw [if_pos h2]
  have e2 : (fillAt p R (fun q => firstOfS (fs q)) (endedX X)).shape 0 q e s =
      (fillZ p R fs).shape 0 q e s := by
    unfold fillZ fillAt
    simp only [e1]
  show ((fillAt p R (fun q => firstOfS (fs q)) (endedX X)).shape 0 q e s && yTree cs S 0 s) = true
  rw [e2, h1]
  rfl

/-- **SH₃, THE FIELD, AT THE LAST TABLE's MEANT BOOK-KEEPING.** -/
theorem sh₃_field_plm {C : CK} {D : WholeD} {all : List LeftT} {Y P₀ X₁ X₂ Cl Wt W₁ : Type}
    (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (R : List Fmt.DeclaredRound)
    (g : ProofFile.InstPub × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁)
    (T : Three C D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃) X₁ X₂ Cl Wt)
    (N : NumbersS) (Pm : PromMeaning St) (split : Bool)
    (N₁ : Numbers) (Mg₁ : Meaning P₀ W₁) (links : List ModelPart) (ps : List Place) (Pw : K13.Where)
    (V : OwnSeats) (H : DoorStays N₁ Mg₁ links ps Pw V)
    (Rc : ProofFile.InstPub × First.S → Prop)
    (hR : ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc q → (g q).2.failed = none →
      FourFacts V (g q).2) (X : St → Bool)
    (hD : ∀ d, Pm.shape (1 + T.l₂.length) d = true → doorSharedB (ProofFile.pAt Z) d = true)
    (hX : ∀ d, Pm.shape (1 + T.l₂.length) d = true → X d = true)
    (cs : Codes) (S : Params.LinShape) :
    ∀ (b : ((ProofFile.InstPub × First.S) × St) × (EAll D all).Str) (s : S₃),
      onQ₂ N Pm (fun q y => ocEnd g N₁ Mg₁ links ps q y ∧ Rc q) split T.p₂ T.l₂
        (1 + T.l₂.length) b →
      ((ProofFile.seatedAt o Z Np c).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s →
      (besideS (fillAt (ProofFile.pAt Z) R (fun q => firstOfS (g q).2) (endedX X)) (yTree cs S)).shape 0
        (b.1.1.1, b.1.1.2) b.1.2 s = true :=
  sh₃_field o pol lay KL Z hZ Np c R g hg T N Pm _ split N₁ Mg₁ links ps Pw V H Rc hR X hD hX
    (fun q e s h1 h2 => shape0_at_layers (ProofFile.pAt Z) R (fun q => (g q).2) X cs S q e s h1 h2)

/-- **The two fillings of the shared table's promise commute.** -/
theorem promSigS_beside {S₂ Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    (ms : List Mem) (stOf : S₂ → OnBytes.Statement) (bookOf : S₂ → OnBytes.TreeBook)
    (Pm₀ : PromMeaning S₂) (X : ℕ → S₂ → Bool) :
    promSigS cs G smp₂ ms stOf bookOf (besideP Pm₀ X) =
      besideP (promSigS cs G smp₂ ms stOf bookOf Pm₀) X := rfl

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.shape0_at_layers
#print axioms VerifiableInference.Desc.Last.sh₃_field_plm
#print axioms VerifiableInference.Desc.Last.promSigS_beside
