-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyFillSeedToy.lean: A CONTROL TO Johnson/RunOne/KeyFillSeed.lean: A MEMBER AT A SAMPLE's TIE THAT READS A RECORD. All closed theorems of the filling so far stood at a tie made of the very message and seed that it was to witness. Here the tie is the sending kind's own (rowIsK: SeedIs):
the record is a value of the first chain's state type whose statement holds, for each member of the toy, a message of the member's shape, marked, WITH THE KIND's OWN SAMPLE ROW (sampleRow) at a point, a factor and a target.
  zK · ρK · reads     eight zero words and the factor one, and the seed of the library's sample map as which they read
  tK · xK · sK        the target: the canonical words of the library's answer of the message «1 everywhere» at that seed · the message's record · the state
  tieT                the sending kind's Tie at the toy's two shapes: by the kernel
  hs                  the record holds both members' samples, BY THE SENDING KIND's TIE
  promise             CLOSED: PIN ∧ hasSmp ∧ NoColl at both seats at B.h₁ at the filled tie. No «there is a tie»: the tie is fixed
  turned              A TURNED CONTROL: the first message's row with its target turned by one: no witness whose table at the first seat is the honest message's is pinned there: SO «meets» IS NOT TRUE BY FIAT HERE
THE TARGET IS LAID BY HAND: that a block lays it (the prover's answer, received) is the sending's law's; the toy is no protocol's description; the state is no state of a run; the seed is no drawn seed.
OBJECT: SeedIs through rowIsK; BaseSt.h₁ (Johnson/RunOne/KeyOneReading.lean) · USER: none: a control · LETTERS: none.
Nothing on soundness.
-/
import Johnson.RunOne.KeyFillSeedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23.ToyK
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill VerifiableInference.Desc.Key.Fill.Toy
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (ReadsOne Tie sampleRow)
open Johnson.RunOne.KeyRows23.ToyB (num at_ apartT)
open Cb Johnson.Pack OnBytes.Slice

def zK : List OnBytes.E := List.replicate 8 OnBytes.zeroE

def ρK (i : Fin l.length) : (OmAt cs l i).Z.D := (fun t => readL zK t.val, 1)

theorem bits_le : ∀ i : Fin l.length, bitsZ cs (l.get i).1 ≤ 8 := by decide +kernel

theorem reads (i : Fin l.length) : ReadsOne cs (l.get i).1 zK OnBytes.oneE (ρK i) :=
  ⟨bits_le i, fun _ => rfl, OnBytes.Slice.readE_one⟩

/-- The honest message: 1 everywhere. -/
def m₁ (i : Fin l.length) : (OmAt cs l i).Msg := fun _ => 1

/-- The target: the canonical words of the library's answer, and d added. -/
def tK (d : GE) (i : Fin l.length) : OnBytes.E := OnBytes.E.ofTriple (ofE ((OmAt cs l i).Z.val (ρK i) (m₁ i) () + d))

theorem read_tK (d : GE) (i : Fin l.length) : OnBytes.Slice.readE (tK d i) = (OmAt cs l i).Z.val (ρK i) (m₁ i) () + d := by
  unfold tK
  rw [OnBytes.Slice.readE_ofTriple, toE_ofE]

def xK (d : GE) (i : Fin l.length) (o : ℕ) : OnBytes.Oracle :=
  { shape := (l.get i).1, sampled := true, sampleRows := #[sampleRow (VerifiableInference.Desc.K1.Msg.of cs (l.get i).1) o zK OnBytes.oneE 0 (tK d i)] }

/-- The state: the first message's target turned by d. -/
def sK (d : GE) : FirstState :=
  { chainStart cs {} with d := { (chainStart cs ({} : LookupRecord)).d with st := { codes := cs, oracles := #[xK d ⟨0, by decide⟩ 0, xK 0 ⟨1, by decide⟩ 1] } } }

theorem tieT : ∀ i : Fin l.length, Tie cs (l.get i).1 := fun i =>
  tie_of_B _ _ ((by decide +kernel : ∀ i : Fin l.length, tieB cs (l.get i).1 = true) i)

/-- What the record spells at the first member: the seed ρK and the answer turned by d. -/
theorem spells₀ (d : GE) : seedIsS cs l num (rowIsK cs l) (src₁ some) ⟨0, by decide⟩ (⟨{}⟩, sK d) (ρK ⟨0, by decide⟩) (fun _ => (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (m₁ ⟨0, by decide⟩) () + d) :=
  ⟨0, xK d ⟨0, by decide⟩ 0, rfl, rfl, zK, OnBytes.oneE, tK d ⟨0, by decide⟩, rfl, rfl, reads _, by rw [read_tK]⟩

theorem spells₁ (d : GE) : seedIsS cs l num (rowIsK cs l) (src₁ some) ⟨1, by decide⟩ (⟨{}⟩, sK d) (ρK ⟨1, by decide⟩) (fun _ => (OmAt cs l ⟨1, by decide⟩).Z.val (ρK ⟨1, by decide⟩) (m₁ ⟨1, by decide⟩) () + 0) :=
  ⟨1, xK 0 ⟨1, by decide⟩ 1, rfl, rfl, zK, OnBytes.oneE, tK 0 ⟨1, by decide⟩, rfl, rfl, reads _, by rw [read_tK]⟩

/-- **The honest record holds both members' samples, by the sending kind's tie.** -/
theorem hs : ∀ i : Fin l.length, True → seedIsS cs l num (rowIsK cs l) (src₁ some) i (⟨{}⟩, sK 0) (ρK i) ((OmAt cs l i).Z.val (ρK i) (m₁ i)) := by
  rintro ⟨k, hk⟩ _
  have hk' : k < 2 := hk
  interval_cases k
  · have h := spells₀ 0
    have e : (fun _ : (OmAt cs l ⟨0, by decide⟩).Z.S => (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (m₁ ⟨0, by decide⟩) () + 0) = (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (m₁ ⟨0, by decide⟩) := by
      funext s
      rw [add_zero]
      cases s
      rfl
    rw [e] at h
    exact h
  · have h := spells₁ 0
    have e : (fun _ : (OmAt cs l ⟨1, by decide⟩).Z.S => (OmAt cs l ⟨1, by decide⟩).Z.val (ρK ⟨1, by decide⟩) (m₁ ⟨1, by decide⟩) () + 0) = (OmAt cs l ⟨1, by decide⟩).Z.val (ρK ⟨1, by decide⟩) (m₁ ⟨1, by decide⟩) := by
      funext s
      rw [add_zero]
      cases s
      rfl
    rw [e] at h
    exact h

/-- **CLOSED: A MEMBER AT A TIE THAT READS A RECORD**: PIN · hasSmp · NoColl at both seats at B.h₁, the sample's tie being the sending kind's own. -/
theorem promise : ∃ (W : Wit Unit Unit Fill.Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length,
      PIN (FW 15) (baseK (Rec := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, sK 0) (Sound.strsOf (FrD 1) y') W ∧
      hasSmp (baseK (Rec := Unit) (Cells := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, sK 0) = true ∧
      NoColl (FW 15) (baseK (Rec := Unit) (Cells := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num i)).1 (at_ (num i)).2 (⟨{}⟩, sK 0) (Sound.strsOf (FrD 1) y') := by
  obtain ⟨W, y', _, h⟩ := promiseK_h₁ cs l num at_ (fun _ _ => none) (fun _ => none) some (FW 15) (fun _ => True) (FrD 1) seat_inj apartT Fin.val_injective fits holds tieT meets
    ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (⟨{}⟩, sK 0) m₁ (fun _ _ => 0) ρK (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩) hs ()
  exact ⟨W, y', fun i => h i trivial⟩

/-- **A TURNED CONTROL**: the first message's target turned by one: no witness whose table at the first seat is the honest message's is pinned there, at any strings. -/
theorem turned (y : Strs) (W : Wit Unit Unit Fill.Tab)
    (hW : msgOf (baseK (Rec := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ W (at_ (num ⟨0, by decide⟩)).1 (at_ (num ⟨0, by decide⟩)).2 = ofU cs (l.get ⟨0, by decide⟩).1 (l.get ⟨0, by decide⟩).2 (m₁ ⟨0, by decide⟩)) :
    ¬ PIN (FW 15) (baseK (Rec := Unit) cs l num at_ (fun _ _ => none) (fun _ => none) some).h₁ (at_ (num ⟨0, by decide⟩)).1 (at_ (num ⟨0, by decide⟩)).2 (⟨{}⟩, sK 1) y W := by
  rintro ⟨o, z, ho, hz, hM⟩
  rw [hW] at hM
  obtain ⟨o₁, _, ho₁, _, hlog, _, _, hm, _, _⟩ := fits ⟨0, by decide⟩
  have hL : ∀ o', (FW 15).oracleAt (seatAt l num at_ ⟨0, by decide⟩).1 = some o' → o'.logLength = aOf cs (l.get ⟨0, by decide⟩).1 := fun o' ho' => by
    obtain rfl : o' = o₁ := Option.some.inj (ho'.symm.trans ho₁)
    exact hlog
  have h2 : (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (toU cs (l.get ⟨0, by decide⟩).1 (l.get ⟨0, by decide⟩).2 (ofU cs (l.get ⟨0, by decide⟩).1 (l.get ⟨0, by decide⟩).2 (m₁ ⟨0, by decide⟩))) =
      fun _ => (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (m₁ ⟨0, by decide⟩) () + 1 :=
    ((sealsK_h₁ cs l num at_ (Cells := Unit) (Rec := Unit) (fun _ _ => none) (fun _ => none) some (FW 15) (fun y : Strs => y) seat_inj apartT ⟨0, by decide⟩ (tieT _) hL hm).mem
      (⟨{}⟩, sK 1) y o z _ _ _ ho hz (spells₀ 1) hM).2
  rw [toU_ofU] at h2
  have h4 : (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (m₁ ⟨0, by decide⟩) () = (OmAt cs l ⟨0, by decide⟩).Z.val (ρK ⟨0, by decide⟩) (m₁ ⟨0, by decide⟩) () + 1 := congrFun h2 ()
  exact one_ne_zero (add_left_cancel (h4.symm.trans (add_zero _).symm))

end Johnson.RunOne.KeyRows23.ToyK

#print axioms Johnson.RunOne.KeyRows23.ToyK.reads
#print axioms Johnson.RunOne.KeyRows23.ToyK.tieT
#print axioms Johnson.RunOne.KeyRows23.ToyK.hs
#print axioms Johnson.RunOne.KeyRows23.ToyK.promise
#print axioms Johnson.RunOne.KeyRows23.ToyK.turned
