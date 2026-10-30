-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K03StatesRaw.lean: THE KIND "LOOKUP" (K3): THE DRIVER's GUARD AROUND A RUN
OF CLAIMS OF THIS KIND IS IDLE: every accepting call of such a run leaves the reply's seat, so the
guarded run IS the run, as a function. SO WHAT THE DESCRIPTION's OWN LINK STATES AT A LOOKUP's PLACE
(K03States.lean: each run behind `IM.guardRun ProofFile.sameReply`) IS WHAT THE KIND's STATED BLOCK
STATES, TO THE LETTER. Theorems with their proofs.

  `guardRun_eq`: where every accepting call of r passes the guard, `IM.guardRun same r = r`.
  `Pass r`: every accepting call of r leaves the reply's seat. `pass_of_puts`: so does a run that
    turns the state by `putFork` alone (`Puts`,
    Johnson/Top/H/Keep/RunsPutFork.lean). `pass_guests`: so does "guests": it leaves the state.
  `theOwn_pass`, `theWhole_pass`, **`theStated_pass`**: every run that `K3.theStated`'s value states
    at the lot's maker of claims `K3Lot.ofForm` passes: by `objects_puts`, `planes_puts`.
  **`k03_states_raw_every`** (no scope), **`k03_states_raw_of`** (the goals' scope, the fifty
    places): `K9.statesOfLink Lk i = b'.claims`.
  **`k03_objects_raw`**, `k03_guests_raw`, `k03_planes_raw`: what `find?` finds there under the
    three names: the runs themselves.

Limits. Nothing on soundness. On texts alone: no view. Of "join" (the calling kind's block's run)
nothing here. The equations are of functions, by `funext`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K03States
import Johnson.Top.H.Keep.RunsPutFork

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits pieceAt)

/-- Where every accepting call of r passes the guard, the guarded run is r. -/
theorem guardRun_eq (same : S → S → Bool) (r : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : ∀ n t y, r n t = .ok y → same t y.2 = true) : IM.guardRun same r = r := by
  funext n t
  unfold IM.guardRun
  cases e : r n t with
  | error x => rfl
  | ok y =>
    show (Desc.seatSame same t y.2).map (fun _ => y) = .ok y
    unfold Desc.seatSame
    rw [if_pos (h n t y e)]
    rfl

/-- Every accepting call of the run leaves the reply's seat. -/
def Pass (r : ℕ → S → Except String (List ProofFile.Cl × S)) : Prop :=
  ∀ n t y, r n t = .ok y → ProofFile.sameReply t y.2 = true

theorem pass_of_puts {r : ℕ → S → Except String (List ProofFile.Cl × S)} (h : Puts r) : Pass r := by
  intro n t y e
  obtain ⟨G, hG⟩ := h n t y.1 y.2 e
  rw [hG]
  exact sameReply_putFork t G

theorem pass_guests : Pass (guestsRun ([] : List (Desc.First.Look.Guest S ProofFile.Cl))) := by
  intro n t y e
  obtain rfl : y = ([], t) := (Except.ok.inj e).symm
  exact beq_self_eq_true _

theorem atS2_seatOf (d : Bool) : AtS2 (seatOf K3Lot.ofForm d) := by
  cases d
  · exact k03_atS2_calls
  · exact k03_atS2_digits

theorem theOwn_pass (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (a : Place) (x : Block S ProofFile.Cl)
    (h : Desc.K3.theOwn K3Lot.ofForm true X codes shape a = some x) :
    ∀ r ∈ x.claims, Pass r.2 := by
  unfold Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      intro r hr
      have hr' : r ∈ [("objects", objectsRun (seatOf K3Lot.ofForm digits)),
          ("guests", guestsRun ([] : List (Desc.First.Look.Guest S ProofFile.Cl)))] := by
        cases digits <;> exact hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact pass_of_puts (objects_puts _ (atS2_seatOf digits))
      · exact pass_guests

theorem theWhole_pass (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (a : Place) (x : Block S ProofFile.Cl)
    (h : Desc.K3.theWhole K3Lot.ofForm true X codes shape a = some x) :
    ∀ r ∈ x.claims, Pass r.2 := by
  unfold Desc.K3.theWhole at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_pass X codes shape a b hb
  split
  · intro r hr
    have hr' : r ∈ b.claims ++ [] := hr
    rw [List.append_nil] at hr'
    exact h0 r hr'
  · exact h0

/-- **Every run that the stated block states at the lot's maker of claims passes the guard.** -/
theorem theStated_pass (readers : ℕ → Option (Desc.K3.Readers S)) (X : Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S ProofFile.Cl)
    (h : Desc.K3.theStated K3Lot.ofForm readers X codes shape a = some B) :
    ∀ r ∈ B.claims, Pass r.2 := by
  unfold Desc.K3.theStated at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  have h0 := theWhole_pass X codes shape a b hb
  split at h
  · obtain rfl := Option.some.inj h
    exact h0
  · split at h
    · obtain rfl := Option.some.inj h
      exact h0
    · split at h
      · obtain rfl := Option.some.inj h
        exact h0
      · rename_i rd _
        obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
        intro r hr
        have hr' : r ∈ b.claims ++
            [("planes", Desc.K3.planesRun (seatCalls K3Lot.ofForm) p.lm rd)] := hr
        rcases List.mem_append.1 hr' with hm | hm
        · exact h0 r hm
        · obtain rfl := List.mem_singleton.1 hm
          exact pass_of_puts (planes_puts _ k03_atS2_calls p.lm rd)

/-- The guard is idle on a list of runs that pass. -/
theorem map_guard_eq (l : List (RunN ProofFile.Cl)) (h : ∀ r ∈ l, Pass r.2) :
    (l.map fun r => (r.1, IM.guardRun ProofFile.sameReply r.2)) = l := by
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun r hr => ?_
  rw [guardRun_eq _ _ (h r hr)]
  rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **What the description's own link states at a lookup's place IS what the stated block states: no
scope.** -/
theorem k03_states_raw_every (O : IM.Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K3) :
    ∃ (Lk : Link S ProofFile.Cl) (b' : Block S ProofFile.Cl), c.links[l]? = some Lk ∧
      Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
        { chain := 1, link := some l, piece := i + 1, kind := .K3 } = some b' ∧
      Desc.K9.statesOfLink Lk i = b'.claims := by
  obtain ⟨Lk, b', h1, h3, h4⟩ := k03_states_every O l sub hl i hk
  exact ⟨Lk, b', h1, h3, h4.trans (map_guard_eq _ (theStated_pass _ _ _ _ _ b' h3))⟩

end

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The same in the goals' scope, at the fifty places.** -/
theorem k03_states_raw_of (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∃ (Lk : Link S ProofFile.Cl) (b' : Block S ProofFile.Cl), c.links[l]? = some Lk ∧
      Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes Z.first.shape
        (IM.k3Place l d) = some b' ∧
      Desc.K9.statesOfLink Lk (IM.k3Ix l d) = b'.claims := by
  obtain ⟨Lk, b', h1, h3, h4⟩ := k03_states_of hS hR O l hl d
  exact ⟨Lk, b', h1, h3, h4.trans (map_guard_eq _ (theStated_pass _ _ _ _ _ b' h3))⟩

/-- **Under "objects": the run itself.** -/
theorem k03_objects_raw (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∃ Lk : Link S ProofFile.Cl, c.links[l]? = some Lk ∧
      (Desc.K9.statesOfLink Lk (IM.k3Ix l d)).find? (fun r => r.1 == "objects") =
        some ("objects", objectsRun (seatOf K3Lot.ofForm d)) := by
  obtain ⟨Lk, h1, h2⟩ := k03_objects_of hS hR O l hl d
  rw [guardRun_eq _ _ (pass_of_puts (objects_puts _ (atS2_seatOf d)))] at h2
  exact ⟨Lk, h1, h2⟩

/-- Under "guests". -/
theorem k03_guests_raw (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∃ Lk : Link S ProofFile.Cl, c.links[l]? = some Lk ∧
      (Desc.K9.statesOfLink Lk (IM.k3Ix l d)).find? (fun r => r.1 == "guests") =
        some ("guests", guestsRun ([] : List (Desc.First.Look.Guest S ProofFile.Cl))) := by
  obtain ⟨Lk, h1, h2⟩ := k03_guests_of hS hR O l hl d
  rw [guardRun_eq _ _ pass_guests] at h2
  exact ⟨Lk, h1, h2⟩

/-- Under "planes". -/
theorem k03_planes_raw (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (r : Desc.K3.Readers S) (hr : K3Lot.readersAt Bs.G₀.W l = some r) :
    ∃ (Lk : Link S ProofFile.Cl) (p : Desc.First.Look.P), c.links[l]? = some Lk ∧
      Desc.First.Look.placeAt Bs.G₀.W l false = some p ∧
      (Desc.K9.statesOfLink Lk (IM.k3Ix l false)).find? (fun x => x.1 == "planes") =
        some ("planes", Desc.K3.planesRun (seatCalls K3Lot.ofForm) p.lm r) := by
  obtain ⟨Lk, p, h1, hp, h2⟩ := k03_planes_of hS hR O l hl r hr
  rw [guardRun_eq _ _ (pass_of_puts (planes_puts _ k03_atS2_calls p.lm r))] at h2
  exact ⟨Lk, p, h1, hp, h2⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.guardRun_eq
#print axioms VerifiableInference.OnPublicFiles.pass_of_puts
#print axioms VerifiableInference.OnPublicFiles.pass_guests
#print axioms VerifiableInference.OnPublicFiles.atS2_seatOf
#print axioms VerifiableInference.OnPublicFiles.theOwn_pass
#print axioms VerifiableInference.OnPublicFiles.theWhole_pass
#print axioms VerifiableInference.OnPublicFiles.theStated_pass
#print axioms VerifiableInference.OnPublicFiles.map_guard_eq
#print axioms VerifiableInference.OnPublicFiles.k03_states_raw_every
#print axioms VerifiableInference.OnPublicFiles.k03_states_raw_of
#print axioms VerifiableInference.OnPublicFiles.k03_objects_raw
#print axioms VerifiableInference.OnPublicFiles.k03_guests_raw
#print axioms VerifiableInference.OnPublicFiles.k03_planes_raw
