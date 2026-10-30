-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3PlanesReaders.lean: WHAT IS LEFT OF A LINK's LAW (K9): THE PREMISE
hr OF SortK3Planes.lean | SortK3PlanesKap.lean | SortK3More.lean ("the calling kind's readers are
there at link m") FOLLOWS FROM `At L (IM.k3Ix m false, "planes") run` ITSELF, IN THE GOALS' SCOPE:
where the readers are not there the stated block states "objects" and "guests" alone. Theorems.

  theOwn_names · theWhole_names   every run that K3.theOwn's | K3.theWhole's value states at the
                    lot's maker of claims is named "objects" or "guests" (on the road of
                    theOwn_pass | theWhole_pass, Johnson/Desc/First/Look/K03StatesRaw.lean)
  lookup_none_of_names   a list of named runs none of which bears the name n answers none to n
  readers_of_at_planes   **At L (IM.k3Ix m false, "planes") run ⊢ ∃ r, K3Lot.readersAt Bs.G₀.W m =
                    some r**

PREMISES: hS hR O · m < 25 · hL : c.links[m]? = some L.
Limits. NO MEMBER: that any link states "planes" is not shown here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortK3Planes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (At)

theorem theOwn_names (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (a : Place) (x : Block S ProofFile.Cl)
    (h : Desc.K3.theOwn K3Lot.ofForm true X codes shape a = some x) :
    ∀ r ∈ x.claims, r.1 = "objects" ∨ r.1 = "guests" := by
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
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem theWhole_names (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (a : Place) (x : Block S ProofFile.Cl)
    (h : Desc.K3.theWhole K3Lot.ofForm true X codes shape a = some x) :
    ∀ r ∈ x.claims, r.1 = "objects" ∨ r.1 = "guests" := by
  unfold Desc.K3.theWhole at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_names X codes shape a b hb
  split
  · intro r hr
    have hr' : r ∈ b.claims ++ [] := hr
    rw [List.append_nil] at hr'
    exact h0 r hr'
  · exact h0

theorem lookup_none_of_names {β : Type} (n : String) :
    ∀ l : List (String × β), (∀ r ∈ l, r.1 ≠ n) → l.lookup n = none
  | [], _ => rfl
  | (k, v) :: l, h => by
    rw [List.lookup_cons]
    have e : (n == k) = false := beq_false_of_ne fun e' => h (k, v) List.mem_cons_self e'.symm
    simp only [e]
    exact lookup_none_of_names n l fun r hr => h r (List.mem_cons_of_mem _ hr)

/-- **Where the link states "planes" at the calls' lookup's block, the calling kind's readers are
there.** -/
theorem readers_of_at_planes {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
    {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
    {run : ℕ → S → Except String (List ProofFile.Cl × S)}
    (h : At L (IM.k3Ix m false, "planes") run) :
    ∃ r, K3Lot.readersAt Bs.G₀.W m = some r := by
  obtain ⟨Lk, b', h1, h3, h4⟩ := k03_states_raw_of hS hR O m hm false
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans hL)
  obtain ⟨b, hb, hl⟩ := Option.bind_eq_some_iff.1 h
  have hb' : Lk.hear[IM.k3Ix m false]? = some b := hb
  have hl' : b.claims.lookup "planes" = some run := hl
  have e : Desc.K9.statesOfLink Lk (IM.k3Ix m false) = b.claims := by
    unfold Desc.K9.statesOfLink
    rw [hb']
    rfl
  rw [e] at h4
  rw [h4] at hl'
  cases hq : K3Lot.readersAt Bs.G₀.W m with
  | some r => exact ⟨r, rfl⟩
  | none =>
    exfalso
    unfold Desc.K3.theStated at h3
    obtain ⟨b₀, hb₀, h3⟩ := Option.bind_eq_some_iff.1 h3
    have hn := theWhole_names _ _ _ _ b₀ hb₀
    have hb : b' = b₀ := by
      have h3' : (if (IM.k3Place m false).piece != Desc.K3.pieceAt Bs.G₀.W m false then some b₀
          else match K3Lot.readersAt Bs.G₀.W m with
            | none => some b₀
            | some r => (Desc.First.Look.placeAt Bs.G₀.W m false).map fun p =>
                Desc.K3.withCaller (Desc.K3.seatCalls K3Lot.ofForm) p r b₀) = some b' := h3
      rw [hq] at h3'
      split at h3' <;> exact (Option.some.inj h3').symm
    rw [hb, lookup_none_of_names "planes" b₀.claims fun r hr e' => by
      rcases hn r hr with e1 | e1 <;> rw [e1] at e' <;> exact absurd e' (by decide)] at hl'
    exact nomatch hl'

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.theOwn_names
#print axioms VerifiableInference.OnPublicFiles.theWhole_names
#print axioms VerifiableInference.OnPublicFiles.lookup_none_of_names
#print axioms VerifiableInference.OnPublicFiles.readers_of_at_planes
