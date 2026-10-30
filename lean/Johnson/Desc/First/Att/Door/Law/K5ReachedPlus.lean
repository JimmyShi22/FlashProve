-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5ReachedPlus.lean: kind K5: THE TWO FACTS THAT THE BRIDGE k5_tiedR (Door/Law/PlusBridge.lean) ASKS AT THE ONE BORDER IN FRONT OF THE KIND's SUB-PROTOCOL (the tests bareAttB and leftAttB of the wider filling say yes at a reached state that meets the narrow promise and bears
no mark), FROM WHAT TWO THEOREMS ALONG THE FOLD CONCLUDE. THIS IS THE HALF OF THAT JOIN THAT NEEDS NO FILE ON "REACHED": Rch stays a letter.
  (bareAtt_of · leftAtt_of: in a light file of their own, Door/Law/K5AttOf.lean, imported here.)
IT STANDS OVER THE BRIDGE THAT WIDENS BY widenP: tiedR_fits' binders and call go with k5_tiedR's (hD · hD' · hopen').
  here_of_onQ: the narrow promise at a border in front of the kind's place, without a mark, has an attention segment open (k5_here, Door/Law/K5DoorAtPlus.lean, off the promise's test shapeAt).
  hbare_of_reached · hleft_of_reached: THEY CONCLUDE k5_tiedR's TWO BINDERS hbare | hleft, SIGN FOR SIGN; tiedR_fits hands both to k5_tiedR: Lean's own check.
PREMISES THAT STAY: hRB | hLA: at every reached state of the border: what rowsBare_reached | leftAt_reached_of conclude (the other half of the join: rch_pure_fold, then these: in a build that holds them).
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.PlusBridge
import Johnson.Desc.First.Att.Door.Law.K5DoorAtPlus
import Johnson.Desc.First.Att.Door.Law.K5AttOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att.P (K5Place onAt_shape)

section
variable {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (get : A → P × S)

/-- **The narrow promise in front of the kind's place, without a mark, has an attention segment open.** -/
theorem here_of_onQ {m k : ℕ} {p p' : Place} (Ix : K5Place links m p p') (hk : ps[k]? = some p) {a : A × Fr.E.Str}
    (ho : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none) : ∃ att, (get a.1).2.here = .att att := by
  unfold onQ at ho
  rw [hk] at ho
  exact k5_here Ix (onAt_shape ho hm)

variable (Rch : ℕ → A × Fr.E.Str → Prop)

theorem hbare_of_reached {m k : ℕ} {p p' : Place} (Ix : K5Place links m p p') (hk : ps[k]? = some p)
    (hRB : ∀ a, Rch k a → ∃ g, (get a.1).2.lookHeard? = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[]) :
    ∀ a, Rch k a → onQ N Mg links ps get k a → (get a.1).2.failed = none → bareAttB (get a.1).2 = true := by
  intro a hr ho hm
  obtain ⟨att, e⟩ := here_of_onQ N Mg links ps get Ix hk ho hm
  exact bareAtt_of e (hRB a hr)

theorem hleft_of_reached {m k : ℕ} {p p' : Place} (Ix : K5Place links m p p') (hk : ps[k]? = some p)
    (hLA : ∀ a, Rch k a → ∃ g G, (get a.1).2.lookHeard? = some g ∧ (get a.1).2.fork? = some G ∧ FillBare.leftAtB g G = true) :
    ∀ a, Rch k a → onQ N Mg links ps get k a → (get a.1).2.failed = none → leftAttB (get a.1).2 = true := by
  intro a hr ho hm
  obtain ⟨att, e⟩ := here_of_onQ N Mg links ps get Ix hk ho hm
  exact leftAtt_of e (hLA a hr)

end

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S) (M0 : More) (D : PubData) (L : VerifiableInference.Desc.K12.Door.Laid)
  (M : List OracleShape) (base : Pub → P × S → Bool) (cs : Codes) (Rch : ℕ → A × Fr.E.Str → Prop)

/-- Lean's own check: the two conclusions ARE the bridge's two binders. (Its other binders: cut by program out of k5_tiedR's own.) -/
theorem tiedR_fits (hpub : Mg.pub = pubAll D base) (F : Facts5 get D L M cs Rch) (k : ℕ) (q : Piece C Fr A Cl W)
    {m : ℕ} {p p' : Place} (Ix : K5Place links m p p') (hk : ps[k]? = some p)
    (hRB : ∀ a, Rch k a → ∃ g, (get a.1).2.lookHeard? = some g ∧ ∀ f ∈ g.rows.toList, f.ents = #[])
    (hLA : ∀ a, Rch k a → ∃ g G, (get a.1).2.lookHeard? = some g ∧ (get a.1).2.fork? = some G ∧ FillBare.leftAtB g G = true)
    (hD : doorsFitB Mg.more (morePlus M0) isWideQ links ps k = true)
    (hD' : doorsFitB Mg.more (morePlus M0) isWideQ links ps (k + 1) = true)
    (hopen' : ∀ x ∈ (pubSets (morePlus M0) links ps)[k + 1]?.getD [],
      x ∈ (pubSets Mg.more links ps)[k + 1]?.getD [] ∨ isThreeQ x = true)
    (hs : HandsOn Rch k q)
    (h : TiedAt N (mgPlus Mg M0 D L M base cs) links ps get k q) : TiedAtR N Mg links ps get Rch k q :=
  k5_tiedR N Mg links ps get M0 D L M base cs Rch hpub F k q (hbare_of_reached N Mg links ps get Rch Ix hk hRB)
    (hleft_of_reached N Mg links ps get Rch Ix hk hLA) hD hD' hopen' hs h

end

end H2K5.Door

#print axioms H2K5.Door.here_of_onQ
#print axioms H2K5.Door.hbare_of_reached
#print axioms H2K5.Door.hleft_of_reached
#print axioms H2K5.Door.tiedR_fits
