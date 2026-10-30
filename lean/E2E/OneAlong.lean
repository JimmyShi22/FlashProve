-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OneAlong.lean: ONE REQUEST's HONEST PROVER OF A BATCH's HONEST SIDE THAT IS PULLED BACK ALONG A
MAP ON INSTANCES (`BatchHonestProver.comap`, Hiop/RecKit.lean): its output, abort sets, external strings and
answers, in terms of the honest side that was pulled back. General lemmas; the library alone is
imported.

What is shown. H: a batch's honest side; f: the map on instances; g: the map on private inputs.
  `one_comap`: `(H.comap f g).one = H.one.comap f g`: by unfolding.
  `ext_one_comap`, `strat_one_comap`, `bad_one_comap`, `hid_one_comap`, `withheld_one_comap`: each
    field, read through f and g: by unfolding.
  `extAns_comap`: the answers at the verifier's positions, at x, are those at f x: by unfolding.
  **`output_one_comap`**: the output at (w, x, ρ) is the output at (g w, f x, ρ) WITH EACH DISCLOSED
    VIEW READ AS ONE OF THE PULLED-BACK PROTOCOL (`DView.comap f`: the same data in another type).
    It is not an equation between the two outputs as they stand: their types differ.
  **`exact_one_comap`**: so, where outside `Hid` the output of `H.one` is a named simulator's, the
    output of `(H.comap f g).one` is that simulator's at f x, its views read likewise.
The same with ANY decision in the place of the pulled-back one. Output, abort sets and answers do
not read a protocol's decision. So they are the same at every protocol that has the pulled-back
shape, marks of blinding and reads, whatever it accepts:
  `reAcc Q f acc`: that protocol; `comap_eq_reAcc`: at the pulled-back decision it is `Q.comap f`:
    by unfolding. `viewRe`, `honestRe`, **`output_re`**, **`exact_re`**: the like of the above.

Limits. Neither section is put to use here. Section 1 is called by no file beside this one. `viewRe`
holds the same data as `DView.comap`, read at the protocol `reAcc Q f acc`, at any decision acc.
Nothing on acceptance. Nothing is shown of any prover: equations that hold for all.


-/
import Hiop.RecKitHonest

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Along
open Iop Prob

variable {Y Y' : Type} {E : ExtSpec}

/-! ## 1. Along `comap` -/

section Batch
variable {Q : BatchInteractiveOracleProof Y E} {Wt Wt' : Type} (H : BatchHonestProver Q Wt) (f : Y' → Y) (g : Wt' → Wt)

theorem one_comap : (H.comap f g).one = H.one.comap f g := rfl

theorem ext_one_comap (w : Wt') : (H.comap f g).one.ext w = H.one.ext (g w) := rfl

theorem strat_one_comap (w : Wt') (x : Y') (c : H.one.Coin) :
    (H.comap f g).one.strat w x c = H.one.strat (g w) (f x) c := rfl

theorem bad_one_comap : (H.comap f g).one.Bad = H.one.Bad := rfl

theorem hid_one_comap (w : Wt') (x : Y') : (H.comap f g).one.Hid w x = H.one.Hid (g w) (f x) := rfl

theorem withheld_one_comap (w : Wt') (x : Y') :
    (H.comap f g).one.withheld w x = H.one.withheld (g w) (f x) := rfl

theorem extAns_comap (P : InteractiveOracleProof Y E) (x : Y') (ρ : Rho P.shape) (y : E.Str) :
    (P.comap f).extAns x ρ y = P.extAns (f x) ρ y := rfl

/-- **The output along the map**: each disclosed view read as one of the pulled-back protocol. -/
theorem output_one_comap (w : Wt') (x : Y') (ρ : Rho Q.loc.shape) :
    (H.comap f g).one.output w x ρ =
      (H.one.output (g w) (f x) ρ).map (Option.map (DView.comap f)) :=
  Honest.output_comap H.one f g w x ρ

/-- **A named simulator along the map.** -/
theorem exact_one_comap
    (sim : Y → (ρ : Rho Q.loc.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q.loc)))
    (w : Wt') (x : Y') (ρ : Rho Q.loc.shape)
    (h : H.one.output (g w) (f x) ρ = sim (f x) ρ (Q.loc.extAns (f x) ρ (H.one.ext (g w)))) :
    (H.comap f g).one.output w x ρ =
      (sim (f x) ρ ((Q.comap f).loc.extAns x ρ ((H.comap f g).one.ext w))).map
        (Option.map (DView.comap f)) := by
  rw [output_one_comap, h]
  rfl

end Batch

/-! ## 2. With any decision -/

/-- The protocol with Q's shape and marks of blinding, Q's reads through f, and the decision acc. -/
def reAcc (Q : InteractiveOracleProof Y E) (f : Y' → Y) (acc : Y' → E.Str → Tr Q.shape → Bool) : InteractiveOracleProof Y' E where
  shape := Q.shape
  blinded := Q.blinded
  extReads := fun x => Q.extReads (f x)
  reads := fun x => Q.reads (f x)
  accept := acc

theorem comap_eq_reAcc (Q : InteractiveOracleProof Y E) (f : Y' → Y) :
    Q.comap f = reAcc Q f fun x => Q.accept (f x) := rfl

section One
variable {Q : InteractiveOracleProof Y E} {Wt Wt' : Type} (H : Honest Q Wt) (f : Y' → Y)
  (acc : Y' → E.Str → Tr Q.shape → Bool) (g : Wt' → Wt)

/-- A disclosed view of Q, read as one of `reAcc Q f acc`: the same data. -/
def viewRe (v : DView Q) : DView (reAcc Q f acc) := ⟨v.plains, v.ext, v.orc⟩

/-- The honest prover: the instance is read through f, the private input through g. -/
def honestRe : Honest (reAcc Q f acc) Wt' where
  Coin := H.Coin
  ext := fun w => H.ext (g w)
  strat := fun w x c => H.strat (g w) (f x) c
  Bad := H.Bad
  Hid := fun w x => H.Hid (g w) (f x)

theorem extAns_re (x : Y') (ρ : Rho Q.shape) (y : E.Str) :
    (reAcc Q f acc).extAns x ρ y = Q.extAns (f x) ρ y := rfl

open Classical in
theorem output_re (w : Wt') (x : Y') (ρ : Rho Q.shape) :
    (honestRe H f acc g).output w x ρ =
      (H.output (g w) (f x) ρ).map (Option.map (viewRe f acc)) := by
  by_cases hρ : ρ ∈ H.withheld (g w) (f x)
  · have e1 : (honestRe H f acc g).output w x ρ = PMF.pure none := if_pos hρ
    have e2 : H.output (g w) (f x) ρ = PMF.pure none := if_pos hρ
    rw [e1, e2, PMF.pure_map]
    rfl
  · have e1 : (honestRe H f acc g).output w x ρ =
        (unif H.Coin).map fun c =>
          some ((reAcc Q f acc).dview x (H.ext (g w)) ((H.strat (g w) (f x) c).run ρ).1) :=
      if_neg hρ
    have e2 : H.output (g w) (f x) ρ =
        (unif H.Coin).map fun c =>
          some (Q.dview (f x) (H.ext (g w)) ((H.strat (g w) (f x) c).run ρ).1) := if_neg hρ
    rw [e1, e2, PMF.map_comp]
    rfl

theorem exact_re
    (sim : Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q)))
    (w : Wt') (x : Y') (ρ : Rho Q.shape)
    (h : H.output (g w) (f x) ρ = sim (f x) ρ (Q.extAns (f x) ρ (H.ext (g w)))) :
    (honestRe H f acc g).output w x ρ =
      (sim (f x) ρ ((reAcc Q f acc).extAns x ρ ((honestRe H f acc g).ext w))).map
        (Option.map (viewRe f acc)) := by
  rw [output_re, h]
  rfl

end One

end AtPublicFiles.Along

#print axioms AtPublicFiles.Along.one_comap
#print axioms AtPublicFiles.Along.output_one_comap
#print axioms AtPublicFiles.Along.exact_one_comap
#print axioms AtPublicFiles.Along.comap_eq_reAcc
#print axioms AtPublicFiles.Along.output_re
#print axioms AtPublicFiles.Along.exact_re
#print axioms AtPublicFiles.Along.ext_one_comap
#print axioms AtPublicFiles.Along.strat_one_comap
#print axioms AtPublicFiles.Along.bad_one_comap
#print axioms AtPublicFiles.Along.hid_one_comap
#print axioms AtPublicFiles.Along.withheld_one_comap
#print axioms AtPublicFiles.Along.extAns_comap
#print axioms AtPublicFiles.Along.extAns_re
