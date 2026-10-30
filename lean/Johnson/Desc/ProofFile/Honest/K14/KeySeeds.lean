-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/KeySeeds.lean: kind K14: THE ONE TEST OF THE EIGHT SUB-PROTOCOLS
OF THE LINEAR CLAIM's SHARED ROUNDS ON A VALUE THAT IS NO CHALLENGE: "no seed of the key has the
factor 0", which "(rec_gamma)" asks in front of its constraints (laysRecL,
Johnson/Desc/K14/Text.lean). It reads the seeds in the key of the committed table: no challenge of
the chain, no random value of the prover's, nothing that is sent. The key is a part of the instance:
so the test is a sentence on the instance, and belongs to what a valid instance is.

  noZeroFactor    the test, as a Bool on a key
  noZeroFactor_clause   it is the second of the three clauses of laysRecL, at the key that the
                  state holds
  rec_passes      where it accepts, the key's sizes fit and the point has its coordinates, all three
                  clauses are passed
  seeds_reject    **where it rejects the key that the state holds, the step of "(rec_gamma)" does
                  not return**: a negative lemma. That the state in front of that member holds the
                  INSTANCE's key is not said here

What is not claimed. That the key of any instance passes the test. The library has the like, in its
own forms, at every key that its own maker of keys returns (tableKey_nz,
OnBytes/Slice/KeyTableRec.lean), and at seeds that the format's own text makes of a committed
table's name, at every plain hash (seedOK_recordSeedsW, OnBytes/Slice/SeedWords.lean). THAT AN
INSTANCE's KEY IS SUCH A KEY IS NOT SHOWN HERE. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K14.Honest.Returns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Own (allZero keyFits)
open VerifiableInference.Desc.Ground (ok)
open Desc.Plain (Par)
open Desc.K14 (P14 St Lin laysRecL withU)
open Desc.K14.Honest (Eight rec_rejects)

/-- **No seed of the key has the factor 0.** -/
def noZeroFactor (k : TableKey) : Bool := k.seeds.all (!allZero ·.beta)

/-- It is the second of the three clauses of laysRecL. -/
theorem noZeroFactor_clause (p : Par) (l : Lin) :
    ((laysRecL p l).drop 1).take 1 =
      [("no seed of the record has the factor 0", noZeroFactor l.key)] := rfl

/-- Where it accepts, the key's sizes fit and the point has its coordinates, the sub-protocol's
three clauses are passed. -/
theorem rec_passes (p : Par) (l : Lin) (h : noZeroFactor l.key = true)
    (hkey : keyFits l.key p.S.fold.index = true)
    (hg : (Desc.K14.gamma p.S l).length = p.S.fold.index.v) : ok (laysRecL p l) = true := by
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq]
  exact ⟨hkey, h, hg⟩

/-- **Where it rejects the key that the state holds, the step of "(rec_gamma)" does not return.** -/
theorem seeds_reject {P : P14} {sentU : Array OnBytes.OracleNotice}
    (hU : withU P.S = some sentU) (B : Eight P) (ft : Nat) (d d' : St) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (h : noZeroFactor d.loc.key = false) :
    B.b3.step ft d rs cols ≠ .ok (d', n) :=
  rec_rejects hU B ft d d' rs cols n h

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.noZeroFactor_clause
#print axioms ProofFile.Honest.K14.rec_passes
#print axioms ProofFile.Honest.K14.seeds_reject
