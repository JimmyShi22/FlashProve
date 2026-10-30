-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/FrontSetAtFiles.lean: the set of ALL requests' early parts at the makers' own spelling
(`FrontSet.ownPub`, Johnson/Flat/FrontSetPub.lean), laid at the objects of the three files at the
two sizes: every premise of that set is paid here but one, which is paid at the data made of a
planner's answer.

THE LETTERS MEET; THIS IS NO TIE.

`FrontSet.ownPub` asks: the window below 2 ^ 32 and the vocabulary at most 2 ^ 32 and not empty; a
one-to-one map enc of the interface's instances into the model's; that the interface's early part is
"the reply laid 0"; a test that lets the fixed record alone through; and a record H that holds, for
an instance, the request file that says it (`hpub`). At both sizes the interface's instances are a
sub-type of the model's (`ReqAt sizesSmall`, `Flat.Req`):
  the three bounds        by evaluation at the sizes (`sizesSmall_T`, `sizesSmall_V`,
                          `sizesSmall_V_pos`, `ppref_T`, `ppref_V`, `ppref_V_pos`);
  enc                     the value of the sub-type; one to one;
  the test                `recIs r₀` (Johnson/Flat/RecIs.lean): a program;
  H                       `holdsWords` at three public files, which are letters; `hpub` by
                          definition (`hpub_holdsWords`);
  the early part          a premise hE on the data G₀ (the object's early part is G₀'s, by
                          unfolding); at `bigReqSmall p` and `bigReq p` it holds by unfolding.

  `holdsSmall`, `frontSmall`, `has_frontSmall`        at data G₀ with hE.
  `frontSmallAt`, `has_frontSmallAt`                  at `bigReqSmall p` and the record of zeros: no
                                                      premise is left.
  `holdsFull`, `frontFull`, `has_frontFull`, `frontFullAt`, `has_frontFullAt`   the full size.

So at both sizes, for all A, E, P and every G₀ with hE, there is a value of `FrontSet` that has
EVERY request, at the spelling "(the item `request`, the request file's bytes)", with nothing
assumed of any hash function. A, E and P are parameters; the type of A carries a law (`mat_cut`,
OnBytes/Slice/DecoderRec.lean); that such A, E, P exist is not shown in this file.

A FIXED HASH STANDS IN THESE TERMS. The spelling's first string is the request's item
(`Proof.requestItem`, OnBytes/Proof/RequestItem.lean), which holds values of the programs' second
hash function (OnBytes/Hash/SecondHashFunction.lean), a fixed public function. The set's field `apart` does not
read that string: it tells two requests apart by the request file's bytes (`FrontSet.ownPub`,
Johnson/Flat/FrontSetPub.lean).

ON CODE. The values are marked noncomputable: a `FrontSet` is indexed by the interface, which is
handed over as a value, and the objects of the three files have no code (`Files.withProvers`,
OnBytes/Flat/Object.lean). What a program needs of a set is its test on a typed instance. That test
is given beside as a program over plain types, `okRun okSSmall (recIs r₀)` and
`okRun okSFull (recIs r₀)`, with the equations `frontSmall_okX` and `frontFull_okX`, by unfolding.
A running form of the whole test of fitness over these is not given here.

Not claimed. That the second string of any program's statement is the request file of the call's
instance (`insOf_bytes`, Johnson/Flat/WordsBytes.lean, is the law for that). The two bounds on the
strings' sizes. That pol, lay, KL are any call's files. That an encoding made at this set is the
one of any arm: the arms are typed over a set and a fixed record that are letters; that an arm's
record is the record of zeros is not said. At which format: the head of
Johnson/Flat/FrontSetPub.lean. Nothing on any hash. Nothing on soundness.


-/
import Johnson.Flat.FrontSetPub
import Johnson.Flat.RecIs
import Johnson.Flat.SmallAtFiles
import Johnson.Flat.ThreeAtFiles

set_option autoImplicit false

namespace VerifiableInference.OnPublicFiles

open OnBytes OnBytes.Flat OnBytes.Slice Inst.Model
open OnBytes.K.Arm.ProofFront (FrontSet holdsWords hpub_holdsWords isOwn)
open Johnson.Session (HoldsPub)

/-! ## The two bounds -/

theorem sizesSmall_T : sizesSmall.T < 2 ^ 32 := by decide
theorem sizesSmall_V : sizesSmall.V ≤ 2 ^ 32 := by decide
theorem ppref_T : ppref.T < 2 ^ 32 := by decide
theorem ppref_V : ppref.V ≤ 2 ^ 32 := by decide

/-! ## The tests as programs -/

/-- The test on a typed instance, over plain types: an instance that passes okS, and twice a record
that passes isR. No interface is handed over. -/
def okRun {X R : Type} (okS : X → Bool) (isR : R → Bool) (z : Option X × R × R) : Bool :=
  (match z.1 with
    | some x => okS x
    | none => false) && isR z.2.1 && isR z.2.2

/-- "The reply is 0", at the small size. -/
def okSSmall (x : ReqAt sizesSmall) : Bool := isOwn sizesSmall_V_pos Subtype.val x && true

/-- "The reply is 0", at the full size. -/
def okSFull (x : Flat.Req) : Bool := isOwn ppref_V_pos Subtype.val x && true

/-! ## The small example -/

section Small
variable (A : (srS.toDecR srZ 524285).Claims (ReqAt sizesSmall)) (E : Coding A)
  (G₀ : FilesParameters (ReqAt sizesSmall) RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G₀).Provers)
  (hE : ∀ x, (G₀.early x).val = withoutReply sizesSmall_V_pos x.val) (r₀ : RecSmall)
  (pol lay KL : ByteArray)

/-- An instance holds the request file and the reply file that say it, at three public files. -/
@[reducible] noncomputable def holdsSmall :
    HoldsPub (ReqAt sizesSmall) ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G₀).withProvers P).early :=
  holdsWords (L := (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G₀).withProvers P) sizesSmall_V_pos Subtype.val hE pol lay KL

/-- **The set of all early parts, at the small size.** -/
noncomputable def frontSmall :
    FrontSet ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G₀).withProvers P) (holdsSmall A E G₀ P hE pol lay KL).req2 r₀ :=
  FrontSet.ownPub sizesSmall_T sizesSmall_V sizesSmall_V_pos Subtype.val Subtype.val_injective hE
    (recIs r₀) (recIs_one r₀) (recIs_self r₀) (holdsSmall A E G₀ P hE pol lay KL)
    (hpub_holdsWords sizesSmall_V_pos Subtype.val hE pol lay KL)

/-- **It has every request.** The one premise hE (the early part lays the reply 0) forms the set. -/
theorem has_frontSmall (i : ReqAt sizesSmall) : (frontSmall A E G₀ P hE r₀ pol lay KL).Has i :=
  FrontSet.has_ownPub sizesSmall_T sizesSmall_V sizesSmall_V_pos Subtype.val Subtype.val_injective
    hE (recIs r₀) (recIs_one r₀) (recIs_self r₀) (holdsSmall A E G₀ P hE pol lay KL)
    (hpub_holdsWords sizesSmall_V_pos Subtype.val hE pol lay KL) i

/-- **Its test on a typed instance is the program** `okRun okSSmall (recIs r₀)`, by unfolding. -/
theorem frontSmall_okX :
    (frontSmall A E G₀ P hE r₀ pol lay KL).okX = okRun okSSmall (recIs r₀) := rfl

end Small

section SmallAt
variable (A : (srS.toDecR srZ 524285).Claims (ReqAt sizesSmall)) (E : Coding A)
  (p : Model.Verify.Planned) (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigReqSmall p)).Provers)
  (pol lay KL : ByteArray)

/-- **At the data made of a planner's answer, and the record of zeros**: no premise is left. -/
noncomputable def frontSmallAt :
    FrontSet ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigReqSmall p)).withProvers P)
      (holdsSmall A E (bigReqSmall p) P (fun _ => rfl) pol lay KL).req2 recZeroSmall :=
  frontSmall A E (bigReqSmall p) P (fun _ => rfl) recZeroSmall pol lay KL

theorem has_frontSmallAt (i : ReqAt sizesSmall) : (frontSmallAt A E p P pol lay KL).Has i :=
  has_frontSmall A E (bigReqSmall p) P (fun _ => rfl) recZeroSmall pol lay KL i

end SmallAt

/-! ## The full size -/

section Full
variable (A : (frS.toDecR frZ 402653181).Claims Flat.Req) (E : Coding A)
  (G₀ : FilesParameters Flat.Req RecFull) (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G₀).Provers)
  (hE : ∀ x, (G₀.early x).val = withoutReply ppref_V_pos x.val) (r₀ : RecFull)
  (pol lay KL : ByteArray)

/-- An instance holds the request file and the reply file that say it, at three public files. -/
@[reducible] noncomputable def holdsFull :
    HoldsPub Flat.Req ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G₀).withProvers P).early :=
  holdsWords (L := (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G₀).withProvers P) ppref_V_pos Subtype.val hE pol lay KL

/-- **The set of all early parts, at the full size.**

No property of the programs' second hash function (OnBytes/Hash/SecondHashFunction.lean) is assumed: the set of
all requests tells two requests apart by the request file's bytes (`frontFull`, `frontSmall`,
Johnson/Flat/FrontSetAtFiles.lean). -/
noncomputable def frontFull :
    FrontSet ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G₀).withProvers P) (holdsFull A E G₀ P hE pol lay KL).req2 r₀ :=
  FrontSet.ownPub ppref_T ppref_V ppref_V_pos Subtype.val Subtype.val_injective hE
    (recIs r₀) (recIs_one r₀) (recIs_self r₀) (holdsFull A E G₀ P hE pol lay KL)
    (hpub_holdsWords ppref_V_pos Subtype.val hE pol lay KL)

/-- **It has every request.** The one premise hE (the early part lays the reply 0) forms the set. -/
theorem has_frontFull (i : Flat.Req) : (frontFull A E G₀ P hE r₀ pol lay KL).Has i :=
  FrontSet.has_ownPub ppref_T ppref_V ppref_V_pos Subtype.val Subtype.val_injective
    hE (recIs r₀) (recIs_one r₀) (recIs_self r₀) (holdsFull A E G₀ P hE pol lay KL)
    (hpub_holdsWords ppref_V_pos Subtype.val hE pol lay KL) i

/-- **Its test on a typed instance is the program** `okRun okSFull (recIs r₀)`, by unfolding. -/
theorem frontFull_okX :
    (frontFull A E G₀ P hE r₀ pol lay KL).okX = okRun okSFull (recIs r₀) := rfl

end Full

section FullAt
variable (A : (frS.toDecR frZ 402653181).Claims Flat.Req) (E : Coding A)
  (p : Model.Verify.Planned) (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigReq p)).Provers)
  (pol lay KL : ByteArray)

/-- **At the data made of a planner's answer, and the record of zeros**: no premise is left. -/
noncomputable def frontFullAt :
    FrontSet ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigReq p)).withProvers P)
      (holdsFull A E (bigReq p) P (fun _ => rfl) pol lay KL).req2 recZeroFull :=
  frontFull A E (bigReq p) P (fun _ => rfl) recZeroFull pol lay KL

theorem has_frontFullAt (i : Flat.Req) : (frontFullAt A E p P pol lay KL).Has i :=
  has_frontFull A E (bigReq p) P (fun _ => rfl) recZeroFull pol lay KL i

end FullAt

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.has_frontSmall
#print axioms VerifiableInference.OnPublicFiles.frontSmall_okX
#print axioms VerifiableInference.OnPublicFiles.frontFull_okX
#print axioms VerifiableInference.OnPublicFiles.has_frontSmallAt
#print axioms VerifiableInference.OnPublicFiles.has_frontFull
#print axioms VerifiableInference.OnPublicFiles.has_frontFullAt
