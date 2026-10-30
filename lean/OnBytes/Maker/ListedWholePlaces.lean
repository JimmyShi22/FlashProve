-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholePlaces.lean: the wire records of a whole file's rounds
(OnBytes/Maker/Wire.lean, wiresOf) number their positions by tree and leaf, at all data, all K and
every chal: under no premise. So at the description of a whole file the verifier along lists on the
cut string is the compiled verifier at the cut string under no premise at all.

No soundness: a test. This module states nothing on soundness.

Why. verifyWholeC_eq (OnBytes/Maker/ListedWholeCutTop.lean) has one premise, PlacesOK at wiresOf's
rounds. verifyWholeC_eq_ckP there takes it from the whole law of the wire (wqWhole_okg_ckP,
OnBytes/Maker/WireLaws.lean), which asks that no round needs more than K blocks or has more than 64
bits of work. These two are spent on the verifier's messages and the tests of work alone: the
clauses on trees and leaves in wireS_okg (OnBytes/TypedOracleCompiler/Run/PlanQSLaws.lean), wireSh_okg
(OnBytes/TypedOracleCompiler/Slice/Batch3Wire.lean) and wireSilent_okg (OnBytes/Maker/WireLaws.lean) use neither.
Here these
clauses are proved again without them, by the same terms.

Main names.
  placesOK_app, seatsOK_app: PlacesOK and SeatsOK of wire records in a row.
  placesOK_wiresLo, placesOK_wiresSh, seatsOK_wiresLo, seatsOK_wiresSh: a chain's written rounds.
  placesOK_sh, seatsOK_sh: a file's rounds, from its six parts'.
  placesOK_wiresOf, seatsOK_wiresOf: at wiresOf: no premise.
  verifyWholeC_eq0: **for every argument string and every two lists**, verifyWholeC π own listed =
    verifyOneProtocol at wqWhole and π.cutTo: no premise.
  verifyWholeC_eq_self: where the openings of π stand at listed places alone (hO, hE),
    verifyWholeC π own listed = verifyOneProtocol at wqWhole and π itself.

Limits. WHAT IS EQUAL TO verifyOneProtocol IS THE RUN ON THE CUT STRING, NOT ON π, unless hO and hE hold:
lists that leave out an unread place with an opening can let a string pass that verifyOneProtocol refuses at
π; lists that leave out a read place can make verifyWholeC refuse a string that verifyOneProtocol takes at π:
both by the definitions' texts; no theorem here says either. The wire record need not be lawful
here: where K is too small for a round, both sides are the same tree of queries all the same, and no
theorem on soundness speaks of either. No oracle functions come in. Nothing on time or memory.
Nothing on soundness. The program does not import this file.


-/
import OnBytes.Maker.ListedWholeCutTop
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedCutKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-! ### Wire records in a row -/

section
variable {lam K : ℕ}

theorem placesOK_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, PlacesOK s A W → PlacesOK u B V →
      PlacesOK (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, hW.2.1, placesOK_app hW.2.2 hV⟩

theorem seatsOK_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} {W : RoundsQueryLayout lam K s A}
    {V : RoundsQueryLayout lam K u B}, SeatsOK s A W → SeatsOK u B V →
      SeatsOK (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, hV => hV
  | _ :: _, _, (_, _), _, (_, _), _, hW, hV => ⟨hW.1, hW.2.1, seatsOK_app hW.2.2 hV⟩

/-- One round's clauses of PlacesOK. -/
def PlacesR {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop :=
  (∀ (k j : ℕ) (p : r.Pos), w.posAt0 k j = some p →
    a.own p = false ∧ w.tree p = k ∧ w.place p = j) ∧
  ∀ (k j : ℕ) (p : r.Pos), w.posAtJ k j = some p → a.own p = true ∧ w.tree p = k ∧ w.place p = j

/-- One round's clauses of SeatsOK. -/
def SeatsR {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Prop :=
  (∀ p : r.Pos, a.own p = false →
    w.tree p < w.depth0.length ∧ w.posAt0 (w.tree p) (w.place p) = some p) ∧
  ∀ p : r.Pos, a.own p = true →
    w.tree p < w.depthJ.length ∧ w.posAtJ (w.tree p) (w.place p) = some p

/-- A file's rounds, from its six parts'. -/
theorem placesOK_sh {G : Chains} (V : Wires lam K G) (hF : PlacesR V.wF)
    (h₁ : PlacesOK _ _ V.W₁) (hJ : PlacesR V.wJ) (h₂ : PlacesOK _ _ V.W₂) (h3 : PlacesR V.w3)
    (h₃ : PlacesOK _ _ V.W₃) : PlacesOK G.sh G.ann V.sh :=
  ⟨hF.1, hF.2, placesOK_app h₁ ⟨hJ.1, hJ.2, placesOK_app h₂ ⟨h3.1, h3.2, h₃⟩⟩⟩

theorem seatsOK_sh {G : Chains} (V : Wires lam K G) (hF : SeatsR V.wF)
    (h₁ : SeatsOK _ _ V.W₁) (hJ : SeatsR V.wJ) (h₂ : SeatsOK _ _ V.W₂) (h3 : SeatsR V.w3)
    (h₃ : SeatsOK _ _ V.W₃) : SeatsOK G.sh G.ann V.sh :=
  ⟨hF.1, hF.2, seatsOK_app h₁ ⟨hJ.1, hJ.2, seatsOK_app h₂ ⟨h3.1, h3.2, h₃⟩⟩⟩

end

/-! ### The rounds' records -/

theorem placesR_silent (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    PlacesR (wireSilent K T t a) :=
  ⟨fun _ _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩

theorem seatsR_silent (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    SeatsR (wireSilent K T t a) :=
  ⟨fun p => p.elim, fun p => p.elim⟩

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem placesR_lo (d : RDT) : PlacesR (wireLo C K chal d) :=
  ⟨fun _ _ _ h => (by cases h), fun k j p h => ⟨rfl, TypedOracleCompiler.Run.PQ.place_posAtT d.toRD.trees k j p h⟩⟩

theorem placesR_sh (d : RDT) : PlacesR (wireSh C K chal d) :=
  ⟨fun k j p h => ⟨rfl, TypedOracleCompiler.Run.PQ.place_posAtT d.toRD.trees k j p h⟩, fun _ _ _ h => (by cases h)⟩

theorem seatsR_lo (d : RDT) : SeatsR (wireLo C K chal d) :=
  ⟨fun _ h => (by cases h), fun p _ =>
    ⟨seat_lt (TypedOracleCompiler.Run.PQ.placeT_lt d.toRD.trees p),
      TypedOracleCompiler.Run.PQ.posAtT_place d.toRD.trees p⟩⟩

theorem seatsR_sh (d : RDT) : SeatsR (wireSh C K chal d) :=
  ⟨fun p _ =>
    ⟨seat_lt (TypedOracleCompiler.Run.PQ.placeT_lt d.toRD.trees p),
      TypedOracleCompiler.Run.PQ.posAtT_place d.toRD.trees p⟩, fun _ h => (by cases h)⟩

theorem placesOK_wiresLo : ∀ ds : List RDT,
    PlacesOK (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [] => trivial
  | d :: ds => ⟨(placesR_lo C K chal d).1, (placesR_lo C K chal d).2, placesOK_wiresLo ds⟩

theorem placesOK_wiresSh : ∀ ds : List RDT,
    PlacesOK (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [] => trivial
  | d :: ds => ⟨(placesR_sh C K chal d).1, (placesR_sh C K chal d).2, placesOK_wiresSh ds⟩

theorem seatsOK_wiresLo : ∀ ds : List RDT,
    SeatsOK (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [] => trivial
  | d :: ds => ⟨(seatsR_lo C K chal d).1, (seatsR_lo C K chal d).2, seatsOK_wiresLo ds⟩

theorem seatsOK_wiresSh : ∀ ds : List RDT,
    SeatsOK (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [] => trivial
  | d :: ds => ⟨(seatsR_sh C K chal d).1, (seatsR_sh C K chal d).2, seatsOK_wiresSh ds⟩

variable (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **A whole file's rounds' wire records: a position that is laid at a leaf has that leaf's
component, tree and number.** No premise. -/
theorem placesOK_wiresOf : PlacesOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
    (wiresOf C K chal D tF tJ t3).sh :=
  placesOK_sh (wiresOf C K chal D tF tJ t3) (placesR_silent _ _ _ _)
    (placesOK_wiresLo C K chal D.ds₁) (placesR_silent _ _ _ _) (placesOK_wiresSh C K chal D.ds₂)
    (placesR_silent _ _ _ _) (placesOK_wiresLo C K chal D.ds₃)

/-- **And every position stands at its own tree and leaf.** No premise. -/
theorem seatsOK_wiresOf : SeatsOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
    (wiresOf C K chal D tF tJ t3).sh :=
  seatsOK_sh (wiresOf C K chal D tF tJ t3) (seatsR_silent _ _ _ _)
    (seatsOK_wiresLo C K chal D.ds₁) (seatsR_silent _ _ _ _) (seatsOK_wiresSh C K chal D.ds₂)
    (seatsR_silent _ _ _ _) (seatsOK_wiresLo C K chal D.ds₃)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The verifier of a whole file along the lists on the cut string is the compiled verifier at the
file's wire record and the cut string**: for every argument string and every two lists; no premise.
-/
theorem verifyWholeC_eq0 (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) :
    verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed =
      verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) :=
  verifyWholeC_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x
    (placesOK_wiresOf C K chal D tF tJ t3) π own listed

/-- **Where the openings of the string stand at listed places alone, it is the compiled verifier at
the string itself.** -/
theorem verifyWholeC_eq_self (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos)
    (hO : ListedOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh π.opens own)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) :
    verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed =
      verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π := by
  rw [verifyWholeC_eq0 C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
    own listed]
  exact congrArg _ (cutTo_of_listed π (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed
    (seatsOK_wiresOf C K chal D tF tJ t3) hO hE)

end

end OnBytes.Maker

#print axioms OnBytes.Maker.placesOK_wiresOf
#print axioms OnBytes.Maker.seatsOK_wiresOf
#print axioms OnBytes.Maker.verifyWholeC_eq0
#print axioms OnBytes.Maker.verifyWholeC_eq_self
