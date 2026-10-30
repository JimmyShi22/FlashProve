-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LessWhole.lean: the verifier of a whole file along the lists (ListedWhole.lean,
verifyWholeL) over lesser wire records that are made straight from the rounds' data, and the
equation between the two.

Why. verifyWholeL takes the file's wire records (wiresOf .. .sh, OnBytes/Maker/Wire.lean). Each
written round's record holds the list of all positions of the round's trees (Round.IsPoint's field
finPos, made by finPosT d.trees, OnBytes/TypedOracleCompiler/Run/PlanQS.lean, wireS), which the verifier never
reads. The list has 2 ^ depth members for each of the round's trees.

What the file contains.
  lessLoS, lessShS, lessSilent: what the verifier reads of the record of a written local round, of a
    written shared round, of a silent round: from the round's data, with no list of positions.
    lessLoS_eq, lessShS_eq, lessSilent_eq: each is what is left of the full record, by definition.
  lessLo, lessSh: the same for a list of written rounds; lessLo_eq, lessSh_eq.
  less₃, lessJ, lessWhole: the file's rounds, as Wires.sh₃, shJ, sh lay them; lessWhole_eq.
  verifyWholeX: verifyWholeL with verifyBSX at lessWhole.
  verifyWholeX_eq: verifyWholeX .. = verifyWholeL .., for all arguments. No premise.

Limits. verifyWholeX_eq equates two terms: a yes of verifyWholeX is worth what a yes of the twin
verifyWholeL is worth, and no more. That the twin is the compiled verifier has premises on own and
listed (ListedWholeTop.lean, verifyWholeL_eq). Nothing on time or memory is a theorem: that no list
of positions is built is read off the definitions' text. Nothing on soundness.
The program does not import this file.

-/
import OnBytes.Maker.ListedWhole
import OnBytes.TypedOracleCompiler.Compile.Batch.LessWireLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- Of a written local round. -/
def lessLoS (d : TypedOracleCompiler.Run.PQ.RD) : WireRL 256 (K + 1) (TypedOracleCompiler.Run.PQ.roundS C d).up where
  ofSyms := fun f => f
  zero := TypedOracleCompiler.Run.PQ.zeroT d.trees
  depth0 := []
  depthJ := d.trees.map (·.a)
  tree := TypedOracleCompiler.Run.PQ.treeT d.trees
  place := TypedOracleCompiler.Run.PQ.placeT d.trees
  posAt0 := fun _ _ => none
  posAtJ := TypedOracleCompiler.Run.PQ.posAtT d.trees
  chal := chalGrind (chal d.entry d.kind) d.entry.work
  pr0 := false
  prJ := true

theorem lessLoS_eq (d : TypedOracleCompiler.Run.PQ.RD) :
    lessLoS C K chal d = lessR (TypedOracleCompiler.Run.PQ.wireS C K chal d) := rfl

/-- Of a written shared round. -/
def lessShS (d : TypedOracleCompiler.Run.PQ.RD) : WireRL 256 (K + 1) (TypedOracleCompiler.Run.PQ.roundS C d).up where
  ofSyms := fun f => f
  zero := TypedOracleCompiler.Run.PQ.zeroT d.trees
  depth0 := d.trees.map (·.a)
  depthJ := []
  tree := TypedOracleCompiler.Run.PQ.treeT d.trees
  place := TypedOracleCompiler.Run.PQ.placeT d.trees
  posAt0 := TypedOracleCompiler.Run.PQ.posAtT d.trees
  posAtJ := fun _ _ => none
  chal := chalGrind (chal d.entry d.kind) d.entry.work
  pr0 := true
  prJ := false

theorem lessShS_eq (d : TypedOracleCompiler.Run.PQ.RD) :
    lessShS C K chal d = lessR (TypedOracleCompiler.Slice.wireSh C K chal d) := rfl

def lessLo : (ds : List RDT) → WireSL 256 (K + 1) (uLT C ds)
  | [] => ()
  | d :: ds => (lessLoS C K chal d.toRD, lessLo ds)

def lessSh : (ds : List RDT) → WireSL 256 (K + 1) (uLT C ds)
  | [] => ()
  | d :: ds => (lessShS C K chal d.toRD, lessSh ds)

theorem lessLo_eq : ∀ ds : List RDT,
    lessLo C K chal ds = lessS (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [] => rfl
  | d :: ds => congrArg (Prod.mk (lessLoS C K chal d.toRD)) (lessLo_eq ds)

theorem lessSh_eq : ∀ ds : List RDT,
    lessSh C K chal ds =
      lessS (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [] => rfl
  | d :: ds => congrArg (Prod.mk (lessShS C K chal d.toRD)) (lessSh_eq ds)

end

/-- Of a round that sends a plain part alone. -/
def lessSilent (K : ℕ) (T : Type) (t : T) : WireRL 256 K (plainRound T t) where
  ofSyms := fun _ => ()
  zero := fun p => p.elim
  depth0 := []
  depthJ := []
  tree := fun p => p.elim
  place := fun p => p.elim
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := fun _ => ()
  pr0 := false
  prJ := false

theorem lessSilent_eq (K : ℕ) (T : Type) (t : T) (a : RAnn (plainRound T t)) :
    lessSilent K T t = lessR (wireSilent K T t a) := rfl

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- the seam and chain 3 -/
def less₃ : WireSL 256 (K + 1) (chainsOf C D tF tJ t3).sh₃ :=
  (lessSilent (K + 1) T3 t3, lessLo C K chal D.ds₃)

/-- the joining round, chain 2, and what follows -/
def lessJ : WireSL 256 (K + 1) (chainsOf C D tF tJ t3).shJ :=
  (lessSilent (K + 1) TJ tJ, WireSL.app (lessSh C K chal D.ds₂) (less₃ C K chal D tF tJ t3))

/-- **The lesser records of all rounds of the file.** -/
def lessWhole : WireSL 256 (K + 1) (chainsOf C D tF tJ t3).sh :=
  (lessSilent (K + 1) TF tF, WireSL.app (lessLo C K chal D.ds₁) (lessJ C K chal D tF tJ t3))

theorem less₃_eq :
    less₃ C K chal D tF tJ t3 =
      lessS (chainsOf C D tF tJ t3).sh₃ (chainsOf C D tF tJ t3).ann₃
        (wiresOf C K chal D tF tJ t3).sh₃ :=
  congrArg (Prod.mk (lessSilent (K + 1) T3 t3)) (lessLo_eq C K chal D.ds₃)

theorem lessJ_eq :
    lessJ C K chal D tF tJ t3 =
      lessS (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ
        (wiresOf C K chal D tF tJ t3).shJ := by
  have h := lessS_app (wiresSh C K chal D.ds₂) (wiresOf C K chal D tF tJ t3).sh₃
  rw [← lessSh_eq, ← less₃_eq] at h
  exact congrArg (Prod.mk (lessSilent (K + 1) TJ tJ)) h.symm

/-- They are what is left of the file's wire records. -/
theorem lessWhole_eq :
    lessWhole C K chal D tF tJ t3 =
      lessS (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
        (wiresOf C K chal D tF tJ t3).sh := by
  have h := lessS_app (wiresLo C K chal D.ds₁) (wiresOf C K chal D tF tJ t3).shJ
  rw [← lessLo_eq, ← lessJ_eq] at h
  exact congrArg (Prod.mk (lessSilent (K + 1) TF tF)) h.symm

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The verifier of a whole file along the lists, over the lesser records.** -/
def verifyWholeX (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) : TypedOracleComputation 256 (K + 1) L Bool :=
  verifyBSX sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
    (lessWhole C K chal D tF tJ t3) (wlOne D.a) (nOpenW D) (maxDepthW D) embS embP xin embE
    depthReq cms x π own listed (fun _ ρ _ => rdWhole C D tF tJ t3 ρ)
    (fun _ ρ => rdEWhole C D tF tJ t3 ρ)

/-- **It is the verifier along the lists**, as a tree of queries. No premise. -/
theorem verifyWholeX_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) :
    verifyWholeX C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed =
      verifyWholeL C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
        own listed := by
  unfold verifyWholeX verifyWholeL
  rw [lessWhole_eq]
  exact verifyBSX_eq (wholeDesc C D tF tJ t3 silent run).batch (wiresOf C K chal D tF tJ t3).sh
    (wlOne D.a) sMT sFS depthReq x π own listed embS embE cms t (nOpenW D) (maxDepthW D) embP xin
    _ _

end

end OnBytes.Maker
