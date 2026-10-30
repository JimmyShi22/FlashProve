-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Yes.lean: what is left to show for a yes of the compiled verifier of one slot
(`verifyOneProtocol`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) under fixed oracle functions g, at every batch
protocol, whether its chain passes a joining round or not.

OnBytes/TypedOracleCompiler/Joined/K/Whole.lean [not in this library] has the like (`yes_of_whole`) for the verifier of a file, whose
chain has passed the joining round. Here the protocol is any, and the premise on the request tree
is split in two: what is asked if the last phase holds a slot value, and what is asked if not.

Main names:
  `count_at`       there are at most `nOpen` checks, by the laws of the wire record
  `strict_at`      the strict format (`proofHasStrictFormat`) from its parts
  `forests_at`     the forests of the string: the rounds', then the external strings'
  `req_at`         the check in the request tree
  `yes_of_parts`   the verifier has the value yes under g, if: the chain has the value (ρ, R, ph)
                   under g; the wire record is lawful; the salt has sFS bits; the string holds no
                   root beyond those in R; the slot's number fits the depth; if ph holds a slot
                   value, the request path has the depth's length and the climb from the leaf that
                   holds this value ends in the request root; if not, the request path and the
                   string behind the slot value are empty; the openings are as `Opened` and
                   `OpenedE` ask (OnBytes/TypedOracleCompiler/Joined/K/YesRead.lean); each forest's walk says yes
                   (`walkP`, OnBytes/TypedOracleCompiler/Joined/WalkAt.lean); and the decision says yes at the
                   transcript that the verifier builds from ρ, R and the string

Limits: one direction only. Nothing on soundness, nothing on probability. Nothing says what ρ, R and
ph are, nor that any string meets the premises: for the compiled prover's strings that is owed by
the other files of this folder.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Inv
import OnBytes.TypedOracleCompiler.Joined.K.Count

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run (chainF rnodeF verifyF afterBOF runForestsF reqPartF reqCheckF)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

section
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)

variable {Q wq embS embE cms x} in
/-- There are at most `nOpen` checks: no more than positions that are read. -/
theorem count_at (hw : wq.OKG) {π : OneProtocolProof lam Q} {ρ : Rho Q.loc.shape} {R : RootsOfChain lam Q.loc.shape}
    {Fs Fe : List (Forest lam L)}
    (f : forestsB Q.loc.shape Q.ann wq.sh embS R (rdS Q wq x π.plains ρ R) π.opens = some Fs)
    (fE : forestExt wq.ext embE cms (rdE Q wq x ρ) π.ext = some Fe) :
    (flatF (Fs ++ Fe)).length ≤ wq.nOpen := by
  have hcs := map_flatF_forestsB Q.loc.shape Q.ann wq.sh embS R (rdS Q wq x π.plains ρ R) π.opens
  rw [f] at hcs
  have h1 := length_checksB_le hw.sh hcs.symm
    (Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann R π.plains)) fun p hp => by
      letI := wq.decO
      exact of_decide_eq_true hp
  obtain ⟨cs, hcE, rfl⟩ := Option.map_eq_some_iff.1 fE
  have h2 := length_checksExtW_le hw.ext hcE (Q.loc.extReads x ρ) fun p hp => by
    letI := wq.ext.dec
    exact of_decide_eq_true hp
  have h3 : (Q.loc.reads x ρ (effPlains Q.loc.shape Q.ann R π.plains)).card +
      (Q.loc.extReads x ρ).card ≤ wq.nOpen :=
    hw.opens x ρ (effPlains Q.loc.shape Q.ann R π.plains)
  rw [flatF_append, List.length_append, flatF_split, List.length_map]
  show (flatF Fs).length + cs.length ≤ wq.nOpen
  omega

variable {sMT sFS Q wq depthReq x} in
/-- The strict format, from its parts. -/
theorem strict_at {π : OneProtocolProof lam Q} {ρ : Rho Q.loc.shape} {R : RootsOfChain lam Q.loc.shape} {ph : Phase lam}
    (hsalt : π.salt.length = sFS) (hroots : π.roots.length ≤ RootsOfChain.count Q.loc.shape R)
    (hslot : π.slot < 2 ^ depthReq) (hnone : ph.slotVal = none → π.path = [] ∧ π.rsalt = [])
    (s1 : strictSB sMT Q.loc.shape Q.ann wq.sh R (rdS Q wq x π.plains ρ R) π.opens = true)
    (sE : strictExt sMT wq.ext (rdE Q wq x ρ) π.ext = true) :
    proofHasStrictFormat sMT sFS Q wq depthReq x π ρ R ph = true := by
  have h6 : (ph.slotVal.isSome || π.path.isEmpty) = true := by
    cases hs : ph.slotVal with
    | some c => rfl
    | none => simp [(hnone hs).1]
  have h7 : (ph.slotVal.isSome || π.rsalt.isEmpty) = true := by
    cases hs : ph.slotVal with
    | some c => rfl
    | none => simp [(hnone hs).2]
  show (decide (π.salt.length = sFS) && decide (π.roots.length ≤ RootsOfChain.count Q.loc.shape R) &&
    strictSB sMT Q.loc.shape Q.ann wq.sh R (rdS Q wq x π.plains ρ R) π.opens &&
    strictExt sMT wq.ext (rdE Q wq x ρ) π.ext && decide (π.slot < 2 ^ depthReq) &&
    (ph.slotVal.isSome || π.path.isEmpty) && (ph.slotVal.isSome || π.rsalt.isEmpty)) = true
  simp only [decide_eq_true hsalt, decide_eq_true hroots, decide_eq_true hslot, s1, sE, h6, h7,
    Bool.and_true]

variable {Q wq embS embE cms x} in
/-- The forests of the string: those of the rounds, then those of the external strings. -/
theorem forests_at {π : OneProtocolProof lam Q} {ρ : Rho Q.loc.shape} {R : RootsOfChain lam Q.loc.shape}
    {Fs Fe : List (Forest lam L)}
    (f : forestsB Q.loc.shape Q.ann wq.sh embS R (rdS Q wq x π.plains ρ R) π.opens = some Fs)
    (fE : forestExt wq.ext embE cms (rdE Q wq x ρ) π.ext = some Fe) :
    forestsOf Q wq embS embE cms x π ρ R = some (Fs ++ Fe) := by
  have h : ∀ a b : Option (List (Forest lam L)), a = some Fs → b = some Fe →
      (match a, b with
        | some a, some b => some (a ++ b)
        | _, _ => none) = some (Fs ++ Fe) := by
    rintro _ _ rfl rfl
    rfl
  exact h _ _ f fE

variable {Q depthReq} in
/-- The check in the request tree, if the last phase holds a slot value. -/
theorem req_at (g : Fam (typedOracleFamily lam K L)) {π : OneProtocolProof lam Q} {ph : Phase lam}
    (hslot : π.slot < 2 ^ depthReq)
    (hreq : ∀ c, ph.slotVal = some c → π.path.length = depthReq ∧
      climbF (rnodeF g) π.path π.slot (g OracleName.rleaf (List.ofFn c ++ π.rsalt : Bits) : Dig lam) =
        π.rtreq) :
    reqPartF g depthReq π ph = true := by
  unfold reqPartF
  cases hs : ph.slotVal with
  | none => rfl
  | some c =>
    obtain ⟨hp, hc⟩ := hreq c hs
    show reqCheckF g depthReq π.rtreq π.slot π.path c π.rsalt = true
    unfold reqCheckF
    rw [if_pos (And.intro hp hslot)]
    exact decide_eq_true hc

/-- **What is left for a yes**, at every protocol, joined or not. -/
theorem yes_of_parts :
  ∀ (g : Fam (typedOracleFamily lam K L)) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (R : RootsOfChain lam Q.loc.shape) (ph : Phase lam),
  chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0 .first π.roots π.plains =
    some (ρ, R, ph) →
  wq.OKG → π.salt.length = sFS → π.roots.length ≤ RootsOfChain.count Q.loc.shape R →
  π.slot < 2 ^ depthReq →
  (∀ c, ph.slotVal = some c → π.path.length = depthReq ∧
    climbF (rnodeF g) π.path π.slot (g OracleName.rleaf (List.ofFn c ++ π.rsalt : Bits) : Dig lam) =
      π.rtreq) →
  (ph.slotVal = none → π.path = [] ∧ π.rsalt = []) →
  Opened sMT Q.loc.shape Q.ann wq.sh R (rdS Q wq x π.plains ρ R) π.opens →
  OpenedE sMT wq.maxDepth wq.ext (rdE Q wq x ρ) π.ext →
  (∀ Fs, forestsB Q.loc.shape Q.ann wq.sh embS R (rdS Q wq x π.plains ρ R) π.opens = some Fs →
    ∀ T ∈ Fs, walkP g T T.reads = true) →
  (∀ Fe, forestExt wq.ext embE cms (rdE Q wq x ρ) π.ext = some Fe →
    ∀ T ∈ Fe, walkP g T T.reads = true) →
  Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
    (mkTr Q.loc.shape Q.ann wq.sh R π.plains ρ π.opens) = true →
  (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true := by
  intro g π ρ R ph hz hw hsalt hroots hslot hreq hnone ho hoE hwalk hwalkE hacc
  obtain ⟨s1, Fs, f1, fit1⟩ := ho.cuts hw.sh hw.depth embS
  obtain ⟨sE, Fe, fE, fitE⟩ := hoE.cuts embE cms
  have hfit : (flatF (Fs ++ Fe)).all
      (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true := by
    rw [flatF_append, List.all_append]
    exact Bool.and_eq_true_iff.2 ⟨fit1, fitE⟩
  have hwk : runForestsF g (Fs ++ Fe) (readsF (Fs ++ Fe)) = true :=
    (TypedOracleCompiler.Run.runForests_det g _ _).symm.trans (walk_at g fun F hF =>
              (List.mem_append.1 hF).elim (hwalk Fs f1 F) (hwalkE Fe fE F))
  have haf : afterBOF g Q wq embS embE depthReq cms x π ρ R ph = true := by
    unfold afterBOF
    rw [forests_at f1 fE]
    dsimp only
    rw [if_pos (And.intro (count_at hw f1 fE) hfit)]
    exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨hwk, req_at g hslot hreq⟩, hacc⟩
  rw [TypedOracleCompiler.Run.verifyBS_det]
  unfold verifyF
  rw [hz]
  dsimp only
  rw [if_pos (strict_at hsalt hroots hslot hnone s1 sE)]
  exact haf

end

end OnBytes.Prover
