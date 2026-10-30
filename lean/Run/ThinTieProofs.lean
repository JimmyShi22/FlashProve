-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinTieProofs.lean: the proofs of the statements of Run/ThinTie.lean. Many statements of this
library are written twice: a definition in the namespace `Spec` states a proposition, and a theorem
of the same name outside that namespace proves it (lean/GLOSSARY.md).

`thin_verify`: `verifyP` as the run of `Compile.Batch.verifyOneProtocol` (statement and hypotheses:
Run/ThinTie.lean).
One lemma for each function of Run/ThinDefs.lean but `sExtP` (its name with `_eq`; for `needP`:
`needThin_eq`). Where both sides hold the same match (Lean has made two matchers of it), the proof
goes by cases on what is matched.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ThinTie
import Run.TwinDetProofs

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

section
variable {I X : Type} {lam K : ℕ} (L : BatchProtocol I X)

/-! ### Forests -/

theorem splitP_eq (pr : Bool) (F : Forest lam L) : splitP (fun _ => L) pr F = Forest.split pr F :=
  rfl
theorem idxP_eq (F : Forest lam L) : idxP (fun _ => L) F = F.idx := rfl
theorem needThin_eq (F : Forest lam L) : needP (fun _ => L) F = F.need := rfl
theorem readsOneP_eq (F : Forest lam L) : readsOneP (fun _ => L) F = F.reads := rfl
theorem flatP_eq (Fs : List (Forest lam L)) : flatP (fun _ => L) Fs = flatF Fs := rfl
theorem readsP_eq (Fs : List (Forest lam L)) : readsP (fun _ => L) Fs = readsF Fs := rfl
theorem wellP_eq (c : Check lam L) : wellP (fun _ => L) c = c.wellFormed := rfl

/-! ### The checks -/

theorem compP_eq (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, compP (fun _ => L) r posAt depth emb rt isRead f js =
      checksComp (r := r.up) posAt depth emb rt isRead f js
  | [] => rfl
  | j :: js => by
    simp only [compP, checksComp, compP_eq r posAt depth emb rt isRead f js]
    generalize checksComp (r := r.up) posAt depth emb rt isRead f js = z
    cases posAt j with
    | none => rfl
    | some p =>
      dsimp only
      cases isRead p with
      | false => rfl
      | true =>
        simp only [if_true]
        generalize f p = o
        cases o <;> cases z <;> rfl

theorem optP_eq (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Option (Dig lam)) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    optP (fun _ => L) r posAt depth emb rt isRead f =
      checksOpt (r := r.up) posAt depth emb rt isRead f := by
  cases rt with
  | none => rfl
  | some c => exact compP_eq L r posAt depth emb c isRead f _

theorem forestsP_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (emb : (p : OPos (up S)) → OSym (up S) p → Body L) (rts : RootsOfChain lam (up S))
        (isRead : OPos (up S) → Bool)
        (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      forestsP (fun _ => L) S A W emb rts isRead f = forestsT S A W emb rts isRead f
  | [], _, _, _, _, _, _ => rfl
  | r :: S, (_, A), (w, W), emb, (rt, rts), isRead, f => by
    simp only [forestsP, forestsT, optP_eq, forestsP_eq S A W, splitP_eq]
    generalize checksOpt w.posAt0 w.depth0 (fun p => emb (.inl p)) rt.1.join
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) = x
    generalize checksOpt w.posAtJ w.depthJ (fun p => emb (.inl p)) rt.2.join
        (fun p => isRead (.inl p)) (fun p => f (.inl p)) = y
    generalize forestsT S A W (fun p => emb (.inr p)) rts
        (fun p => isRead (.inr p)) (fun p => f (.inr p)) = z
    cases x <;> cases y <;> cases z <;> rfl

theorem extWP_eq {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ ps : List E.Pos, extWP (fun _ => L) we emb cms isRead g ps = checksExtW we emb cms isRead g ps
  | [] => rfl
  | p :: ps => by
    simp only [extWP, checksExtW, extWP_eq we emb cms isRead g ps]
    generalize checksExtW we emb cms isRead g ps = z
    cases isRead p with
    | false => rfl
    | true =>
      simp only [if_true]
      generalize g p = o
      cases o <;> cases z <;> rfl

theorem forestExtP_eq {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    forestExtP (fun _ => L) we emb cms isRead g = forestExt we emb cms isRead g := by
  unfold forestExtP forestExt
  rw [extWP_eq]
  rfl

end

/-! ### The local transcript; the strict format -/

section
variable {lam K : ℕ}

theorem rootP_eq (r : RS) (a : RAnn r.up) (rt : RtC lam × RtC lam) (p : r.Pos) :
    rootP r a rt p = rootAt (r := r.up) a rt p := rfl
theorem effP_eq (r : RS) (a : RAnn r.up) (rt : RtC lam × RtC lam) (pl : r.Plain) :
    effP r a rt pl = effPlainT r a rt pl := rfl

theorem effsP_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (rts : RootsOfChain lam (up S)) (pls : Plains (up S)),
      effsP S A rts pls = effPlainsT S A rts pls
  | [], _, _, _ => rfl
  | r :: S, (a, A), (rt, rts), (pl, pls) => by
    show (effP r a rt pl, effsP S A rts pls) = (effPlainT r a rt pl, effPlainsT S A rts pls)
    rw [effsP_eq S A rts pls]
    rfl

theorem trP_eq :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (rts : RootsOfChain lam (up S))
        (pls : Plains (up S)) (ρ : Rho (up S))
        (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      trP S A W rts pls ρ f = mkTrT S A W rts pls ρ f
  | [], _, _, _, _, _, _ => rfl
  | r :: S, (a, A), (w, W), (rt, rts), (pl, pls), (c, ρ), f => by
    simp only [trP, mkTrT, trP_eq S A W rts pls ρ]
    refine Prod.ext (Prod.ext (congrArg w.pt.ofSyms (funext fun p => ?_)) rfl) rfl
    show (match rootAt (r := r.up) a rt p, f (.inl p) with
        | true, some op => op.sym
        | _, _ => w.pt.zero p) = _
    generalize rootAt (r := r.up) a rt p = b
    generalize f (.inl p) = o
    cases b <;> cases o <;> rfl

theorem cntP_eq : ∀ (S : List RS) (rts : RootsOfChain lam (up S)), cntP S rts = countT S rts
  | [], _ => rfl
  | _ :: S, (rt, rts) => by simp only [cntP, countT, cntP_eq S rts]

theorem sCompP_eq (sMT : ℕ) (r : RS) (posAt : ℕ → Option r.Pos) (depth : ℕ) (hasRoot : Bool)
    (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    sCompP sMT r posAt depth hasRoot isRead f =
      strictComp (r := r.up) sMT posAt depth hasRoot isRead f := by
  unfold sCompP strictComp
  refine congrArg _ (funext fun j => ?_)
  cases posAt j with
  | none => rfl
  | some p =>
    dsimp only
    generalize f p = o
    cases o <;> rfl

theorem sSP_eq (sMT : ℕ) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (rts : RootsOfChain lam (up S))
        (isRead : OPos (up S) → Bool)
        (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
      sSP sMT S A W rts isRead f = strictST sMT S A W rts isRead f
  | [], _, _, _, _, _ => rfl
  | r :: S, (_, A), (w, W), (rt, rts), isRead, f => by
    simp only [sSP, strictST, sCompP_eq, sSP_eq sMT S A W]

end

/-! ### At oracle functions -/

section
variable {I X : Type} {lam K : ℕ} (L : BatchProtocol I X) (g : Fam (Batch.spec lam K L))

theorem nodeP_eq : nodeP (fun _ => L) g = nodeF g := rfl
theorem rnodeP_eq : rnodeP (fun _ => L) g = rnodeF g := rfl

theorem chainP_eq (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
        (rts : List (Dig lam)) (pls : Plains (up S)),
      chainP (fun _ => L) g early late t cms x salt rtreq S A W embP i ph rts pls =
        chainTF g early late t cms x salt rtreq S A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [chainP, chainTF]
      generalize actOf cms (x.map early) salt a.kind ph = act
      cases act with
      | none => rfl
      | some ac =>
        cases ac with
        | one h own next =>
          cases own with
          | true =>
            dsimp only
            generalize takeRt w.hasJ rts = tr
            cases tr with
            | none => rfl
            | some p =>
              dsimp only
              rw [chainP_eq early late t cms x salt rtreq S A W]
              rfl
          | false =>
            dsimp only
            generalize takeRt w.has0 rts = tr
            cases tr with
            | none => rfl
            | some p =>
              dsimp only
              rw [chainP_eq early late t cms x salt rtreq S A W]
        | join ρ =>
          dsimp only
          generalize takeRt w.hasJ rts = tr
          cases tr with
          | none => rfl
          | some p =>
            dsimp only
            generalize takeRt w.has0 p.2 = tr2
            cases tr2 with
            | none => rfl
            | some p2 =>
              dsimp only
              rw [chainP_eq early late t cms x salt rtreq S A W]

theorem runForestP_eq (F : Forest lam L) (s : List (Dig lam)) :
    runForestP (fun _ => L) g F s = runForestF g F s := rfl

theorem runForestsP_eq :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
      runForestsP (fun _ => L) g Fs s = runForestsF g Fs s
  | [], _ => rfl
  | F :: Fs, s => by
    show (runForestP (fun _ => L) g F (s.take F.need) &&
        runForestsP (fun _ => L) g Fs (s.drop F.need)) =
      (runForestF g F (s.take F.need) && runForestsF g Fs (s.drop F.need))
    rw [runForestsP_eq Fs, runForestP_eq]

theorem reqCheckP_eq (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) :
    reqCheckP (fun _ => L) g depthReq rtreq slot path c = reqCheckF g depthReq rtreq slot path c :=
  rfl

variable {Y : Type} {E : ExtSpec}

theorem reqPartP_eq {Q : BatchInteractiveOracleProof Y E} (depthReq : ℕ) (π : OneProtocolProof lam Q) (ph : Phase lam) :
    reqPartP (fun _ => L) g depthReq π.rtreq π.slot π.path ph = reqPartF g depthReq π ph := by
  unfold reqPartP reqPartF
  cases ph.slotVal <;> rfl

theorem strictP_eq (sMT sFS : ℕ) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (depthReq : ℕ) (x : Y)
    (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    strictP sMT sFS P wq depthReq x π ρ rts ph = strictBT sMT sFS P wq depthReq x π ρ rts ph := by
  unfold strictP strictBT
  dsimp only
  rw [cntP_eq, sSP_eq, effsP_eq]
  rfl

theorem forestsOfP_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S)) (rts : RootsOfChain lam (up P.S)) :
    forestsOfP (fun _ => L) P wq embS embE cms x π ρ rts =
      forestsOfT P wq embS embE cms x π ρ rts := by
  unfold forestsOfP forestsOfT
  dsimp only
  rw [forestsP_eq, forestExtP_eq, effsP_eq]
  generalize forestsT P.S P.ann wq.sh embS rts _ π.opens = a
  generalize forestExt wq.ext embE cms _ π.ext = b
  cases a <;> cases b <;> rfl

theorem afterP_eq (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    afterP (fun _ => L) g P wq embS embE depthReq cms x π ρ rts ph =
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterP afterBOTF
  rw [forestsOfP_eq]
  cases forestsOfT P wq embS embE cms x π ρ rts with
  | none => rfl
  | some Fs =>
    dsimp only
    rw [runForestsP_eq, reqPartP_eq, trP_eq]
    rfl

theorem verifyP_eq (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    verifyP (fun _ => L) g early late sMT sFS t P wq embS embP xin embE depthReq cms x π =
      verifyTF g early late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  unfold verifyP verifyTF
  rw [chainP_eq]
  cases chainTF g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
    dsimp only
    rw [strictP_eq, afterP_eq]

end

theorem thin_chain : Spec.thin_chain := fun _ _ _ _ L g early late t cms x salt rtreq =>
  chainP_eq L g early late t cms x salt rtreq

theorem thin_strict : Spec.thin_strict := fun _ _ _ _ => strictP_eq

theorem thin_after : Spec.thin_after := fun _ _ _ _ L g _ _ => afterP_eq L g

theorem thin_twin : Spec.thin_twin := fun _ _ _ _ L g _ _ => verifyP_eq L g

theorem thin_verify :
    Spec.thin_verify := fun I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π =>
  (verifyP_eq L g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π).trans
    (twd_verify I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π).symm

end Run.Thin
