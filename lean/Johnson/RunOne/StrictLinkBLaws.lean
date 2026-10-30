-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkBLaws.lean: THE LAWS OF THE PROBE Johnson/RunOne/StrictLinkB.lean: its four lists meet
the five premises of verifyBSL_eq (OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifierLaws.lean:132-141) at the link's true wire
wqXE D dec, at every string that assembleT lays; so the probe's fourteen lines, behind a chain that returns, all
say yes just where the second compiler's strict verifier verifyOneProtocol itself says yes at that string.
  pieces_sh, pieces_ext, pieces_nOpen, pieces_maxDepth   what ran of the wire is wqXE's: by rfl
  mem_of_lookup2 · mem_of_opTS · listedOK_opLS · listedOK_assembleT   (hO) own openings stand at listed leaves alone
  ext_listed · ext_listed_assembleT   (hE) stored openings stand at listed positions alone
  [hA ships: weX_all, OnBytes/TypedOracleCompiler/Slice/EntryVerdictShort.lean]
  leavesOK_link   (hR) over leavesOK_rdOfR (StrictLinkRdLaws.lean) and placeOKS_wqXL (ships)
  lstX_is   (hRE) lstX is the wire's list of all positions, filtered by what the link reads
  assembleT_is   at the file's own two tables assembleT is assembleS
  **stagesB_yes**   the top
Limits. The carrier, the family, the list of outer roots and the instance are the probe's letters: nothing here carries
a yes to innerCompiledVerifier's link (another carrier, list, number of blocks, xin none, the input's p and m). A run is an
evaluation, no theorem. Nothing on soundness.

-/
import Johnson.RunOne.StrictLinkB
import Johnson.RunOne.StrictLinkRdLaws
import Johnson.RunOne.AskShellLaws
import OnBytes.Maker.ListedStepsLaws
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedVerifierLaws
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictShortEq

set_option autoImplicit false

namespace Johnson.RunOne.StrictB
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE bodyS)
open _root_.Run.PQ (View SgX weX)
open _root_.Run (bytesToBits bytesToDig rootsB)
open TypedOracleCompiler.Slice
open OnBytes.Maker (Steps behindSteps)

/-- What a look-up finds is a member. -/
theorem mem_of_lookup2 {β : Type} : ∀ (l : List ((ℕ × ℕ) × β)) (j : ℕ × ℕ) (b : β),
    l.lookup j = some b → (j, b) ∈ l
  | [], _, _, h => by cases h
  | (a, b0) :: l, j, b, h => by
    rw [List.lookup_cons] at h
    by_cases e : j = a
    · subst e
      rw [beq_self_eq_true] at h
      cases h
      exact List.mem_cons_self
    · rw [beq_eq_false_iff_ne.2 e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup2 l j b h)

/-- The places that a table lists under a tree's own number. -/
def placesOf (tab : Tab) (s : _root_.Fmt.Shape) : List ℕ :=
  (tab.filter fun z => z.1.1 == s.tree).map fun z => z.1.2

/-- One round's trees: where the look-up gives an opening, the leaf is listed under its tree. -/
theorem mem_of_opTS (run : ByteArray) (tab : Tab) :
    ∀ (ts : List _root_.Fmt.Shape) (n k j : ℕ) (p : PQ.PosT ts), PQ.posAtT ts k j = some p →
      opTS (lookE run tab) n ts p ≠ none → j ∈ (ts.map (placesOf tab)).getD k []
  | [], _, _, _, p, _, _ => p.elim
  | s :: ts, n, 0, j, p, h, hf => by
      unfold PQ.posAtT at h
      split at h
      · cases h
        show j ∈ placesOf tab s
        cases e : tab.lookup (s.tree, j) with
        | none =>
          refine absurd ?_ hf
          show lookF (fun _ => run) tab s.tree s _ = none
          unfold lookF
          simp only [e]
        | some v =>
          exact List.mem_map.2 ⟨((s.tree, j), v),
            List.mem_filter.2 ⟨mem_of_lookup2 tab _ v e, beq_self_eq_true _⟩, rfl⟩
      · cases h
  | s :: ts, n, k + 1, j, p, h, hf => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 (show (PQ.posAtT ts k j).map Sum.inr = some p from h)
      exact mem_of_opTS run tab ts (n + 1) k j q hq hf

/-- The written rounds: own openings stand at listed leaves alone. -/
theorem listedOK_opLS (C : PQ.CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (run : ByteArray) (tab : Tab) : ∀ (ds : List PQ.RD) (n : ℕ),
      ListedOK (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds)
        (opLS C (lookE run tab) n ds) (ds.map fun d => ([], d.trees.map (placesOf tab)))
  | [], _ => trivial
  | d :: ds, n =>
    ⟨fun _ _ _ _ h => (by cases h),
      fun k _ j p h hf => mem_of_opTS run tab d.trees n k j p h hf,
      listedOK_opLS C K chal run tab ds (n + d.trees.length)⟩

section
variable {X : Type} (D : XD) (dec : X → View → Bool)

theorem pieces_sh : (wqXL D dec []).sh = (wqXE D dec).sh := rfl
theorem pieces_ext : (weXL D.a []).less = (wqXE D dec).ext.less := rfl
theorem pieces_nOpen : (wqXL D dec []).nOpen = (wqXE D dec).nOpen := rfl
theorem pieces_maxDepth : (wqXL D dec []).maxDepth = (wqXE D dec).maxDepth := rfl

/-- **(hO)** -/
theorem listedOK_assembleT (o : _root_.Fmt.ChainOut) (tab tx : Tab) (π : OneProtocolProof 256 (PSXE D dec).up)
    (h : assembleT D dec o tab tx = some π) :
    ListedOK (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh π.opens
      (ownOfTab D tab) := by
  unfold assembleT at h
  split at h
  · cases h
    exact ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h),
      listedOK_opLS D.C D.K _ _ tab D.ds 0⟩
  · cases h

/-- Stored openings stand at listed positions alone. -/
theorem ext_listed (a : ℕ) (cfg : ByteArray) (tx : Tab) :
    ∀ p, extE a cfg tx p ≠ none → p ∈ listedOfTx a tx
  | .inl q, h => by
      cases e : tx.lookup (0, q.val) with
      | none => exact absurd (by simp only [extE, e, Option.map_none]) h
      | some v =>
        refine List.mem_filterMap.2 ⟨((0, q.val), v), mem_of_lookup2 tx _ v e, ?_⟩
        show (if h : q.val < 2 ^ a then
          some (if (0 : ℕ) == 0 then Sum.inl ⟨q.val, h⟩ else Sum.inr ⟨q.val, h⟩) else none) =
            some (Sum.inl q)
        rw [dif_pos q.isLt]
        rfl
  | .inr q, h => by
      cases e : tx.lookup (1, q.val) with
      | none => exact absurd (by simp only [extE, e, Option.map_none]) h
      | some v =>
        refine List.mem_filterMap.2 ⟨((1, q.val), v), mem_of_lookup2 tx _ v e, ?_⟩
        show (if h : q.val < 2 ^ a then
          some (if (1 : ℕ) == 0 then Sum.inl ⟨q.val, h⟩ else Sum.inr ⟨q.val, h⟩) else none) =
            some (Sum.inr q)
        rw [dif_pos q.isLt]
        rfl

/-- **(hE)** -/
theorem ext_listed_assembleT (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (PSXE D dec).up) (h : assembleT D dec o tab tx = some π) :
    ∀ p, π.ext p ≠ none → p ∈ listedOfTx D.a tx := by
  unfold assembleT at h
  split at h
  · cases h
    exact ext_listed D.a D.base.cfg tx
  · cases h

/-- The probe's list of read leaves. -/
def mkRdB (x : X) (ρ : Rho (PSXE D dec).up.loc.shape) (pl : Plains (PSXE D dec).up.loc.shape) :
    Leaves :=
  TypedOracleCompiler.Run.Thin.rdOfR (PSXE D dec).S (PSXE D dec).ann (wqXL D dec []).sh
    ((PSXE D dec).reads x ρ pl)

/-- **(hR)** -/
theorem leavesOK_link (x : X) (ρ : Rho (PSXE D dec).up.loc.shape)
    (pl : Plains (PSXE D dec).up.loc.shape) :
    LeavesOK (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh
      (isReadOf (PSXE D dec).up (wqXE D dec) x ρ pl) (mkRdB D dec x ρ pl) :=
  TypedOracleCompiler.Run.Thin.leavesOK_rdOfR (PSXE D dec).S (PSXE D dec).ann (wqXL D dec []).sh
    (placeOKS_wqXL D dec []) ((PSXE D dec).reads x ρ pl) _ fun _ => decide_eq_true_iff

/-- **(hRE)** -/
theorem lstX_is (x : X) (ρ : Rho (PSXE D dec).up.loc.shape) :
    lstX D dec x ρ =
      (wqXE D dec).ext.all.filter (isReadEOf (PSXE D dec).up (wqXE D dec) x ρ) := by
  refine TypedOracleCompiler.Run.Thin.eq_of_sorted_mem (ix2 (2 ^ D.a)) _ _ (lstX_sorted D dec x ρ)
    ((weX_sorted D.a).filter _) fun p => ?_
  rw [List.mem_filter]
  constructor
  · intro hp
    exact ⟨weX_all D.a p,
      decide_eq_true (List.mem_toFinset.2 ((sortU_mem _ (ix2_inj _) p _).1 hp))⟩
  · rintro ⟨-, hp⟩
    exact lstX_cover D dec x ρ p (of_decide_eq_true hp)

/-- **At the file's own two tables assembleT is assembleS.** -/
theorem assembleT_is (o : _root_.Fmt.ChainOut) :
    assembleS D dec o = (tabsOf D o).bind fun t => assembleT D dec o t.1 t.2 := by
  unfold assembleS tabsOf assembleT
  cases o.run <;> cases PQ.plainsSL D.C D.ds o.rounds.toList <;>
    cases tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) <;>
    cases tabOf (whichOf D) ((opsOf 1 o).filter fun op => op.sh.stored) <;> rfl

variable {Bd : Type} (B : BodyD Bd) (E : OwnE Bd D) (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- **THE TOP: behind a chain that returns, the fourteen lines all say yes just where verifyOneProtocol says yes**, at the
link's true wire and at every string that assembleT lays. -/
theorem stagesB_yes
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X) (o : _root_.Fmt.ChainOut) (tab tx : Tab)
    (π : OneProtocolProof 256 (PSXE D dec).up) (h : assembleT D dec o tab tx = some π) :
    ((stagesB D dec B E early Tf F cms x π tab tx).map OnBytes.Maker.Steps.yes).getD false =
      (verifyOneProtocol (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1)
        (256 + 8 * D.base.plan.salt) 256 .link (PSXE D dec).up (wqXE D dec) E.emb
        (embPXE D early (Tf ())) some B.embE 0 cms x π).det F := by
  rw [← verifyBSL_eq (L := LXE (Bd := Bd) D early (Tf ())) (PSXE D dec).up (wqXE D dec)
    (256 + 8 * D.base.plan.salt) 256 0 x π (ownOfTab D tab) (listedOfTx D.a tx) E.emb B.embE cms
    .link (embPXE D early (Tf ())) some (mkRdB D dec) (lstX D dec)
    (listedOK_assembleT D dec o tab tx π h) (ext_listed_assembleT D dec o tab tx π h)
    (weX_all D.a) (leavesOK_link D dec x) (lstX_is D dec x)]
  unfold stagesB verifyBSL
  rw [Johnson.RunOne.Ask.runOk_fst, OComp.det_bind]
  have e : (recomputeChain (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1) .link cms (some x) π.salt
      π.rtreq (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXE D dec).sh
      (embPXE D early (Tf ())) 0 .first π.roots π.plains).det F =
    (recomputeChain (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1) .link cms (some x) π.salt
      π.rtreq (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXL D dec []).sh
      (embPXE D early (Tf ())) 0 .first π.roots π.plains).det F := rfl
  rw [e]
  cases (recomputeChain (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1) .link cms (some x) π.salt
      π.rtreq (PSXE D dec).up.loc.shape (PSXE D dec).up.ann (wqXL D dec []).sh
      (embPXE D early (Tf ())) 0 .first π.roots π.plains).det F with
  | none => rfl
  | some r =>
    obtain ⟨ρ, rts, ph⟩ := r
    show (behindSteps (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1)
        (256 + 8 * D.base.plan.salt) 256 (PSXE D dec).up (wqXL D dec []).sh (weXL D.a []).less
        (wqXL D dec []).nOpen (wqXL D dec []).maxDepth E.emb B.embE 0 cms x π
        (ownOfTab D tab) (listedOfTx D.a tx)
        (mkRdB D dec x ρ (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains))
        (lstX D dec x ρ) F ρ rts ph).yes = _
    rw [OnBytes.Maker.behindSteps_yes]
    show _ = (if strictBBL (256 + 8 * D.base.plan.salt) 256 (PSXE D dec).up (wqXL D dec []).sh
          (weXL D.a []).less 0 π (ownOfTab D tab) (listedOfTx D.a tx)
          (mkRdB D dec x ρ (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains))
          (lstX D dec x ρ) rts ph = true then
        afterBOL (L := LXE (Bd := Bd) D early (Tf ())) (K := D.K + 1) (PSXE D dec).up
          (wqXL D dec []).sh (weXL D.a []).less (wqXL D dec []).nOpen (wqXL D dec []).maxDepth
          E.emb B.embE 0 cms x π
          (mkRdB D dec x ρ (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains))
          (lstX D dec x ρ) ρ rts ph
      else pure false).det F
    rw [OnBytes.Maker.det_ite]
    cases strictBBL (256 + 8 * D.base.plan.salt) 256 (PSXE D dec).up (wqXL D dec []).sh
      (weXL D.a []).less 0 π (ownOfTab D tab) (listedOfTx D.a tx)
      (mkRdB D dec x ρ (effPlains (PSXE D dec).up.loc.shape (PSXE D dec).up.ann rts π.plains))
      (lstX D dec x ρ) rts ph <;> rfl

end

end Johnson.RunOne.StrictB

#print axioms Johnson.RunOne.StrictB.listedOK_assembleT
#print axioms Johnson.RunOne.StrictB.ext_listed_assembleT
#print axioms Johnson.RunOne.StrictB.leavesOK_link
#print axioms Johnson.RunOne.StrictB.lstX_is
#print axioms Johnson.RunOne.StrictB.assembleT_is
#print axioms Johnson.RunOne.StrictB.stagesB_yes
