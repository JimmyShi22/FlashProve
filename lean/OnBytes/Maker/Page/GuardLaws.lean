-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardLaws.lean: laws of the run that refuses at the first query which a test
turns away, and of that run at the test `okJ` (OnBytes/Maker/Page/Guard.lean,
OnBytes/Maker/Page/GuardVerify.lean).

Main names:
  `detG_det`: a value of the guarded run is the value of the plain run (`Rom.OComp.det`). So a law
    on a yes of the plain run serves a yes of the guarded run.
  `detG_eq_asked`: it is the library's test on the queries asked (`Rom.OComp.askedOK`,
    Run/DetAlong.lean) and the plain run, in one pass.
  `detG_congr`: the guarded run reads the oracle functions at queries that pass the test alone: two
    families that agree there give one result.
  `detG_det_of_agree`: so a value of the guarded run under g is the value of the plain run under
    every family that agrees with g at the queries that pass.
  `detG_bind`: the guarded run of two algorithms in a row.
  `okJ_rleaf`: at a leaf of the request tree the test is the test on the length.
  `reqCheck_guard`: where the check in the request tree, run so, has a value and the path and the
    slot fit, the string behind the slot value has the one length.
  `rsaltFit_iff`, `verifyBSR_det`: under every family a yes of `verifyBSR` gives the test's yes and
    a yes of `verifyOneProtocol`.
  `verifyGuard_iff`: a yes of `verifyGuard` is the test of `rsalt` and the value yes of the guarded
    run of `verifyOneProtocol`. `verifyGuard_yes`: so a yes of the plain run under the page's family.
  `verifyGuard_agree`: and a yes of `verifyOneProtocol` under every family that agrees with the page's at the
    queries that `okJ P` passes. No family but the page's own is shown to agree so. For K > 0: a
    yes passes a chain's first call, and there such a family must answer what the page's does in the
    K front blocks: zeros, where no taken spelling writes them: as no drawn family and no encoding
    behind an escape does. (An encoding that tests a call further, or writes leaves otherwise, parts
    from the page's family besides.)
  `verifyGuard_no`: at any other length of `rsalt`: no, whatever the run says.
  `reqCheck_hole`, `runCheck_hole`: the two holes under the plain run: at a string of another length
    behind the slot value the check in the request tree has one verdict at every slot value; two
    checks along one path to one root at leaves without a string have one verdict.
  `runCheck_guard`: the guarded run has no value at such a leaf.
  `leavesV_hole`, `leavesV_guard`, `runForest_guard`: the same at the routine by which `verifyOneProtocol`
    asks the leaves of a forest.
No letter stands under "there is".

What is not claimed. What the heads of these two files do not claim. Nothing here carries
`reqCheck_guard` to `verifyOneProtocol`: that needs that the chain has joined; under `verifyGuard` the test
of `rsalt` stands in front and says the same length. Nor is `runForest_guard` carried to
`runForests`, `afterF` or `verifyOneProtocol`. `runCheck` stands in `verifyB`; `verifyOneProtocol` asks its leaves by
`leavesV`. The premises of `runCheck_hole` and `leavesV_hole` are met at a page whose fields `leaf`
and `leafX` both write nothing at that leaf; whether a prover's string reaches such a leaf at a page
that is rightly laid is not said. No law elsewhere takes a yes of `(verifyOneProtocol ..).det (gJ P O)` as
its premise. An equation of plain runs carries to the guarded run only together with an equation
of `askedOK` (`detG_eq_asked`). "The program's yes gives that no asked query is turned away" is
not shown. Nothing on soundness.


-/
import OnBytes.Maker.Page.GuardVerify
import Run.DetAlong

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol ProtocolQueryLayout
open _root_.Run

section Gen
variable {S : OSpec} {α β : Type} (ok : ∀ o : S.ι, S.Dom o → Bool)

/-- **A value of the guarded run is the value of the plain run.** -/
theorem detG_det (g : Fam S) (c : OComp S α) {a : α} (h : detG ok g c = some a) : c.det g = a := by
  induction c with
  | pure b => exact Option.some.inj h
  | query o q k ih =>
    unfold detG at h
    split at h
    · exact ih _ h
    · cases h
  | sample n k ih => exact ih _ h

/-- **The guarded run is the library's test on the queries asked and its plain run, in one pass**
(`Rom.OComp.askedOK`, Run/DetAlong.lean). -/
theorem detG_eq_asked (g : Fam S) (c : OComp S α) :
    detG ok g c = if c.askedOK g ok then some (c.det g) else none := by
  induction c with
  | pure b => rfl
  | query o q k ih =>
    show (if ok o q then detG ok g (k (g o q)) else none) =
      if (ok o q && (k (g o q)).askedOK g ok) then some ((k (g o q)).det g) else none
    by_cases h : ok o q = true
    · rw [if_pos h, h, Bool.true_and]
      exact ih _
    · rw [if_neg h, Bool.eq_false_iff.2 h, Bool.false_and]
      rfl
  | sample n k ih => exact ih _

/-- **The guarded run reads the oracle functions at queries that pass the test alone.** -/
theorem detG_congr {g g' : Fam S} (hg : ∀ o q, ok o q = true → g o q = g' o q) (c : OComp S α) :
    detG ok g c = detG ok g' c := by
  induction c with
  | pure b => rfl
  | query o q k ih =>
    unfold detG
    by_cases h : ok o q = true
    · rw [if_pos h, if_pos h, hg o q h]
      exact ih _
    · rw [if_neg h, if_neg h]
  | sample n k ih => exact ih _

/-- A value of the guarded run under g is the value of the plain run under every family that agrees
with g at the queries that pass. With `detG_eq_asked` it is the library's `det_congr_asked`
(Run/DetAlong.lean). -/
theorem detG_det_of_agree {g g' : Fam S} (hg : ∀ o q, ok o q = true → g o q = g' o q)
    (c : OComp S α) {a : α} (h : detG ok g c = some a) : c.det g' = a :=
  detG_det ok g' c ((detG_congr ok hg c).symm.trans h)

/-- Two algorithms in a row. -/
theorem detG_bind (g : Fam S) (c : OComp S α) (k : α → OComp S β) :
    detG ok g (c.bind k) = (detG ok g c).bind fun a => detG ok g (k a) := by
  induction c with
  | pure b => rfl
  | query o q f ih =>
    show (if ok o q then detG ok g ((f (g o q)).bind k) else none) =
      (if ok o q then detG ok g (f (g o q)) else none).bind fun a => detG ok g (k a)
    by_cases h : ok o q = true
    · rw [if_pos h, if_pos h]
      exact ih _
    · rw [if_neg h, if_neg h]
      rfl
  | sample n f ih => exact ih _

end Gen

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **At a leaf of the request tree the test is the test on the length.** -/
theorem okJ_rleaf (P : PageJ L K) (q : Bits) :
    okJ P .rleaf q = decide (q.length = 256 + 8 * P.sR + 64) := by
  show (codeJ P .rleaf q (0 : Fin 1)).isSome = _
  show ((rleafCall P.cfg P.sR q).map strOf).isSome = _
  unfold rleafCall
  by_cases h : q.length = 256 + 8 * P.sR + 64
  · rw [if_pos h, decide_eq_true h]
    rfl
  · rw [if_neg h, decide_eq_false h]
    rfl

section V
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout 256 K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q)

/-- What the test of `rsalt` says. -/
theorem rsaltFit_iff (sR : ℕ) :
    rsaltFit sR depthReq π = true ↔
      π.rsalt.length = 8 * sR + 64 ∧
        π.rsalt.drop (8 * sR) = bytesToBits (Fmt.u64n (2 ^ depthReq + π.slot)) := by
  unfold rsaltFit
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]

/-- **Under every family: a yes behind the test gives the test's yes and a yes of `verifyOneProtocol`.** -/
theorem verifyBSR_det (sR : ℕ) (g : Fam (typedOracleFamily 256 K L))
    (h : (verifyBSR sR sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true) :
    rsaltFit sR depthReq π = true ∧
      (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true := by
  unfold verifyBSR at h
  by_cases e : rsaltFit sR depthReq π = true
  · rw [if_pos e] at h
    exact ⟨e, h⟩
  · rw [if_neg e] at h
    cases h

/-- **What a yes of `verifyGuard` is**: the test of `rsalt`, and the guarded run of `verifyOneProtocol` has
the value yes. -/
theorem verifyGuard_iff (P : PageJ L K) (O : ByteArray → ByteArray) :
    verifyGuard P O sMT sFS t Q wq embS embP xin embE depthReq cms x π = true ↔
      rsaltFit P.sR depthReq π = true ∧
        runGuard P O (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) = some true := by
  unfold verifyGuard verifyBSR
  by_cases e : rsaltFit P.sR depthReq π = true
  · rw [if_pos e]
    constructor
    · intro h
      refine ⟨e, ?_⟩
      cases r : runGuard P O (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) with
      | none =>
        rw [r] at h
        cases h
      | some b =>
        rw [r] at h
        exact congrArg some h
    · intro h
      rw [h.2]
      rfl
  · rw [if_neg e]
    constructor
    · intro h
      cases h
    · intro h
      exact absurd h.1 e

/-- A yes of `verifyGuard` is a yes of the plain run of `verifyOneProtocol` under the page's family. -/
theorem verifyGuard_yes (P : PageJ L K) (O : ByteArray → ByteArray)
    (h : verifyGuard P O sMT sFS t Q wq embS embP xin embE depthReq cms x π = true) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det (gJ P O) = true :=
  detG_det (S := typedOracleFamily 256 K L) (okJ P) (gJ P O) _
    ((verifyGuard_iff sMT sFS t Q wq embS embP xin embE depthReq cms x π P O).1 h).2

/-- **A yes of `verifyGuard` is a yes of `verifyOneProtocol` under every family that agrees with the page's
at the queries that `okJ P` passes.** No family but the page's own is shown to agree
so: at every first call of a chain that passes, such a family must answer zeros in the K
front blocks, as no drawn family and no encoding behind an escape does. -/
theorem verifyGuard_agree (P : PageJ L K) (O : ByteArray → ByteArray) (g : Fam (typedOracleFamily 256 K L))
    (hg : ∀ o q, okJ P o q = true → gJ P O o q = g o q)
    (h : verifyGuard P O sMT sFS t Q wq embS embP xin embE depthReq cms x π = true) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true :=
  detG_det_of_agree (S := typedOracleFamily 256 K L) (okJ P) hg _
    ((verifyGuard_iff sMT sFS t Q wq embS embP xin embE depthReq cms x π P O).1 h).2

/-- **At any other length of `rsalt`: no**, at every function O, whatever the run says. -/
theorem verifyGuard_no (P : PageJ L K) (O : ByteArray → ByteArray)
    (h : π.rsalt.length ≠ 8 * P.sR + 64) :
    verifyGuard P O sMT sFS t Q wq embS embP xin embE depthReq cms x π = false := by
  have e : rsaltFit P.sR depthReq π = false := by
    unfold rsaltFit
    rw [decide_eq_false h]
    rfl
  unfold verifyGuard verifyBSR
  rw [e]
  rfl

end V

/-- **The guard alone turns a leaf of another length away**: where the check in the request tree,
run so, has a value, and the path and the slot fit, the string behind the slot value has the one
length. -/
theorem reqCheck_guard (P : PageJ L K) (O : ByteArray → ByteArray) (depthReq : ℕ)
    (rtreq : Dig 256) (slot : ℕ) (path : List (Dig 256)) (c : Dig 256) (rs : Bits)
    (hp : path.length = depthReq ∧ slot < 2 ^ depthReq) {b : Bool}
    (h : runGuard P O (reqCheck (L := L) (K := K) depthReq rtreq slot path c rs) = some b) :
    rs.length = 8 * P.sR + 64 := by
  unfold reqCheck at h
  rw [if_pos hp] at h
  have h' : (if okJ P .rleaf (List.ofFn c ++ rs) then
      detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O)
        ((OComp.pure (gJ P O .rleaf (List.ofFn c ++ rs))).bind fun d =>
          (climbM rnodeV path slot d).bind fun r => pure (decide (r = rtreq)))
      else none) = some b := h
  by_cases e : okJ P .rleaf (List.ofFn c ++ rs) = true
  · rw [okJ_rleaf] at e
    have e' := of_decide_eq_true e
    rw [List.length_append, List.length_ofFn] at e'
    omega
  · rw [if_neg e] at h'
    cases h'

/-! ## The two holes as laws: the plain run does not see what the guarded run refuses -/

/-- A leaf of the request tree of another length has no string. -/
theorem codeJ_rleaf_none (P : PageJ L K) (q : Bits) (h : q.length ≠ 256 + 8 * P.sR + 64) :
    codeJ P .rleaf q (0 : Fin 1) = none := by
  show (rleafCall P.cfg P.sR q).map strOf = none
  unfold rleafCall
  rw [if_neg h]
  rfl

/-- **The hole at the request tree's leaf, under the plain run**: at a string behind the slot value
of another length the check's verdict is the same at every slot value. -/
theorem reqCheck_hole (P : PageJ L K) (O : ByteArray → ByteArray) (depthReq : ℕ) (rtreq : Dig 256)
    (slot : ℕ) (path : List (Dig 256)) (c c' : Dig 256) (rs : Bits)
    (hl : rs.length ≠ 8 * P.sR + 64) :
    (reqCheck (L := L) (K := K) depthReq rtreq slot path c rs).det (gJ P O) =
      (reqCheck (L := L) (K := K) depthReq rtreq slot path c' rs).det (gJ P O) := by
  have n : ∀ d : Dig 256, (List.ofFn d ++ rs).length ≠ 256 + 8 * P.sR + 64 := by
    intro d
    rw [List.length_append, List.length_ofFn]
    omega
  have e : gJ P O .rleaf (List.ofFn c ++ rs) = gJ P O .rleaf (List.ofFn c' ++ rs) := by
    show ansJ O (codeJ P .rleaf (List.ofFn c ++ rs) (0 : Fin 1)) =
      ansJ O (codeJ P .rleaf (List.ofFn c' ++ rs) (0 : Fin 1))
    rw [codeJ_rleaf_none P _ (n c), codeJ_rleaf_none P _ (n c')]
  unfold reqCheck
  by_cases hp : path.length = depthReq ∧ slot < 2 ^ depthReq
  · rw [if_pos hp, if_pos hp]
    show ((climbM rnodeV path slot (gJ P O .rleaf (List.ofFn c ++ rs))).bind fun r =>
        (pure (decide (r = rtreq)) : TypedOracleComputation 256 K L Bool)).det (gJ P O) =
      ((climbM rnodeV path slot (gJ P O .rleaf (List.ofFn c' ++ rs))).bind fun r =>
        (pure (decide (r = rtreq)) : TypedOracleComputation 256 K L Bool)).det (gJ P O)
    rw [e]
  · rw [if_neg hp, if_neg hp]

/-- **A hole at a tree's leaf, under the plain run**: two checks along one path to one root, at two
leaves for which the page writes no string, have one verdict, whatever the leaves hold. -/
theorem runCheck_hole (P : PageJ L K) (O : ByteArray → ByteArray) (c c' : Check 256 L)
    (hc : codeJ P .leaf c.inp (0 : Fin 1) = none) (hc' : codeJ P .leaf c'.inp (0 : Fin 1) = none)
    (hp : c.path = c'.path) (hj : c.j = c'.j) (hr : c.root = c'.root) :
    (runCheck (K := K) c).det (gJ P O) = (runCheck (K := K) c').det (gJ P O) := by
  have e : gJ P O .leaf c.inp = gJ P O .leaf c'.inp := by
    show ansJ O (codeJ P .leaf c.inp (0 : Fin 1)) = ansJ O (codeJ P .leaf c'.inp (0 : Fin 1))
    rw [hc, hc']
  show ((climbM TypedOracleCompiler.Compile.Batch.hashTreeNode c.path c.j (gJ P O .leaf c.inp)).bind fun r =>
      (pure (decide (r = c.root)) : TypedOracleComputation 256 K L Bool)).det (gJ P O) =
    ((climbM TypedOracleCompiler.Compile.Batch.hashTreeNode c'.path c'.j (gJ P O .leaf c'.inp)).bind fun r =>
      (pure (decide (r = c'.root)) : TypedOracleComputation 256 K L Bool)).det (gJ P O)
  rw [e, hp, hj, hr]

/-- **The guarded run refuses it**: where a check in a tree, run so, has a value, the page writes a
string for its leaf. The test of `rsalt` has no part in this. -/
theorem runCheck_guard (P : PageJ L K) (O : ByteArray → ByteArray) (c : Check 256 L) {b : Bool}
    (h : runGuard P O (runCheck (K := K) c) = some b) :
    (codeJ P .leaf c.inp (0 : Fin 1)).isSome = true := by
  have h' : (if okJ P .leaf c.inp then
      detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O)
        ((OComp.pure (gJ P O .leaf c.inp)).bind fun d =>
          (climbM TypedOracleCompiler.Compile.Batch.hashTreeNode c.path c.j d).bind fun r => pure (decide (r = c.root)))
      else none) = some b := h
  by_cases e : okJ P .leaf c.inp = true
  · exact e
  · rw [if_neg e] at h'
    cases h'

/-! ## The same at the routine by which `verifyOneProtocol` asks the leaves -/

/-- At a leaf without a string the page's family answers zeros. -/
theorem gJ_leaf_hole (P : PageJ L K) (O : ByteArray → ByteArray) (q : LeafIn L)
    (h : codeJ P .leaf q (0 : Fin 1) = none) : gJ P O .leaf q = fun _ => false := by
  show ansJ O (codeJ P .leaf q (0 : Fin 1)) = _
  rw [h]
  rfl

/-- **The hole under the plain run**: the digests of opened leaves without a string are zeros,
whatever the leaves hold. -/
theorem leavesV_hole (P : PageJ L K) (O : ByteArray → ByteArray) :
    ∀ es : List (ℕ × Check 256 L), (∀ e ∈ es, codeJ P .leaf e.2.inp (0 : Fin 1) = none) →
      (leavesV (K := K) es).det (gJ P O) = es.map fun _ => (fun _ => false : Dig 256)
  | [], _ => rfl
  | e :: es, h => by
    show ((leavesV (K := K) es).bind fun r =>
      (pure (gJ P O .leaf e.2.inp :: r) : TypedOracleComputation 256 K L (List (Dig 256)))).det (gJ P O) = _
    rw [OComp.det_bind, leavesV_hole P O es fun x hx => h x (List.mem_cons_of_mem _ hx),
      gJ_leaf_hole P O _ (h e List.mem_cons_self)]
    rfl

/-- **The guarded run refuses it**: where the leaves' digests, asked so, have a value, the page
writes a string for every one of the leaves. -/
theorem leavesV_guard (P : PageJ L K) (O : ByteArray → ByteArray) :
    ∀ (es : List (ℕ × Check 256 L)) {v : List (Dig 256)},
      runGuard P O (leavesV (K := K) es) = some v →
      ∀ e ∈ es, (codeJ P .leaf e.2.inp (0 : Fin 1)).isSome = true
  | [], _, _, _, he => by cases he
  | e :: es, v, h, e', he' => by
    have h' : (if okJ P .leaf e.2.inp then
        detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O)
          ((leavesV (K := K) es).bind fun r =>
            (pure (gJ P O .leaf e.2.inp :: r) : TypedOracleComputation 256 K L (List (Dig 256))))
        else none) = some v := h
    by_cases k : okJ P .leaf e.2.inp = true
    · rw [if_pos k, detG_bind] at h'
      cases r : detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O) (leavesV (K := K) es) with
      | none =>
        rw [r] at h'
        cases h'
      | some w =>
        rcases List.mem_cons.1 he' with rfl | hm
        · exact k
        · exact leavesV_guard P O es r e' hm
    · rw [if_neg k] at h'
      cases h'

/-- **So where the joint check of a forest, run so, has a value, every opened leaf has a string.**
The test of `rsalt` has no part in this. -/
theorem runForest_guard (P : PageJ L K) (O : ByteArray → ByteArray) (F : Forest 256 L)
    (s : List (Dig 256)) {b : Bool} (h : runGuard P O (runForest (K := K) F s) = some b) :
    ∀ e ∈ F.cs, (codeJ P .leaf e.2.inp (0 : Fin 1)).isSome = true := by
  have h' : detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O)
      ((leavesV (K := K) F.cs).bind fun v =>
        (Octopus.octC TypedOracleCompiler.Compile.Batch.hashTreeNode F.depth F.idx v s).bind fun out =>
          (pure (((Octopus.upN F.depth F.idx).zip out).all fun m =>
            decide (m.2 = F.treeRoot m.1)) : TypedOracleComputation 256 K L Bool)) = some b := h
  rw [detG_bind] at h'
  cases r : detG (S := typedOracleFamily 256 K L) (okJ P) (gJ P O) (leavesV (K := K) F.cs) with
  | none =>
    rw [r] at h'
    cases h'
  | some w => exact leavesV_guard P O F.cs r

end OnBytes.Maker.Page

#print axioms OnBytes.Maker.Page.detG_det
#print axioms OnBytes.Maker.Page.detG_congr
#print axioms OnBytes.Maker.Page.detG_det_of_agree
#print axioms OnBytes.Maker.Page.detG_bind
#print axioms OnBytes.Maker.Page.okJ_rleaf
#print axioms OnBytes.Maker.Page.rsaltFit_iff
#print axioms OnBytes.Maker.Page.verifyBSR_det
#print axioms OnBytes.Maker.Page.verifyGuard_iff
#print axioms OnBytes.Maker.Page.verifyGuard_yes
#print axioms OnBytes.Maker.Page.verifyGuard_agree
#print axioms OnBytes.Maker.Page.verifyGuard_no
#print axioms OnBytes.Maker.Page.reqCheck_guard
#print axioms OnBytes.Maker.Page.reqCheck_hole
#print axioms OnBytes.Maker.Page.runCheck_hole
#print axioms OnBytes.Maker.Page.runCheck_guard
#print axioms OnBytes.Maker.Page.detG_eq_asked
#print axioms OnBytes.Maker.Page.leavesV_hole
#print axioms OnBytes.Maker.Page.leavesV_guard
#print axioms OnBytes.Maker.Page.runForest_guard
